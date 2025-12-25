//! # SPHINCS+ Keystore Pallet
//!
//! Stores the mapping from AccountId32 (32-byte hash) to full SPHINCS+ public keys (64 bytes).
//!
//! ## Purpose
//!
//! SPHINCS+ public keys are 64 bytes, but Substrate's AccountId32 is only 32 bytes.
//! The AccountId is derived from the public key via: `Keccak-256(sphincs_public_key) → AccountId32`
//!
//! This pallet stores the reverse mapping so that signature verification can retrieve
//! the full 64-byte public key from the AccountId32.
//!
//! ## Usage
//!
//! 1. When a transaction is submitted, the extrinsic includes the full SPHINCS+ public key
//! 2. The runtime automatically registers the key mapping if not present
//! 3. MultiSignature::verify() queries this pallet to get the full public key
//! 4. Signature verification proceeds with the correct 64-byte public key
//!
//! ## Security
//!
//! - Keys are immutable once registered (prevent key replacement attacks)
//! - Only the account owner can register their key (via signed extrinsic)
//! - The AccountId MUST match Keccak-256(public_key) for registration

#![cfg_attr(not(feature = "std"), no_std)]

pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {
    use frame_support::pallet_prelude::*;
    use frame_support::BoundedVec;
    use frame_system::pallet_prelude::*;
    use codec::{Encode, Decode, DecodeWithMemTracking, MaxEncodedLen};
    use scale_info::TypeInfo;
    use sp_core::{sphincs::Public as SphincsPublic, H256};
    use sp_core::ConstU32;
    use sp_runtime::traits::{IdentifyAccount, SaturatedConversion};
    use sp_runtime::{AccountId32, MultiSigner};
    use sp_std::vec::Vec;

    #[pallet::pallet]
    pub struct Pallet<T>(_);

    #[pallet::config]
    pub trait Config: frame_system::Config<AccountId = AccountId32> {}

    /// Mapping from AccountId32 → SPHINCS+ Public Key (64 bytes)
    ///
    /// Storage: StorageMap
    /// Key: AccountId32 (32 bytes) - Keccak-256 hash of public key
    /// Value: SphincsPublic (64 bytes) - Full SPHINCS+ public key
    /// Maximum length for HSM key IDs (128 bytes should be enough for any HSM)
    pub type MaxHsmKeyIdLen = ConstU32<128>;

    /// HSM anchor status for a public key
    #[derive(Clone, Debug, Encode, Decode, TypeInfo, PartialEq, Eq, MaxEncodedLen)]
    pub struct HsmAnchorStatus {
        /// Whether the key has been anchored to HSM
        pub anchored: bool,
        /// HSM key identifier (if anchored)
        pub hsm_key_id: Option<BoundedVec<u8, MaxHsmKeyIdLen>>,
        /// Timestamp of last HSM sync
        pub last_sync: u64,
    }

    impl Default for HsmAnchorStatus {
        fn default() -> Self {
            Self {
                anchored: false,
                hsm_key_id: None,
                last_sync: 0,
            }
        }
    }

    #[pallet::storage]
    #[pallet::getter(fn public_key)]
    pub type PublicKeys<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        AccountId32,
        SphincsPublic,
        OptionQuery,
    >;

    /// HSM anchoring status for each registered key
    #[pallet::storage]
    #[pallet::getter(fn hsm_anchor_status)]
    pub type HsmAnchors<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        AccountId32,
        HsmAnchorStatus,
        ValueQuery,
    >;

    #[pallet::event]
    #[pallet::generate_deposit(pub(super) fn deposit_event)]
    pub enum Event<T: Config> {
        /// SPHINCS+ public key registered for an account
        KeyRegistered {
            account: AccountId32,
            public_key_hash: H256,
        },
        /// Key has been anchored to HSM
        KeyAnchoredToHsm {
            account: AccountId32,
            hsm_key_id: Vec<u8>,
        },
    }

    #[pallet::error]
    pub enum Error<T> {
        /// The provided public key doesn't match the AccountId
        /// (AccountId must be Keccak-256(public_key))
        PublicKeyMismatch,
        /// The account already has a registered public key
        KeyAlreadyRegistered,
        /// The key is not registered for this account
        KeyNotRegistered,
        /// The HSM key ID is too long (max 128 bytes)
        HsmKeyIdTooLong,
    }

    #[pallet::call]
    impl<T: Config> Pallet<T> {
        /// Register a SPHINCS+ public key for an account
        ///
        /// This is typically called automatically when submitting a transaction,
        /// but can also be called explicitly to pre-register a key.
        ///
        /// # Security
        ///
        /// - The account_id MUST equal Keccak-256(public_key)
        /// - Keys are immutable once registered (prevents key replacement attacks)
        #[pallet::call_index(0)]
        #[pallet::weight(Weight::from_parts(10_000, 0))]
        pub fn register_key(
            origin: OriginFor<T>,
            public_key: SphincsPublic,
        ) -> DispatchResult {
            let who = ensure_signed(origin)?;

            // Verify the public key matches the account ID
            let derived_account = Self::derive_account_id(&public_key);
            ensure!(
                who == derived_account,
                Error::<T>::PublicKeyMismatch
            );

            // Check if already registered (keys are immutable)
            ensure!(
                !PublicKeys::<T>::contains_key(&who),
                Error::<T>::KeyAlreadyRegistered
            );

            // Store the mapping
            PublicKeys::<T>::insert(&who, public_key);

            // Emit event
            let key_hash = sp_io::hashing::keccak_256(public_key.as_ref());
            Self::deposit_event(Event::KeyRegistered {
                account: who,
                public_key_hash: H256::from(key_hash),
            });

            Ok(())
        }

        /// Mark a key as anchored to HSM (privileged operation)
        ///
        /// This should be called by an off-chain worker or authorized service
        /// after successfully storing the key in the HSM.
        ///
        /// # Arguments
        /// * `account` - The account whose key was anchored
        /// * `hsm_key_id` - The HSM's identifier for the stored key
        #[pallet::call_index(1)]
        #[pallet::weight(Weight::from_parts(10_000, 0))]
        pub fn mark_hsm_anchored(
            origin: OriginFor<T>,
            account: AccountId32,
            hsm_key_id: Vec<u8>,
        ) -> DispatchResult {
            // Only root can mark keys as anchored (called by offchain worker)
            ensure_root(origin)?;

            // Verify the key exists
            ensure!(
                PublicKeys::<T>::contains_key(&account),
                Error::<T>::KeyNotRegistered
            );

            // Convert to BoundedVec
            let bounded_key_id = BoundedVec::<u8, MaxHsmKeyIdLen>::try_from(hsm_key_id.clone())
                .map_err(|_| Error::<T>::HsmKeyIdTooLong)?;

            // Get current timestamp (block number as proxy)
            let now = <frame_system::Pallet<T>>::block_number().saturated_into::<u64>();

            // Update HSM anchor status
            let status = HsmAnchorStatus {
                anchored: true,
                hsm_key_id: Some(bounded_key_id),
                last_sync: now,
            };
            HsmAnchors::<T>::insert(&account, status);

            // Emit event
            Self::deposit_event(Event::KeyAnchoredToHsm {
                account,
                hsm_key_id,
            });

            Ok(())
        }
    }

    impl<T: Config> Pallet<T> {
        /// Derive AccountId32 from SPHINCS+ public key
        ///
        /// Uses the same method as MultiSigner::into_account()
        pub fn derive_account_id(public_key: &SphincsPublic) -> AccountId32 {
            let signer = MultiSigner::SphincsPlus(*public_key);
            signer.into_account()
        }

        /// Get the full SPHINCS+ public key for an account
        ///
        /// Returns None if the account hasn't registered a key yet
        pub fn get_public_key(account: &AccountId32) -> Option<SphincsPublic> {
            PublicKeys::<T>::get(account)
        }

        /// Auto-register a public key (called by transaction pool)
        ///
        /// This is used when processing extrinsics to automatically register
        /// the sender's public key if not already present.
        pub fn auto_register(account: &AccountId32, public_key: SphincsPublic) -> DispatchResult {
            // Verify the public key matches the account ID
            let derived_account = Self::derive_account_id(&public_key);
            ensure!(
                *account == derived_account,
                Error::<T>::PublicKeyMismatch
            );

            // Only register if not already present
            if !PublicKeys::<T>::contains_key(account) {
                PublicKeys::<T>::insert(account, public_key);

                let key_hash = sp_io::hashing::keccak_256(public_key.as_ref());
                Self::deposit_event(Event::KeyRegistered {
                    account: account.clone(),
                    public_key_hash: H256::from(key_hash),
                });
            }

            Ok(())
        }
    }

    /// SignedExtension for auto-registering SPHINCS+ public keys
    ///
    /// This extension runs during transaction pool validation and automatically
    /// registers the sender's SPHINCS+ public key if not already present.
    ///
    /// ## How it works:
    ///
    /// 1. When a transaction is submitted, `validate()` is called
    /// 2. It extracts the SPHINCS+ public key from the signature
    /// 3. It calls `Pallet::auto_register()` to store the key mapping
    /// 4. Subsequent signature verifications can retrieve the full 64-byte key
    ///
    /// ## Integration:
    ///
    /// Add to runtime's `SignedExtra` tuple:
    /// ```ignore
    /// pub type SignedExtra = (
    ///     // ... other extensions
    ///     pallet_sphincs_keystore::AutoRegisterKey<Runtime>,
    /// );
    /// ```
    #[derive(Encode, Decode, DecodeWithMemTracking, Clone, Eq, PartialEq, TypeInfo)]
    #[scale_info(skip_type_params(T))]
    pub struct AutoRegisterKey<T: Config + Send + Sync>(core::marker::PhantomData<T>);

    impl<T: Config + Send + Sync> core::fmt::Debug for AutoRegisterKey<T> {
        fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
            write!(f, "AutoRegisterKey")
        }
    }

    impl<T: Config + Send + Sync> AutoRegisterKey<T> {
        pub fn new() -> Self {
            Self(Default::default())
        }
    }

    impl<T: Config + Send + Sync> sp_runtime::traits::SignedExtension for AutoRegisterKey<T>
    where
        T::RuntimeCall: sp_runtime::traits::Dispatchable<Info = frame_support::dispatch::DispatchInfo>,
    {
        type AccountId = AccountId32;
        type Call = T::RuntimeCall;
        type AdditionalSigned = ();
        type Pre = ();
        const IDENTIFIER: &'static str = "AutoRegisterKey";

        fn additional_signed(&self) -> Result<Self::AdditionalSigned, sp_runtime::transaction_validity::TransactionValidityError> {
            Ok(())
        }

        fn pre_dispatch(
            self,
            _who: &Self::AccountId,
            _call: &Self::Call,
            _info: &frame_support::dispatch::DispatchInfo,
            _len: usize,
        ) -> Result<Self::Pre, sp_runtime::transaction_validity::TransactionValidityError> {
            // In pre_dispatch, we don't have access to the public key
            // The actual registration happens in validate() before this
            Ok(())
        }

        fn validate(
            &self,
            _who: &Self::AccountId,
            _call: &Self::Call,
            _info: &frame_support::dispatch::DispatchInfo,
            _len: usize,
        ) -> sp_runtime::transaction_validity::TransactionValidity {
            // Note: At this point, the signature has already been verified
            // by CheckNonZeroSender and other extensions. We just need to
            // register the key mapping if it doesn't exist.
            //
            // However, we don't have direct access to the public key here.
            // The key is embedded in the extrinsic signature and already
            // verified by the core runtime.
            //
            // For SPHINCS+ support, the integration needs to happen at a
            // lower level in the signature verification process, or we need
            // to extract the key from the transaction format itself.
            //
            // For now, this extension serves as a placeholder and documentation
            // of the intended integration point. The actual auto-registration
            // should be called from:
            //
            // 1. Custom transaction format that includes the public key
            // 2. Modified signature verification that calls auto_register()
            // 3. Client-side explicit registration before first transaction

            // Return valid - no additional validation needed
            Ok(sp_runtime::transaction_validity::ValidTransaction::default())
        }
    }

    /// Genesis configuration
    #[pallet::genesis_config]
    pub struct GenesisConfig<T: Config> {
        /// Initial public keys to register
        pub keys: Vec<(AccountId32, SphincsPublic)>,
        #[serde(skip)]
        pub _phantom: core::marker::PhantomData<T>,
    }

    impl<T: Config> Default for GenesisConfig<T> {
        fn default() -> Self {
            Self {
                keys: Vec::new(),
                _phantom: Default::default(),
            }
        }
    }

    #[pallet::genesis_build]
    impl<T: Config> BuildGenesisConfig for GenesisConfig<T> {
        fn build(&self) {
            for (account, public_key) in &self.keys {
                // Verify the mapping is correct
                let derived = Pallet::<T>::derive_account_id(public_key);
                if *account != derived {
                    panic!(
                        "Genesis config error: AccountId {:?} doesn't match public key {:?}",
                        account, public_key
                    );
                }

                PublicKeys::<T>::insert(account, public_key);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use frame_support::{assert_err, assert_ok, parameter_types, traits::BuildGenesisConfig};
    use sp_core::{sphincs::Pair as SphincsPair, H256, Pair};
    use sp_runtime::{
        traits::{BlakeTwo256, IdentifyAccount, IdentityLookup},
        AccountId32, BuildStorage, MultiSigner,
    };

    // Configure a mock runtime for testing
    type Block = frame_system::mocking::MockBlock<Test>;

    frame_support::construct_runtime!(
        pub enum Test
        {
            System: frame_system,
            SphincsKeystore: crate,
        }
    );

    parameter_types! {
        pub const BlockHashCount: u64 = 250;
    }

    impl frame_system::Config for Test {
        type BaseCallFilter = frame_support::traits::Everything;
        type BlockWeights = ();
        type BlockLength = ();
        type DbWeight = ();
        type RuntimeOrigin = RuntimeOrigin;
        type RuntimeCall = RuntimeCall;
        type Nonce = u64;
        type Hash = sp_core::H256;
        type Hashing = BlakeTwo256;
        type AccountId = AccountId32;
        type Lookup = IdentityLookup<Self::AccountId>;
        type Block = Block;
        type RuntimeEvent = RuntimeEvent;
        type BlockHashCount = BlockHashCount;
        type Version = ();
        type PalletInfo = PalletInfo;
        type AccountData = ();
        type OnNewAccount = ();
        type OnKilledAccount = ();
        type SystemWeightInfo = ();
        type SS58Prefix = ();
        type OnSetCode = ();
        type MaxConsumers = frame_support::traits::ConstU32<16>;
        type RuntimeTask = ();
        type ExtensionsWeightInfo = ();
        type SingleBlockMigrations = ();
        type MultiBlockMigrator = ();
        type PreInherents = ();
        type PostInherents = ();
        type PostTransactions = ();
    }

    impl Config for Test {}

    // Helper function to create a new test environment
    fn new_test_ext() -> sp_io::TestExternalities {
        let t = frame_system::GenesisConfig::<Test>::default()
            .build_storage()
            .unwrap();
        let mut ext = sp_io::TestExternalities::new(t);
        ext.execute_with(|| System::set_block_number(1));
        ext
    }

    #[test]
    fn test_register_key_success() {
        new_test_ext().execute_with(|| {
            // Generate a SPHINCS+ keypair
            let (pair, _seed) = SphincsPair::generate();
            let public_key = pair.public();

            // Derive the account ID
            let account = Pallet::<Test>::derive_account_id(&public_key);

            // Register the key
            assert_ok!(SphincsKeystore::register_key(
                RuntimeOrigin::signed(account.clone()),
                public_key
            ));

            // Verify the key is stored
            assert_eq!(
                SphincsKeystore::public_key(&account),
                Some(public_key)
            );

            // Verify event was emitted
            System::assert_has_event(
                Event::KeyRegistered {
                    account: account.clone(),
                    public_key_hash: H256::from(sp_io::hashing::keccak_256(public_key.as_ref())),
                }
                .into(),
            );
        });
    }

    #[test]
    fn test_register_key_mismatch() {
        new_test_ext().execute_with(|| {
            // Generate two different keypairs
            let (pair1, _) = SphincsPair::generate();
            let (pair2, _) = SphincsPair::generate();

            let public_key1 = pair1.public();
            let account2 = Pallet::<Test>::derive_account_id(&pair2.public());

            // Try to register key1 with account2 (should fail)
            assert_err!(
                SphincsKeystore::register_key(
                    RuntimeOrigin::signed(account2),
                    public_key1
                ),
                Error::<Test>::PublicKeyMismatch
            );
        });
    }

    #[test]
    fn test_register_key_already_registered() {
        new_test_ext().execute_with(|| {
            // Generate a keypair
            let (pair, _) = SphincsPair::generate();
            let public_key = pair.public();
            let account = Pallet::<Test>::derive_account_id(&public_key);

            // Register the key first time
            assert_ok!(SphincsKeystore::register_key(
                RuntimeOrigin::signed(account.clone()),
                public_key
            ));

            // Try to register again (should fail)
            assert_err!(
                SphincsKeystore::register_key(
                    RuntimeOrigin::signed(account),
                    public_key
                ),
                Error::<Test>::KeyAlreadyRegistered
            );
        });
    }

    #[test]
    fn test_auto_register_success() {
        new_test_ext().execute_with(|| {
            // Generate a keypair
            let (pair, _) = SphincsPair::generate();
            let public_key = pair.public();
            let account = Pallet::<Test>::derive_account_id(&public_key);

            // Auto-register the key
            assert_ok!(Pallet::<Test>::auto_register(&account, public_key));

            // Verify the key is stored
            assert_eq!(SphincsKeystore::public_key(&account), Some(public_key));
        });
    }

    #[test]
    fn test_auto_register_idempotent() {
        new_test_ext().execute_with(|| {
            // Generate a keypair
            let (pair, _) = SphincsPair::generate();
            let public_key = pair.public();
            let account = Pallet::<Test>::derive_account_id(&public_key);

            // Auto-register twice (should not error)
            assert_ok!(Pallet::<Test>::auto_register(&account, public_key));
            assert_ok!(Pallet::<Test>::auto_register(&account, public_key));

            // Verify the key is still stored correctly
            assert_eq!(SphincsKeystore::public_key(&account), Some(public_key));
        });
    }

    #[test]
    fn test_auto_register_mismatch() {
        new_test_ext().execute_with(|| {
            // Generate two keypairs
            let (pair1, _) = SphincsPair::generate();
            let (pair2, _) = SphincsPair::generate();

            let public_key1 = pair1.public();
            let account2 = Pallet::<Test>::derive_account_id(&pair2.public());

            // Try to auto-register with mismatched account (should fail)
            assert_err!(
                Pallet::<Test>::auto_register(&account2, public_key1),
                Error::<Test>::PublicKeyMismatch
            );
        });
    }

    #[test]
    fn test_get_public_key() {
        new_test_ext().execute_with(|| {
            // Generate a keypair
            let (pair, _) = SphincsPair::generate();
            let public_key = pair.public();
            let account = Pallet::<Test>::derive_account_id(&public_key);

            // Initially no key
            assert_eq!(Pallet::<Test>::get_public_key(&account), None);

            // Register the key
            assert_ok!(SphincsKeystore::register_key(
                RuntimeOrigin::signed(account.clone()),
                public_key
            ));

            // Now key should be retrievable
            assert_eq!(
                Pallet::<Test>::get_public_key(&account),
                Some(public_key)
            );
        });
    }

    #[test]
    fn test_derive_account_id_consistency() {
        new_test_ext().execute_with(|| {
            // Generate a keypair
            let (pair, _) = SphincsPair::generate();
            let public_key = pair.public();

            // Derive account ID using pallet method
            let account1 = Pallet::<Test>::derive_account_id(&public_key);

            // Derive using MultiSigner directly
            let signer = MultiSigner::SphincsPlus(public_key);
            let account2 = signer.into_account();

            // Should be identical
            assert_eq!(account1, account2);
        });
    }

    #[test]
    fn test_genesis_config() {
        // Generate test keypairs
        let (pair1, _) = SphincsPair::generate();
        let (pair2, _) = SphincsPair::generate();

        let public_key1 = pair1.public();
        let public_key2 = pair2.public();

        let account1 = Pallet::<Test>::derive_account_id(&public_key1);
        let account2 = Pallet::<Test>::derive_account_id(&public_key2);

        // Create genesis config with initial keys
        let genesis_config = GenesisConfig::<Test> {
            keys: vec![(account1.clone(), public_key1), (account2.clone(), public_key2)],
            _phantom: Default::default(),
        };

        let t = frame_system::GenesisConfig::<Test>::default()
            .build_storage()
            .unwrap();

        let mut ext = sp_io::TestExternalities::new(t);
        ext.execute_with(|| {
            genesis_config.build();

            // Verify both keys are registered
            assert_eq!(SphincsKeystore::public_key(&account1), Some(public_key1));
            assert_eq!(SphincsKeystore::public_key(&account2), Some(public_key2));
        });
    }

    #[test]
    #[should_panic(expected = "Genesis config error")]
    fn test_genesis_config_invalid_mapping() {
        // Generate test keypairs
        let (pair1, _) = SphincsPair::generate();
        let (pair2, _) = SphincsPair::generate();

        let public_key1 = pair1.public();
        let account2 = Pallet::<Test>::derive_account_id(&pair2.public());

        // Create genesis config with INVALID mapping (account2 with key1)
        let genesis_config = GenesisConfig::<Test> {
            keys: vec![(account2, public_key1)],
            _phantom: Default::default(),
        };

        let t = frame_system::GenesisConfig::<Test>::default()
            .build_storage()
            .unwrap();

        let mut ext = sp_io::TestExternalities::new(t);
        ext.execute_with(|| {
            // This should panic
            genesis_config.build();
        });
    }

    #[test]
    fn test_sphincs_signature_verification() {
        new_test_ext().execute_with(|| {
            // Generate a SPHINCS+ keypair
            let (pair, _seed) = SphincsPair::generate();
            let public_key = pair.public();
            let account = Pallet::<Test>::derive_account_id(&public_key);

            // Register the key
            assert_ok!(SphincsKeystore::register_key(
                RuntimeOrigin::signed(account.clone()),
                public_key
            ));

            // Create a message to sign
            let message = b"Hello, quantum world!";

            // Sign the message with SPHINCS+
            let signature = pair.sign(message);

            // Verify the signature
            use sp_core::Pair;
            assert!(SphincsPair::verify(&signature, message, &public_key));

            // Verify that the stored key matches
            let retrieved_key = Pallet::<Test>::get_public_key(&account);
            assert_eq!(retrieved_key, Some(public_key));

            // Verify signature with retrieved key
            assert!(SphincsPair::verify(&signature, message, &retrieved_key.unwrap()));
        });
    }

    #[test]
    fn test_multiple_signatures_same_key() {
        new_test_ext().execute_with(|| {
            // Generate a keypair
            let (pair, _) = SphincsPair::generate();
            let public_key = pair.public();
            let account = Pallet::<Test>::derive_account_id(&public_key);

            // Register the key
            assert_ok!(SphincsKeystore::register_key(
                RuntimeOrigin::signed(account.clone()),
                public_key
            ));

            // Sign multiple messages
            let messages = vec![
                b"First message".to_vec(),
                b"Second message".to_vec(),
                b"Third message with different length".to_vec(),
            ];

            use sp_core::Pair;
            for msg in &messages {
                let signature = pair.sign(msg);
                assert!(SphincsPair::verify(&signature, msg, &public_key));
            }
        });
    }

    #[test]
    fn test_signature_verification_failure() {
        new_test_ext().execute_with(|| {
            // Generate two different keypairs
            let (pair1, _) = SphincsPair::generate();
            let (pair2, _) = SphincsPair::generate();

            let public_key1 = pair1.public();
            let public_key2 = pair2.public();

            // Sign message with pair1
            let message = b"Test message";
            let signature1 = pair1.sign(message);

            use sp_core::Pair;
            // Verify with correct public key (should pass)
            assert!(SphincsPair::verify(&signature1, message, &public_key1));

            // Verify with wrong public key (should fail)
            assert!(!SphincsPair::verify(&signature1, message, &public_key2));

            // Verify with wrong message (should fail)
            let wrong_message = b"Different message";
            assert!(!SphincsPair::verify(&signature1, wrong_message, &public_key1));
        });
    }

    #[test]
    fn test_hsm_anchoring() {
        new_test_ext().execute_with(|| {
            // Generate a keypair
            let (pair, _) = SphincsPair::generate();
            let public_key = pair.public();
            let account = Pallet::<Test>::derive_account_id(&public_key);

            // Register the key
            assert_ok!(SphincsKeystore::register_key(
                RuntimeOrigin::signed(account.clone()),
                public_key
            ));

            // Initially not anchored
            let status = SphincsKeystore::hsm_anchor_status(&account);
            assert!(!status.anchored);
            assert_eq!(status.hsm_key_id, None);

            // Anchor to HSM (as root)
            let hsm_key_id = b"hsm-key-12345".to_vec();
            assert_ok!(SphincsKeystore::mark_hsm_anchored(
                RuntimeOrigin::root(),
                account.clone(),
                hsm_key_id.clone()
            ));

            // Verify anchored status
            let status = SphincsKeystore::hsm_anchor_status(&account);
            assert!(status.anchored);
            assert_eq!(status.hsm_key_id.as_ref().map(|v| v.to_vec()), Some(hsm_key_id));
            assert!(status.last_sync > 0);
        });
    }

    #[test]
    fn test_hsm_anchoring_key_not_registered() {
        new_test_ext().execute_with(|| {
            // Generate a keypair but don't register it
            let (pair, _) = SphincsPair::generate();
            let public_key = pair.public();
            let account = Pallet::<Test>::derive_account_id(&public_key);

            // Try to anchor without registering (should fail)
            let hsm_key_id = b"hsm-key-12345".to_vec();
            assert_err!(
                SphincsKeystore::mark_hsm_anchored(
                    RuntimeOrigin::root(),
                    account,
                    hsm_key_id
                ),
                Error::<Test>::KeyNotRegistered
            );
        });
    }
}
