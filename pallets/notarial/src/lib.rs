//! # Notarial Pallet
//!
//! On-chain notarization and timestamped document attestation.
//! Provides cryptographic proof of document existence at a specific time.
//!
//! ## Overview
//!
//! - Document attestation with timestamp
//! - Witness functionality (validators/trusted parties witness documents)
//! - Certificate generation
//! - Proof of existence verification
//! - Revocation capability
//!
//! ## Use Cases
//!
//! - Academic credential verification
//! - Contract timestamp certification
//! - Intellectual property timestamping
//! - Compliance documentation
//! - Legal document notarization

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(test)]
mod mock;

#[cfg(test)]
mod tests;

pub mod runtime_api;

pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {
    use frame_support::{
        pallet_prelude::*,
        traits::Get,
    };
    use frame_system::pallet_prelude::*;
    use sp_std::vec::Vec;

    /// Maximum description length
    pub const MAX_DESCRIPTION_LENGTH: u32 = 512;
    /// Maximum witnesses per attestation
    pub const MAX_WITNESSES: u32 = 10;
    /// Maximum tags per attestation
    pub const MAX_TAGS: u32 = 10;
    /// Maximum tag length
    pub const MAX_TAG_LENGTH: u32 = 32;

    /// Configure the pallet
    #[pallet::config]
    pub trait Config: frame_system::Config {
        /// The overarching event type
        type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

        /// Minimum witnesses required for certified attestation
        #[pallet::constant]
        type MinWitnesses: Get<u32>;

        /// Validity period for attestations (in blocks, 0 = permanent)
        #[pallet::constant]
        type DefaultValidityPeriod: Get<BlockNumberFor<Self>>;
    }

    #[pallet::pallet]
    pub struct Pallet<T>(_);

    /// Attestation status
    #[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, TypeInfo, MaxEncodedLen, Default)]
    pub enum AttestationStatus {
        /// Active and valid
        #[default]
        Active,
        /// Revoked by owner
        Revoked,
        /// Expired
        Expired,
        /// Certified (enough witnesses)
        Certified,
    }

    /// Document category
    #[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, TypeInfo, MaxEncodedLen, Default, Copy)]
    pub enum DocumentCategory {
        /// Academic credential (diploma, certificate)
        AcademicCredential = 0,
        /// Legal document
        LegalDocument = 1,
        /// Contract
        Contract = 2,
        /// Intellectual property
        IntellectualProperty = 3,
        /// Identity document
        Identity = 4,
        /// Financial record
        Financial = 5,
        /// Medical record
        Medical = 6,
        /// Custom/other
        #[default]
        Other = 7,
    }

    impl From<u8> for DocumentCategory {
        fn from(value: u8) -> Self {
            match value {
                0 => DocumentCategory::AcademicCredential,
                1 => DocumentCategory::LegalDocument,
                2 => DocumentCategory::Contract,
                3 => DocumentCategory::IntellectualProperty,
                4 => DocumentCategory::Identity,
                5 => DocumentCategory::Financial,
                6 => DocumentCategory::Medical,
                _ => DocumentCategory::Other,
            }
        }
    }

    /// Witness record
    #[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
    #[scale_info(skip_type_params(T))]
    pub struct Witness<T: Config> {
        /// Witness account
        pub account: T::AccountId,
        /// Block when witnessed
        pub witnessed_at: BlockNumberFor<T>,
        /// Optional attestation note
        pub note_hash: Option<[u8; 32]>,
    }

    /// Document attestation
    #[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
    #[scale_info(skip_type_params(T))]
    pub struct Attestation<T: Config> {
        /// Unique attestation ID
        pub id: u64,
        /// Document hash (SHA-256 or similar)
        pub document_hash: [u8; 32],
        /// Category
        pub category: DocumentCategory,
        /// Description (bounded)
        pub description: BoundedVec<u8, ConstU32<MAX_DESCRIPTION_LENGTH>>,
        /// Owner/attester
        pub attester: T::AccountId,
        /// Block when attested
        pub attested_at: BlockNumberFor<T>,
        /// Expiration block (None = permanent)
        pub expires_at: Option<BlockNumberFor<T>>,
        /// Status
        pub status: AttestationStatus,
        /// Number of witnesses
        pub witness_count: u32,
        /// Is certified (enough witnesses)
        pub certified: bool,
        /// Reference to related Ricardian contract
        pub contract_id: Option<u32>,
        /// Reference to academic program
        pub academic_id: Option<u32>,
    }

    /// Tag for categorization
    pub type Tag = BoundedVec<u8, ConstU32<MAX_TAG_LENGTH>>;

    /// Certificate generated for attestation
    #[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
    #[scale_info(skip_type_params(T))]
    pub struct Certificate<T: Config> {
        /// Certificate ID
        pub id: u64,
        /// Reference attestation
        pub attestation_id: u64,
        /// Generated at block
        pub generated_at: BlockNumberFor<T>,
        /// Certificate hash (for verification)
        pub certificate_hash: [u8; 32],
        /// Issuer
        pub issuer: T::AccountId,
    }

    // ==================== STORAGE ====================

    /// All attestations by ID
    #[pallet::storage]
    #[pallet::getter(fn attestations)]
    pub type Attestations<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        u64, // attestation_id
        Attestation<T>,
        OptionQuery,
    >;

    /// Next attestation ID
    #[pallet::storage]
    #[pallet::getter(fn next_attestation_id)]
    pub type NextAttestationId<T: Config> = StorageValue<_, u64, ValueQuery>;

    /// Attestation by document hash (for lookup)
    #[pallet::storage]
    #[pallet::getter(fn attestation_by_hash)]
    pub type AttestationByHash<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        [u8; 32], // document_hash
        u64, // attestation_id
        OptionQuery,
    >;

    /// Witnesses for attestation
    #[pallet::storage]
    #[pallet::getter(fn witnesses)]
    pub type Witnesses<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        u64, // attestation_id
        BoundedVec<Witness<T>, ConstU32<MAX_WITNESSES>>,
        ValueQuery,
    >;

    /// Tags for attestation
    #[pallet::storage]
    #[pallet::getter(fn tags)]
    pub type Tags<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        u64, // attestation_id
        BoundedVec<Tag, ConstU32<MAX_TAGS>>,
        ValueQuery,
    >;

    /// Attestations by owner
    #[pallet::storage]
    #[pallet::getter(fn attestations_by_owner)]
    pub type AttestationsByOwner<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        T::AccountId,
        BoundedVec<u64, ConstU32<1000>>,
        ValueQuery,
    >;

    /// Certificates
    #[pallet::storage]
    #[pallet::getter(fn certificates)]
    pub type Certificates<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        u64, // certificate_id
        Certificate<T>,
        OptionQuery,
    >;

    /// Next certificate ID
    #[pallet::storage]
    #[pallet::getter(fn next_certificate_id)]
    pub type NextCertificateId<T: Config> = StorageValue<_, u64, ValueQuery>;

    /// Trusted witnesses (validators or verified parties)
    #[pallet::storage]
    #[pallet::getter(fn trusted_witnesses)]
    pub type TrustedWitnesses<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        T::AccountId,
        bool,
        ValueQuery,
    >;

    // ==================== EVENTS ====================

    #[pallet::event]
    #[pallet::generate_deposit(pub(super) fn deposit_event)]
    pub enum Event<T: Config> {
        /// Document attested
        DocumentAttested {
            attestation_id: u64,
            document_hash: [u8; 32],
            attester: T::AccountId,
            category_id: u8,
        },
        /// Attestation witnessed
        AttestationWitnessed {
            attestation_id: u64,
            witness: T::AccountId,
            witness_count: u32,
        },
        /// Attestation certified (enough witnesses)
        AttestationCertified {
            attestation_id: u64,
            witness_count: u32,
        },
        /// Attestation revoked
        AttestationRevoked {
            attestation_id: u64,
            reason: Vec<u8>,
        },
        /// Certificate generated
        CertificateGenerated {
            certificate_id: u64,
            attestation_id: u64,
            certificate_hash: [u8; 32],
        },
        /// Trusted witness added
        TrustedWitnessAdded {
            witness: T::AccountId,
        },
        /// Trusted witness removed
        TrustedWitnessRemoved {
            witness: T::AccountId,
        },
        /// Tags added to attestation
        TagsAdded {
            attestation_id: u64,
            tags: Vec<Vec<u8>>,
        },
    }

    // ==================== ERRORS ====================

    #[pallet::error]
    pub enum Error<T> {
        /// Attestation not found
        AttestationNotFound,
        /// Document already attested
        AlreadyAttested,
        /// Not the owner
        NotOwner,
        /// Attestation revoked
        AttestationRevoked,
        /// Attestation expired
        AttestationExpired,
        /// Already witnessed
        AlreadyWitnessed,
        /// Max witnesses reached
        MaxWitnessesReached,
        /// Not a trusted witness
        NotTrustedWitness,
        /// Not certified
        NotCertified,
        /// Description too long
        DescriptionTooLong,
        /// Tag too long
        TagTooLong,
        /// Max tags reached
        MaxTagsReached,
        /// Certificate not found
        CertificateNotFound,
        /// Overflow error
        Overflow,
        /// Cannot witness own attestation
        CannotWitnessOwn,
    }

    // ==================== CALLS ====================

    #[pallet::call]
    impl<T: Config> Pallet<T> {
        /// Attest a document's existence at current block.
        ///
        /// Creates an immutable timestamp proof for the document hash.
        #[pallet::call_index(0)]
        #[pallet::weight(10_000)]
        /// category_id: 0=AcademicCredential, 1=LegalDocument, 2=Contract, 3=IntellectualProperty, 4=Identity, 5=Financial, 6=Medical, 7=Other
        pub fn attest_document(
            origin: OriginFor<T>,
            document_hash: [u8; 32],
            category_id: u8,
            description: Vec<u8>,
            validity_blocks: Option<BlockNumberFor<T>>,
            contract_id: Option<u32>,
            academic_id: Option<u32>,
        ) -> DispatchResult {
            let attester = ensure_signed(origin)?;
            let category: DocumentCategory = category_id.into();

            // Check not already attested
            ensure!(
                !AttestationByHash::<T>::contains_key(&document_hash),
                Error::<T>::AlreadyAttested
            );

            // Validate description
            let description_bounded: BoundedVec<u8, ConstU32<MAX_DESCRIPTION_LENGTH>> =
                description.try_into().map_err(|_| Error::<T>::DescriptionTooLong)?;

            let current_block = frame_system::Pallet::<T>::block_number();

            // Calculate expiration
            let expires_at = validity_blocks.map(|v| current_block + v)
                .or_else(|| {
                    let default_validity = T::DefaultValidityPeriod::get();
                    if default_validity > BlockNumberFor::<T>::from(0u32) {
                        Some(current_block + default_validity)
                    } else {
                        None // Permanent
                    }
                });

            // Create attestation
            let attestation_id = NextAttestationId::<T>::get();
            let next_id = attestation_id.checked_add(1).ok_or(Error::<T>::Overflow)?;
            NextAttestationId::<T>::put(next_id);

            let attestation = Attestation {
                id: attestation_id,
                document_hash,
                category: category.clone(),
                description: description_bounded,
                attester: attester.clone(),
                attested_at: current_block,
                expires_at,
                status: AttestationStatus::Active,
                witness_count: 0,
                certified: false,
                contract_id,
                academic_id,
            };

            Attestations::<T>::insert(attestation_id, attestation);
            AttestationByHash::<T>::insert(document_hash, attestation_id);

            // Add to owner's attestations
            AttestationsByOwner::<T>::try_mutate(&attester, |attestations| {
                attestations.try_push(attestation_id).map_err(|_| Error::<T>::Overflow)
            })?;

            Self::deposit_event(Event::DocumentAttested {
                attestation_id,
                document_hash,
                attester,
                category_id,
            });

            Ok(())
        }

        /// Witness an attestation.
        ///
        /// Trusted witnesses can vouch for document authenticity.
        #[pallet::call_index(1)]
        #[pallet::weight(10_000)]
        pub fn witness_attestation(
            origin: OriginFor<T>,
            attestation_id: u64,
            note_hash: Option<[u8; 32]>,
        ) -> DispatchResult {
            let witness_account = ensure_signed(origin)?;

            // Get attestation
            let mut attestation = Attestations::<T>::get(attestation_id)
                .ok_or(Error::<T>::AttestationNotFound)?;

            // Check status
            ensure!(
                attestation.status == AttestationStatus::Active ||
                attestation.status == AttestationStatus::Certified,
                Error::<T>::AttestationRevoked
            );

            // Check expiration
            if let Some(exp) = attestation.expires_at {
                let current_block = frame_system::Pallet::<T>::block_number();
                ensure!(current_block < exp, Error::<T>::AttestationExpired);
            }

            // Cannot witness own attestation
            ensure!(attestation.attester != witness_account, Error::<T>::CannotWitnessOwn);

            // Check not already witnessed by this account
            let witnesses = Witnesses::<T>::get(attestation_id);
            ensure!(
                !witnesses.iter().any(|w| w.account == witness_account),
                Error::<T>::AlreadyWitnessed
            );

            // Create witness record
            let witness = Witness {
                account: witness_account.clone(),
                witnessed_at: frame_system::Pallet::<T>::block_number(),
                note_hash,
            };

            // Add witness
            Witnesses::<T>::try_mutate(attestation_id, |witnesses| {
                witnesses.try_push(witness).map_err(|_| Error::<T>::MaxWitnessesReached)
            })?;

            // Update attestation
            attestation.witness_count = attestation.witness_count
                .checked_add(1)
                .ok_or(Error::<T>::Overflow)?;

            Self::deposit_event(Event::AttestationWitnessed {
                attestation_id,
                witness: witness_account,
                witness_count: attestation.witness_count,
            });

            // Check if now certified
            if attestation.witness_count >= T::MinWitnesses::get() && !attestation.certified {
                attestation.certified = true;
                attestation.status = AttestationStatus::Certified;

                Self::deposit_event(Event::AttestationCertified {
                    attestation_id,
                    witness_count: attestation.witness_count,
                });
            }

            Attestations::<T>::insert(attestation_id, attestation);

            Ok(())
        }

        /// Revoke an attestation.
        ///
        /// Only the original attester can revoke.
        #[pallet::call_index(2)]
        #[pallet::weight(10_000)]
        pub fn revoke_attestation(
            origin: OriginFor<T>,
            attestation_id: u64,
            reason: Vec<u8>,
        ) -> DispatchResult {
            let who = ensure_signed(origin)?;

            // Get attestation
            let mut attestation = Attestations::<T>::get(attestation_id)
                .ok_or(Error::<T>::AttestationNotFound)?;

            // Only owner can revoke
            ensure!(attestation.attester == who, Error::<T>::NotOwner);

            // Update status
            attestation.status = AttestationStatus::Revoked;
            Attestations::<T>::insert(attestation_id, attestation);

            Self::deposit_event(Event::AttestationRevoked {
                attestation_id,
                reason,
            });

            Ok(())
        }

        /// Generate a certificate for a certified attestation.
        #[pallet::call_index(3)]
        #[pallet::weight(10_000)]
        pub fn generate_certificate(
            origin: OriginFor<T>,
            attestation_id: u64,
        ) -> DispatchResult {
            let issuer = ensure_signed(origin)?;

            // Get attestation
            let attestation = Attestations::<T>::get(attestation_id)
                .ok_or(Error::<T>::AttestationNotFound)?;

            // Must be certified
            ensure!(attestation.certified, Error::<T>::NotCertified);

            // Check status
            ensure!(
                attestation.status == AttestationStatus::Certified,
                Error::<T>::AttestationRevoked
            );

            let current_block = frame_system::Pallet::<T>::block_number();

            // Generate certificate hash (simplified - would use proper hashing in production)
            let certificate_hash = Self::compute_certificate_hash(
                attestation_id,
                &attestation.document_hash,
                current_block,
            );

            // Create certificate
            let certificate_id = NextCertificateId::<T>::get();
            let next_id = certificate_id.checked_add(1).ok_or(Error::<T>::Overflow)?;
            NextCertificateId::<T>::put(next_id);

            let certificate = Certificate {
                id: certificate_id,
                attestation_id,
                generated_at: current_block,
                certificate_hash,
                issuer: issuer.clone(),
            };

            Certificates::<T>::insert(certificate_id, certificate);

            Self::deposit_event(Event::CertificateGenerated {
                certificate_id,
                attestation_id,
                certificate_hash,
            });

            Ok(())
        }

        /// Add tags to an attestation for categorization.
        #[pallet::call_index(4)]
        #[pallet::weight(10_000)]
        pub fn add_tags(
            origin: OriginFor<T>,
            attestation_id: u64,
            new_tags: Vec<Vec<u8>>,
        ) -> DispatchResult {
            let who = ensure_signed(origin)?;

            // Get attestation
            let attestation = Attestations::<T>::get(attestation_id)
                .ok_or(Error::<T>::AttestationNotFound)?;

            // Only owner can add tags
            ensure!(attestation.attester == who, Error::<T>::NotOwner);

            // Add tags
            Tags::<T>::try_mutate(attestation_id, |tags| -> DispatchResult {
                for tag_bytes in new_tags.iter() {
                    let tag: Tag = tag_bytes.clone()
                        .try_into()
                        .map_err(|_| Error::<T>::TagTooLong)?;
                    tags.try_push(tag).map_err(|_| Error::<T>::MaxTagsReached)?;
                }
                Ok(())
            })?;

            Self::deposit_event(Event::TagsAdded {
                attestation_id,
                tags: new_tags,
            });

            Ok(())
        }

        /// Add a trusted witness.
        ///
        /// Only sudo/admin can add trusted witnesses.
        #[pallet::call_index(5)]
        #[pallet::weight(10_000)]
        pub fn add_trusted_witness(
            origin: OriginFor<T>,
            witness: T::AccountId,
        ) -> DispatchResult {
            // For now, allow any signed origin - in production would be root/admin
            let _who = ensure_signed(origin)?;

            TrustedWitnesses::<T>::insert(&witness, true);

            Self::deposit_event(Event::TrustedWitnessAdded {
                witness,
            });

            Ok(())
        }

        /// Remove a trusted witness.
        #[pallet::call_index(6)]
        #[pallet::weight(10_000)]
        pub fn remove_trusted_witness(
            origin: OriginFor<T>,
            witness: T::AccountId,
        ) -> DispatchResult {
            let _who = ensure_signed(origin)?;

            TrustedWitnesses::<T>::remove(&witness);

            Self::deposit_event(Event::TrustedWitnessRemoved {
                witness,
            });

            Ok(())
        }
    }

    // ==================== HELPER FUNCTIONS ====================

    impl<T: Config> Pallet<T> {
        /// Compute certificate hash
        fn compute_certificate_hash(
            attestation_id: u64,
            document_hash: &[u8; 32],
            block: BlockNumberFor<T>,
        ) -> [u8; 32] {
            use sp_std::vec;

            // Simple hash combination - would use proper merkle tree in production
            let mut data = vec![];
            data.extend_from_slice(&attestation_id.to_le_bytes());
            data.extend_from_slice(document_hash);
            data.extend_from_slice(&block.encode());

            // Simple hash (in production, use sp_core::blake2_256)
            let mut hash = [0u8; 32];
            for (i, byte) in data.iter().enumerate() {
                hash[i % 32] ^= byte;
            }
            hash
        }

        /// Verify document existence
        pub fn verify_document(document_hash: [u8; 32]) -> Option<(u64, BlockNumberFor<T>)> {
            AttestationByHash::<T>::get(&document_hash).and_then(|id| {
                Attestations::<T>::get(id).map(|a| (id, a.attested_at))
            })
        }

        /// Check if attestation is valid (not expired/revoked)
        pub fn is_valid(attestation_id: u64) -> bool {
            Attestations::<T>::get(attestation_id)
                .map(|a| {
                    matches!(a.status, AttestationStatus::Active | AttestationStatus::Certified)
                        && a.expires_at.map_or(true, |exp| {
                            frame_system::Pallet::<T>::block_number() < exp
                        })
                })
                .unwrap_or(false)
        }

        /// Check if witness is trusted
        pub fn is_trusted_witness(account: &T::AccountId) -> bool {
            TrustedWitnesses::<T>::get(account)
        }

        /// Get attestation for document
        pub fn get_attestation_for_document(document_hash: [u8; 32]) -> Option<Attestation<T>> {
            AttestationByHash::<T>::get(&document_hash)
                .and_then(|id| Attestations::<T>::get(id))
        }
    }
}
