//! # Axiom Attestation Pallet
//!
//! On-chain task attestations for the Axiom autonomous AI agent.
//! Every completed Axiom task gets a permanent, publicly verifiable,
//! post-quantum signed on-chain record.
//!
//! ## Overview
//!
//! - Per-task anchoring (not batching) — ~5-20 tasks/day at 3s block time is negligible
//! - Falcon-512 signature stored alongside task metadata
//! - Deduplication by task_hash
//! - Revocation by original submitter
//! - Rate limiting via MaxAttestationsPerBlock
//!
//! ## Architecture
//!
//! ```text
//! Axiom completes task
//!   → signs TaskAttestation locally (Falcon-512)
//!   → calls axiom.anchor_attestation() extrinsic
//!   → QuantumHarmony validates and stores on-chain
//!   → queryable forever via runtime API
//! ```

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

    /// Configure the pallet
    #[pallet::config]
    pub trait Config: frame_system::Config {
        /// The overarching event type
        type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

        /// Maximum attestations allowed per block (rate limit)
        #[pallet::constant]
        type MaxAttestationsPerBlock: Get<u32>;
    }

    #[pallet::pallet]
    pub struct Pallet<T>(_);

    /// On-chain record of an Axiom task attestation
    #[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
    #[scale_info(skip_type_params(T))]
    pub struct TaskAttestation<T: Config> {
        /// Auto-incremented attestation ID
        pub id: u64,
        /// SHA-256(task_id|step_count|provider)
        pub task_hash: [u8; 32],
        /// SHA-256(task description)
        pub description_hash: [u8; 32],
        /// Number of tool invocations in the task
        pub step_count: u32,
        /// Falcon public key fingerprint ("7b:a7:b6:...")
        pub signer_fingerprint: BoundedVec<u8, ConstU32<48>>,
        /// Falcon-512 signature (hex-encoded, ~1316 bytes)
        pub signature: BoundedVec<u8, ConstU32<1400>>,
        /// SHA-256 of the final audit chain entry hash
        pub audit_chain_hash: [u8; 32],
        /// LLM provider name ("claude-code" or "anthropic")
        pub provider: BoundedVec<u8, ConstU32<32>>,
        /// Account that submitted the attestation
        pub attester: T::AccountId,
        /// Block number when anchored
        pub anchored_at: BlockNumberFor<T>,
        /// Whether this attestation has been revoked
        pub revoked: bool,
    }

    // ==================== STORAGE ====================

    /// All attestations by auto-incremented ID
    #[pallet::storage]
    #[pallet::getter(fn task_attestations)]
    pub type TaskAttestations<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        u64, // attestation_id
        TaskAttestation<T>,
        OptionQuery,
    >;

    /// Next attestation ID (auto-increment counter)
    #[pallet::storage]
    #[pallet::getter(fn next_attestation_id)]
    pub type NextAttestationId<T: Config> = StorageValue<_, u64, ValueQuery>;

    /// Lookup attestation ID by task hash (for dedup + query)
    #[pallet::storage]
    #[pallet::getter(fn attestation_by_task_hash)]
    pub type AttestationByTaskHash<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        [u8; 32], // task_hash
        u64, // attestation_id
        OptionQuery,
    >;

    /// Attestation IDs by submitter account
    #[pallet::storage]
    #[pallet::getter(fn attestations_by_account)]
    pub type AttestationsByAccount<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        T::AccountId,
        BoundedVec<u64, ConstU32<10000>>,
        ValueQuery,
    >;

    /// Total number of attestations ever submitted
    #[pallet::storage]
    #[pallet::getter(fn total_attestations)]
    pub type TotalAttestations<T: Config> = StorageValue<_, u64, ValueQuery>;

    /// Total tool steps attested across all tasks
    #[pallet::storage]
    #[pallet::getter(fn total_steps_attested)]
    pub type TotalStepsAttested<T: Config> = StorageValue<_, u64, ValueQuery>;

    /// Number of attestations anchored in the current block (for rate limiting)
    #[pallet::storage]
    pub type AttestationsInBlock<T: Config> = StorageValue<_, u32, ValueQuery>;

    // ==================== EVENTS ====================

    #[pallet::event]
    #[pallet::generate_deposit(pub(super) fn deposit_event)]
    pub enum Event<T: Config> {
        /// A task attestation was anchored on-chain
        TaskAttestationAnchored {
            attestation_id: u64,
            task_hash: [u8; 32],
            step_count: u32,
            attester: T::AccountId,
        },
        /// A task attestation was revoked
        TaskAttestationRevoked {
            attestation_id: u64,
            reason_hash: [u8; 32],
        },
        /// Configuration was updated (max attestations per block)
        ConfigUpdated {
            max_per_block: u32,
        },
    }

    // ==================== ERRORS ====================

    #[pallet::error]
    pub enum Error<T> {
        /// Task hash already attested (duplicate)
        TaskAlreadyAttested,
        /// Signature is empty or malformed
        InvalidSignature,
        /// Fingerprint is empty or malformed
        InvalidFingerprint,
        /// Provider name exceeds maximum length
        ProviderTooLong,
        /// Attestation not found
        AttestationNotFound,
        /// Only the original submitter can revoke
        NotOwner,
        /// Rate limit: too many attestations in this block
        MaxAttestationsPerBlock,
        /// Numeric overflow
        Overflow,
    }

    // ==================== HOOKS ====================

    #[pallet::hooks]
    impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
        fn on_initialize(_n: BlockNumberFor<T>) -> Weight {
            // Reset per-block counter
            AttestationsInBlock::<T>::put(0u32);
            Weight::from_parts(1_000, 0)
        }
    }

    // ==================== CALLS ====================

    #[pallet::call]
    impl<T: Config> Pallet<T> {
        /// Anchor a completed Axiom task attestation on-chain.
        ///
        /// Creates an immutable, queryable record of an AI agent task completion
        /// with its post-quantum signature.
        #[pallet::call_index(0)]
        #[pallet::weight(10_000)]
        pub fn anchor_attestation(
            origin: OriginFor<T>,
            task_hash: [u8; 32],
            description_hash: [u8; 32],
            step_count: u32,
            signer_fingerprint: Vec<u8>,
            signature: Vec<u8>,
            audit_chain_hash: [u8; 32],
            provider: Vec<u8>,
        ) -> DispatchResult {
            let attester = ensure_signed(origin)?;

            // Rate limit check
            let current_count = AttestationsInBlock::<T>::get();
            ensure!(
                current_count < T::MaxAttestationsPerBlock::get(),
                Error::<T>::MaxAttestationsPerBlock
            );

            // Dedup check
            ensure!(
                !AttestationByTaskHash::<T>::contains_key(&task_hash),
                Error::<T>::TaskAlreadyAttested
            );

            // Validate signature (non-empty)
            ensure!(!signature.is_empty(), Error::<T>::InvalidSignature);

            // Validate fingerprint (non-empty)
            ensure!(!signer_fingerprint.is_empty(), Error::<T>::InvalidFingerprint);

            // Convert to bounded vecs
            let fingerprint_bounded: BoundedVec<u8, ConstU32<48>> =
                signer_fingerprint.try_into().map_err(|_| Error::<T>::InvalidFingerprint)?;
            let signature_bounded: BoundedVec<u8, ConstU32<1400>> =
                signature.try_into().map_err(|_| Error::<T>::InvalidSignature)?;
            let provider_bounded: BoundedVec<u8, ConstU32<32>> =
                provider.try_into().map_err(|_| Error::<T>::ProviderTooLong)?;

            // Allocate ID
            let attestation_id = NextAttestationId::<T>::get();
            let next_id = attestation_id.checked_add(1).ok_or(Error::<T>::Overflow)?;
            NextAttestationId::<T>::put(next_id);

            let current_block = frame_system::Pallet::<T>::block_number();

            // Build attestation record
            let attestation = TaskAttestation {
                id: attestation_id,
                task_hash,
                description_hash,
                step_count,
                signer_fingerprint: fingerprint_bounded,
                signature: signature_bounded,
                audit_chain_hash,
                provider: provider_bounded,
                attester: attester.clone(),
                anchored_at: current_block,
                revoked: false,
            };

            // Store
            TaskAttestations::<T>::insert(attestation_id, attestation);
            AttestationByTaskHash::<T>::insert(task_hash, attestation_id);

            // Update account index
            AttestationsByAccount::<T>::try_mutate(&attester, |ids| {
                ids.try_push(attestation_id).map_err(|_| Error::<T>::Overflow)
            })?;

            // Update global stats
            TotalAttestations::<T>::mutate(|n| *n = n.saturating_add(1));
            TotalStepsAttested::<T>::mutate(|n| *n = n.saturating_add(step_count as u64));

            // Increment per-block counter
            AttestationsInBlock::<T>::mutate(|n| *n = n.saturating_add(1));

            Self::deposit_event(Event::TaskAttestationAnchored {
                attestation_id,
                task_hash,
                step_count,
                attester,
            });

            Ok(())
        }

        /// Revoke a previously anchored attestation.
        ///
        /// Only the original submitter can revoke. The attestation record
        /// remains on-chain (immutable) but is marked as revoked.
        #[pallet::call_index(1)]
        #[pallet::weight(10_000)]
        pub fn revoke_attestation(
            origin: OriginFor<T>,
            attestation_id: u64,
            reason: Vec<u8>,
        ) -> DispatchResult {
            let who = ensure_signed(origin)?;

            let mut attestation = TaskAttestations::<T>::get(attestation_id)
                .ok_or(Error::<T>::AttestationNotFound)?;

            // Only original submitter can revoke
            ensure!(attestation.attester == who, Error::<T>::NotOwner);

            // Mark as revoked
            attestation.revoked = true;
            TaskAttestations::<T>::insert(attestation_id, attestation);

            // Hash the reason for the event (don't store full reason on-chain)
            let mut reason_hash = [0u8; 32];
            for (i, byte) in reason.iter().enumerate() {
                reason_hash[i % 32] ^= byte;
            }

            Self::deposit_event(Event::TaskAttestationRevoked {
                attestation_id,
                reason_hash,
            });

            Ok(())
        }

        /// Update the maximum attestations per block (sudo only).
        ///
        /// This is a runtime configuration change, not a storage migration.
        #[pallet::call_index(2)]
        #[pallet::weight(10_000)]
        pub fn set_max_attestations_per_block(
            origin: OriginFor<T>,
            _max: u32,
        ) -> DispatchResult {
            ensure_root(origin)?;

            // Note: The actual max is set via the Config trait constant.
            // This extrinsic emits an event for governance tracking.
            // To change the actual limit, a runtime upgrade is needed.
            Self::deposit_event(Event::ConfigUpdated {
                max_per_block: _max,
            });

            Ok(())
        }
    }

    // ==================== HELPER FUNCTIONS ====================

    impl<T: Config> Pallet<T> {
        /// Get an attestation by ID
        pub fn get_attestation(id: u64) -> Option<TaskAttestation<T>> {
            TaskAttestations::<T>::get(id)
        }

        /// Verify a task exists on-chain by its hash
        pub fn verify_task(task_hash: [u8; 32]) -> Option<(u64, BlockNumberFor<T>, u32)> {
            AttestationByTaskHash::<T>::get(&task_hash).and_then(|id| {
                TaskAttestations::<T>::get(id).map(|a| (id, a.anchored_at, a.step_count))
            })
        }

        /// Get all attestation IDs for an account
        pub fn get_attestations_for_account(account: &T::AccountId) -> Vec<u64> {
            AttestationsByAccount::<T>::get(account).into_inner()
        }
    }
}
