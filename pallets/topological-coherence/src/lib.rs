//! # Topological Coherence Pallet
//!
//! On-chain validation of topological coherence for inference systems.
//!
//! ## Overview
//!
//! This pallet provides mechanisms for:
//! - Storing coherence validation configurations
//! - Registering topological embeddings for accounts/entities
//! - Validating coherence of submitted inference transitions
//! - Tracking coherence scores and violations
//!
//! ## Theory
//!
//! Based on "Topological Constraints for Coherent Language Models" (Cormier, 2026).
//! Hallucination is a geometry problem: unconstrained latent dynamics permit
//! arbitrary drift through latent space. Topological constraints bound this drift.
//!
//! ## Usage
//!
//! ```ignore
//! // Register an embedding position
//! TopologicalCoherence::register_embedding(origin, entity_id, position)?;
//!
//! // Submit a transition for validation
//! TopologicalCoherence::submit_transition(origin, entity_id, from, to)?;
//!
//! // Query coherence score
//! let score = TopologicalCoherence::coherence_score(entity_id);
//! ```

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;

#[cfg(test)]
mod mock;

#[cfg(test)]
mod tests;

pub mod weights;

pub use pallet::*;
pub use weights::WeightInfo;

#[frame_support::pallet]
pub mod pallet {
    use crate::weights::WeightInfo;
    use frame_support::pallet_prelude::*;
    use frame_system::pallet_prelude::*;
    use topological_coherence::Tonnetz;
    use codec::DecodeWithMemTracking;

    /// Position on the Tonnetz torus.
    #[derive(
        Clone, Copy, Encode, Decode, DecodeWithMemTracking, MaxEncodedLen, TypeInfo, Default, PartialEq, Eq,
    )]
    pub struct ToroidalPosition {
        pub row: u8,
        pub col: u8,
    }

    impl ToroidalPosition {
        pub fn new(row: u8, col: u8) -> Self {
            Self { row, col }
        }

        pub fn as_tuple(&self) -> (usize, usize) {
            (self.row as usize, self.col as usize)
        }

        /// Distance to another position on a 12x12 torus.
        pub fn distance_to(&self, other: &Self) -> u8 {
            Tonnetz::<12>::distance(self.as_tuple(), other.as_tuple()) as u8
        }
    }

    impl core::fmt::Debug for ToroidalPosition {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            write!(f, "({}, {})", self.row, self.col)
        }
    }

    /// Coherence configuration parameters.
    #[derive(
        Clone, Copy, Encode, Decode, DecodeWithMemTracking, MaxEncodedLen, TypeInfo, PartialEq, Eq,
        serde::Serialize, serde::Deserialize,
    )]
    pub struct CoherenceConfig {
        /// Grid size for Tonnetz topology (default 12)
        pub grid_size: u8,
        /// Drift threshold - transitions beyond this are violations
        pub drift_threshold: u8,
        /// Maximum allowed violation rate (scaled by 1000, e.g., 100 = 10%)
        pub max_violation_rate: u16,
        /// Minimum transitions before evaluation
        pub min_transitions: u32,
    }

    impl Default for CoherenceConfig {
        fn default() -> Self {
            Self {
                grid_size: 12,
                drift_threshold: 2,
                max_violation_rate: 100, // 10%
                min_transitions: 10,
            }
        }
    }

    impl core::fmt::Debug for CoherenceConfig {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            write!(
                f,
                "Config(grid={}, threshold={}, max_rate={}‰, min={})",
                self.grid_size, self.drift_threshold, self.max_violation_rate, self.min_transitions
            )
        }
    }

    /// Coherence tracking for an entity.
    #[derive(
        Clone, Copy, Encode, Decode, DecodeWithMemTracking, MaxEncodedLen, TypeInfo, Default, PartialEq, Eq,
    )]
    pub struct CoherenceTracker {
        /// Current position on the torus
        pub position: ToroidalPosition,
        /// Total transitions recorded
        pub transitions: u32,
        /// Number of drift violations
        pub violations: u32,
        /// Block number of last update
        pub last_update: u32,
    }

    impl CoherenceTracker {
        /// Violation rate scaled by 1000 (e.g., 100 = 10%).
        pub fn violation_rate_scaled(&self) -> u16 {
            if self.transitions == 0 {
                0
            } else {
                ((self.violations as u64 * 1000) / self.transitions as u64) as u16
            }
        }

        /// Check if coherent based on config.
        pub fn is_coherent(&self, config: &CoherenceConfig) -> bool {
            if self.transitions < config.min_transitions {
                true // Not enough data yet
            } else {
                self.violation_rate_scaled() <= config.max_violation_rate
            }
        }
    }

    impl core::fmt::Debug for CoherenceTracker {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            write!(
                f,
                "Tracker(pos={:?}, {}/{} violations, rate={}‰)",
                self.position,
                self.violations,
                self.transitions,
                self.violation_rate_scaled()
            )
        }
    }

    #[pallet::pallet]
    pub struct Pallet<T>(_);

    #[pallet::config]
    pub trait Config: frame_system::Config {
        /// Maximum entities that can be tracked per account.
        #[pallet::constant]
        type MaxEntitiesPerAccount: Get<u32>;

        /// Weight information for extrinsics.
        type WeightInfo: crate::weights::WeightInfo;
    }

    /// Global coherence configuration.
    #[pallet::storage]
    #[pallet::getter(fn config)]
    pub type GlobalConfig<T: Config> = StorageValue<_, CoherenceConfig, ValueQuery>;

    /// Coherence tracking per entity.
    /// Key: (AccountId, EntityId)
    #[pallet::storage]
    #[pallet::getter(fn tracker)]
    pub type Trackers<T: Config> = StorageDoubleMap<
        _,
        Blake2_128Concat,
        T::AccountId,
        Blake2_128Concat,
        u32, // EntityId
        CoherenceTracker,
        OptionQuery,
    >;

    /// Number of entities per account.
    #[pallet::storage]
    #[pallet::getter(fn entity_count)]
    pub type EntityCount<T: Config> = StorageMap<_, Blake2_128Concat, T::AccountId, u32, ValueQuery>;

    /// Accounts flagged for coherence violations.
    #[pallet::storage]
    #[pallet::getter(fn flagged)]
    pub type Flagged<T: Config> = StorageMap<_, Blake2_128Concat, T::AccountId, bool, ValueQuery>;

    #[pallet::event]
    #[pallet::generate_deposit(pub(super) fn deposit_event)]
    pub enum Event<T: Config> {
        /// Entity registered with initial position.
        EntityRegistered {
            account: T::AccountId,
            entity_id: u32,
            position: ToroidalPosition,
        },
        /// Transition recorded.
        TransitionRecorded {
            account: T::AccountId,
            entity_id: u32,
            from: ToroidalPosition,
            to: ToroidalPosition,
            distance: u8,
            is_violation: bool,
        },
        /// Account flagged for excessive violations.
        AccountFlagged {
            account: T::AccountId,
            violation_rate: u16,
        },
        /// Account unflagged (coherence restored).
        AccountUnflagged {
            account: T::AccountId,
        },
        /// Global config updated.
        ConfigUpdated {
            config: CoherenceConfig,
        },
    }

    #[pallet::error]
    pub enum Error<T> {
        /// Entity not found.
        EntityNotFound,
        /// Entity already exists.
        EntityAlreadyExists,
        /// Too many entities for this account.
        TooManyEntities,
        /// Invalid position (out of grid bounds).
        InvalidPosition,
        /// Account is flagged for violations.
        AccountFlagged,
        /// Not authorized to perform this action.
        NotAuthorized,
    }

    #[pallet::call]
    impl<T: Config> Pallet<T> {
        /// Register a new entity with an initial position.
        #[pallet::call_index(0)]
        #[pallet::weight(T::WeightInfo::register_entity())]
        pub fn register_entity(
            origin: OriginFor<T>,
            entity_id: u32,
            position: ToroidalPosition,
        ) -> DispatchResult {
            let who = ensure_signed(origin)?;

            // Check position validity
            let config = GlobalConfig::<T>::get();
            ensure!(
                position.row < config.grid_size && position.col < config.grid_size,
                Error::<T>::InvalidPosition
            );

            // Check entity doesn't exist
            ensure!(
                !Trackers::<T>::contains_key(&who, entity_id),
                Error::<T>::EntityAlreadyExists
            );

            // Check entity limit
            let count = EntityCount::<T>::get(&who);
            ensure!(
                count < T::MaxEntitiesPerAccount::get(),
                Error::<T>::TooManyEntities
            );

            // Create tracker
            let block = frame_system::Pallet::<T>::block_number();
            let tracker = CoherenceTracker {
                position,
                transitions: 0,
                violations: 0,
                last_update: block.try_into().unwrap_or(0),
            };

            Trackers::<T>::insert(&who, entity_id, tracker);
            EntityCount::<T>::insert(&who, count + 1);

            Self::deposit_event(Event::EntityRegistered {
                account: who,
                entity_id,
                position,
            });

            Ok(())
        }

        /// Submit a transition for coherence validation.
        #[pallet::call_index(1)]
        #[pallet::weight(T::WeightInfo::submit_transition())]
        pub fn submit_transition(
            origin: OriginFor<T>,
            entity_id: u32,
            new_position: ToroidalPosition,
        ) -> DispatchResult {
            let who = ensure_signed(origin)?;

            // Check not flagged
            ensure!(!Flagged::<T>::get(&who), Error::<T>::AccountFlagged);

            // Get tracker
            let mut tracker =
                Trackers::<T>::get(&who, entity_id).ok_or(Error::<T>::EntityNotFound)?;

            let config = GlobalConfig::<T>::get();

            // Check position validity
            ensure!(
                new_position.row < config.grid_size && new_position.col < config.grid_size,
                Error::<T>::InvalidPosition
            );

            // Calculate distance
            let distance = tracker.position.distance_to(&new_position);
            let is_violation = distance > config.drift_threshold;

            // Update tracker
            let from = tracker.position;
            tracker.position = new_position;
            tracker.transitions = tracker.transitions.saturating_add(1);
            if is_violation {
                tracker.violations = tracker.violations.saturating_add(1);
            }

            let block = frame_system::Pallet::<T>::block_number();
            tracker.last_update = block.try_into().unwrap_or(0);

            Trackers::<T>::insert(&who, entity_id, tracker);

            Self::deposit_event(Event::TransitionRecorded {
                account: who.clone(),
                entity_id,
                from,
                to: new_position,
                distance,
                is_violation,
            });

            // Check if should flag account
            if tracker.transitions >= config.min_transitions
                && tracker.violation_rate_scaled() > config.max_violation_rate
                && !Flagged::<T>::get(&who)
            {
                Flagged::<T>::insert(&who, true);
                Self::deposit_event(Event::AccountFlagged {
                    account: who,
                    violation_rate: tracker.violation_rate_scaled(),
                });
            }

            Ok(())
        }

        /// Update global coherence configuration (governance/sudo only).
        #[pallet::call_index(2)]
        #[pallet::weight(T::WeightInfo::update_config())]
        pub fn update_config(origin: OriginFor<T>, new_config: CoherenceConfig) -> DispatchResult {
            ensure_root(origin)?;

            GlobalConfig::<T>::put(new_config);

            Self::deposit_event(Event::ConfigUpdated { config: new_config });

            Ok(())
        }

        /// Unflag an account (governance/sudo only).
        #[pallet::call_index(3)]
        #[pallet::weight(T::WeightInfo::unflag_account())]
        pub fn unflag_account(origin: OriginFor<T>, account: T::AccountId) -> DispatchResult {
            ensure_root(origin)?;

            Flagged::<T>::remove(&account);

            Self::deposit_event(Event::AccountUnflagged { account });

            Ok(())
        }
    }

    #[pallet::genesis_config]
    #[derive(frame_support::DefaultNoBound)]
    pub struct GenesisConfig<T: Config> {
        pub config: CoherenceConfig,
        #[serde(skip)]
        pub _phantom: PhantomData<T>,
    }

    #[pallet::genesis_build]
    impl<T: Config> BuildGenesisConfig for GenesisConfig<T> {
        fn build(&self) {
            GlobalConfig::<T>::put(self.config);
        }
    }
}
