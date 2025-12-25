//! # Validator Entropy Pallet
//!
//! This pallet allows validators to register their entropy source configurations on-chain.
//! This enables transparent identification of QKD validators vs. pure PQC validators.
//!
//! ## Overview
//!
//! The Validator Entropy pallet provides functionality for:
//! - Registering entropy source type (HardwareRNG, QKD, Hybrid, StakeOnly)
//! - Storing device configurations (device types, threshold K)
//! - Querying which validators have QKD capabilities
//! - Enabling relay coordination to identify QKD islands

#![cfg_attr(not(feature = "std"), no_std)]

pub use pallet::*;

// Weights module (uses unit weights in dev mode for now)
pub mod weights;
pub use weights::WeightInfo;

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;

#[cfg(test)]
mod mock;

#[cfg(test)]
mod tests;

#[frame_support::pallet]
pub mod pallet {
    use crate::weights::WeightInfo;
    use frame_support::pallet_prelude::*;
    use frame_system::pallet_prelude::*;
    use sp_std::prelude::*;
    use scale_codec::DecodeWithMemTracking;

    /// Entropy source type for a validator
    #[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
    #[codec(dumb_trait_bound)]
    pub enum EntropySourceType {
        /// Pure hardware RNG (Crypto4A, EntropyKey, /dev/hwrng)
        /// Post-quantum secure but not quantum-based
        HardwareRNG,

        /// Quantum Key Distribution devices (Toshiba, IdQuantique)
        /// True quantum entropy source
        QKD,

        /// Hybrid: Mix of HWRNG + QKD
        /// Both quantum and classical entropy sources
        Hybrid,

        /// Stake only (no quantum hardware)
        /// Relies purely on stake-weighted randomness
        StakeOnly,
    }

    impl Default for EntropySourceType {
        fn default() -> Self {
            Self::StakeOnly
        }
    }

    // Implement DecodeWithMemTracking for EntropySourceType
    impl DecodeWithMemTracking for EntropySourceType {}

    /// Device type identifier
    #[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
    #[codec(dumb_trait_bound)]
    pub enum DeviceType {
        ToshibaQKD,
        IdQuantiqueQKD,
        Crypto4A,
        EntropyKey,
        HardwareRNG,
    }

    // Implement DecodeWithMemTracking for DeviceType
    impl DecodeWithMemTracking for DeviceType {}

    /// Validator entropy configuration
    #[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
    #[scale_info(skip_type_params(T))]
    pub struct ValidatorEntropyConfig<T: Config> {
        /// Type of entropy source
        pub source_type: EntropySourceType,

        /// Device types being used (e.g., [ToshibaQKD, Crypto4A])
        pub devices: BoundedVec<DeviceType, T::MaxDevices>,

        /// Threshold K for Shamir secret sharing
        pub threshold_k: u8,

        /// Total number of devices (M in K-of-M)
        pub total_devices: u8,

        /// Block number when config was last updated
        pub updated_at: BlockNumberFor<T>,
    }

    #[pallet::config]
    pub trait Config: frame_system::Config {
        /// The overarching event type
        type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

        /// Maximum number of devices a validator can register
        #[pallet::constant]
        type MaxDevices: Get<u32>;

        /// Maximum number of validators that can register entropy configs
        #[pallet::constant]
        type MaxValidators: Get<u32>;

        /// Weight information for extrinsics in this pallet
        type WeightInfo: crate::WeightInfo;
    }

    #[pallet::pallet]
    pub struct Pallet<T>(_);

    /// Validator entropy configurations
    /// Maps validator AccountId -> ValidatorEntropyConfig
    #[pallet::storage]
    #[pallet::getter(fn validator_configs)]
    pub type ValidatorConfigs<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        T::AccountId,
        ValidatorEntropyConfig<T>,
        OptionQuery,
    >;

    /// Count of validators by entropy source type
    /// Useful for querying network composition
    #[pallet::storage]
    #[pallet::getter(fn source_type_counts)]
    pub type SourceTypeCounts<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        EntropySourceType,
        u32,
        ValueQuery,
    >;

    /// List of QKD validators (for relay coordination)
    /// Only includes validators with QKD or Hybrid entropy sources
    #[pallet::storage]
    #[pallet::getter(fn qkd_validators)]
    pub type QkdValidators<T: Config> = StorageValue<
        _,
        BoundedVec<T::AccountId, T::MaxValidators>,
        ValueQuery,
    >;

    #[pallet::event]
    #[pallet::generate_deposit(pub(super) fn deposit_event)]
    pub enum Event<T: Config> {
        /// Validator registered their entropy configuration
        EntropyConfigRegistered {
            validator: T::AccountId,
            source_type: EntropySourceType,
            threshold_k: u8,
            total_devices: u8,
        },
        /// Validator updated their entropy configuration
        EntropyConfigUpdated {
            validator: T::AccountId,
            source_type: EntropySourceType,
            threshold_k: u8,
            total_devices: u8,
        },
        /// Validator removed their entropy configuration
        EntropyConfigRemoved {
            validator: T::AccountId,
        },
    }

    #[pallet::error]
    pub enum Error<T> {
        /// Too many devices specified
        TooManyDevices,
        /// Invalid threshold (K must be <= M)
        InvalidThreshold,
        /// Total devices is zero
        ZeroDevices,
        /// Threshold K is zero
        ZeroThreshold,
        /// Configuration not found for validator
        ConfigNotFound,
        /// Too many validators registered
        TooManyValidators,
    }

    #[pallet::call]
    impl<T: Config> Pallet<T> {
        /// Register or update validator entropy configuration
        ///
        /// # Arguments
        /// - `origin`: The validator registering the config (must be signed)
        /// - `source_type`: Type of entropy source (HardwareRNG, QKD, Hybrid, StakeOnly)
        /// - `devices`: List of device types being used
        /// - `threshold_k`: Minimum devices needed for Shamir secret sharing
        ///
        /// # Errors
        /// - `TooManyDevices`: If devices list exceeds MaxDevices
        /// - `InvalidThreshold`: If K > M (total devices)
        /// - `ZeroDevices`: If total_devices is 0
        /// - `ZeroThreshold`: If threshold_k is 0
        #[pallet::call_index(0)]
        #[pallet::weight(T::WeightInfo::register_entropy_config())]
        pub fn register_entropy_config(
            origin: OriginFor<T>,
            source_type: EntropySourceType,
            devices: Vec<DeviceType>,
            threshold_k: u8,
        ) -> DispatchResult {
            let who = ensure_signed(origin)?;

            // Validate inputs
            ensure!(!devices.is_empty(), Error::<T>::ZeroDevices);
            ensure!(threshold_k > 0, Error::<T>::ZeroThreshold);
            let total_devices = devices.len() as u8;
            ensure!(threshold_k <= total_devices, Error::<T>::InvalidThreshold);

            let bounded_devices: BoundedVec<DeviceType, T::MaxDevices> =
                devices.try_into().map_err(|_| Error::<T>::TooManyDevices)?;

            let current_block = frame_system::Pallet::<T>::block_number();

            let config = ValidatorEntropyConfig {
                source_type: source_type.clone(),
                devices: bounded_devices,
                threshold_k,
                total_devices,
                updated_at: current_block,
            };

            // Check if this is an update or new registration
            let is_new = ValidatorConfigs::<T>::get(&who).is_none();

            // Update storage
            ValidatorConfigs::<T>::insert(&who, &config);

            // Update source type counts
            SourceTypeCounts::<T>::mutate(&source_type, |count| *count += 1);

            // Update QKD validators list if applicable
            if matches!(source_type, EntropySourceType::QKD | EntropySourceType::Hybrid) {
                QkdValidators::<T>::try_mutate(|validators| -> DispatchResult {
                    if !validators.contains(&who) {
                        validators.try_push(who.clone())
                            .map_err(|_| Error::<T>::TooManyValidators)?;
                    }
                    Ok(())
                })?;
            }

            // Emit event
            if is_new {
                Self::deposit_event(Event::EntropyConfigRegistered {
                    validator: who,
                    source_type,
                    threshold_k,
                    total_devices,
                });
            } else {
                Self::deposit_event(Event::EntropyConfigUpdated {
                    validator: who,
                    source_type,
                    threshold_k,
                    total_devices,
                });
            }

            Ok(())
        }

        /// Remove validator entropy configuration
        ///
        /// # Arguments
        /// - `origin`: The validator removing their config (must be signed)
        ///
        /// # Errors
        /// - `ConfigNotFound`: If no configuration exists for the validator
        #[pallet::call_index(1)]
        #[pallet::weight(T::WeightInfo::remove_entropy_config())]
        pub fn remove_entropy_config(origin: OriginFor<T>) -> DispatchResult {
            let who = ensure_signed(origin)?;

            let config = ValidatorConfigs::<T>::get(&who)
                .ok_or(Error::<T>::ConfigNotFound)?;

            // Remove from storage
            ValidatorConfigs::<T>::remove(&who);

            // Update source type counts
            SourceTypeCounts::<T>::mutate(&config.source_type, |count| {
                *count = count.saturating_sub(1);
            });

            // Remove from QKD validators list if applicable
            if matches!(config.source_type, EntropySourceType::QKD | EntropySourceType::Hybrid) {
                QkdValidators::<T>::mutate(|validators| {
                    validators.retain(|v| v != &who);
                });
            }

            Self::deposit_event(Event::EntropyConfigRemoved { validator: who });

            Ok(())
        }
    }

    impl<T: Config> Pallet<T> {
        /// Check if a validator has QKD capabilities
        pub fn has_qkd(validator: &T::AccountId) -> bool {
            if let Some(config) = ValidatorConfigs::<T>::get(validator) {
                matches!(config.source_type, EntropySourceType::QKD | EntropySourceType::Hybrid)
            } else {
                false
            }
        }

        /// Get all validators with QKD capabilities
        pub fn get_qkd_validators() -> Vec<T::AccountId> {
            QkdValidators::<T>::get().into_inner()
        }

        /// Get network composition statistics
        pub fn get_network_stats() -> (u32, u32, u32, u32) {
            (
                SourceTypeCounts::<T>::get(EntropySourceType::HardwareRNG),
                SourceTypeCounts::<T>::get(EntropySourceType::QKD),
                SourceTypeCounts::<T>::get(EntropySourceType::Hybrid),
                SourceTypeCounts::<T>::get(EntropySourceType::StakeOnly),
            )
        }
    }
}
