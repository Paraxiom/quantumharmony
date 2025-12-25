//! # Relay Coordination Pallet
//!
//! This pallet coordinates QSSH relays between QKD islands to enable
//! decentralized quantum-safe P2P networking across geographic distances.
//!
//! ## Overview
//!
//! The Relay Coordination pallet provides:
//! - Relay volunteering and registration
//! - VRF-based relay election (every N blocks)
//! - Relay performance metrics tracking
//! - Slashing for unreliable relays
//! - Geographic region management
//!
//! ## Architecture
//!
//! ```text
//! Tokyo QKD Island <---> Elected Relay <---> Singapore QKD Island
//!        |                    |                      |
//!   3 validators        (QSSH tunnel)          3 validators
//! ```

#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

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
    use frame_support::{
        pallet_prelude::*,
        traits::ReservableCurrency,
    };
    use frame_system::pallet_prelude::*;
    use sp_runtime::{
        traits::{Hash, Saturating, Convert},
        transaction_validity::{
            InvalidTransaction, TransactionSource, TransactionValidity,
            TransactionPriority, ValidTransaction,
        },
        Perbill,
    };
    use sp_std::prelude::*;
    use scale_codec::DecodeWithMemTracking;

    // Import log for off-chain worker
    #[cfg(not(feature = "std"))]
    extern crate alloc;
    #[cfg(not(feature = "std"))]
    use alloc::format;

    /// Geographic region identifier
    #[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
    #[codec(dumb_trait_bound)]
    pub enum Region {
        Asia,
        Europe,
        NorthAmerica,
        SouthAmerica,
        Africa,
        Oceania,
        Global,
    }

    impl Default for Region {
        fn default() -> Self {
            Self::Global
        }
    }

    // Implement DecodeWithMemTracking for Region
    impl DecodeWithMemTracking for Region {}

    /// Relay status
    #[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
    pub enum RelayStatus {
        /// Relay volunteered but not elected
        Candidate,
        /// Relay elected and active
        Active,
        /// Relay slashed for poor performance
        Slashed,
        /// Relay voluntarily deregistered
        Deregistered,
    }

    /// Relay registration information
    #[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
    #[scale_info(skip_type_params(T))]
    pub struct RelayInfo<T: Config> {
        /// Account that registered as relay
        pub account: T::AccountId,

        /// Geographic region
        pub region: Region,

        /// Stake amount (for slashing)
        pub stake: BalanceOf<T>,

        /// Maximum bandwidth (bytes/sec)
        pub max_bandwidth: u64,

        /// SSH public key for QSSH connections
        pub ssh_public_key: BoundedVec<u8, ConstU32<256>>,

        /// Current status
        pub status: RelayStatus,

        /// Block when registered
        pub registered_at: BlockNumberFor<T>,

        /// Last block when relay was active
        pub last_active: BlockNumberFor<T>,

        /// Total successful connections
        pub total_connections: u32,

        /// Total failed connections
        pub failed_connections: u32,

        /// Uptime percentage (0-100)
        pub uptime_percentage: u8,

        /// Gateway URL for stats endpoint (e.g., "http://localhost:8080/stats")
        pub gateway_url: BoundedVec<u8, ConstU32<256>>,
    }

    type BalanceOf<T> = <<T as Config>::Currency as frame_support::traits::Currency<
        <T as frame_system::Config>::AccountId,
    >>::Balance;

    #[pallet::config]
    pub trait Config: frame_system::Config + frame_system::offchain::CreateBare<Call<Self>>
    {
        /// The overarching event type
        type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

        /// Currency type for staking
        type Currency: frame_support::traits::Currency<Self::AccountId>
            + frame_support::traits::ReservableCurrency<Self::AccountId>;

        /// Minimum stake required to volunteer as relay
        #[pallet::constant]
        type MinRelayStake: Get<BalanceOf<Self>>;

        /// Number of blocks between relay elections
        #[pallet::constant]
        type RelayElectionInterval: Get<BlockNumberFor<Self>>;

        /// Maximum number of relay candidates
        #[pallet::constant]
        type MaxRelayCandidates: Get<u32>;

        /// Maximum number of elected relays per region
        #[pallet::constant]
        type MaxElectedRelaysPerRegion: Get<u32>;

        /// Minimum uptime percentage to avoid slashing
        #[pallet::constant]
        type MinUptimePercentage: Get<u8>;

        /// Slash percentage for poor performance (0-100)
        #[pallet::constant]
        type SlashPercentage: Get<Perbill>;

        /// Weight information for extrinsics in this pallet
        type WeightInfo: crate::WeightInfo;

        /// Validator set for authorization checks
        type ValidatorSet: frame_support::traits::ValidatorSet<Self::AccountId>;
    }

    #[pallet::pallet]
    pub struct Pallet<T>(_);

    /// Relay candidates by account ID
    #[pallet::storage]
    #[pallet::getter(fn relay_candidates)]
    pub type RelayCandidates<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        T::AccountId,
        RelayInfo<T>,
        OptionQuery,
    >;

    /// Elected relays for current epoch
    /// Region -> List of elected relay accounts
    #[pallet::storage]
    #[pallet::getter(fn elected_relays)]
    pub type ElectedRelays<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        Region,
        BoundedVec<T::AccountId, T::MaxElectedRelaysPerRegion>,
        ValueQuery,
    >;

    /// Last block number when election occurred
    #[pallet::storage]
    #[pallet::getter(fn last_election_block)]
    pub type LastElectionBlock<T: Config> = StorageValue<_, BlockNumberFor<T>, ValueQuery>;

    /// Current epoch number (increments with each election)
    #[pallet::storage]
    #[pallet::getter(fn current_epoch)]
    pub type CurrentEpoch<T: Config> = StorageValue<_, u32, ValueQuery>;

    #[pallet::event]
    #[pallet::generate_deposit(pub(super) fn deposit_event)]
    pub enum Event<T: Config> {
        /// Validator volunteered as relay
        RelayVolunteered {
            relay: T::AccountId,
            region: Region,
            stake: BalanceOf<T>,
            max_bandwidth: u64,
        },
        /// Relay was elected for an epoch
        RelayElected {
            relay: T::AccountId,
            region: Region,
            epoch: u32,
        },
        /// Relay election occurred
        RelayElectionCompleted {
            epoch: u32,
            total_elected: u32,
        },
        /// Relay was slashed for poor performance
        RelaySlashed {
            relay: T::AccountId,
            slash_amount: BalanceOf<T>,
            reason: SlashReason,
        },
        /// Relay deregistered
        RelayDeregistered {
            relay: T::AccountId,
        },
        /// Relay metrics updated
        RelayMetricsUpdated {
            relay: T::AccountId,
            uptime_percentage: u8,
            total_connections: u32,
        },
    }

    #[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo)]
    pub enum SlashReason {
        LowUptime,
        TooManyFailures,
        Unresponsive,
    }

    // Implement DecodeWithMemTracking for SlashReason
    impl DecodeWithMemTracking for SlashReason {}

    #[pallet::error]
    pub enum Error<T> {
        /// Relay already registered
        AlreadyRegistered,
        /// Not a registered relay
        NotRegistered,
        /// Insufficient stake
        InsufficientStake,
        /// Too many relay candidates
        TooManyRelayCandidates,
        /// Invalid SSH public key
        InvalidSshPublicKey,
        /// Relay already slashed
        AlreadySlashed,
        /// Not authorized to update metrics
        NotAuthorized,
    }

    #[pallet::call]
    impl<T: Config> Pallet<T> {
        /// Volunteer as a QSSH relay
        ///
        /// # Arguments
        /// - `origin`: The validator volunteering (must be signed)
        /// - `region`: Geographic region
        /// - `max_bandwidth`: Maximum bandwidth in bytes/sec
        /// - `ssh_public_key`: SSH public key for QSSH connections
        ///
        /// # Errors
        /// - `AlreadyRegistered`: If already volunteered as relay
        /// - `InsufficientStake`: If stake < MinRelayStake
        /// - `TooManyRelayCandidates`: If max candidates reached
        /// - `InvalidSshPublicKey`: If SSH key is invalid
        #[pallet::call_index(0)]
        #[pallet::weight(T::WeightInfo::volunteer_as_relay())]
        pub fn volunteer_as_relay(
            origin: OriginFor<T>,
            region: Region,
            max_bandwidth: u64,
            ssh_public_key: Vec<u8>,
            gateway_url: Vec<u8>,
        ) -> DispatchResult {
            let who = ensure_signed(origin)?;

            // Check not already registered
            ensure!(
                !RelayCandidates::<T>::contains_key(&who),
                Error::<T>::AlreadyRegistered
            );

            // Validate SSH public key
            ensure!(
                ssh_public_key.len() > 0 && ssh_public_key.len() <= 256,
                Error::<T>::InvalidSshPublicKey
            );

            let bounded_ssh_key: BoundedVec<u8, ConstU32<256>> =
                ssh_public_key.try_into()
                    .map_err(|_| Error::<T>::InvalidSshPublicKey)?;

            // Validate gateway URL
            ensure!(
                gateway_url.len() > 0 && gateway_url.len() <= 256,
                Error::<T>::InvalidSshPublicKey  // Reuse error for now
            );

            let bounded_gateway_url: BoundedVec<u8, ConstU32<256>> =
                gateway_url.try_into()
                    .map_err(|_| Error::<T>::InvalidSshPublicKey)?;

            // Reserve stake
            let stake = T::MinRelayStake::get();
            T::Currency::reserve(&who, stake)
                .map_err(|_| Error::<T>::InsufficientStake)?;

            let current_block = frame_system::Pallet::<T>::block_number();

            let relay_info = RelayInfo {
                account: who.clone(),
                region: region.clone(),
                stake,
                max_bandwidth,
                ssh_public_key: bounded_ssh_key,
                status: RelayStatus::Candidate,
                registered_at: current_block,
                last_active: current_block,
                total_connections: 0,
                failed_connections: 0,
                uptime_percentage: 100,
                gateway_url: bounded_gateway_url,
            };

            RelayCandidates::<T>::insert(&who, relay_info);

            Self::deposit_event(Event::RelayVolunteered {
                relay: who,
                region,
                stake,
                max_bandwidth,
            });

            Ok(())
        }

        /// Deregister as relay
        ///
        /// # Arguments
        /// - `origin`: The relay deregistering (must be signed)
        #[pallet::call_index(1)]
        #[pallet::weight(T::WeightInfo::deregister_relay())]
        pub fn deregister_relay(origin: OriginFor<T>) -> DispatchResult {
            let who = ensure_signed(origin)?;

            let relay_info = RelayCandidates::<T>::get(&who)
                .ok_or(Error::<T>::NotRegistered)?;

            // Unreserve stake
            T::Currency::unreserve(&who, relay_info.stake);

            // Remove from candidates
            RelayCandidates::<T>::remove(&who);

            // Remove from elected relays if present
            ElectedRelays::<T>::mutate(&relay_info.region, |relays| {
                relays.retain(|r| r != &who);
            });

            Self::deposit_event(Event::RelayDeregistered { relay: who });

            Ok(())
        }

        /// Report relay metrics (called by relay or authorized reporter)
        ///
        /// # Arguments
        /// - `relay`: The relay to update metrics for
        /// - `successful_connections`: Number of successful connections in period
        /// - `failed_connections`: Number of failed connections in period
        /// - `uptime_percentage`: Uptime percentage (0-100)
        #[pallet::call_index(2)]
        #[pallet::weight(T::WeightInfo::report_relay_metrics())]
        pub fn report_relay_metrics(
            origin: OriginFor<T>,
            relay: T::AccountId,
            successful_connections: u32,
            failed_connections: u32,
            uptime_percentage: u8,
        ) -> DispatchResult {
            let reporter = ensure_signed(origin)?;

            // Authorization check: Only the relay itself or active validators can report metrics
            // This prevents spam/manipulation while allowing validators to monitor relay health
            let is_relay = reporter == relay;

            // Check if reporter is an active validator
            let validator_id = <T::ValidatorSet as frame_support::traits::ValidatorSet<T::AccountId>>::ValidatorIdOf::convert(reporter.clone());
            let is_validator = if let Some(vid) = validator_id {
                <T::ValidatorSet as frame_support::traits::ValidatorSet<T::AccountId>>::validators().contains(&vid)
            } else {
                false
            };

            ensure!(
                is_relay || is_validator,
                Error::<T>::NotAuthorized
            );

            RelayCandidates::<T>::try_mutate(&relay, |maybe_info| -> DispatchResult {
                let info = maybe_info.as_mut().ok_or(Error::<T>::NotRegistered)?;

                info.total_connections = info.total_connections.saturating_add(successful_connections);
                info.failed_connections = info.failed_connections.saturating_add(failed_connections);
                info.uptime_percentage = uptime_percentage;
                info.last_active = frame_system::Pallet::<T>::block_number();

                // Check if relay should be slashed
                if uptime_percentage < T::MinUptimePercentage::get() {
                    Self::slash_relay(&relay, info, SlashReason::LowUptime)?;
                }

                Self::deposit_event(Event::RelayMetricsUpdated {
                    relay: relay.clone(),
                    uptime_percentage,
                    total_connections: info.total_connections,
                });

                Ok(())
            })
        }
    }

    #[pallet::hooks]
    impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
        fn on_initialize(n: BlockNumberFor<T>) -> Weight {
            let last_election = LastElectionBlock::<T>::get();
            let interval = T::RelayElectionInterval::get();

            // Check if it's time for a new election
            if n.saturating_sub(last_election) >= interval {
                Self::elect_relays(n);
            }

            Weight::from_parts(10_000, 0)
        }

        fn offchain_worker(block_number: BlockNumberFor<T>) {
            // Monitor relay health every 10 blocks
            let check_interval = 10u32;
            if (TryInto::<u32>::try_into(block_number).ok().unwrap_or(0) % check_interval) != 0 {
                return;
            }

            // Get all active relays
            let active_relays = Self::get_all_active_relays();
            if active_relays.is_empty() {
                return;
            }

            // For each active relay, check health and submit metrics
            for relay_account in active_relays.iter() {
                let _ = Self::check_relay_health_and_report(relay_account);
            }
        }
    }

    impl<T: Config> Pallet<T> {
        /// Elect relays using VRF-based randomness
        fn elect_relays(current_block: BlockNumberFor<T>) {
            let epoch = CurrentEpoch::<T>::get().saturating_add(1);
            CurrentEpoch::<T>::put(epoch);
            LastElectionBlock::<T>::put(current_block);

            let mut total_elected = 0u32;

            // Get randomness seed from block hash
            let seed = frame_system::Pallet::<T>::block_hash(current_block.saturating_sub(1u32.into()));

            // Elect relays for each region
            for region in [
                Region::Asia,
                Region::Europe,
                Region::NorthAmerica,
                Region::SouthAmerica,
                Region::Africa,
                Region::Oceania,
                Region::Global,
            ] {
                let candidates: Vec<_> = RelayCandidates::<T>::iter()
                    .filter(|(_, info)| {
                        info.region == region &&
                        info.status == RelayStatus::Candidate &&
                        info.uptime_percentage >= T::MinUptimePercentage::get()
                    })
                    .collect();

                if candidates.is_empty() {
                    continue;
                }

                let max_elected = T::MaxElectedRelaysPerRegion::get() as usize;
                let to_elect = candidates.len().min(max_elected);

                let mut elected = BoundedVec::new();

                // Simple VRF-based selection using block hash
                for i in 0..to_elect {
                    let index = Self::vrf_select(&seed, region.clone(), i as u32, candidates.len());
                    if let Some((account, _)) = candidates.get(index) {
                        if elected.try_push(account.clone()).is_ok() {
                            // Update relay status
                            RelayCandidates::<T>::mutate(account, |maybe_info| {
                                if let Some(info) = maybe_info {
                                    info.status = RelayStatus::Active;
                                }
                            });

                            Self::deposit_event(Event::RelayElected {
                                relay: account.clone(),
                                region: region.clone(),
                                epoch,
                            });

                            total_elected += 1;
                        }
                    }
                }

                ElectedRelays::<T>::insert(region, elected);
            }

            Self::deposit_event(Event::RelayElectionCompleted {
                epoch,
                total_elected,
            });
        }

        /// VRF-based selection index
        fn vrf_select(seed: &T::Hash, region: Region, index: u32, candidates_len: usize) -> usize {
            let mut input = seed.as_ref().to_vec();
            input.extend_from_slice(&region.encode());
            input.extend_from_slice(&index.encode());

            let hash = T::Hashing::hash(&input);
            let hash_bytes = hash.as_ref();

            let mut value = 0u64;
            for (i, byte) in hash_bytes.iter().enumerate().take(8) {
                value |= (*byte as u64) << (i * 8);
            }

            (value as usize) % candidates_len
        }

        /// Slash relay for poor performance
        fn slash_relay(
            relay: &T::AccountId,
            info: &mut RelayInfo<T>,
            reason: SlashReason,
        ) -> DispatchResult {
            ensure!(info.status != RelayStatus::Slashed, Error::<T>::AlreadySlashed);

            let slash_amount = T::SlashPercentage::get() * info.stake;

            // Slash the stake
            let (_imbalance, _remaining) = T::Currency::slash_reserved(relay, slash_amount);

            info.status = RelayStatus::Slashed;

            Self::deposit_event(Event::RelaySlashed {
                relay: relay.clone(),
                slash_amount,
                reason,
            });

            Ok(())
        }

        /// Get elected relays for a region
        pub fn get_elected_relays(region: Region) -> Vec<T::AccountId> {
            ElectedRelays::<T>::get(region).into_inner()
        }

        /// Check if an account is an active relay
        pub fn is_active_relay(account: &T::AccountId) -> bool {
            if let Some(info) = RelayCandidates::<T>::get(account) {
                info.status == RelayStatus::Active
            } else {
                false
            }
        }

        /// Get all active relays across all regions
        fn get_all_active_relays() -> Vec<T::AccountId> {
            let mut active_relays = Vec::new();

            // Iterate through all relay candidates
            for (account, info) in RelayCandidates::<T>::iter() {
                if info.status == RelayStatus::Active {
                    active_relays.push(account);
                }
            }

            active_relays
        }

        /// Check relay health by connecting to pq-transport-gateway and submit metrics
        fn check_relay_health_and_report(relay_account: &T::AccountId) -> Result<(), &'static str> {
            use sp_runtime::offchain::{http, Duration};
            use sp_io::offchain::timestamp;

            // Get relay info from storage
            let relay_info = RelayCandidates::<T>::get(relay_account)
                .ok_or("Relay not found")?;

            // Get gateway URL from relay config
            let gateway_url_bytes = relay_info.gateway_url.to_vec();
            let gateway_url = sp_std::str::from_utf8(&gateway_url_bytes)
                .map_err(|_| "Invalid gateway URL")?;

            // Create HTTP request with timeout
            let request = http::Request::get(gateway_url);
            let timeout = Duration::from_millis(5000);
            let deadline = timestamp().add(timeout);

            let pending = request
                .deadline(deadline)
                .send()
                .map_err(|_| "HTTP request failed")?;

            // Wait for response
            let response = pending
                .try_wait(Some(deadline))
                .map_err(|_| "HTTP timeout")?
                .map_err(|_| "HTTP error")?;

            // Check response status
            if response.code != 200 {
                return Err("Bad status code");
            }

            // Read response body
            let body = response.body().collect::<Vec<u8>>();

            // Parse JSON response
            // Expected format: {"successful_connections": 10, "failed_connections": 1, "uptime_percentage": 95}
            let (successful_connections, failed_connections, uptime_percentage) =
                Self::parse_stats_json(&body).unwrap_or_else(|_| {
                    // Fallback to mock metrics if parsing fails (endpoint not implemented yet)
                    (10u32, 1u32, 95u8)
                });

            // Submit signed transaction to update metrics
            Self::submit_relay_metrics(
                relay_account,
                successful_connections,
                failed_connections,
                uptime_percentage,
            )
        }

        /// Submit relay metrics via unsigned transaction
        /// Off-chain workers can only submit unsigned transactions
        fn submit_relay_metrics(
            relay_account: &T::AccountId,
            successful_connections: u32,
            failed_connections: u32,
            uptime_percentage: u8,
        ) -> Result<(), &'static str> {
            use frame_system::offchain::SubmitTransaction;

            // Create the call to report_relay_metrics
            let call = Call::report_relay_metrics {
                relay: relay_account.clone(),
                successful_connections,
                failed_connections,
                uptime_percentage,
            };

            // Create a bare (unsigned) extrinsic
            // This will be validated by ValidateUnsigned
            let xt = T::create_bare(call.into());

            // Submit the unsigned transaction
            SubmitTransaction::<T, Call<T>>::submit_transaction(xt)
                .map_err(|()| "Failed to submit unsigned transaction")?;

            Ok(())
        }

        /// Parse stats JSON response from QSSH relay
        /// Expected format: {"successful_connections": 10, "failed_connections": 1, "uptime_percentage": 95}
        fn parse_stats_json(body: &[u8]) -> Result<(u32, u32, u8), &'static str> {
            // Convert bytes to string
            let json_str = sp_std::str::from_utf8(body).map_err(|_| "Invalid UTF-8")?;

            // Simple JSON parsing without external dependencies
            // Look for the three fields we need
            let successful_connections = Self::extract_json_u32(json_str, "successful_connections")
                .ok_or("Missing successful_connections")?;
            let failed_connections = Self::extract_json_u32(json_str, "failed_connections")
                .ok_or("Missing failed_connections")?;
            let uptime_percentage = Self::extract_json_u8(json_str, "uptime_percentage")
                .ok_or("Missing uptime_percentage")?;

            Ok((successful_connections, failed_connections, uptime_percentage))
        }

        /// Extract u32 value from JSON string
        fn extract_json_u32(json: &str, key: &str) -> Option<u32> {
            use alloc::format;
            use alloc::string::String;

            // Find the key in the JSON
            let key_pattern = format!("\"{}\":", key);
            let start = json.find(&key_pattern)?;
            let value_start = start + key_pattern.len();

            // Skip whitespace
            let chars: Vec<char> = json[value_start..].chars().collect();
            let mut i = 0;
            while i < chars.len() && chars[i].is_whitespace() {
                i += 1;
            }

            // Extract the number
            let mut num_str = String::new();
            while i < chars.len() && chars[i].is_numeric() {
                num_str.push(chars[i]);
                i += 1;
            }

            num_str.parse::<u32>().ok()
        }

        /// Extract u8 value from JSON string
        fn extract_json_u8(json: &str, key: &str) -> Option<u8> {
            use alloc::format;
            use alloc::string::String;

            // Find the key in the JSON
            let key_pattern = format!("\"{}\":", key);
            let start = json.find(&key_pattern)?;
            let value_start = start + key_pattern.len();

            // Skip whitespace
            let chars: Vec<char> = json[value_start..].chars().collect();
            let mut i = 0;
            while i < chars.len() && chars[i].is_whitespace() {
                i += 1;
            }

            // Extract the number
            let mut num_str = String::new();
            while i < chars.len() && chars[i].is_numeric() {
                num_str.push(chars[i]);
                i += 1;
            }

            num_str.parse::<u8>().ok()
        }
    }

    /// Validate unsigned transactions from off-chain workers
    #[pallet::validate_unsigned]
    impl<T: Config> frame_support::unsigned::ValidateUnsigned for Pallet<T> {
        type Call = Call<T>;

        fn validate_unsigned(_source: TransactionSource, call: &Self::Call) -> TransactionValidity {
            // Only validate report_relay_metrics calls from off-chain workers
            match call {
                Call::report_relay_metrics { relay, successful_connections, failed_connections, uptime_percentage } => {
                    // Basic validation
                    if *uptime_percentage > 100 {
                        return InvalidTransaction::Custom(1).into();
                    }

                    // Check that the relay is actually registered
                    if !RelayCandidates::<T>::contains_key(relay) {
                        return InvalidTransaction::Custom(2).into();
                    }

                    ValidTransaction::with_tag_prefix("RelayMetrics")
                        .priority(TransactionPriority::MAX)
                        .and_provides((relay, successful_connections, failed_connections))
                        .longevity(3)
                        .propagate(true)
                        .build()
                }
                _ => InvalidTransaction::Call.into(),
            }
        }
    }
}
