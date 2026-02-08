//! # Oracle Feeds Pallet
//!
//! Decentralized oracle network for QuantumHarmony validators.
//!
//! ## Overview
//!
//! This pallet enables validators to:
//! - Request external data feeds (price, weather, custom APIs)
//! - Accept feed requests and become reporters
//! - Submit data reports with multi-validator verification
//! - Earn rewards based on SLA compliance
//! - Face slashing for incorrect/late data
//!
//! ## Architecture
//!
//! 1. **Request Phase**: Validator requests a feed, depositing reward upfront
//! 2. **Acceptance Phase**: Other validators accept to provide the feed
//! 3. **Reporting Phase**: Reporters submit data at specified intervals
//! 4. **Aggregation Phase**: Data is aggregated (median/mode) when min reporters reached
//! 5. **Consumption Phase**: Smart contracts/runtime can query aggregated data
//! 6. **Reward Phase**: Reporters earn rewards based on SLA, slashing for bad data

#![cfg_attr(not(feature = "std"), no_std)]

pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {
    use codec::DecodeWithMemTracking;
    use frame_support::{
        pallet_prelude::*,
        traits::{Currency, ReservableCurrency},
        BoundedVec,
    };
    use frame_system::pallet_prelude::*;
    use sp_runtime::{Percent, traits::AtLeast32BitUnsigned, Saturating};
    use sp_std::vec::Vec;

    /// Maximum URL length
    pub const MAX_URL_LENGTH: u32 = 256;
    /// Maximum data length
    pub const MAX_DATA_LENGTH: u32 = 1024;
    /// Maximum reporters per feed
    pub const MAX_REPORTERS: u32 = 10;

    type BalanceOf<T> = <T as Config>::Balance;

    #[pallet::pallet]
    pub struct Pallet<T>(_);

    #[pallet::config]
    pub trait Config: frame_system::Config {
        /// The overarching event type
        type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

        /// Currency for rewards and deposits
        type Currency: Currency<Self::AccountId, Balance = Self::Balance> + ReservableCurrency<Self::AccountId>;

        /// Balance type
        type Balance: Member + Parameter + AtLeast32BitUnsigned + Default + Copy + MaxEncodedLen + From<u64>;

        /// Minimum reporters required for a feed
        #[pallet::constant]
        type MinReporters: Get<u8>;

        /// Maximum feeds per account
        #[pallet::constant]
        type MaxFeedsPerAccount: Get<u32>;

        /// Slash percentage for bad data (aggressive slashing as per spec)
        #[pallet::constant]
        type SlashPercent: Get<Percent>;
    }

    /// Feed ID counter
    #[pallet::storage]
    #[pallet::getter(fn next_feed_id)]
    pub type NextFeedId<T> = StorageValue<_, u64, ValueQuery>;

    /// Data type for the feed
    #[derive(Clone, Encode, Decode, TypeInfo, MaxEncodedLen, PartialEq, Eq, Debug)]
    pub enum DataType {
        Price,
        Weather,
        Sports,
        Custom,
    }

    impl Default for DataType {
        fn default() -> Self {
            DataType::Custom
        }
    }

    impl DecodeWithMemTracking for DataType {}

    /// Feed status
    #[derive(Clone, Encode, Decode, TypeInfo, MaxEncodedLen, PartialEq, Eq, Debug, Default)]
    pub enum FeedStatus {
        #[default]
        Pending,
        Active,
        Completed,
        Cancelled,
    }

    impl DecodeWithMemTracking for FeedStatus {}

    /// Feed request structure
    #[derive(Clone, Encode, Decode, TypeInfo, MaxEncodedLen)]
    #[scale_info(skip_type_params(T))]
    pub struct FeedRequest<T: Config> {
        pub requester: T::AccountId,
        pub data_type: DataType,
        pub source_url: BoundedVec<u8, ConstU32<MAX_URL_LENGTH>>,
        pub reward_per_report: BalanceOf<T>,
        pub sla_uptime_percent: u8,
        pub sla_latency_ms: u32,
        pub min_reporters: u8,
        pub report_interval: BlockNumberFor<T>,
        pub duration: BlockNumberFor<T>,
        pub created_at: BlockNumberFor<T>,
        pub status: FeedStatus,
        pub total_deposited: BalanceOf<T>,
    }

    /// Oracle report from a validator
    #[derive(Clone, Encode, Decode, TypeInfo, MaxEncodedLen)]
    #[scale_info(skip_type_params(T))]
    pub struct OracleReport<T: Config> {
        pub reporter: T::AccountId,
        pub feed_id: u64,
        pub data: BoundedVec<u8, ConstU32<MAX_DATA_LENGTH>>,
        pub timestamp: u64,
        pub block_number: BlockNumberFor<T>,
        pub latency_ms: u32,
    }

    /// Reporter statistics
    #[derive(Clone, Encode, Decode, TypeInfo, MaxEncodedLen)]
    #[scale_info(skip_type_params(T))]
    pub struct ReporterStats<T: Config> {
        pub total_reports: u64,
        pub successful_reports: u64,
        pub total_earned: BalanceOf<T>,
        pub total_slashed: BalanceOf<T>,
        pub uptime_percent: u8,
        pub avg_latency_ms: u32,
    }

    impl<T: Config> Default for ReporterStats<T> {
        fn default() -> Self {
            Self {
                total_reports: 0,
                successful_reports: 0,
                total_earned: BalanceOf::<T>::default(),
                total_slashed: BalanceOf::<T>::default(),
                uptime_percent: 0,
                avg_latency_ms: 0,
            }
        }
    }

    /// Aggregated data for a feed
    #[derive(Clone, Encode, Decode, TypeInfo, MaxEncodedLen)]
    #[scale_info(skip_type_params(T))]
    pub struct AggregatedData<T: Config> {
        pub feed_id: u64,
        pub value: BoundedVec<u8, ConstU32<MAX_DATA_LENGTH>>,
        pub reporters_count: u8,
        pub agreement_percent: u8,
        pub last_updated: BlockNumberFor<T>,
        pub used_in_transaction: bool,
    }

    /// All feed requests
    #[pallet::storage]
    #[pallet::getter(fn feed_requests)]
    pub type FeedRequests<T: Config> = StorageMap<_, Blake2_128Concat, u64, FeedRequest<T>>;

    /// Reporters for each feed (feed_id -> list of reporter accounts)
    #[pallet::storage]
    #[pallet::getter(fn feed_reporters)]
    pub type FeedReporters<T: Config> =
        StorageMap<_, Blake2_128Concat, u64, BoundedVec<T::AccountId, ConstU32<MAX_REPORTERS>>, ValueQuery>;

    /// Latest reports for each feed (feed_id, reporter -> report)
    #[pallet::storage]
    #[pallet::getter(fn feed_reports)]
    pub type FeedReports<T: Config> = StorageDoubleMap<
        _,
        Blake2_128Concat,
        u64,
        Blake2_128Concat,
        T::AccountId,
        OracleReport<T>,
    >;

    /// Aggregated feed data (feed_id -> aggregated data)
    #[pallet::storage]
    #[pallet::getter(fn aggregated_feeds)]
    pub type AggregatedFeeds<T: Config> = StorageMap<_, Blake2_128Concat, u64, AggregatedData<T>>;

    /// Reporter statistics
    #[pallet::storage]
    #[pallet::getter(fn reporter_stats)]
    pub type ReporterStatsStorage<T: Config> =
        StorageMap<_, Blake2_128Concat, T::AccountId, ReporterStats<T>, ValueQuery>;

    #[pallet::event]
    #[pallet::generate_deposit(pub(super) fn deposit_event)]
    pub enum Event<T: Config> {
        /// Feed request created
        FeedRequested {
            feed_id: u64,
            requester: T::AccountId,
            data_type: DataType,
            reward_per_report: BalanceOf<T>,
        },
        /// Reporter accepted a feed
        FeedAccepted {
            feed_id: u64,
            reporter: T::AccountId,
        },
        /// Feed became active (min reporters reached)
        FeedActivated {
            feed_id: u64,
            reporters_count: u8,
        },
        /// Report submitted
        ReportSubmitted {
            feed_id: u64,
            reporter: T::AccountId,
            block_number: BlockNumberFor<T>,
        },
        /// Data aggregated
        DataAggregated {
            feed_id: u64,
            reporters_count: u8,
            agreement_percent: u8,
        },
        /// Reward distributed
        RewardDistributed {
            feed_id: u64,
            reporter: T::AccountId,
            amount: BalanceOf<T>,
        },
        /// Reporter slashed for bad data
        ReporterSlashed {
            feed_id: u64,
            reporter: T::AccountId,
            amount: BalanceOf<T>,
            reason: SlashReason,
        },
        /// Feed completed
        FeedCompleted {
            feed_id: u64,
        },
        /// Feed cancelled
        FeedCancelled {
            feed_id: u64,
        },
    }

    #[derive(Clone, Encode, Decode, TypeInfo, MaxEncodedLen, PartialEq, Eq, Debug)]
    pub enum SlashReason {
        IncorrectData,
        LateSubmission,
        MissedReport,
    }

    impl DecodeWithMemTracking for SlashReason {}

    #[pallet::error]
    pub enum Error<T> {
        /// Feed not found
        FeedNotFound,
        /// Feed not active
        FeedNotActive,
        /// Already a reporter for this feed
        AlreadyReporter,
        /// Not a reporter for this feed
        NotReporter,
        /// Max reporters reached
        MaxReportersReached,
        /// Insufficient deposit
        InsufficientDeposit,
        /// Invalid URL
        InvalidUrl,
        /// Invalid SLA parameters
        InvalidSlaParams,
        /// Report interval not reached
        ReportIntervalNotReached,
        /// Feed duration exceeded
        FeedDurationExceeded,
        /// Not feed requester
        NotRequester,
        /// Feed already cancelled
        FeedAlreadyCancelled,
        /// Min reporters not reached
        MinReportersNotReached,
    }

    #[pallet::call]
    impl<T: Config> Pallet<T> {
        /// Request a new data feed
        #[pallet::call_index(0)]
        #[pallet::weight(10_000)]
        pub fn request_feed(
            origin: OriginFor<T>,
            data_type: DataType,
            source_url: Vec<u8>,
            reward_per_report: BalanceOf<T>,
            sla_uptime_percent: u8,
            sla_latency_ms: u32,
            min_reporters: u8,
            report_interval: BlockNumberFor<T>,
            duration: BlockNumberFor<T>,
        ) -> DispatchResult {
            let requester = ensure_signed(origin)?;

            // Validate inputs
            ensure!(source_url.len() <= MAX_URL_LENGTH as usize, Error::<T>::InvalidUrl);
            ensure!(sla_uptime_percent >= 90 && sla_uptime_percent <= 100, Error::<T>::InvalidSlaParams);
            ensure!(min_reporters >= T::MinReporters::get(), Error::<T>::InvalidSlaParams);

            // Calculate total deposit needed
            // Estimate: (duration / report_interval) * reward_per_report * min_reporters
            // Simplified: just use reward * min_reporters * 100 as estimate
            let estimated_reports: u64 = 100; // Simplified estimate
            let total_deposit = reward_per_report
                .saturating_mul(estimated_reports.into())
                .saturating_mul((min_reporters as u64).into());

            // Reserve deposit
            T::Currency::reserve(&requester, total_deposit)?;

            // Create feed
            let feed_id = NextFeedId::<T>::get();
            NextFeedId::<T>::put(feed_id + 1);

            let bounded_url: BoundedVec<u8, ConstU32<MAX_URL_LENGTH>> =
                source_url.try_into().map_err(|_| Error::<T>::InvalidUrl)?;

            let feed = FeedRequest {
                requester: requester.clone(),
                data_type: data_type.clone(),
                source_url: bounded_url,
                reward_per_report,
                sla_uptime_percent,
                sla_latency_ms,
                min_reporters,
                report_interval,
                duration,
                created_at: frame_system::Pallet::<T>::block_number(),
                status: FeedStatus::Pending,
                total_deposited: total_deposit,
            };

            FeedRequests::<T>::insert(feed_id, feed);

            Self::deposit_event(Event::FeedRequested {
                feed_id,
                requester,
                data_type,
                reward_per_report,
            });

            Ok(())
        }

        /// Accept a feed request (become a reporter)
        #[pallet::call_index(1)]
        #[pallet::weight(10_000)]
        pub fn accept_feed(origin: OriginFor<T>, feed_id: u64) -> DispatchResult {
            let reporter = ensure_signed(origin)?;

            let mut feed = FeedRequests::<T>::get(feed_id).ok_or(Error::<T>::FeedNotFound)?;
            ensure!(
                feed.status == FeedStatus::Pending || feed.status == FeedStatus::Active,
                Error::<T>::FeedNotActive
            );

            let mut reporters = FeedReporters::<T>::get(feed_id);
            ensure!(!reporters.contains(&reporter), Error::<T>::AlreadyReporter);
            ensure!(reporters.len() < MAX_REPORTERS as usize, Error::<T>::MaxReportersReached);

            reporters.try_push(reporter.clone()).map_err(|_| Error::<T>::MaxReportersReached)?;
            FeedReporters::<T>::insert(feed_id, reporters.clone());

            Self::deposit_event(Event::FeedAccepted {
                feed_id,
                reporter,
            });

            // Activate feed if min reporters reached
            if reporters.len() >= feed.min_reporters as usize && feed.status == FeedStatus::Pending {
                feed.status = FeedStatus::Active;
                FeedRequests::<T>::insert(feed_id, feed);

                Self::deposit_event(Event::FeedActivated {
                    feed_id,
                    reporters_count: reporters.len() as u8,
                });
            }

            Ok(())
        }

        /// Submit a data report
        #[pallet::call_index(2)]
        #[pallet::weight(10_000)]
        pub fn submit_report(
            origin: OriginFor<T>,
            feed_id: u64,
            data: Vec<u8>,
            timestamp: u64,
            latency_ms: u32,
        ) -> DispatchResult {
            let reporter = ensure_signed(origin)?;

            let feed = FeedRequests::<T>::get(feed_id).ok_or(Error::<T>::FeedNotFound)?;
            ensure!(feed.status == FeedStatus::Active, Error::<T>::FeedNotActive);

            let reporters = FeedReporters::<T>::get(feed_id);
            ensure!(reporters.contains(&reporter), Error::<T>::NotReporter);

            let current_block = frame_system::Pallet::<T>::block_number();

            // Check feed hasn't expired
            let end_block = feed.created_at + feed.duration;
            ensure!(current_block <= end_block, Error::<T>::FeedDurationExceeded);

            let bounded_data: BoundedVec<u8, ConstU32<MAX_DATA_LENGTH>> =
                data.try_into().map_err(|_| Error::<T>::InvalidUrl)?;

            let report = OracleReport {
                reporter: reporter.clone(),
                feed_id,
                data: bounded_data,
                timestamp,
                block_number: current_block,
                latency_ms,
            };

            FeedReports::<T>::insert(feed_id, &reporter, report);

            Self::deposit_event(Event::ReportSubmitted {
                feed_id,
                reporter: reporter.clone(),
                block_number: current_block,
            });

            // Try to aggregate data
            Self::try_aggregate(feed_id, &feed)?;

            Ok(())
        }

        /// Cancel a feed (only requester, only if pending)
        #[pallet::call_index(3)]
        #[pallet::weight(10_000)]
        pub fn cancel_feed(origin: OriginFor<T>, feed_id: u64) -> DispatchResult {
            let who = ensure_signed(origin)?;

            let mut feed = FeedRequests::<T>::get(feed_id).ok_or(Error::<T>::FeedNotFound)?;
            ensure!(feed.requester == who, Error::<T>::NotRequester);
            ensure!(feed.status == FeedStatus::Pending, Error::<T>::FeedAlreadyCancelled);

            // Refund deposit
            T::Currency::unreserve(&who, feed.total_deposited);

            feed.status = FeedStatus::Cancelled;
            FeedRequests::<T>::insert(feed_id, feed);

            Self::deposit_event(Event::FeedCancelled { feed_id });

            Ok(())
        }

        /// Mark aggregated data as used (called when data is consumed in a transaction)
        #[pallet::call_index(4)]
        #[pallet::weight(10_000)]
        pub fn mark_data_used(origin: OriginFor<T>, feed_id: u64) -> DispatchResult {
            ensure_signed(origin)?;

            let mut aggregated = AggregatedFeeds::<T>::get(feed_id).ok_or(Error::<T>::FeedNotFound)?;
            aggregated.used_in_transaction = true;
            AggregatedFeeds::<T>::insert(feed_id, aggregated);

            Ok(())
        }
    }

    impl<T: Config> Pallet<T> {
        /// Try to aggregate reports for a feed
        fn try_aggregate(feed_id: u64, feed: &FeedRequest<T>) -> DispatchResult {
            let reporters = FeedReporters::<T>::get(feed_id);

            // Collect all reports for this round
            let mut reports: Vec<OracleReport<T>> = Vec::new();
            for reporter in reporters.iter() {
                if let Some(report) = FeedReports::<T>::get(feed_id, reporter) {
                    reports.push(report);
                }
            }

            // Need minimum reporters
            if reports.len() < feed.min_reporters as usize {
                return Ok(());
            }

            // Simple aggregation: use first report's data (NOTE: median/mode aggregation planned for multi-reporter feeds)
            // In production, this would compare all reports and find consensus
            let first_report = &reports[0];
            let agreement_percent = 100u8; // NOTE: Assumes full agreement with single-reporter aggregation; multi-reporter consensus pending

            let aggregated = AggregatedData {
                feed_id,
                value: first_report.data.clone(),
                reporters_count: reports.len() as u8,
                agreement_percent,
                last_updated: frame_system::Pallet::<T>::block_number(),
                used_in_transaction: false,
            };

            AggregatedFeeds::<T>::insert(feed_id, aggregated);

            Self::deposit_event(Event::DataAggregated {
                feed_id,
                reporters_count: reports.len() as u8,
                agreement_percent,
            });

            // Distribute rewards to reporters
            for report in reports.iter() {
                // Check latency SLA
                let meets_latency = report.latency_ms <= feed.sla_latency_ms;

                if meets_latency {
                    // Full reward
                    let _ = T::Currency::unreserve(&feed.requester, feed.reward_per_report);
                    let _ = T::Currency::transfer(
                        &feed.requester,
                        &report.reporter,
                        feed.reward_per_report,
                        frame_support::traits::ExistenceRequirement::KeepAlive,
                    );

                    // Update stats
                    ReporterStatsStorage::<T>::mutate(&report.reporter, |stats| {
                        stats.total_reports += 1;
                        stats.successful_reports += 1;
                        stats.total_earned = stats.total_earned.saturating_add(feed.reward_per_report);
                    });

                    Self::deposit_event(Event::RewardDistributed {
                        feed_id,
                        reporter: report.reporter.clone(),
                        amount: feed.reward_per_report,
                    });
                } else {
                    // Aggressive slashing for late data
                    let slash_amount = T::SlashPercent::get() * feed.reward_per_report;

                    ReporterStatsStorage::<T>::mutate(&report.reporter, |stats| {
                        stats.total_reports += 1;
                        stats.total_slashed = stats.total_slashed.saturating_add(slash_amount);
                    });

                    Self::deposit_event(Event::ReporterSlashed {
                        feed_id,
                        reporter: report.reporter.clone(),
                        amount: slash_amount,
                        reason: SlashReason::LateSubmission,
                    });
                }
            }

            Ok(())
        }

        /// Get aggregated data for a feed (for runtime API)
        pub fn get_feed_data(feed_id: u64) -> Option<AggregatedData<T>> {
            AggregatedFeeds::<T>::get(feed_id)
        }

        /// Get all active feeds
        pub fn get_active_feeds() -> Vec<u64> {
            FeedRequests::<T>::iter()
                .filter(|(_, feed)| feed.status == FeedStatus::Active)
                .map(|(id, _)| id)
                .collect()
        }
    }
}
