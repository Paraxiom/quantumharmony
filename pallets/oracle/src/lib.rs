//! # Decentralized Oracle Pallet
//!
//! A priority-queue based decentralized oracle for CAD price feeds.
//!
//! ## Overview
//!
//! This pallet implements a decentralized oracle system that:
//! - Allows authorized reporters to submit CAD/USD price data
//! - Uses a priority queue for submission ordering (reporter reputation-based)
//! - Aggregates prices using median calculation with QRNG tie-breaking
//! - Integrates with the stablecoin pallet for QCAD pegging
//!
//! ## Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────────┐
//! │                    Oracle Price Feed System                         │
//! ├─────────────────────────────────────────────────────────────────────┤
//! │                                                                     │
//! │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐              │
//! │  │ Reporter 1   │  │ Reporter 2   │  │ Reporter N   │              │
//! │  │ (Priority 90)│  │ (Priority 75)│  │ (Priority 50)│              │
//! │  └──────┬───────┘  └──────┬───────┘  └──────┬───────┘              │
//! │         │                 │                 │                       │
//! │         └─────────────────┼─────────────────┘                       │
//! │                           ↓                                         │
//! │              ┌────────────────────────┐                             │
//! │              │  Priority Queue        │                             │
//! │              │  (Reputation-Weighted) │                             │
//! │              └───────────┬────────────┘                             │
//! │                          ↓                                          │
//! │              ┌────────────────────────┐                             │
//! │              │  Median Aggregation    │                             │
//! │              │  + QRNG Tie-Breaking   │                             │
//! │              └───────────┬────────────┘                             │
//! │                          ↓                                          │
//! │              ┌────────────────────────┐                             │
//! │              │  Stablecoin Pallet     │                             │
//! │              │  (QCAD Price Update)   │                             │
//! │              └────────────────────────┘                             │
//! │                                                                     │
//! └─────────────────────────────────────────────────────────────────────┘
//! ```
//!
//! ## Security
//!
//! - Reporters must stake QMHY to participate (slashable)
//! - Price submissions are validated against deviation limits
//! - Reputation system rewards accurate reporters
//! - QRNG provides unpredictable tie-breaking

#![cfg_attr(not(feature = "std"), no_std)]

pub use pallet::*;

#[cfg(test)]
mod tests;

#[frame_support::pallet]
pub mod pallet {
    use frame_support::{
        pallet_prelude::*,
        traits::{Currency, ReservableCurrency, Get},
    };
    use frame_system::pallet_prelude::*;
    use sp_runtime::{
        traits::Saturating,
        FixedU128, FixedPointNumber,
    };
    use sp_std::prelude::*;

    /// Balance type
    pub type BalanceOf<T> =
        <<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;

    /// Price type - fixed point with 18 decimals
    pub type Price = FixedU128;

    /// Maximum reporters
    pub const MAX_REPORTERS: u32 = 50;

    /// Maximum price submissions per round
    pub const MAX_SUBMISSIONS_PER_ROUND: u32 = 100;

    /// Minimum reporters for valid price
    pub const MIN_REPORTERS_FOR_VALID_PRICE: u32 = 3;

    /// Maximum supported feeds per reporter (there are only 3 feeds)
    pub const MAX_SUPPORTED_FEEDS: u32 = 3;

    /// Reporter proposal voting period in blocks
    pub const REPORTER_VOTING_PERIOD: u32 = 100;

    /// Minimum votes required to finalize a proposal
    pub const MIN_VOTES_FOR_PROPOSAL: u32 = 2;

    // ==================== DATA STRUCTURES ====================

    /// Reporter status
    #[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, TypeInfo, MaxEncodedLen, Default)]
    pub enum ReporterStatus {
        /// Reporter is active and can submit prices
        #[default]
        Active,
        /// Reporter is suspended (missed too many rounds)
        Suspended,
        /// Reporter is slashed (submitted malicious data)
        Slashed,
    }

    /// Price feed types
    #[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, TypeInfo, MaxEncodedLen, Default, Copy)]
    pub enum PriceFeed {
        /// CAD/USD exchange rate
        #[default]
        CadUsd,
        /// QMHY/USD price
        QmhyUsd,
        /// QMHY/CAD price (derived or direct)
        QmhyCad,
    }

    /// Oracle reporter registration
    #[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
    #[scale_info(skip_type_params(T))]
    pub struct Reporter<T: Config> {
        /// Reporter account
        pub account: T::AccountId,
        /// Staked QMHY (slashable)
        pub stake: BalanceOf<T>,
        /// Reputation score (0-100)
        pub reputation: u8,
        /// Priority in queue (derived from reputation + stake)
        pub priority: u32,
        /// Total successful submissions
        pub successful_submissions: u64,
        /// Total submissions
        pub total_submissions: u64,
        /// Block when registered
        pub registered_at: BlockNumberFor<T>,
        /// Reporter status
        pub status: ReporterStatus,
        /// Supported price feeds (stored as u8: 0=CadUsd, 1=QmhyUsd, 2=QmhyCad)
        pub supported_feeds: BoundedVec<u8, ConstU32<MAX_SUPPORTED_FEEDS>>,
    }

    /// Price submission from a reporter
    #[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
    #[scale_info(skip_type_params(T))]
    pub struct PriceSubmission<T: Config> {
        /// Reporter who submitted
        pub reporter: T::AccountId,
        /// Price value (18 decimals)
        pub price: u128,
        /// Feed type
        pub feed: PriceFeed,
        /// Block when submitted
        pub submitted_at: BlockNumberFor<T>,
        /// Reporter's priority at submission time
        pub priority: u32,
        /// Source identifier (e.g., "binance", "kraken", "average")
        pub source: [u8; 32],
    }

    /// Aggregated price for a round
    #[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
    pub struct AggregatedPrice {
        /// Median price
        pub price: u128,
        /// Number of submissions
        pub submission_count: u32,
        /// Block when aggregated
        pub aggregated_at: u64,
        /// Feed type
        pub feed: PriceFeed,
        /// Standard deviation (for quality assessment)
        pub std_deviation: u128,
    }

    /// Reporter proposal for validator approval
    #[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
    #[scale_info(skip_type_params(T))]
    pub struct ReporterProposal<T: Config> {
        /// Candidate account wanting to become a reporter
        pub candidate: T::AccountId,
        /// Proposed stake amount
        pub stake: BalanceOf<T>,
        /// Supported price feeds
        pub supported_feeds: BoundedVec<u8, ConstU32<MAX_SUPPORTED_FEEDS>>,
        /// Block when proposed
        pub proposed_at: BlockNumberFor<T>,
        /// Account that created the proposal
        pub proposer: T::AccountId,
        /// Yes votes count
        pub yes_votes: u32,
        /// No votes count
        pub no_votes: u32,
        /// Whether voting has been finalized
        pub finalized: bool,
        /// Whether proposal was approved (only valid if finalized)
        pub approved: bool,
    }

    // ==================== PALLET CONFIG ====================

    #[pallet::config]
    pub trait Config: frame_system::Config {
        /// The overarching event type
        type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

        /// Currency type for staking
        type Currency: Currency<Self::AccountId> + ReservableCurrency<Self::AccountId>;

        /// Minimum stake to become a reporter
        #[pallet::constant]
        type MinReporterStake: Get<BalanceOf<Self>>;

        /// Maximum price deviation from median (in parts per million)
        /// e.g., 50_000 = 5%
        #[pallet::constant]
        type MaxPriceDeviation: Get<u32>;

        /// Blocks between price aggregation rounds
        #[pallet::constant]
        type AggregationPeriod: Get<BlockNumberFor<Self>>;

        /// Slash percentage for malicious reporters (parts per million)
        #[pallet::constant]
        type SlashPercent: Get<u32>;

        /// Origin that can force price updates (emergency governance)
        type ForceOrigin: EnsureOrigin<Self::RuntimeOrigin>;

        /// Origin that can manage reporters
        type AdminOrigin: EnsureOrigin<Self::RuntimeOrigin>;
    }

    #[pallet::pallet]
    #[pallet::without_storage_info]
    pub struct Pallet<T>(_);

    // ==================== STORAGE ====================

    /// All registered reporters
    #[pallet::storage]
    #[pallet::getter(fn reporters)]
    pub type Reporters<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        T::AccountId,
        Reporter<T>,
        OptionQuery,
    >;

    /// Current round submissions (feed -> submissions)
    #[pallet::storage]
    #[pallet::getter(fn current_submissions)]
    pub type CurrentSubmissions<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        PriceFeed,
        BoundedVec<PriceSubmission<T>, ConstU32<MAX_SUBMISSIONS_PER_ROUND>>,
        ValueQuery,
    >;

    /// Latest aggregated prices
    #[pallet::storage]
    #[pallet::getter(fn latest_price)]
    pub type LatestPrice<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        PriceFeed,
        AggregatedPrice,
        OptionQuery,
    >;

    /// Last aggregation block
    #[pallet::storage]
    #[pallet::getter(fn last_aggregation_block)]
    pub type LastAggregationBlock<T: Config> = StorageValue<_, BlockNumberFor<T>, ValueQuery>;

    /// Current round number
    #[pallet::storage]
    #[pallet::getter(fn current_round)]
    pub type CurrentRound<T: Config> = StorageValue<_, u64, ValueQuery>;

    /// Total active reporters
    #[pallet::storage]
    #[pallet::getter(fn total_reporters)]
    pub type TotalReporters<T: Config> = StorageValue<_, u32, ValueQuery>;

    /// QRNG seed for tie-breaking (updated each round)
    #[pallet::storage]
    #[pallet::getter(fn qrng_seed)]
    pub type QrngSeed<T: Config> = StorageValue<_, [u8; 32], ValueQuery>;

    /// Reporter approval proposals
    #[pallet::storage]
    #[pallet::getter(fn reporter_proposals)]
    pub type ReporterProposals<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        u32, // proposal_id
        ReporterProposal<T>,
        OptionQuery,
    >;

    /// Votes on reporter proposals (proposal_id -> voter -> has_voted)
    #[pallet::storage]
    pub type ReporterVotes<T: Config> = StorageDoubleMap<
        _,
        Blake2_128Concat,
        u32, // proposal_id
        Blake2_128Concat,
        T::AccountId, // voter
        bool,
        ValueQuery,
    >;

    /// Next reporter proposal ID
    #[pallet::storage]
    pub type NextReporterProposalId<T: Config> = StorageValue<_, u32, ValueQuery>;

    // ==================== EVENTS ====================

    #[pallet::event]
    #[pallet::generate_deposit(pub(super) fn deposit_event)]
    pub enum Event<T: Config> {
        /// Reporter registered
        ReporterRegistered {
            reporter: T::AccountId,
            stake: BalanceOf<T>,
        },
        /// Reporter deregistered
        ReporterDeregistered {
            reporter: T::AccountId,
            stake_returned: BalanceOf<T>,
        },
        /// Price submitted
        /// feed: 0=CadUsd, 1=QmhyUsd, 2=QmhyCad
        PriceSubmitted {
            reporter: T::AccountId,
            feed: u8,
            price: u128,
            priority: u32,
        },
        /// Price aggregated
        /// feed: 0=CadUsd, 1=QmhyUsd, 2=QmhyCad
        PriceAggregated {
            feed: u8,
            price: u128,
            submission_count: u32,
            round: u64,
        },
        /// Reporter reputation updated
        ReputationUpdated {
            reporter: T::AccountId,
            old_reputation: u8,
            new_reputation: u8,
        },
        /// Reporter slashed
        /// reason: 0=ExcessiveDeviation, 1=InactiveReporter, 2=GovernanceSlash
        ReporterSlashed {
            reporter: T::AccountId,
            amount: BalanceOf<T>,
            reason: u8,
        },
        /// QRNG seed updated
        QrngSeedUpdated {
            seed: [u8; 32],
        },
        /// Emergency price update
        /// feed: 0=CadUsd, 1=QmhyUsd, 2=QmhyCad
        EmergencyPriceUpdate {
            feed: u8,
            price: u128,
        },
        /// Reporter proposal created
        ReporterProposalCreated {
            proposal_id: u32,
            candidate: T::AccountId,
            proposer: T::AccountId,
        },
        /// Vote cast on reporter proposal
        ReporterVoteCast {
            proposal_id: u32,
            voter: T::AccountId,
            approve: bool,
        },
        /// Reporter proposal finalized
        ReporterProposalFinalized {
            proposal_id: u32,
            approved: bool,
            yes_votes: u32,
            no_votes: u32,
        },
    }

    impl PriceFeed {
        fn to_u8(&self) -> u8 {
            match self {
                PriceFeed::CadUsd => 0,
                PriceFeed::QmhyUsd => 1,
                PriceFeed::QmhyCad => 2,
            }
        }

        fn from_u8(val: u8) -> Option<Self> {
            match val {
                0 => Some(PriceFeed::CadUsd),
                1 => Some(PriceFeed::QmhyUsd),
                2 => Some(PriceFeed::QmhyCad),
                _ => None,
            }
        }
    }

    // ==================== ERRORS ====================

    #[pallet::error]
    pub enum Error<T> {
        /// Already registered as reporter
        AlreadyRegistered,
        /// Not registered as reporter
        NotRegistered,
        /// Insufficient stake
        InsufficientStake,
        /// Reporter not active
        ReporterNotActive,
        /// Price deviation too high
        PriceDeviationTooHigh,
        /// Too many submissions this round
        TooManySubmissions,
        /// Not enough reporters for valid price
        NotEnoughReporters,
        /// Feed not supported by reporter
        FeedNotSupported,
        /// Cannot deregister during active round
        ActiveRoundInProgress,
        /// Overflow error
        Overflow,
        /// Zero price not allowed
        ZeroPrice,
        /// Already submitted this round
        AlreadySubmittedThisRound,
        /// Invalid feed value
        InvalidFeed,
        /// Proposal not found
        ProposalNotFound,
        /// Already voted on this proposal
        AlreadyVoted,
        /// Voting period not ended
        VotingPeriodNotEnded,
        /// Proposal already finalized
        ProposalAlreadyFinalized,
        /// Not a validator (cannot vote)
        NotValidator,
        /// Proposal not approved
        ProposalNotApproved,
    }

    // ==================== HOOKS ====================

    #[pallet::hooks]
    impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
        fn on_initialize(block: BlockNumberFor<T>) -> Weight {
            let last_aggregation = LastAggregationBlock::<T>::get();
            let period = T::AggregationPeriod::get();

            // Check if we should aggregate
            if block >= last_aggregation.saturating_add(period) {
                // Aggregate all feeds
                let _ = Self::aggregate_all_prices(block);
                LastAggregationBlock::<T>::put(block);

                // Increment round
                let round = CurrentRound::<T>::get().saturating_add(1);
                CurrentRound::<T>::put(round);

                Weight::from_parts(100_000, 0)
            } else {
                Weight::from_parts(1_000, 0)
            }
        }
    }

    // ==================== DISPATCHABLES ====================

    #[pallet::call]
    impl<T: Config> Pallet<T> {
        /// Register as an oracle reporter.
        ///
        /// ## Parameters
        /// - `stake`: Amount of QMHY to stake (min: MinReporterStake)
        /// - `supported_feeds`: Price feeds this reporter will support (0=CadUsd, 1=QmhyUsd, 2=QmhyCad)
        #[pallet::call_index(0)]
        #[pallet::weight(Weight::from_parts(60_000, 0))]
        pub fn register_reporter(
            origin: OriginFor<T>,
            stake: BalanceOf<T>,
            supported_feeds_u8: Vec<u8>,
        ) -> DispatchResult {
            let who = ensure_signed(origin)?;

            // Validate feed values
            for feed_u8 in supported_feeds_u8.iter() {
                ensure!(PriceFeed::from_u8(*feed_u8).is_some(), Error::<T>::InvalidFeed);
            }

            // Convert to BoundedVec
            let supported_feeds: BoundedVec<u8, ConstU32<MAX_SUPPORTED_FEEDS>> =
                supported_feeds_u8.try_into().map_err(|_| Error::<T>::TooManySubmissions)?;

            ensure!(!Reporters::<T>::contains_key(&who), Error::<T>::AlreadyRegistered);
            ensure!(stake >= T::MinReporterStake::get(), Error::<T>::InsufficientStake);
            ensure!(!supported_feeds.is_empty(), Error::<T>::FeedNotSupported);

            // Reserve stake
            T::Currency::reserve(&who, stake)?;

            let current_block = frame_system::Pallet::<T>::block_number();

            // Initial priority based on stake (normalized to 0-100)
            let stake_u128: u128 = stake.try_into().map_err(|_| Error::<T>::Overflow)?;
            let min_stake_u128: u128 = T::MinReporterStake::get().try_into().map_err(|_| Error::<T>::Overflow)?;
            let stake_factor = (stake_u128.saturating_mul(50) / min_stake_u128).min(50) as u32;
            let initial_priority = 50u32.saturating_add(stake_factor); // 50-100 based on stake

            let reporter = Reporter {
                account: who.clone(),
                stake,
                reputation: 50, // Start with neutral reputation
                priority: initial_priority,
                successful_submissions: 0,
                total_submissions: 0,
                registered_at: current_block,
                status: ReporterStatus::Active,
                supported_feeds,
            };

            Reporters::<T>::insert(&who, reporter);
            TotalReporters::<T>::mutate(|t| *t = t.saturating_add(1));

            Self::deposit_event(Event::ReporterRegistered {
                reporter: who,
                stake,
            });

            Ok(())
        }

        /// Deregister as a reporter and reclaim stake.
        #[pallet::call_index(1)]
        #[pallet::weight(Weight::from_parts(50_000, 0))]
        pub fn deregister_reporter(origin: OriginFor<T>) -> DispatchResult {
            let who = ensure_signed(origin)?;

            let reporter = Reporters::<T>::get(&who).ok_or(Error::<T>::NotRegistered)?;

            // Check not in active round (simple check: not submitted this round)
            let all_feeds = [PriceFeed::CadUsd, PriceFeed::QmhyUsd, PriceFeed::QmhyCad];
            for feed in all_feeds.iter() {
                let submissions = CurrentSubmissions::<T>::get(feed);
                let has_submission = submissions.iter().any(|s| s.reporter == who);
                ensure!(!has_submission, Error::<T>::ActiveRoundInProgress);
            }

            // Return stake
            T::Currency::unreserve(&who, reporter.stake);

            Reporters::<T>::remove(&who);
            TotalReporters::<T>::mutate(|t| *t = t.saturating_sub(1));

            Self::deposit_event(Event::ReporterDeregistered {
                reporter: who,
                stake_returned: reporter.stake,
            });

            Ok(())
        }

        /// Submit a price for a feed.
        ///
        /// ## Parameters
        /// - `feed`: The price feed type (0=CadUsd, 1=QmhyUsd, 2=QmhyCad)
        /// - `price`: Price value (18 decimals fixed point)
        /// - `source`: Source identifier (32 bytes, e.g., "binance", "kraken")
        #[pallet::call_index(2)]
        #[pallet::weight(Weight::from_parts(40_000, 0))]
        pub fn submit_price(
            origin: OriginFor<T>,
            feed: u8,
            price: u128,
            source: [u8; 32],
        ) -> DispatchResult {
            let who = ensure_signed(origin)?;

            ensure!(price > 0, Error::<T>::ZeroPrice);
            let feed_enum = PriceFeed::from_u8(feed).ok_or(Error::<T>::InvalidFeed)?;

            let mut reporter = Reporters::<T>::get(&who).ok_or(Error::<T>::NotRegistered)?;
            ensure!(reporter.status == ReporterStatus::Active, Error::<T>::ReporterNotActive);
            ensure!(reporter.supported_feeds.contains(&feed), Error::<T>::FeedNotSupported);

            let feed = feed_enum;

            // Check not already submitted this round
            let submissions = CurrentSubmissions::<T>::get(&feed);
            ensure!(
                !submissions.iter().any(|s| s.reporter == who),
                Error::<T>::AlreadySubmittedThisRound
            );

            // Validate price against current median (if exists)
            if let Some(current_price) = LatestPrice::<T>::get(&feed) {
                let deviation = Self::calculate_deviation(price, current_price.price);
                ensure!(
                    deviation <= T::MaxPriceDeviation::get(),
                    Error::<T>::PriceDeviationTooHigh
                );
            }

            let current_block = frame_system::Pallet::<T>::block_number();

            let submission = PriceSubmission {
                reporter: who.clone(),
                price,
                feed,
                submitted_at: current_block,
                priority: reporter.priority,
                source,
            };

            // Add to submissions (priority queue ordering happens during aggregation)
            CurrentSubmissions::<T>::try_mutate(&feed, |subs| {
                subs.try_push(submission).map_err(|_| Error::<T>::TooManySubmissions)
            })?;

            // Update reporter stats
            reporter.total_submissions = reporter.total_submissions.saturating_add(1);
            Reporters::<T>::insert(&who, reporter.clone());

            Self::deposit_event(Event::PriceSubmitted {
                reporter: who,
                feed: feed.to_u8(),
                price,
                priority: reporter.priority,
            });

            Ok(())
        }

        /// Add stake to increase priority.
        #[pallet::call_index(3)]
        #[pallet::weight(Weight::from_parts(30_000, 0))]
        pub fn add_stake(origin: OriginFor<T>, additional_stake: BalanceOf<T>) -> DispatchResult {
            let who = ensure_signed(origin)?;

            let mut reporter = Reporters::<T>::get(&who).ok_or(Error::<T>::NotRegistered)?;

            T::Currency::reserve(&who, additional_stake)?;

            reporter.stake = reporter.stake.saturating_add(additional_stake);

            // Recalculate priority
            let stake_u128: u128 = reporter.stake.try_into().map_err(|_| Error::<T>::Overflow)?;
            let min_stake_u128: u128 = T::MinReporterStake::get().try_into().map_err(|_| Error::<T>::Overflow)?;
            let stake_factor = (stake_u128.saturating_mul(50) / min_stake_u128).min(50) as u32;
            let reputation_factor = (reporter.reputation as u32).saturating_mul(50) / 100;
            reporter.priority = stake_factor.saturating_add(reputation_factor);

            Reporters::<T>::insert(&who, reporter);

            Ok(())
        }

        /// Update QRNG seed for tie-breaking (called by QRNG system).
        #[pallet::call_index(4)]
        #[pallet::weight(Weight::from_parts(10_000, 0))]
        pub fn update_qrng_seed(origin: OriginFor<T>, seed: [u8; 32]) -> DispatchResult {
            T::AdminOrigin::ensure_origin(origin)?;

            QrngSeed::<T>::put(seed);

            Self::deposit_event(Event::QrngSeedUpdated { seed });

            Ok(())
        }

        /// Emergency price update (governance only).
        /// feed: 0=CadUsd, 1=QmhyUsd, 2=QmhyCad
        #[pallet::call_index(5)]
        #[pallet::weight(Weight::from_parts(20_000, 0))]
        pub fn force_price_update(
            origin: OriginFor<T>,
            feed: u8,
            price: u128,
        ) -> DispatchResult {
            T::ForceOrigin::ensure_origin(origin)?;

            ensure!(price > 0, Error::<T>::ZeroPrice);
            let feed = PriceFeed::from_u8(feed).ok_or(Error::<T>::InvalidFeed)?;

            let current_block = frame_system::Pallet::<T>::block_number();
            let block_number: u64 = current_block.try_into().unwrap_or(0);

            let aggregated = AggregatedPrice {
                price,
                submission_count: 1,
                aggregated_at: block_number,
                feed,
                std_deviation: 0,
            };

            LatestPrice::<T>::insert(feed, aggregated);

            Self::deposit_event(Event::EmergencyPriceUpdate { feed: feed.to_u8(), price });

            Ok(())
        }

        /// Slash a malicious reporter (admin only).
        /// reason: 0=ExcessiveDeviation, 1=InactiveReporter, 2=GovernanceSlash
        #[pallet::call_index(6)]
        #[pallet::weight(Weight::from_parts(40_000, 0))]
        pub fn slash_reporter(
            origin: OriginFor<T>,
            reporter_account: T::AccountId,
            reason: u8,
        ) -> DispatchResult {
            T::AdminOrigin::ensure_origin(origin)?;

            let mut reporter = Reporters::<T>::get(&reporter_account).ok_or(Error::<T>::NotRegistered)?;

            // Calculate slash amount
            let stake_u128: u128 = reporter.stake.try_into().map_err(|_| Error::<T>::Overflow)?;
            let slash_percent = T::SlashPercent::get() as u128;
            let slash_amount_u128 = stake_u128.saturating_mul(slash_percent) / 1_000_000;
            let slash_amount: BalanceOf<T> = slash_amount_u128.try_into().map_err(|_| Error::<T>::Overflow)?;

            // Slash stake (burn it)
            // slash_reserved returns (NegativeImbalance, remaining_balance)
            let (_imbalance, remaining) = T::Currency::slash_reserved(&reporter_account, slash_amount);
            let actual_slashed = slash_amount.saturating_sub(remaining);

            reporter.stake = reporter.stake.saturating_sub(actual_slashed);
            reporter.status = ReporterStatus::Slashed;
            reporter.reputation = 0;

            Reporters::<T>::insert(&reporter_account, reporter);

            Self::deposit_event(Event::ReporterSlashed {
                reporter: reporter_account,
                amount: actual_slashed,
                reason,
            });

            Ok(())
        }

        // ==================== REPORTER APPROVAL EXTRINSICS ====================

        /// Propose a new reporter for validator approval.
        ///
        /// Anyone can propose a candidate. The candidate must stake tokens.
        /// Validators vote to approve or reject the proposal.
        #[pallet::call_index(7)]
        #[pallet::weight(Weight::from_parts(50_000, 0))]
        pub fn propose_reporter(
            origin: OriginFor<T>,
            candidate: T::AccountId,
            stake: BalanceOf<T>,
            supported_feeds_u8: Vec<u8>,
        ) -> DispatchResult {
            let proposer = ensure_signed(origin)?;

            // Validate feed values
            for feed_u8 in supported_feeds_u8.iter() {
                ensure!(PriceFeed::from_u8(*feed_u8).is_some(), Error::<T>::InvalidFeed);
            }

            // Convert to BoundedVec
            let supported_feeds: BoundedVec<u8, ConstU32<MAX_SUPPORTED_FEEDS>> =
                supported_feeds_u8.try_into().map_err(|_| Error::<T>::TooManySubmissions)?;

            ensure!(!Reporters::<T>::contains_key(&candidate), Error::<T>::AlreadyRegistered);
            ensure!(stake >= T::MinReporterStake::get(), Error::<T>::InsufficientStake);
            ensure!(!supported_feeds.is_empty(), Error::<T>::FeedNotSupported);

            // Reserve stake from candidate
            T::Currency::reserve(&candidate, stake)?;

            let current_block = frame_system::Pallet::<T>::block_number();
            let proposal_id = NextReporterProposalId::<T>::get();

            let proposal = ReporterProposal {
                candidate: candidate.clone(),
                stake,
                supported_feeds,
                proposed_at: current_block,
                proposer: proposer.clone(),
                yes_votes: 0,
                no_votes: 0,
                finalized: false,
                approved: false,
            };

            ReporterProposals::<T>::insert(proposal_id, proposal);
            NextReporterProposalId::<T>::put(proposal_id.saturating_add(1));

            Self::deposit_event(Event::ReporterProposalCreated {
                proposal_id,
                candidate,
                proposer,
            });

            Ok(())
        }

        /// Vote on a reporter proposal.
        ///
        /// Only existing active reporters (validators) can vote.
        #[pallet::call_index(8)]
        #[pallet::weight(Weight::from_parts(30_000, 0))]
        pub fn vote_on_reporter(
            origin: OriginFor<T>,
            proposal_id: u32,
            approve: bool,
        ) -> DispatchResult {
            let voter = ensure_signed(origin)?;

            // Only active reporters can vote
            let voter_reporter = Reporters::<T>::get(&voter).ok_or(Error::<T>::NotValidator)?;
            ensure!(voter_reporter.status == ReporterStatus::Active, Error::<T>::NotValidator);

            let mut proposal = ReporterProposals::<T>::get(proposal_id).ok_or(Error::<T>::ProposalNotFound)?;
            ensure!(!proposal.finalized, Error::<T>::ProposalAlreadyFinalized);

            // Check voting period
            let current_block = frame_system::Pallet::<T>::block_number();
            let voting_end = proposal.proposed_at.saturating_add(REPORTER_VOTING_PERIOD.into());
            ensure!(current_block <= voting_end, Error::<T>::VotingPeriodNotEnded);

            // Check not already voted
            ensure!(!ReporterVotes::<T>::get(proposal_id, &voter), Error::<T>::AlreadyVoted);

            // Record vote
            ReporterVotes::<T>::insert(proposal_id, &voter, true);

            if approve {
                proposal.yes_votes = proposal.yes_votes.saturating_add(1);
            } else {
                proposal.no_votes = proposal.no_votes.saturating_add(1);
            }

            ReporterProposals::<T>::insert(proposal_id, proposal);

            Self::deposit_event(Event::ReporterVoteCast {
                proposal_id,
                voter,
                approve,
            });

            Ok(())
        }

        /// Finalize a reporter proposal after voting period ends.
        ///
        /// If approved, registers the candidate as a reporter.
        /// If rejected, returns the stake to the candidate.
        #[pallet::call_index(9)]
        #[pallet::weight(Weight::from_parts(60_000, 0))]
        pub fn finalize_reporter_proposal(
            origin: OriginFor<T>,
            proposal_id: u32,
        ) -> DispatchResult {
            let _who = ensure_signed(origin)?;

            let mut proposal = ReporterProposals::<T>::get(proposal_id).ok_or(Error::<T>::ProposalNotFound)?;
            ensure!(!proposal.finalized, Error::<T>::ProposalAlreadyFinalized);

            // Check voting period ended
            let current_block = frame_system::Pallet::<T>::block_number();
            let voting_end = proposal.proposed_at.saturating_add(REPORTER_VOTING_PERIOD.into());
            ensure!(current_block > voting_end, Error::<T>::VotingPeriodNotEnded);

            // Check minimum votes
            let total_votes = proposal.yes_votes.saturating_add(proposal.no_votes);
            let approved = total_votes >= MIN_VOTES_FOR_PROPOSAL && proposal.yes_votes > proposal.no_votes;

            proposal.finalized = true;
            proposal.approved = approved;

            if approved {
                // Register the reporter
                let stake_u128: u128 = proposal.stake.try_into().map_err(|_| Error::<T>::Overflow)?;
                let min_stake_u128: u128 = T::MinReporterStake::get().try_into().map_err(|_| Error::<T>::Overflow)?;
                let stake_factor = (stake_u128.saturating_mul(50) / min_stake_u128).min(50) as u32;
                let initial_priority = 50u32.saturating_add(stake_factor);

                let reporter = Reporter {
                    account: proposal.candidate.clone(),
                    stake: proposal.stake,
                    reputation: 50,
                    priority: initial_priority,
                    successful_submissions: 0,
                    total_submissions: 0,
                    registered_at: current_block,
                    status: ReporterStatus::Active,
                    supported_feeds: proposal.supported_feeds.clone(),
                };

                Reporters::<T>::insert(&proposal.candidate, reporter);
                TotalReporters::<T>::mutate(|n| *n = n.saturating_add(1));

                Self::deposit_event(Event::ReporterRegistered {
                    reporter: proposal.candidate.clone(),
                    stake: proposal.stake,
                });
            } else {
                // Return stake to candidate
                T::Currency::unreserve(&proposal.candidate, proposal.stake);
            }

            ReporterProposals::<T>::insert(proposal_id, proposal.clone());

            Self::deposit_event(Event::ReporterProposalFinalized {
                proposal_id,
                approved,
                yes_votes: proposal.yes_votes,
                no_votes: proposal.no_votes,
            });

            Ok(())
        }
    }

    // ==================== HELPER FUNCTIONS ====================

    impl<T: Config> Pallet<T> {
        /// Aggregate prices for all feeds
        fn aggregate_all_prices(block: BlockNumberFor<T>) -> DispatchResult {
            let feeds = [PriceFeed::CadUsd, PriceFeed::QmhyUsd, PriceFeed::QmhyCad];
            let round = CurrentRound::<T>::get();

            for feed in feeds.iter() {
                let _ = Self::aggregate_price_for_feed(*feed, block, round);
            }

            Ok(())
        }

        /// Aggregate price for a specific feed
        fn aggregate_price_for_feed(feed: PriceFeed, block: BlockNumberFor<T>, round: u64) -> DispatchResult {
            let submissions = CurrentSubmissions::<T>::take(&feed);

            if submissions.len() < MIN_REPORTERS_FOR_VALID_PRICE as usize {
                return Err(Error::<T>::NotEnoughReporters.into());
            }

            // Sort by priority (descending) for weighted consideration
            let mut sorted_submissions: Vec<_> = submissions.into_iter().collect();
            sorted_submissions.sort_by(|a, b| b.priority.cmp(&a.priority));

            // Extract prices
            let prices: Vec<u128> = sorted_submissions.iter().map(|s| s.price).collect();

            // Calculate weighted median
            let median_price = Self::calculate_weighted_median(&sorted_submissions);

            // Calculate standard deviation
            let std_dev = Self::calculate_std_deviation(&prices, median_price);

            // Update reporter reputations
            for submission in sorted_submissions.iter() {
                let deviation = Self::calculate_deviation(submission.price, median_price);
                let _ = Self::update_reporter_reputation(&submission.reporter, deviation);
            }

            let block_number: u64 = block.try_into().unwrap_or(0);

            let aggregated = AggregatedPrice {
                price: median_price,
                submission_count: sorted_submissions.len() as u32,
                aggregated_at: block_number,
                feed,
                std_deviation: std_dev,
            };

            LatestPrice::<T>::insert(feed, aggregated);

            Self::deposit_event(Event::PriceAggregated {
                feed: feed.to_u8(),
                price: median_price,
                submission_count: sorted_submissions.len() as u32,
                round,
            });

            Ok(())
        }

        /// Calculate weighted median using priority scores
        fn calculate_weighted_median(submissions: &[PriceSubmission<T>]) -> u128 {
            if submissions.is_empty() {
                return 0;
            }

            // Sort by price
            let mut price_priority: Vec<(u128, u32)> = submissions
                .iter()
                .map(|s| (s.price, s.priority))
                .collect();
            price_priority.sort_by(|a, b| a.0.cmp(&b.0));

            // Calculate total weight
            let total_weight: u32 = price_priority.iter().map(|(_, p)| *p).sum();
            let half_weight = total_weight / 2;

            // Find weighted median
            let mut cumulative_weight = 0u32;
            for (price, priority) in price_priority.iter() {
                cumulative_weight = cumulative_weight.saturating_add(*priority);
                if cumulative_weight >= half_weight {
                    return *price;
                }
            }

            // Fallback to last price
            price_priority.last().map(|(p, _)| *p).unwrap_or(0)
        }

        /// Calculate standard deviation
        fn calculate_std_deviation(prices: &[u128], mean: u128) -> u128 {
            if prices.is_empty() {
                return 0;
            }

            let variance: u128 = prices.iter().map(|p| {
                let diff = if *p > mean { *p - mean } else { mean - *p };
                diff.saturating_mul(diff) / prices.len() as u128
            }).sum();

            // Integer square root approximation
            Self::isqrt(variance)
        }

        /// Integer square root
        fn isqrt(n: u128) -> u128 {
            if n == 0 {
                return 0;
            }
            let mut x = n;
            let mut y = (x + 1) / 2;
            while y < x {
                x = y;
                y = (x + n / x) / 2;
            }
            x
        }

        /// Calculate deviation between two prices (parts per million)
        fn calculate_deviation(price: u128, reference: u128) -> u32 {
            if reference == 0 {
                return 0;
            }

            let diff = if price > reference {
                price.saturating_sub(reference)
            } else {
                reference.saturating_sub(price)
            };

            (diff.saturating_mul(1_000_000) / reference).min(u32::MAX as u128) as u32
        }

        /// Update reporter reputation based on submission accuracy
        fn update_reporter_reputation(account: &T::AccountId, deviation: u32) -> DispatchResult {
            let mut reporter = Reporters::<T>::get(account).ok_or(Error::<T>::NotRegistered)?;

            let old_reputation = reporter.reputation;

            // Deviation < 1% = +2 reputation
            // Deviation < 2% = +1 reputation
            // Deviation < 5% = no change
            // Deviation > 5% = -2 reputation
            // Deviation > 10% = -5 reputation
            let new_reputation = if deviation < 10_000 {
                reporter.reputation.saturating_add(2).min(100)
            } else if deviation < 20_000 {
                reporter.reputation.saturating_add(1).min(100)
            } else if deviation < 50_000 {
                reporter.reputation
            } else if deviation < 100_000 {
                reporter.reputation.saturating_sub(2)
            } else {
                reporter.reputation.saturating_sub(5)
            };

            reporter.reputation = new_reputation;
            reporter.successful_submissions = reporter.successful_submissions.saturating_add(1);

            // Recalculate priority
            let stake_u128: u128 = reporter.stake.try_into().unwrap_or(0);
            let min_stake_u128: u128 = T::MinReporterStake::get().try_into().unwrap_or(1);
            let stake_factor = (stake_u128.saturating_mul(50) / min_stake_u128).min(50) as u32;
            let reputation_factor = (reporter.reputation as u32).saturating_mul(50) / 100;
            reporter.priority = stake_factor.saturating_add(reputation_factor);

            Reporters::<T>::insert(account, reporter);

            if old_reputation != new_reputation {
                Self::deposit_event(Event::ReputationUpdated {
                    reporter: account.clone(),
                    old_reputation,
                    new_reputation,
                });
            }

            Ok(())
        }

        // ==================== PUBLIC QUERIES ====================

        /// Get the latest price for a feed
        pub fn get_price(feed: PriceFeed) -> Option<u128> {
            LatestPrice::<T>::get(feed).map(|p| p.price)
        }

        /// Get CAD/USD exchange rate
        pub fn get_cad_usd_rate() -> Option<u128> {
            Self::get_price(PriceFeed::CadUsd)
        }

        /// Get QMHY/CAD price
        pub fn get_qmhy_cad_price() -> Option<u128> {
            Self::get_price(PriceFeed::QmhyCad)
        }

        /// Get all active reporters
        pub fn get_active_reporters() -> Vec<T::AccountId> {
            Reporters::<T>::iter()
                .filter(|(_, r)| r.status == ReporterStatus::Active)
                .map(|(_, r)| r.account)
                .collect()
        }

        /// Get reporter count
        pub fn get_reporter_count() -> u32 {
            TotalReporters::<T>::get()
        }
    }
}
