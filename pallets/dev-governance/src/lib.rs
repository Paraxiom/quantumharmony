//! # Dev Governance Pallet
//!
//! Tokenized voting system for feature proposals and dev bounties.
//!
//! ## Overview
//!
//! This pallet enables token-weighted governance for development decisions:
//! - Create feature proposals with optional bounties
//! - Vote on proposals by staking tokens
//! - Claim bounties for completed work
//! - Track proposal status through lifecycle
//!
//! ## Dispatchables
//!
//! - `create_proposal` - Submit a new feature proposal
//! - `vote` - Cast a token-weighted vote on a proposal
//! - `close_voting` - End voting period and determine outcome
//! - `claim_bounty` - Claim bounty for approved work
//! - `cancel_proposal` - Cancel a proposal (proposer or admin only)

#![cfg_attr(not(feature = "std"), no_std)]

pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {
    use frame_support::{
        pallet_prelude::*,
        traits::{Currency, ReservableCurrency, ExistenceRequirement},
    };
    use frame_system::pallet_prelude::*;
    use scale_codec::{Decode, DecodeWithMemTracking, Encode, MaxEncodedLen};
    use scale_info::TypeInfo;
    use sp_runtime::traits::{Saturating, Zero};
    use sp_std::vec::Vec;

    /// Maximum length for proposal title
    pub const MAX_TITLE_LENGTH: u32 = 128;
    /// Maximum length for proposal description
    pub const MAX_DESCRIPTION_LENGTH: u32 = 1024;

    /// Proposal status
    #[derive(Clone, Encode, Decode, TypeInfo, MaxEncodedLen, PartialEq, Eq, Debug)]
    pub enum ProposalStatus {
        /// Voting is open
        Open,
        /// Proposal approved, work in progress
        Approved,
        /// Proposal rejected by vote
        Rejected,
        /// Work completed, bounty claimed
        Completed,
        /// Cancelled by proposer or admin
        Cancelled,
    }

    impl Default for ProposalStatus {
        fn default() -> Self {
            ProposalStatus::Open
        }
    }

    /// Vote direction
    #[derive(Clone, Encode, Decode, DecodeWithMemTracking, TypeInfo, MaxEncodedLen, PartialEq, Eq, Debug)]
    pub enum VoteDirection {
        Aye,
        Nay,
    }

    /// A feature proposal
    #[derive(Clone, Encode, Decode, TypeInfo, MaxEncodedLen)]
    #[scale_info(skip_type_params(T))]
    pub struct Proposal<T: Config> {
        /// Proposal creator
        pub proposer: T::AccountId,
        /// Title (bounded)
        pub title: BoundedVec<u8, ConstU32<MAX_TITLE_LENGTH>>,
        /// Description (bounded)
        pub description: BoundedVec<u8, ConstU32<MAX_DESCRIPTION_LENGTH>>,
        /// Bounty amount (0 = no bounty)
        pub bounty: BalanceOf<T>,
        /// Current status
        pub status: ProposalStatus,
        /// Total Aye votes (token-weighted)
        pub aye_votes: BalanceOf<T>,
        /// Total Nay votes (token-weighted)
        pub nay_votes: BalanceOf<T>,
        /// Block when voting ends
        pub voting_end: BlockNumberFor<T>,
        /// Assigned developer (if approved)
        pub assignee: Option<T::AccountId>,
    }

    /// A vote record
    #[derive(Clone, Encode, Decode, TypeInfo, MaxEncodedLen)]
    #[scale_info(skip_type_params(T))]
    pub struct Vote<T: Config> {
        /// Vote direction
        pub direction: VoteDirection,
        /// Amount staked for this vote
        pub amount: BalanceOf<T>,
    }

    /// Balance type alias
    pub type BalanceOf<T> =
        <<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;

    #[pallet::pallet]
    pub struct Pallet<T>(_);

    #[pallet::config]
    pub trait Config: frame_system::Config {
        /// Runtime event type
        type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

        /// Currency for staking/bounties
        type Currency: Currency<Self::AccountId> + ReservableCurrency<Self::AccountId>;

        /// Minimum stake required to create a proposal
        #[pallet::constant]
        type MinProposalDeposit: Get<BalanceOf<Self>>;

        /// Minimum stake required to vote
        #[pallet::constant]
        type MinVoteStake: Get<BalanceOf<Self>>;

        /// Default voting period in blocks
        #[pallet::constant]
        type DefaultVotingPeriod: Get<BlockNumberFor<Self>>;

        /// Admin origin for privileged operations
        type AdminOrigin: EnsureOrigin<Self::RuntimeOrigin>;
    }

    /// Next proposal ID
    #[pallet::storage]
    #[pallet::getter(fn next_proposal_id)]
    pub type NextProposalId<T> = StorageValue<_, u32, ValueQuery>;

    /// All proposals
    #[pallet::storage]
    #[pallet::getter(fn proposals)]
    pub type Proposals<T: Config> = StorageMap<_, Blake2_128Concat, u32, Proposal<T>>;

    /// Votes by (proposal_id, voter)
    #[pallet::storage]
    #[pallet::getter(fn votes)]
    pub type Votes<T: Config> =
        StorageDoubleMap<_, Blake2_128Concat, u32, Blake2_128Concat, T::AccountId, Vote<T>>;

    #[pallet::event]
    #[pallet::generate_deposit(pub(super) fn deposit_event)]
    pub enum Event<T: Config> {
        /// Proposal created [proposal_id, proposer, bounty]
        ProposalCreated {
            proposal_id: u32,
            proposer: T::AccountId,
            bounty: BalanceOf<T>,
        },
        /// Vote cast [proposal_id, voter, direction, amount]
        VoteCast {
            proposal_id: u32,
            voter: T::AccountId,
            direction: VoteDirection,
            amount: BalanceOf<T>,
        },
        /// Voting closed [proposal_id, approved]
        VotingClosed {
            proposal_id: u32,
            approved: bool,
        },
        /// Developer assigned [proposal_id, assignee]
        DeveloperAssigned {
            proposal_id: u32,
            assignee: T::AccountId,
        },
        /// Bounty claimed [proposal_id, claimer, amount]
        BountyClaimed {
            proposal_id: u32,
            claimer: T::AccountId,
            amount: BalanceOf<T>,
        },
        /// Proposal cancelled [proposal_id]
        ProposalCancelled {
            proposal_id: u32,
        },
    }

    #[pallet::error]
    pub enum Error<T> {
        /// Proposal not found
        ProposalNotFound,
        /// Voting period has ended
        VotingEnded,
        /// Voting period still active
        VotingNotEnded,
        /// Proposal not in expected status
        InvalidProposalStatus,
        /// Already voted on this proposal
        AlreadyVoted,
        /// Insufficient balance for operation
        InsufficientBalance,
        /// Not authorized for this operation
        NotAuthorized,
        /// Title too long
        TitleTooLong,
        /// Description too long
        DescriptionTooLong,
        /// No bounty to claim
        NoBounty,
        /// Not assigned to this proposal
        NotAssigned,
    }

    #[pallet::call]
    impl<T: Config> Pallet<T> {
        /// Create a new feature proposal
        ///
        /// - `title`: Short title for the proposal
        /// - `description`: Detailed description
        /// - `bounty`: Optional bounty amount for the work
        /// - `voting_blocks`: Custom voting period (or use default)
        #[pallet::call_index(0)]
        #[pallet::weight(10_000)]
        pub fn create_proposal(
            origin: OriginFor<T>,
            title: Vec<u8>,
            description: Vec<u8>,
            bounty: BalanceOf<T>,
            voting_blocks: Option<BlockNumberFor<T>>,
        ) -> DispatchResult {
            let proposer = ensure_signed(origin)?;

            // Validate inputs
            let title: BoundedVec<u8, ConstU32<MAX_TITLE_LENGTH>> =
                title.try_into().map_err(|_| Error::<T>::TitleTooLong)?;
            let description: BoundedVec<u8, ConstU32<MAX_DESCRIPTION_LENGTH>> =
                description.try_into().map_err(|_| Error::<T>::DescriptionTooLong)?;

            // Reserve deposit
            let deposit = T::MinProposalDeposit::get();
            T::Currency::reserve(&proposer, deposit)?;

            // Reserve bounty if provided
            if !bounty.is_zero() {
                T::Currency::reserve(&proposer, bounty)?;
            }

            // Calculate voting end block
            let current_block = <frame_system::Pallet<T>>::block_number();
            let voting_period = voting_blocks.unwrap_or_else(T::DefaultVotingPeriod::get);
            let voting_end = current_block.saturating_add(voting_period);

            // Create proposal
            let proposal_id = NextProposalId::<T>::get();
            let proposal = Proposal {
                proposer: proposer.clone(),
                title,
                description,
                bounty,
                status: ProposalStatus::Open,
                aye_votes: Zero::zero(),
                nay_votes: Zero::zero(),
                voting_end,
                assignee: None,
            };

            // Store
            Proposals::<T>::insert(proposal_id, proposal);
            NextProposalId::<T>::put(proposal_id.saturating_add(1));

            Self::deposit_event(Event::ProposalCreated {
                proposal_id,
                proposer,
                bounty,
            });

            Ok(())
        }

        /// Vote on a proposal
        ///
        /// Tokens are reserved until voting closes.
        #[pallet::call_index(1)]
        #[pallet::weight(10_000)]
        pub fn vote(
            origin: OriginFor<T>,
            proposal_id: u32,
            direction: VoteDirection,
            amount: BalanceOf<T>,
        ) -> DispatchResult {
            let voter = ensure_signed(origin)?;

            // Validate amount
            ensure!(amount >= T::MinVoteStake::get(), Error::<T>::InsufficientBalance);

            // Get proposal
            let mut proposal = Proposals::<T>::get(proposal_id)
                .ok_or(Error::<T>::ProposalNotFound)?;

            // Check status
            ensure!(proposal.status == ProposalStatus::Open, Error::<T>::InvalidProposalStatus);

            // Check voting period
            let current_block = <frame_system::Pallet<T>>::block_number();
            ensure!(current_block <= proposal.voting_end, Error::<T>::VotingEnded);

            // Check not already voted
            ensure!(!Votes::<T>::contains_key(proposal_id, &voter), Error::<T>::AlreadyVoted);

            // Reserve tokens
            T::Currency::reserve(&voter, amount)?;

            // Record vote
            let vote = Vote {
                direction: direction.clone(),
                amount,
            };
            Votes::<T>::insert(proposal_id, &voter, vote);

            // Update totals
            match direction {
                VoteDirection::Aye => proposal.aye_votes = proposal.aye_votes.saturating_add(amount),
                VoteDirection::Nay => proposal.nay_votes = proposal.nay_votes.saturating_add(amount),
            }
            Proposals::<T>::insert(proposal_id, proposal);

            Self::deposit_event(Event::VoteCast {
                proposal_id,
                voter,
                direction,
                amount,
            });

            Ok(())
        }

        /// Close voting and determine outcome
        ///
        /// Anyone can call this after voting period ends.
        #[pallet::call_index(2)]
        #[pallet::weight(10_000)]
        pub fn close_voting(
            origin: OriginFor<T>,
            proposal_id: u32,
        ) -> DispatchResult {
            ensure_signed(origin)?;

            let mut proposal = Proposals::<T>::get(proposal_id)
                .ok_or(Error::<T>::ProposalNotFound)?;

            // Check status
            ensure!(proposal.status == ProposalStatus::Open, Error::<T>::InvalidProposalStatus);

            // Check voting period ended
            let current_block = <frame_system::Pallet<T>>::block_number();
            ensure!(current_block > proposal.voting_end, Error::<T>::VotingNotEnded);

            // Determine outcome
            let approved = proposal.aye_votes > proposal.nay_votes;
            proposal.status = if approved {
                ProposalStatus::Approved
            } else {
                ProposalStatus::Rejected
            };

            // If rejected, return bounty to proposer
            if !approved && !proposal.bounty.is_zero() {
                T::Currency::unreserve(&proposal.proposer, proposal.bounty);
            }

            // Return deposit to proposer
            T::Currency::unreserve(&proposal.proposer, T::MinProposalDeposit::get());

            Proposals::<T>::insert(proposal_id, proposal);

            Self::deposit_event(Event::VotingClosed {
                proposal_id,
                approved,
            });

            Ok(())
        }

        /// Assign a developer to work on approved proposal
        ///
        /// Only proposer or admin can assign.
        #[pallet::call_index(3)]
        #[pallet::weight(10_000)]
        pub fn assign_developer(
            origin: OriginFor<T>,
            proposal_id: u32,
            developer: T::AccountId,
        ) -> DispatchResult {
            let caller = ensure_signed(origin)?;

            let mut proposal = Proposals::<T>::get(proposal_id)
                .ok_or(Error::<T>::ProposalNotFound)?;

            // Check authorization
            ensure!(caller == proposal.proposer, Error::<T>::NotAuthorized);

            // Check status
            ensure!(proposal.status == ProposalStatus::Approved, Error::<T>::InvalidProposalStatus);

            proposal.assignee = Some(developer.clone());
            Proposals::<T>::insert(proposal_id, proposal);

            Self::deposit_event(Event::DeveloperAssigned {
                proposal_id,
                assignee: developer,
            });

            Ok(())
        }

        /// Claim bounty for completed work
        ///
        /// Only assigned developer can claim. Proposer must approve.
        #[pallet::call_index(4)]
        #[pallet::weight(10_000)]
        pub fn approve_and_pay_bounty(
            origin: OriginFor<T>,
            proposal_id: u32,
        ) -> DispatchResult {
            let caller = ensure_signed(origin)?;

            let mut proposal = Proposals::<T>::get(proposal_id)
                .ok_or(Error::<T>::ProposalNotFound)?;

            // Check caller is proposer
            ensure!(caller == proposal.proposer, Error::<T>::NotAuthorized);

            // Check status
            ensure!(proposal.status == ProposalStatus::Approved, Error::<T>::InvalidProposalStatus);

            // Check there's a bounty
            ensure!(!proposal.bounty.is_zero(), Error::<T>::NoBounty);

            // Check there's an assignee
            let assignee = proposal.assignee.clone().ok_or(Error::<T>::NotAssigned)?;

            // Transfer bounty from proposer's reserved to assignee
            T::Currency::unreserve(&proposal.proposer, proposal.bounty);
            T::Currency::transfer(
                &proposal.proposer,
                &assignee,
                proposal.bounty,
                ExistenceRequirement::KeepAlive,
            )?;

            // Mark completed
            proposal.status = ProposalStatus::Completed;
            let bounty_amount = proposal.bounty;
            Proposals::<T>::insert(proposal_id, proposal);

            Self::deposit_event(Event::BountyClaimed {
                proposal_id,
                claimer: assignee,
                amount: bounty_amount,
            });

            Ok(())
        }

        /// Cancel a proposal
        ///
        /// Proposer can cancel if still open. Returns all reserved funds.
        #[pallet::call_index(5)]
        #[pallet::weight(10_000)]
        pub fn cancel_proposal(
            origin: OriginFor<T>,
            proposal_id: u32,
        ) -> DispatchResult {
            let caller = ensure_signed(origin)?;

            let mut proposal = Proposals::<T>::get(proposal_id)
                .ok_or(Error::<T>::ProposalNotFound)?;

            // Check authorization
            ensure!(caller == proposal.proposer, Error::<T>::NotAuthorized);

            // Check status (can only cancel if open)
            ensure!(proposal.status == ProposalStatus::Open, Error::<T>::InvalidProposalStatus);

            // Return all reserved funds
            T::Currency::unreserve(&proposal.proposer, T::MinProposalDeposit::get());
            if !proposal.bounty.is_zero() {
                T::Currency::unreserve(&proposal.proposer, proposal.bounty);
            }

            // Update status
            proposal.status = ProposalStatus::Cancelled;
            Proposals::<T>::insert(proposal_id, proposal);

            Self::deposit_event(Event::ProposalCancelled { proposal_id });

            Ok(())
        }

        /// Return staked tokens after voting closes
        ///
        /// Anyone can call to return their stake.
        #[pallet::call_index(6)]
        #[pallet::weight(10_000)]
        pub fn return_vote_stake(
            origin: OriginFor<T>,
            proposal_id: u32,
        ) -> DispatchResult {
            let voter = ensure_signed(origin)?;

            let proposal = Proposals::<T>::get(proposal_id)
                .ok_or(Error::<T>::ProposalNotFound)?;

            // Check voting has closed
            ensure!(
                proposal.status != ProposalStatus::Open,
                Error::<T>::VotingNotEnded
            );

            // Get and remove vote
            let vote = Votes::<T>::take(proposal_id, &voter)
                .ok_or(Error::<T>::NotAuthorized)?;

            // Return stake
            T::Currency::unreserve(&voter, vote.amount);

            Ok(())
        }
    }
}
