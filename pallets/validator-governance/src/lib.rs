//! # Validator Governance Pallet
//!
//! A governance mechanism for adding new validators to QuantumHarmony.
//! Existing validators vote on proposals to add new validators.
//!
//! ## Overview
//!
//! - Any account can propose a new validator (with the validator's public key)
//! - Existing validators vote on proposals
//! - After the voting period ends, anyone can finalize the proposal
//! - If approved (>50% of validators voted yes), the new validator is added
//!
//! ## Voting Period
//!
//! Default voting period is 10 blocks (~1 minute) for testing.
//! This can be configured via the `VotingPeriod` constant.

#![cfg_attr(not(feature = "std"), no_std)]

pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {
    use frame_support::{
        pallet_prelude::*,
        traits::Get,
    };
    use frame_system::pallet_prelude::*;
    use sp_runtime::traits::Convert;
    use sp_std::vec::Vec;

    /// Configure the pallet
    #[pallet::config]
    pub trait Config: frame_system::Config + substrate_validator_set::Config {
        /// The overarching event type
        type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

        /// Number of blocks for the voting period (default: 10 blocks for testing)
        #[pallet::constant]
        type VotingPeriod: Get<BlockNumberFor<Self>>;

        /// Minimum number of votes required for a proposal to be valid
        #[pallet::constant]
        type MinimumVotes: Get<u32>;
    }

    #[pallet::pallet]
    pub struct Pallet<T>(_);

    /// A proposal to add a new validator
    #[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
    #[scale_info(skip_type_params(T))]
    pub struct Proposal<T: Config> {
        /// The account ID of the proposed validator
        pub validator: T::AccountId,
        /// The block number when the proposal was created
        pub proposed_at: BlockNumberFor<T>,
        /// The account that proposed this validator
        pub proposer: T::AccountId,
        /// Number of yes votes
        pub yes_votes: u32,
        /// Number of no votes
        pub no_votes: u32,
        /// Whether the proposal has been finalized
        pub finalized: bool,
    }

    /// Storage for proposals
    #[pallet::storage]
    #[pallet::getter(fn proposals)]
    pub type Proposals<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        u32, // proposal_id
        Proposal<T>,
        OptionQuery,
    >;

    /// Next proposal ID
    #[pallet::storage]
    #[pallet::getter(fn next_proposal_id)]
    pub type NextProposalId<T: Config> = StorageValue<_, u32, ValueQuery>;

    /// Track who voted on which proposal (proposal_id -> voter -> voted)
    #[pallet::storage]
    #[pallet::getter(fn votes)]
    pub type Votes<T: Config> = StorageDoubleMap<
        _,
        Blake2_128Concat,
        u32, // proposal_id
        Blake2_128Concat,
        T::AccountId, // voter
        bool, // has_voted
        ValueQuery,
    >;

    /// Events
    #[pallet::event]
    #[pallet::generate_deposit(pub(super) fn deposit_event)]
    pub enum Event<T: Config> {
        /// A new validator proposal was created
        ProposalCreated {
            proposal_id: u32,
            proposer: T::AccountId,
            validator: T::AccountId,
        },
        /// A vote was cast on a proposal
        VoteCast {
            proposal_id: u32,
            voter: T::AccountId,
            approve: bool,
        },
        /// A proposal was finalized
        ProposalFinalized {
            proposal_id: u32,
            approved: bool,
            yes_votes: u32,
            no_votes: u32,
        },
        /// A new validator was added
        ValidatorAdded {
            validator: T::AccountId,
        },
    }

    /// Errors
    #[pallet::error]
    pub enum Error<T> {
        /// The proposal does not exist
        ProposalNotFound,
        /// The voting period has not ended yet
        VotingPeriodNotEnded,
        /// The voting period has already ended
        VotingPeriodEnded,
        /// The caller is not a validator
        NotAValidator,
        /// The caller has already voted on this proposal
        AlreadyVoted,
        /// The proposal has already been finalized
        AlreadyFinalized,
        /// The proposed validator is already in the validator set
        AlreadyValidator,
        /// Overflow error
        Overflow,
        /// Invalid account/validator conversion
        InvalidConversion,
    }

    #[pallet::call]
    impl<T: Config> Pallet<T> {
        /// Propose a new validator to be added to the network.
        ///
        /// Any account can propose a new validator.
        /// The proposal will be open for voting for `VotingPeriod` blocks.
        #[pallet::call_index(0)]
        #[pallet::weight(10_000)]
        pub fn propose_validator(
            origin: OriginFor<T>,
            validator: T::AccountId,
        ) -> DispatchResult {
            let proposer = ensure_signed(origin)?;

            // Convert AccountId to ValidatorId to check the validator set
            let validator_id = T::AccountIdToValidatorId::convert(validator.clone())
                .ok_or(Error::<T>::InvalidConversion)?;

            // Check if already a validator
            let validators = substrate_validator_set::Pallet::<T>::validators();
            ensure!(!validators.contains(&validator_id), Error::<T>::AlreadyValidator);

            // Create the proposal
            let proposal_id = NextProposalId::<T>::get();
            let next_id = proposal_id.checked_add(1).ok_or(Error::<T>::Overflow)?;
            NextProposalId::<T>::put(next_id);

            let proposal = Proposal {
                validator: validator.clone(),
                proposed_at: frame_system::Pallet::<T>::block_number(),
                proposer: proposer.clone(),
                yes_votes: 0,
                no_votes: 0,
                finalized: false,
            };

            Proposals::<T>::insert(proposal_id, proposal);

            Self::deposit_event(Event::ProposalCreated {
                proposal_id,
                proposer,
                validator,
            });

            Ok(())
        }

        /// Vote on a validator proposal.
        ///
        /// Only existing validators can vote.
        /// Each validator can only vote once per proposal.
        #[pallet::call_index(1)]
        #[pallet::weight(10_000)]
        pub fn vote(
            origin: OriginFor<T>,
            proposal_id: u32,
            approve: bool,
        ) -> DispatchResult {
            let voter = ensure_signed(origin)?;

            // Convert AccountId to ValidatorId to check if voter is a validator
            let voter_validator_id = T::AccountIdToValidatorId::convert(voter.clone())
                .ok_or(Error::<T>::InvalidConversion)?;

            // Check if voter is a validator
            let validators = substrate_validator_set::Pallet::<T>::validators();
            ensure!(validators.contains(&voter_validator_id), Error::<T>::NotAValidator);

            // Get the proposal
            let mut proposal = Proposals::<T>::get(proposal_id)
                .ok_or(Error::<T>::ProposalNotFound)?;

            // Check if already finalized
            ensure!(!proposal.finalized, Error::<T>::AlreadyFinalized);

            // Check voting period
            let current_block = frame_system::Pallet::<T>::block_number();
            let voting_end = proposal.proposed_at + T::VotingPeriod::get();
            ensure!(current_block <= voting_end, Error::<T>::VotingPeriodEnded);

            // Check if already voted
            ensure!(!Votes::<T>::get(proposal_id, &voter), Error::<T>::AlreadyVoted);

            // Record the vote
            Votes::<T>::insert(proposal_id, &voter, true);

            if approve {
                proposal.yes_votes = proposal.yes_votes.checked_add(1).ok_or(Error::<T>::Overflow)?;
            } else {
                proposal.no_votes = proposal.no_votes.checked_add(1).ok_or(Error::<T>::Overflow)?;
            }

            Proposals::<T>::insert(proposal_id, proposal);

            Self::deposit_event(Event::VoteCast {
                proposal_id,
                voter,
                approve,
            });

            Ok(())
        }

        /// Finalize a proposal after the voting period ends.
        ///
        /// Anyone can call this after the voting period ends.
        /// If approved (yes votes > no votes and minimum votes met), the validator is added.
        #[pallet::call_index(2)]
        #[pallet::weight(10_000)]
        pub fn finalize_proposal(
            origin: OriginFor<T>,
            proposal_id: u32,
        ) -> DispatchResult {
            let _who = ensure_signed(origin)?;

            // Get the proposal
            let mut proposal = Proposals::<T>::get(proposal_id)
                .ok_or(Error::<T>::ProposalNotFound)?;

            // Check if already finalized
            ensure!(!proposal.finalized, Error::<T>::AlreadyFinalized);

            // Check voting period has ended
            let current_block = frame_system::Pallet::<T>::block_number();
            let voting_end = proposal.proposed_at + T::VotingPeriod::get();
            ensure!(current_block > voting_end, Error::<T>::VotingPeriodNotEnded);

            // Mark as finalized
            proposal.finalized = true;

            // Determine if approved
            let total_votes = proposal.yes_votes + proposal.no_votes;
            let approved = proposal.yes_votes > proposal.no_votes
                && total_votes >= T::MinimumVotes::get();

            Proposals::<T>::insert(proposal_id, proposal.clone());

            Self::deposit_event(Event::ProposalFinalized {
                proposal_id,
                approved,
                yes_votes: proposal.yes_votes,
                no_votes: proposal.no_votes,
            });

            // If approved, add the validator
            if approved {
                // Use internal add_validator from substrate-validator-set
                // This requires the pallet to have permission
                substrate_validator_set::Pallet::<T>::add_validator_internal(
                    proposal.validator.clone()
                )?;

                Self::deposit_event(Event::ValidatorAdded {
                    validator: proposal.validator,
                });
            }

            Ok(())
        }
    }

    impl<T: Config> Pallet<T> {
        /// Get all active proposals
        pub fn active_proposals() -> Vec<(u32, Proposal<T>)> {
            let current_block = frame_system::Pallet::<T>::block_number();

            Proposals::<T>::iter()
                .filter(|(_, p)| {
                    !p.finalized && current_block <= p.proposed_at + T::VotingPeriod::get()
                })
                .collect()
        }

        /// Get the voting status for a proposal
        pub fn get_proposal_status(proposal_id: u32) -> Option<(u32, u32, bool, bool)> {
            Proposals::<T>::get(proposal_id).map(|p| {
                let current_block = frame_system::Pallet::<T>::block_number();
                let voting_ended = current_block > p.proposed_at + T::VotingPeriod::get();
                (p.yes_votes, p.no_votes, p.finalized, voting_ended)
            })
        }
    }
}
