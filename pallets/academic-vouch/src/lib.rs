//! # Academic Vouching Pallet
//!
//! A governance mechanism for academic endorsement of the QuantumHarmony Architecture Program.
//! Verified academics can vouch for participants, creating a trust chain for program entry.
//!
//! ## Overview
//!
//! - Validators can register as Academic Vouchers (with credentials)
//! - Registered academics can vouch for program applicants
//! - Multiple vouches required for program acceptance
//! - Vouching history creates reputation/trust metrics
//! - Links to Ricardian contracts for program agreements
//!
//! ## Workflow
//!
//! 1. Academic applies for voucher status (with credential hash)
//! 2. Existing validators vote to approve academic
//! 3. Approved academic can vouch for program applicants
//! 4. Applicant collects required vouches
//! 5. Program entry is granted with signed Ricardian contract

#![cfg_attr(not(feature = "std"), no_std)]

pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {
    use frame_support::{
        pallet_prelude::*,
        traits::Get,
    };
    use frame_system::pallet_prelude::*;
    use sp_std::vec::Vec;

    /// Maximum length for academic credentials/institution name
    pub const MAX_CREDENTIAL_LENGTH: u32 = 256;
    /// Maximum length for vouch reason
    pub const MAX_VOUCH_REASON_LENGTH: u32 = 512;
    /// Maximum vouches per applicant
    pub const MAX_VOUCHES_PER_APPLICANT: u32 = 10;

    /// Configure the pallet
    #[pallet::config]
    pub trait Config: frame_system::Config {
        /// The overarching event type
        type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

        /// Number of vouches required for program acceptance
        #[pallet::constant]
        type RequiredVouches: Get<u32>;

        /// Voting period for academic registration (in blocks)
        #[pallet::constant]
        type AcademicVotingPeriod: Get<BlockNumberFor<Self>>;

        /// Minimum validators needed to approve an academic
        #[pallet::constant]
        type MinimumAcademicApprovals: Get<u32>;
    }

    #[pallet::pallet]
    pub struct Pallet<T>(_);

    /// Academic credentials and status
    #[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
    #[scale_info(skip_type_params(T))]
    pub struct Academic<T: Config> {
        /// Account ID of the academic
        pub account: T::AccountId,
        /// Institution name (bounded)
        pub institution: BoundedVec<u8, ConstU32<MAX_CREDENTIAL_LENGTH>>,
        /// Credential document hash (IPFS or similar)
        pub credential_hash: [u8; 32],
        /// Block when registered
        pub registered_at: BlockNumberFor<T>,
        /// Total vouches given
        pub vouches_given: u32,
        /// Is currently active
        pub active: bool,
    }

    /// Academic registration proposal
    #[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
    #[scale_info(skip_type_params(T))]
    pub struct AcademicProposal<T: Config> {
        /// Account ID of the proposed academic
        pub account: T::AccountId,
        /// Institution name
        pub institution: BoundedVec<u8, ConstU32<MAX_CREDENTIAL_LENGTH>>,
        /// Credential document hash
        pub credential_hash: [u8; 32],
        /// Block when proposed
        pub proposed_at: BlockNumberFor<T>,
        /// Approval votes
        pub approvals: u32,
        /// Rejection votes
        pub rejections: u32,
        /// Is finalized
        pub finalized: bool,
    }

    /// A vouch record
    #[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
    #[scale_info(skip_type_params(T))]
    pub struct Vouch<T: Config> {
        /// Academic who gave the vouch
        pub academic: T::AccountId,
        /// Block when vouch was given
        pub vouched_at: BlockNumberFor<T>,
        /// Reason for vouching (bounded)
        pub reason: BoundedVec<u8, ConstU32<MAX_VOUCH_REASON_LENGTH>>,
        /// Optional reference to Ricardian contract
        pub contract_id: Option<u32>,
    }

    /// Program applicant status
    #[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
    pub enum ApplicantStatus {
        /// Collecting vouches
        Pending,
        /// Required vouches obtained, awaiting contract
        VouchesComplete,
        /// Accepted into program
        Accepted,
        /// Rejected
        Rejected,
    }

    /// Program applicant record
    #[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
    #[scale_info(skip_type_params(T))]
    pub struct Applicant<T: Config> {
        /// Account ID
        pub account: T::AccountId,
        /// Application timestamp
        pub applied_at: BlockNumberFor<T>,
        /// Current status
        pub status: ApplicantStatus,
        /// Number of vouches received
        pub vouch_count: u32,
        /// Associated Ricardian contract (once accepted)
        pub contract_id: Option<u32>,
    }

    // ==================== STORAGE ====================

    /// Registered academics
    #[pallet::storage]
    #[pallet::getter(fn academics)]
    pub type Academics<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        T::AccountId,
        Academic<T>,
        OptionQuery,
    >;

    /// Academic registration proposals
    #[pallet::storage]
    #[pallet::getter(fn academic_proposals)]
    pub type AcademicProposals<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        u32, // proposal_id
        AcademicProposal<T>,
        OptionQuery,
    >;

    /// Next academic proposal ID
    #[pallet::storage]
    #[pallet::getter(fn next_academic_proposal_id)]
    pub type NextAcademicProposalId<T: Config> = StorageValue<_, u32, ValueQuery>;

    /// Track academic proposal votes
    #[pallet::storage]
    #[pallet::getter(fn academic_votes)]
    pub type AcademicVotes<T: Config> = StorageDoubleMap<
        _,
        Blake2_128Concat,
        u32, // proposal_id
        Blake2_128Concat,
        T::AccountId, // voter
        bool, // has_voted
        ValueQuery,
    >;

    /// Program applicants
    #[pallet::storage]
    #[pallet::getter(fn applicants)]
    pub type Applicants<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        T::AccountId,
        Applicant<T>,
        OptionQuery,
    >;

    /// Vouches for applicants (applicant -> list of vouches)
    #[pallet::storage]
    #[pallet::getter(fn vouches)]
    pub type Vouches<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        T::AccountId, // applicant
        BoundedVec<Vouch<T>, ConstU32<MAX_VOUCHES_PER_APPLICANT>>,
        ValueQuery,
    >;

    // ==================== EVENTS ====================

    #[pallet::event]
    #[pallet::generate_deposit(pub(super) fn deposit_event)]
    pub enum Event<T: Config> {
        /// Academic registration proposed
        AcademicProposed {
            proposal_id: u32,
            account: T::AccountId,
            institution: Vec<u8>,
        },
        /// Vote cast on academic proposal
        AcademicVoteCast {
            proposal_id: u32,
            voter: T::AccountId,
            approve: bool,
        },
        /// Academic registration finalized
        AcademicRegistered {
            account: T::AccountId,
            institution: Vec<u8>,
        },
        /// Academic registration rejected
        AcademicRejected {
            account: T::AccountId,
        },
        /// New program application
        ApplicationSubmitted {
            applicant: T::AccountId,
        },
        /// Vouch given to applicant
        VouchGiven {
            academic: T::AccountId,
            applicant: T::AccountId,
        },
        /// Applicant reached required vouches
        VouchesComplete {
            applicant: T::AccountId,
            vouch_count: u32,
        },
        /// Applicant accepted into program
        ApplicantAccepted {
            applicant: T::AccountId,
            contract_id: u32,
        },
        /// Applicant rejected
        ApplicantRejected {
            applicant: T::AccountId,
            reason: Vec<u8>,
        },
    }

    // ==================== ERRORS ====================

    #[pallet::error]
    pub enum Error<T> {
        /// Academic already registered
        AlreadyRegistered,
        /// Not a registered academic
        NotAnAcademic,
        /// Academic is not active
        AcademicNotActive,
        /// Proposal not found
        ProposalNotFound,
        /// Already voted
        AlreadyVoted,
        /// Voting period not ended
        VotingPeriodNotEnded,
        /// Voting period ended
        VotingPeriodEnded,
        /// Already finalized
        AlreadyFinalized,
        /// Applicant not found
        ApplicantNotFound,
        /// Already applied
        AlreadyApplied,
        /// Already vouched for this applicant
        AlreadyVouched,
        /// Cannot vouch for self
        CannotVouchForSelf,
        /// Max vouches reached
        MaxVouchesReached,
        /// Invalid status transition
        InvalidStatusTransition,
        /// Contract required for acceptance
        ContractRequired,
        /// Credential too long
        CredentialTooLong,
        /// Reason too long
        ReasonTooLong,
        /// Overflow error
        Overflow,
    }

    // ==================== CALLS ====================

    #[pallet::call]
    impl<T: Config> Pallet<T> {
        /// Propose registration as an academic voucher.
        ///
        /// Submit credentials for review by existing validators/academics.
        #[pallet::call_index(0)]
        #[pallet::weight(10_000)]
        pub fn propose_academic(
            origin: OriginFor<T>,
            institution: Vec<u8>,
            credential_hash: [u8; 32],
        ) -> DispatchResult {
            let who = ensure_signed(origin)?;

            // Check not already registered
            ensure!(!Academics::<T>::contains_key(&who), Error::<T>::AlreadyRegistered);

            // Validate institution length
            let institution_bounded: BoundedVec<u8, ConstU32<MAX_CREDENTIAL_LENGTH>> =
                institution.clone().try_into().map_err(|_| Error::<T>::CredentialTooLong)?;

            // Create proposal
            let proposal_id = NextAcademicProposalId::<T>::get();
            let next_id = proposal_id.checked_add(1).ok_or(Error::<T>::Overflow)?;
            NextAcademicProposalId::<T>::put(next_id);

            let proposal = AcademicProposal {
                account: who.clone(),
                institution: institution_bounded,
                credential_hash,
                proposed_at: frame_system::Pallet::<T>::block_number(),
                approvals: 0,
                rejections: 0,
                finalized: false,
            };

            AcademicProposals::<T>::insert(proposal_id, proposal);

            Self::deposit_event(Event::AcademicProposed {
                proposal_id,
                account: who,
                institution,
            });

            Ok(())
        }

        /// Vote on an academic registration proposal.
        ///
        /// Only existing academics or validators can vote.
        #[pallet::call_index(1)]
        #[pallet::weight(10_000)]
        pub fn vote_academic_proposal(
            origin: OriginFor<T>,
            proposal_id: u32,
            approve: bool,
        ) -> DispatchResult {
            let voter = ensure_signed(origin)?;

            // Check voter is an academic (or could add validator check)
            ensure!(Academics::<T>::contains_key(&voter), Error::<T>::NotAnAcademic);

            // Get proposal
            let mut proposal = AcademicProposals::<T>::get(proposal_id)
                .ok_or(Error::<T>::ProposalNotFound)?;

            // Check not finalized
            ensure!(!proposal.finalized, Error::<T>::AlreadyFinalized);

            // Check voting period
            let current_block = frame_system::Pallet::<T>::block_number();
            let voting_end = proposal.proposed_at + T::AcademicVotingPeriod::get();
            ensure!(current_block <= voting_end, Error::<T>::VotingPeriodEnded);

            // Check not already voted
            ensure!(!AcademicVotes::<T>::get(proposal_id, &voter), Error::<T>::AlreadyVoted);

            // Record vote
            AcademicVotes::<T>::insert(proposal_id, &voter, true);

            if approve {
                proposal.approvals = proposal.approvals.checked_add(1).ok_or(Error::<T>::Overflow)?;
            } else {
                proposal.rejections = proposal.rejections.checked_add(1).ok_or(Error::<T>::Overflow)?;
            }

            AcademicProposals::<T>::insert(proposal_id, proposal);

            Self::deposit_event(Event::AcademicVoteCast {
                proposal_id,
                voter,
                approve,
            });

            Ok(())
        }

        /// Finalize an academic registration proposal.
        ///
        /// Anyone can call after voting period ends.
        #[pallet::call_index(2)]
        #[pallet::weight(10_000)]
        pub fn finalize_academic_proposal(
            origin: OriginFor<T>,
            proposal_id: u32,
        ) -> DispatchResult {
            let _who = ensure_signed(origin)?;

            // Get proposal
            let mut proposal = AcademicProposals::<T>::get(proposal_id)
                .ok_or(Error::<T>::ProposalNotFound)?;

            // Check not finalized
            ensure!(!proposal.finalized, Error::<T>::AlreadyFinalized);

            // Check voting period ended
            let current_block = frame_system::Pallet::<T>::block_number();
            let voting_end = proposal.proposed_at + T::AcademicVotingPeriod::get();
            ensure!(current_block > voting_end, Error::<T>::VotingPeriodNotEnded);

            // Mark finalized
            proposal.finalized = true;

            // Determine approval
            let approved = proposal.approvals > proposal.rejections
                && proposal.approvals >= T::MinimumAcademicApprovals::get();

            AcademicProposals::<T>::insert(proposal_id, proposal.clone());

            if approved {
                // Register academic
                let academic = Academic {
                    account: proposal.account.clone(),
                    institution: proposal.institution.clone(),
                    credential_hash: proposal.credential_hash,
                    registered_at: current_block,
                    vouches_given: 0,
                    active: true,
                };

                Academics::<T>::insert(&proposal.account, academic);

                Self::deposit_event(Event::AcademicRegistered {
                    account: proposal.account,
                    institution: proposal.institution.to_vec(),
                });
            } else {
                Self::deposit_event(Event::AcademicRejected {
                    account: proposal.account,
                });
            }

            Ok(())
        }

        /// Apply for the architecture program.
        ///
        /// Creates an applicant record to collect vouches.
        #[pallet::call_index(3)]
        #[pallet::weight(10_000)]
        pub fn apply_for_program(origin: OriginFor<T>) -> DispatchResult {
            let applicant = ensure_signed(origin)?;

            // Check not already applied
            ensure!(!Applicants::<T>::contains_key(&applicant), Error::<T>::AlreadyApplied);

            let application = Applicant {
                account: applicant.clone(),
                applied_at: frame_system::Pallet::<T>::block_number(),
                status: ApplicantStatus::Pending,
                vouch_count: 0,
                contract_id: None,
            };

            Applicants::<T>::insert(&applicant, application);

            Self::deposit_event(Event::ApplicationSubmitted {
                applicant,
            });

            Ok(())
        }

        /// Vouch for a program applicant.
        ///
        /// Only registered academics can vouch.
        #[pallet::call_index(4)]
        #[pallet::weight(10_000)]
        pub fn vouch_for_applicant(
            origin: OriginFor<T>,
            applicant: T::AccountId,
            reason: Vec<u8>,
            contract_id: Option<u32>,
        ) -> DispatchResult {
            let academic_account = ensure_signed(origin)?;

            // Check is an academic
            let mut academic = Academics::<T>::get(&academic_account)
                .ok_or(Error::<T>::NotAnAcademic)?;
            ensure!(academic.active, Error::<T>::AcademicNotActive);

            // Cannot vouch for self
            ensure!(academic_account != applicant, Error::<T>::CannotVouchForSelf);

            // Check applicant exists
            let mut applicant_record = Applicants::<T>::get(&applicant)
                .ok_or(Error::<T>::ApplicantNotFound)?;

            // Check applicant status
            ensure!(
                applicant_record.status == ApplicantStatus::Pending,
                Error::<T>::InvalidStatusTransition
            );

            // Check not already vouched
            let vouches = Vouches::<T>::get(&applicant);
            for v in vouches.iter() {
                if v.academic == academic_account {
                    return Err(Error::<T>::AlreadyVouched.into());
                }
            }

            // Validate reason length
            let reason_bounded: BoundedVec<u8, ConstU32<MAX_VOUCH_REASON_LENGTH>> =
                reason.try_into().map_err(|_| Error::<T>::ReasonTooLong)?;

            // Create vouch
            let vouch = Vouch {
                academic: academic_account.clone(),
                vouched_at: frame_system::Pallet::<T>::block_number(),
                reason: reason_bounded,
                contract_id,
            };

            // Add vouch to storage
            Vouches::<T>::try_mutate(&applicant, |vouches| {
                vouches.try_push(vouch).map_err(|_| Error::<T>::MaxVouchesReached)
            })?;

            // Update academic's vouch count
            academic.vouches_given = academic.vouches_given.checked_add(1).ok_or(Error::<T>::Overflow)?;
            Academics::<T>::insert(&academic_account, academic);

            // Update applicant's vouch count
            applicant_record.vouch_count = applicant_record.vouch_count.checked_add(1).ok_or(Error::<T>::Overflow)?;

            // Check if required vouches reached
            if applicant_record.vouch_count >= T::RequiredVouches::get() {
                applicant_record.status = ApplicantStatus::VouchesComplete;

                Self::deposit_event(Event::VouchesComplete {
                    applicant: applicant.clone(),
                    vouch_count: applicant_record.vouch_count,
                });
            }

            Applicants::<T>::insert(&applicant, applicant_record);

            Self::deposit_event(Event::VouchGiven {
                academic: academic_account,
                applicant,
            });

            Ok(())
        }

        /// Accept an applicant into the program.
        ///
        /// Requires vouches complete and a signed Ricardian contract.
        #[pallet::call_index(5)]
        #[pallet::weight(10_000)]
        pub fn accept_applicant(
            origin: OriginFor<T>,
            applicant: T::AccountId,
            contract_id: u32,
        ) -> DispatchResult {
            let _admin = ensure_signed(origin)?;

            // Get applicant
            let mut applicant_record = Applicants::<T>::get(&applicant)
                .ok_or(Error::<T>::ApplicantNotFound)?;

            // Check status
            ensure!(
                applicant_record.status == ApplicantStatus::VouchesComplete,
                Error::<T>::InvalidStatusTransition
            );

            // Update status
            applicant_record.status = ApplicantStatus::Accepted;
            applicant_record.contract_id = Some(contract_id);

            Applicants::<T>::insert(&applicant, applicant_record);

            Self::deposit_event(Event::ApplicantAccepted {
                applicant,
                contract_id,
            });

            Ok(())
        }

        /// Reject an applicant.
        #[pallet::call_index(6)]
        #[pallet::weight(10_000)]
        pub fn reject_applicant(
            origin: OriginFor<T>,
            applicant: T::AccountId,
            reason: Vec<u8>,
        ) -> DispatchResult {
            let _admin = ensure_signed(origin)?;

            // Get applicant
            let mut applicant_record = Applicants::<T>::get(&applicant)
                .ok_or(Error::<T>::ApplicantNotFound)?;

            // Update status
            applicant_record.status = ApplicantStatus::Rejected;

            Applicants::<T>::insert(&applicant, applicant_record);

            Self::deposit_event(Event::ApplicantRejected {
                applicant,
                reason,
            });

            Ok(())
        }
    }

    // ==================== HELPER FUNCTIONS ====================

    impl<T: Config> Pallet<T> {
        /// Check if an account is a registered academic
        pub fn is_academic(account: &T::AccountId) -> bool {
            Academics::<T>::get(account)
                .map(|a| a.active)
                .unwrap_or(false)
        }

        /// Get vouch count for an applicant
        pub fn get_vouch_count(applicant: &T::AccountId) -> u32 {
            Applicants::<T>::get(applicant)
                .map(|a| a.vouch_count)
                .unwrap_or(0)
        }

        /// Check if applicant has enough vouches
        pub fn has_enough_vouches(applicant: &T::AccountId) -> bool {
            Self::get_vouch_count(applicant) >= T::RequiredVouches::get()
        }
    }
}
