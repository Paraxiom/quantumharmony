//! # Ricardian Contracts Pallet
//!
//! On-chain Ricardian contracts combining human-readable legal agreements
//! with machine-readable cryptographic verification.
//!
//! ## Overview
//!
//! Ricardian contracts are legal documents that are:
//! - Human readable (legal prose)
//! - Machine readable (structured data)
//! - Cryptographically signed (legally binding)
//! - Immutable once executed
//!
//! ## Contract Lifecycle
//!
//! 1. Draft: Contract created, awaiting signatures
//! 2. Active: All parties have signed
//! 3. Executed: Contract terms fulfilled
//! 4. Terminated: Contract cancelled or expired
//!
//! ## Features
//!
//! - Multi-party signing support
//! - IPFS hash storage for off-chain content
//! - Amendment tracking
//! - Expiration dates
//! - Integration with academic vouching

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(test)]
mod tests;

pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {
    use frame_support::{
        pallet_prelude::*,
        traits::Get,
    };
    use frame_system::pallet_prelude::*;
    use sp_std::vec::Vec;

    /// Maximum title length
    pub const MAX_TITLE_LENGTH: u32 = 128;
    /// Maximum parties per contract
    pub const MAX_PARTIES: u32 = 10;
    /// Maximum terms/clauses
    pub const MAX_TERMS: u32 = 50;
    /// Maximum amendments
    pub const MAX_AMENDMENTS: u32 = 20;

    /// Configure the pallet
    #[pallet::config]
    pub trait Config: frame_system::Config {
        /// The overarching event type
        type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

        /// Grace period after creation before contract can expire (in blocks)
        #[pallet::constant]
        type MinContractDuration: Get<BlockNumberFor<Self>>;
    }

    #[pallet::pallet]
    pub struct Pallet<T>(_);

    /// Contract status
    #[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, TypeInfo, MaxEncodedLen, Default)]
    pub enum ContractStatus {
        /// Awaiting signatures
        #[default]
        Draft,
        /// All signatures collected, contract is active
        Active,
        /// Contract terms have been fulfilled
        Executed,
        /// Contract was terminated or cancelled
        Terminated,
        /// Contract expired
        Expired,
    }

    /// Contract type classification
    #[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, TypeInfo, MaxEncodedLen, Default, Copy)]
    pub enum ContractType {
        /// Academic program agreement
        AcademicProgram = 0,
        /// Partnership agreement
        Partnership = 1,
        /// Service agreement
        Service = 2,
        /// Non-disclosure agreement
        NDA = 3,
        /// Employment contract
        Employment = 4,
        /// License agreement
        License = 5,
        /// Custom/other
        #[default]
        Custom = 6,
    }

    impl From<u8> for ContractType {
        fn from(value: u8) -> Self {
            match value {
                0 => ContractType::AcademicProgram,
                1 => ContractType::Partnership,
                2 => ContractType::Service,
                3 => ContractType::NDA,
                4 => ContractType::Employment,
                5 => ContractType::License,
                _ => ContractType::Custom,
            }
        }
    }

    /// A party to the contract
    #[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
    #[scale_info(skip_type_params(T))]
    pub struct Party<T: Config> {
        /// Account ID
        pub account: T::AccountId,
        /// Role in contract (e.g., "Licensor", "Licensee", "Student", "Institution")
        pub role: BoundedVec<u8, ConstU32<64>>,
        /// Has signed
        pub signed: bool,
        /// Signature timestamp
        pub signed_at: Option<BlockNumberFor<T>>,
    }

    /// Contract term/clause
    #[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
    pub struct Term {
        /// Term number
        pub number: u32,
        /// Term hash (content stored off-chain)
        pub content_hash: [u8; 32],
        /// Is this term mandatory
        pub mandatory: bool,
    }

    /// Contract amendment
    #[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
    #[scale_info(skip_type_params(T))]
    pub struct Amendment<T: Config> {
        /// Amendment number
        pub number: u32,
        /// Amendment content hash
        pub content_hash: [u8; 32],
        /// Proposed by
        pub proposed_by: T::AccountId,
        /// Proposed at block
        pub proposed_at: BlockNumberFor<T>,
        /// Approved by all parties
        pub approved: bool,
        /// Approvals received
        pub approvals: u32,
    }

    /// The Ricardian Contract
    #[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
    #[scale_info(skip_type_params(T))]
    pub struct Contract<T: Config> {
        /// Contract ID
        pub id: u32,
        /// Title (bounded)
        pub title: BoundedVec<u8, ConstU32<MAX_TITLE_LENGTH>>,
        /// Contract type
        pub contract_type: ContractType,
        /// Current status
        pub status: ContractStatus,
        /// Creator
        pub creator: T::AccountId,
        /// Creation block
        pub created_at: BlockNumberFor<T>,
        /// Expiration block (optional)
        pub expires_at: Option<BlockNumberFor<T>>,
        /// Main document hash (IPFS or similar)
        pub document_hash: [u8; 32],
        /// Number of parties
        pub party_count: u32,
        /// Signatures collected
        pub signatures_collected: u32,
        /// Number of terms
        pub term_count: u32,
        /// Number of amendments
        pub amendment_count: u32,
        /// Is this contract linked to academic vouching
        pub academic_program_id: Option<u32>,
    }

    // ==================== STORAGE ====================

    /// All contracts
    #[pallet::storage]
    #[pallet::getter(fn contracts)]
    pub type Contracts<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        u32, // contract_id
        Contract<T>,
        OptionQuery,
    >;

    /// Next contract ID
    #[pallet::storage]
    #[pallet::getter(fn next_contract_id)]
    pub type NextContractId<T: Config> = StorageValue<_, u32, ValueQuery>;

    /// Contract parties
    #[pallet::storage]
    #[pallet::getter(fn parties)]
    pub type Parties<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        u32, // contract_id
        BoundedVec<Party<T>, ConstU32<MAX_PARTIES>>,
        ValueQuery,
    >;

    /// Contract terms
    #[pallet::storage]
    #[pallet::getter(fn terms)]
    pub type Terms<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        u32, // contract_id
        BoundedVec<Term, ConstU32<MAX_TERMS>>,
        ValueQuery,
    >;

    /// Contract amendments
    #[pallet::storage]
    #[pallet::getter(fn amendments)]
    pub type Amendments<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        u32, // contract_id
        BoundedVec<Amendment<T>, ConstU32<MAX_AMENDMENTS>>,
        ValueQuery,
    >;

    /// Amendment approvals tracking
    #[pallet::storage]
    #[pallet::getter(fn amendment_approvals)]
    pub type AmendmentApprovals<T: Config> = StorageDoubleMap<
        _,
        Blake2_128Concat,
        (u32, u32), // (contract_id, amendment_number)
        Blake2_128Concat,
        T::AccountId,
        bool,
        ValueQuery,
    >;

    /// Contracts by party (account -> list of contract IDs)
    #[pallet::storage]
    #[pallet::getter(fn contracts_by_party)]
    pub type ContractsByParty<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        T::AccountId,
        BoundedVec<u32, ConstU32<100>>,
        ValueQuery,
    >;

    // ==================== EVENTS ====================

    #[pallet::event]
    #[pallet::generate_deposit(pub(super) fn deposit_event)]
    pub enum Event<T: Config> {
        /// Contract created
        ContractCreated {
            contract_id: u32,
            creator: T::AccountId,
            title: Vec<u8>,
            contract_type_id: u8,
        },
        /// Party added to contract
        PartyAdded {
            contract_id: u32,
            party: T::AccountId,
            role: Vec<u8>,
        },
        /// Contract signed by party
        ContractSigned {
            contract_id: u32,
            signer: T::AccountId,
        },
        /// All parties signed, contract now active
        ContractActivated {
            contract_id: u32,
        },
        /// Contract marked as executed
        ContractExecuted {
            contract_id: u32,
        },
        /// Contract terminated
        ContractTerminated {
            contract_id: u32,
            reason: Vec<u8>,
        },
        /// Amendment proposed
        AmendmentProposed {
            contract_id: u32,
            amendment_number: u32,
            proposed_by: T::AccountId,
        },
        /// Amendment approved by party
        AmendmentApproved {
            contract_id: u32,
            amendment_number: u32,
            approver: T::AccountId,
        },
        /// Amendment fully approved and applied
        AmendmentApplied {
            contract_id: u32,
            amendment_number: u32,
        },
        /// Term added to contract
        TermAdded {
            contract_id: u32,
            term_number: u32,
        },
    }

    // ==================== ERRORS ====================

    #[pallet::error]
    pub enum Error<T> {
        /// Contract not found
        ContractNotFound,
        /// Not a party to this contract
        NotAParty,
        /// Already signed
        AlreadySigned,
        /// Contract not in draft status
        NotDraft,
        /// Contract not active
        NotActive,
        /// Contract expired
        ContractExpired,
        /// All parties already added
        MaxPartiesReached,
        /// Max terms reached
        MaxTermsReached,
        /// Max amendments reached
        MaxAmendmentsReached,
        /// Not authorized
        NotAuthorized,
        /// Amendment not found
        AmendmentNotFound,
        /// Amendment already approved by this party
        AmendmentAlreadyApproved,
        /// Title too long
        TitleTooLong,
        /// Role too long
        RoleTooLong,
        /// Expiration too soon
        ExpirationTooSoon,
        /// Overflow error
        Overflow,
        /// Cannot modify active contract
        CannotModifyActive,
    }

    // ==================== CALLS ====================

    #[pallet::call]
    impl<T: Config> Pallet<T> {
        /// Create a new Ricardian contract.
        ///
        /// contract_type_id: 0=AcademicProgram, 1=Partnership, 2=Service, 3=NDA, 4=Employment, 5=License, 6=Custom
        #[pallet::call_index(0)]
        #[pallet::weight(10_000)]
        pub fn create_contract(
            origin: OriginFor<T>,
            title: Vec<u8>,
            contract_type_id: u8,
            document_hash: [u8; 32],
            expires_at: Option<BlockNumberFor<T>>,
            academic_program_id: Option<u32>,
        ) -> DispatchResult {
            let creator = ensure_signed(origin)?;
            let contract_type: ContractType = contract_type_id.into();

            // Validate title
            let title_bounded: BoundedVec<u8, ConstU32<MAX_TITLE_LENGTH>> =
                title.clone().try_into().map_err(|_| Error::<T>::TitleTooLong)?;

            let current_block = frame_system::Pallet::<T>::block_number();

            // Validate expiration
            if let Some(exp) = expires_at {
                ensure!(
                    exp >= current_block + T::MinContractDuration::get(),
                    Error::<T>::ExpirationTooSoon
                );
            }

            // Create contract
            let contract_id = NextContractId::<T>::get();
            let next_id = contract_id.checked_add(1).ok_or(Error::<T>::Overflow)?;
            NextContractId::<T>::put(next_id);

            let contract = Contract {
                id: contract_id,
                title: title_bounded,
                contract_type: contract_type.clone(),
                status: ContractStatus::Draft,
                creator: creator.clone(),
                created_at: current_block,
                expires_at,
                document_hash,
                party_count: 0,
                signatures_collected: 0,
                term_count: 0,
                amendment_count: 0,
                academic_program_id,
            };

            Contracts::<T>::insert(contract_id, contract);

            Self::deposit_event(Event::ContractCreated {
                contract_id,
                creator,
                title,
                contract_type_id,
            });

            Ok(())
        }

        /// Add a party to the contract.
        ///
        /// Only creator can add parties while in draft status.
        #[pallet::call_index(1)]
        #[pallet::weight(10_000)]
        pub fn add_party(
            origin: OriginFor<T>,
            contract_id: u32,
            party_account: T::AccountId,
            role: Vec<u8>,
        ) -> DispatchResult {
            let who = ensure_signed(origin)?;

            // Get contract
            let mut contract = Contracts::<T>::get(contract_id)
                .ok_or(Error::<T>::ContractNotFound)?;

            // Only creator can add parties
            ensure!(contract.creator == who, Error::<T>::NotAuthorized);

            // Must be in draft
            ensure!(contract.status == ContractStatus::Draft, Error::<T>::NotDraft);

            // Validate role
            let role_bounded: BoundedVec<u8, ConstU32<64>> =
                role.clone().try_into().map_err(|_| Error::<T>::RoleTooLong)?;

            // Create party
            let party = Party {
                account: party_account.clone(),
                role: role_bounded,
                signed: false,
                signed_at: None,
            };

            // Add to parties
            Parties::<T>::try_mutate(contract_id, |parties| {
                parties.try_push(party).map_err(|_| Error::<T>::MaxPartiesReached)
            })?;

            // Update contract party count
            contract.party_count = contract.party_count.checked_add(1).ok_or(Error::<T>::Overflow)?;
            Contracts::<T>::insert(contract_id, contract);

            // Add to party's contracts list
            ContractsByParty::<T>::try_mutate(&party_account, |contracts| {
                contracts.try_push(contract_id).map_err(|_| Error::<T>::Overflow)
            })?;

            Self::deposit_event(Event::PartyAdded {
                contract_id,
                party: party_account,
                role,
            });

            Ok(())
        }

        /// Add a term to the contract.
        #[pallet::call_index(2)]
        #[pallet::weight(10_000)]
        pub fn add_term(
            origin: OriginFor<T>,
            contract_id: u32,
            content_hash: [u8; 32],
            mandatory: bool,
        ) -> DispatchResult {
            let who = ensure_signed(origin)?;

            // Get contract
            let mut contract = Contracts::<T>::get(contract_id)
                .ok_or(Error::<T>::ContractNotFound)?;

            // Only creator can add terms
            ensure!(contract.creator == who, Error::<T>::NotAuthorized);

            // Must be in draft
            ensure!(contract.status == ContractStatus::Draft, Error::<T>::NotDraft);

            let term_number = contract.term_count.checked_add(1).ok_or(Error::<T>::Overflow)?;

            let term = Term {
                number: term_number,
                content_hash,
                mandatory,
            };

            // Add term
            Terms::<T>::try_mutate(contract_id, |terms| {
                terms.try_push(term).map_err(|_| Error::<T>::MaxTermsReached)
            })?;

            contract.term_count = term_number;
            Contracts::<T>::insert(contract_id, contract);

            Self::deposit_event(Event::TermAdded {
                contract_id,
                term_number,
            });

            Ok(())
        }

        /// Sign the contract.
        ///
        /// Party must be listed in contract parties.
        #[pallet::call_index(3)]
        #[pallet::weight(10_000)]
        pub fn sign_contract(
            origin: OriginFor<T>,
            contract_id: u32,
        ) -> DispatchResult {
            let signer = ensure_signed(origin)?;

            // Get contract
            let mut contract = Contracts::<T>::get(contract_id)
                .ok_or(Error::<T>::ContractNotFound)?;

            // Must be in draft
            ensure!(contract.status == ContractStatus::Draft, Error::<T>::NotDraft);

            // Check expiration
            if let Some(exp) = contract.expires_at {
                let current_block = frame_system::Pallet::<T>::block_number();
                ensure!(current_block < exp, Error::<T>::ContractExpired);
            }

            // Find and update party
            let mut found = false;
            Parties::<T>::try_mutate(contract_id, |parties| -> DispatchResult {
                for party in parties.iter_mut() {
                    if party.account == signer {
                        ensure!(!party.signed, Error::<T>::AlreadySigned);
                        party.signed = true;
                        party.signed_at = Some(frame_system::Pallet::<T>::block_number());
                        found = true;
                        break;
                    }
                }
                Ok(())
            })?;

            ensure!(found, Error::<T>::NotAParty);

            // Update signatures count
            contract.signatures_collected = contract.signatures_collected
                .checked_add(1)
                .ok_or(Error::<T>::Overflow)?;

            Self::deposit_event(Event::ContractSigned {
                contract_id,
                signer,
            });

            // Check if all parties signed
            if contract.signatures_collected >= contract.party_count && contract.party_count > 0 {
                contract.status = ContractStatus::Active;

                Self::deposit_event(Event::ContractActivated {
                    contract_id,
                });
            }

            Contracts::<T>::insert(contract_id, contract);

            Ok(())
        }

        /// Propose an amendment to an active contract.
        #[pallet::call_index(4)]
        #[pallet::weight(10_000)]
        pub fn propose_amendment(
            origin: OriginFor<T>,
            contract_id: u32,
            content_hash: [u8; 32],
        ) -> DispatchResult {
            let proposer = ensure_signed(origin)?;

            // Get contract
            let mut contract = Contracts::<T>::get(contract_id)
                .ok_or(Error::<T>::ContractNotFound)?;

            // Must be active
            ensure!(contract.status == ContractStatus::Active, Error::<T>::NotActive);

            // Check proposer is a party
            let parties = Parties::<T>::get(contract_id);
            ensure!(
                parties.iter().any(|p| p.account == proposer),
                Error::<T>::NotAParty
            );

            let amendment_number = contract.amendment_count
                .checked_add(1)
                .ok_or(Error::<T>::Overflow)?;

            let amendment = Amendment {
                number: amendment_number,
                content_hash,
                proposed_by: proposer.clone(),
                proposed_at: frame_system::Pallet::<T>::block_number(),
                approved: false,
                approvals: 1, // Proposer automatically approves
            };

            // Add amendment
            Amendments::<T>::try_mutate(contract_id, |amendments| {
                amendments.try_push(amendment).map_err(|_| Error::<T>::MaxAmendmentsReached)
            })?;

            // Record proposer's approval
            AmendmentApprovals::<T>::insert((contract_id, amendment_number), &proposer, true);

            contract.amendment_count = amendment_number;
            Contracts::<T>::insert(contract_id, contract);

            Self::deposit_event(Event::AmendmentProposed {
                contract_id,
                amendment_number,
                proposed_by: proposer,
            });

            Ok(())
        }

        /// Approve an amendment.
        #[pallet::call_index(5)]
        #[pallet::weight(10_000)]
        pub fn approve_amendment(
            origin: OriginFor<T>,
            contract_id: u32,
            amendment_number: u32,
        ) -> DispatchResult {
            let approver = ensure_signed(origin)?;

            // Get contract
            let contract = Contracts::<T>::get(contract_id)
                .ok_or(Error::<T>::ContractNotFound)?;

            // Must be active
            ensure!(contract.status == ContractStatus::Active, Error::<T>::NotActive);

            // Check approver is a party
            let parties = Parties::<T>::get(contract_id);
            ensure!(
                parties.iter().any(|p| p.account == approver),
                Error::<T>::NotAParty
            );

            // Check not already approved by this party
            ensure!(
                !AmendmentApprovals::<T>::get((contract_id, amendment_number), &approver),
                Error::<T>::AmendmentAlreadyApproved
            );

            // Record approval
            AmendmentApprovals::<T>::insert((contract_id, amendment_number), &approver, true);

            // Update amendment
            Amendments::<T>::try_mutate(contract_id, |amendments| -> DispatchResult {
                let amendment = amendments.iter_mut()
                    .find(|a| a.number == amendment_number)
                    .ok_or(Error::<T>::AmendmentNotFound)?;

                amendment.approvals = amendment.approvals
                    .checked_add(1)
                    .ok_or(Error::<T>::Overflow)?;

                Self::deposit_event(Event::AmendmentApproved {
                    contract_id,
                    amendment_number,
                    approver: approver.clone(),
                });

                // Check if all parties approved
                if amendment.approvals >= contract.party_count {
                    amendment.approved = true;

                    Self::deposit_event(Event::AmendmentApplied {
                        contract_id,
                        amendment_number,
                    });
                }

                Ok(())
            })?;

            Ok(())
        }

        /// Mark contract as executed (terms fulfilled).
        #[pallet::call_index(6)]
        #[pallet::weight(10_000)]
        pub fn execute_contract(
            origin: OriginFor<T>,
            contract_id: u32,
        ) -> DispatchResult {
            let who = ensure_signed(origin)?;

            // Get contract
            let mut contract = Contracts::<T>::get(contract_id)
                .ok_or(Error::<T>::ContractNotFound)?;

            // Must be active
            ensure!(contract.status == ContractStatus::Active, Error::<T>::NotActive);

            // Check who is a party
            let parties = Parties::<T>::get(contract_id);
            ensure!(
                parties.iter().any(|p| p.account == who),
                Error::<T>::NotAParty
            );

            contract.status = ContractStatus::Executed;
            Contracts::<T>::insert(contract_id, contract);

            Self::deposit_event(Event::ContractExecuted {
                contract_id,
            });

            Ok(())
        }

        /// Terminate a contract.
        #[pallet::call_index(7)]
        #[pallet::weight(10_000)]
        pub fn terminate_contract(
            origin: OriginFor<T>,
            contract_id: u32,
            reason: Vec<u8>,
        ) -> DispatchResult {
            let who = ensure_signed(origin)?;

            // Get contract
            let mut contract = Contracts::<T>::get(contract_id)
                .ok_or(Error::<T>::ContractNotFound)?;

            // Check who is creator or a party
            let parties = Parties::<T>::get(contract_id);
            ensure!(
                contract.creator == who || parties.iter().any(|p| p.account == who),
                Error::<T>::NotAuthorized
            );

            contract.status = ContractStatus::Terminated;
            Contracts::<T>::insert(contract_id, contract);

            Self::deposit_event(Event::ContractTerminated {
                contract_id,
                reason,
            });

            Ok(())
        }
    }

    // ==================== HELPER FUNCTIONS ====================

    impl<T: Config> Pallet<T> {
        /// Get contract status
        pub fn get_contract_status(contract_id: u32) -> Option<ContractStatus> {
            Contracts::<T>::get(contract_id).map(|c| c.status)
        }

        /// Check if contract is active
        pub fn is_active(contract_id: u32) -> bool {
            Contracts::<T>::get(contract_id)
                .map(|c| c.status == ContractStatus::Active)
                .unwrap_or(false)
        }

        /// Check if account is party to contract
        pub fn is_party(contract_id: u32, account: &T::AccountId) -> bool {
            Parties::<T>::get(contract_id)
                .iter()
                .any(|p| &p.account == account)
        }

        /// Get contracts for an account
        pub fn get_contracts_for_account(account: &T::AccountId) -> Vec<u32> {
            ContractsByParty::<T>::get(account).to_vec()
        }
    }
}
