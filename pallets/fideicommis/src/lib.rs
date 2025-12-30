//! # Fideicommis Pallet
//!
//! Civil law trust accounts for QuantumHarmony - Quebec/civil law compliant.
//!
//! ## Overview
//!
//! A fideicommis (from Latin fideicommissum) is a civil law trust mechanism where
//! assets are held for a primary beneficiary (grevé), with automatic transfer to a
//! substitute beneficiary (appelé) upon triggering conditions (time-based).
//!
//! ## Civil Law Concepts
//!
//! - **Constituant (Settlor)**: Creator of the trust who deposits funds
//! - **Fiduciaire (Fiduciary)**: Trustee who manages the trust
//! - **Grevé (Institute)**: Primary beneficiary who can claim before trigger
//! - **Appelé (Substitute)**: Beneficiary who receives remainder after trigger
//!
//! ## Features
//!
//! - Time-based automatic transfers (block number triggers)
//! - Token-only trusts (QH balance via Currency trait)
//! - Single appelé (substitute beneficiary)
//! - Revocable or irrevocable trusts
//! - Escrow via ReservableCurrency
//!
//! ## Security
//!
//! - Only constituant can deposit
//! - Grevé can only claim before trigger_block
//! - Appelé can only claim after trigger_block
//! - Cancel only works if revocable AND before trigger
//! - Funds held via ReservableCurrency (on-chain escrow)

#![cfg_attr(not(feature = "std"), no_std)]

pub use pallet::*;

#[cfg(test)]
mod tests;

#[frame_support::pallet]
pub mod pallet {
    use frame_support::{
        pallet_prelude::*,
        traits::{Currency, ReservableCurrency, ExistenceRequirement},
    };
    use frame_system::pallet_prelude::*;
    use sp_runtime::traits::{Saturating, Zero};
    use sp_std::prelude::*;

    /// Balance type alias
    pub type BalanceOf<T> =
        <<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;

    /// Maximum length for trust name
    pub const MAX_NAME_LENGTH: u32 = 128;

    /// Maximum trusts per account (as any role)
    pub const MAX_TRUSTS_PER_ACCOUNT: u32 = 100;

    /// Maximum trusts triggering at same block
    pub const MAX_TRUSTS_PER_BLOCK: u32 = 1000;

    // ==================== DATA STRUCTURES ====================

    /// Status of the fideicommis account
    #[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, TypeInfo, MaxEncodedLen, Default)]
    pub enum FideicommisStatus {
        /// Trust is created but not yet activated (no funds deposited)
        #[default]
        Pending,
        /// Trust is active with funds, grevé can claim
        Active,
        /// Trust has been triggered (block reached), appelé can claim
        Triggered,
        /// All funds have been claimed, trust completed
        Completed,
        /// Trust has been cancelled and funds returned
        Cancelled,
    }

    /// The fideicommis trust account structure
    #[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
    #[scale_info(skip_type_params(T))]
    pub struct Fideicommis<T: Config> {
        /// Unique trust ID
        pub id: u64,
        /// Human-readable name
        pub name: BoundedVec<u8, ConstU32<MAX_NAME_LENGTH>>,
        /// The settlor who created the trust
        pub constituant: T::AccountId,
        /// The fiduciary (trustee) who manages the trust
        pub fiduciary: T::AccountId,
        /// The primary beneficiary
        pub greve: T::AccountId,
        /// The substitute beneficiary
        pub appele: T::AccountId,
        /// Current status
        pub status: FideicommisStatus,
        /// Total balance deposited
        pub balance: BalanceOf<T>,
        /// Block number when trust was created
        pub created_at: BlockNumberFor<T>,
        /// Block number when trust triggers (transfers to appelé)
        pub trigger_block: BlockNumberFor<T>,
        /// Optional: Block before trigger when grevé can claim
        pub greve_claim_before: Option<BlockNumberFor<T>>,
        /// Amount grevé has claimed
        pub greve_claimed: BalanceOf<T>,
        /// Amount appelé has claimed
        pub appele_claimed: BalanceOf<T>,
        /// Is the trust revocable by constituant
        pub revocable: bool,
    }

    // ==================== PALLET CONFIG ====================

    #[pallet::config]
    pub trait Config: frame_system::Config {
        /// The overarching event type
        type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

        /// Currency type for trust balances
        type Currency: Currency<Self::AccountId> + ReservableCurrency<Self::AccountId>;

        /// Minimum duration before trigger block (in blocks)
        #[pallet::constant]
        type MinTrustDuration: Get<BlockNumberFor<Self>>;

        /// Maximum trust duration (in blocks)
        #[pallet::constant]
        type MaxTrustDuration: Get<BlockNumberFor<Self>>;

        /// Minimum deposit to create a trust
        #[pallet::constant]
        type MinDeposit: Get<BalanceOf<Self>>;

        /// Origin that can force-cancel trusts (governance/sudo)
        type ForceOrigin: EnsureOrigin<Self::RuntimeOrigin>;
    }

    #[pallet::pallet]
    #[pallet::without_storage_info]
    pub struct Pallet<T>(_);

    // ==================== STORAGE ====================

    /// All fideicommis trusts by ID
    #[pallet::storage]
    #[pallet::getter(fn fideicommis)]
    pub type Fideicommissa<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        u64,
        Fideicommis<T>,
        OptionQuery,
    >;

    /// Next trust ID counter
    #[pallet::storage]
    #[pallet::getter(fn next_trust_id)]
    pub type NextTrustId<T: Config> = StorageValue<_, u64, ValueQuery>;

    /// Trusts by constituant (settlor)
    #[pallet::storage]
    #[pallet::getter(fn trusts_by_constituant)]
    pub type TrustsByConstituant<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        T::AccountId,
        BoundedVec<u64, ConstU32<MAX_TRUSTS_PER_ACCOUNT>>,
        ValueQuery,
    >;

    /// Trusts by grevé (primary beneficiary)
    #[pallet::storage]
    #[pallet::getter(fn trusts_by_greve)]
    pub type TrustsByGreve<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        T::AccountId,
        BoundedVec<u64, ConstU32<MAX_TRUSTS_PER_ACCOUNT>>,
        ValueQuery,
    >;

    /// Trusts by appelé (substitute beneficiary)
    #[pallet::storage]
    #[pallet::getter(fn trusts_by_appele)]
    pub type TrustsByAppele<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        T::AccountId,
        BoundedVec<u64, ConstU32<MAX_TRUSTS_PER_ACCOUNT>>,
        ValueQuery,
    >;

    /// Trusts by trigger block (for efficient trigger checking)
    #[pallet::storage]
    #[pallet::getter(fn trusts_by_trigger)]
    pub type TrustsByTrigger<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        BlockNumberFor<T>,
        BoundedVec<u64, ConstU32<MAX_TRUSTS_PER_BLOCK>>,
        ValueQuery,
    >;

    /// Total value locked in all trusts
    #[pallet::storage]
    #[pallet::getter(fn total_locked)]
    pub type TotalLocked<T: Config> = StorageValue<_, BalanceOf<T>, ValueQuery>;

    /// Total number of active trusts
    #[pallet::storage]
    #[pallet::getter(fn active_count)]
    pub type ActiveCount<T: Config> = StorageValue<_, u32, ValueQuery>;

    // ==================== EVENTS ====================

    #[pallet::event]
    #[pallet::generate_deposit(pub(super) fn deposit_event)]
    pub enum Event<T: Config> {
        /// Trust created
        TrustCreated {
            trust_id: u64,
            constituant: T::AccountId,
            greve: T::AccountId,
            appele: T::AccountId,
            trigger_block: BlockNumberFor<T>,
        },
        /// Funds deposited into trust
        FundsDeposited {
            trust_id: u64,
            depositor: T::AccountId,
            amount: BalanceOf<T>,
            total_balance: BalanceOf<T>,
        },
        /// Trust activated (first deposit received)
        TrustActivated {
            trust_id: u64,
            balance: BalanceOf<T>,
        },
        /// Grevé claimed funds before trigger
        GreveClaimed {
            trust_id: u64,
            claimer: T::AccountId,
            amount: BalanceOf<T>,
            remaining: BalanceOf<T>,
        },
        /// Trust triggered (block reached)
        TrustTriggered {
            trust_id: u64,
            trigger_block: BlockNumberFor<T>,
            balance_for_appele: BalanceOf<T>,
        },
        /// Appelé claimed funds after trigger
        AppeleClaimed {
            trust_id: u64,
            claimer: T::AccountId,
            amount: BalanceOf<T>,
        },
        /// Trust cancelled
        TrustCancelled {
            trust_id: u64,
            cancelled_by: T::AccountId,
            returned_to: T::AccountId,
            amount: BalanceOf<T>,
        },
        /// Trust completed (all funds distributed)
        TrustCompleted {
            trust_id: u64,
            greve_total: BalanceOf<T>,
            appele_total: BalanceOf<T>,
        },
        /// Fiduciary changed
        FiduciaryChanged {
            trust_id: u64,
            old_fiduciary: T::AccountId,
            new_fiduciary: T::AccountId,
        },
    }

    // ==================== ERRORS ====================

    #[pallet::error]
    pub enum Error<T> {
        /// Trust not found
        TrustNotFound,
        /// Not authorized for this operation
        NotAuthorized,
        /// Trust is not in expected status
        InvalidStatus,
        /// Trust trigger block has not been reached
        TriggerNotReached,
        /// Trust trigger block has already passed
        TriggerAlreadyPassed,
        /// Duration too short (below minimum)
        DurationTooShort,
        /// Duration too long (above maximum)
        DurationTooLong,
        /// Deposit below minimum
        DepositTooLow,
        /// Insufficient balance in trust
        InsufficientTrustBalance,
        /// Insufficient balance in caller's account
        InsufficientBalance,
        /// Cannot cancel - trust is irrevocable
        TrustIrrevocable,
        /// Cannot cancel - trust already triggered
        CannotCancelTriggered,
        /// Name too long
        NameTooLong,
        /// Overflow error
        Overflow,
        /// Cannot claim - wrong time period
        ClaimPeriodInvalid,
        /// No funds available to claim
        NoFundsToClaim,
        /// Cannot deposit to cancelled/completed trust
        TrustNotActive,
        /// Maximum trusts per account reached
        MaxTrustsReached,
        /// Grevé and appelé cannot be the same
        SameBeneficiary,
    }

    // ==================== HOOKS ====================

    #[pallet::hooks]
    impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
        /// Check for trusts that need to be triggered at this block
        fn on_initialize(block_number: BlockNumberFor<T>) -> Weight {
            let trusts_to_trigger = TrustsByTrigger::<T>::take(block_number);
            let mut weight = Weight::from_parts(1_000, 0);

            for trust_id in trusts_to_trigger.iter() {
                if let Some(mut trust) = Fideicommissa::<T>::get(trust_id) {
                    if trust.status == FideicommisStatus::Active {
                        trust.status = FideicommisStatus::Triggered;

                        let balance_for_appele = trust.balance.saturating_sub(trust.greve_claimed);

                        Fideicommissa::<T>::insert(trust_id, trust);

                        Self::deposit_event(Event::TrustTriggered {
                            trust_id: *trust_id,
                            trigger_block: block_number,
                            balance_for_appele,
                        });

                        weight = weight.saturating_add(Weight::from_parts(10_000, 0));
                    }
                }
            }

            weight
        }
    }

    // ==================== DISPATCHABLES ====================

    #[pallet::call]
    impl<T: Config> Pallet<T> {
        /// Create a new fideicommis trust account.
        ///
        /// ## Parameters
        /// - `name`: Human-readable name for the trust
        /// - `fiduciary`: Trustee who manages the trust (can be same as constituant)
        /// - `greve`: Primary beneficiary
        /// - `appele`: Substitute beneficiary who receives after trigger
        /// - `trigger_block`: Block number when trust transfers to appelé
        /// - `greve_claim_before`: Optional block before which grevé can claim
        /// - `initial_deposit`: Initial funds to deposit
        /// - `revocable`: Whether constituant can cancel the trust
        #[pallet::call_index(0)]
        #[pallet::weight(Weight::from_parts(75_000, 0))]
        pub fn create(
            origin: OriginFor<T>,
            name: Vec<u8>,
            fiduciary: T::AccountId,
            greve: T::AccountId,
            appele: T::AccountId,
            trigger_block: BlockNumberFor<T>,
            greve_claim_before: Option<BlockNumberFor<T>>,
            initial_deposit: BalanceOf<T>,
            revocable: bool,
        ) -> DispatchResult {
            let constituant = ensure_signed(origin)?;

            // Validate name
            let name_bounded: BoundedVec<u8, ConstU32<MAX_NAME_LENGTH>> =
                name.try_into().map_err(|_| Error::<T>::NameTooLong)?;

            // Validate beneficiaries are different
            ensure!(greve != appele, Error::<T>::SameBeneficiary);

            // Validate duration
            let current_block = frame_system::Pallet::<T>::block_number();
            let duration = trigger_block.saturating_sub(current_block);
            ensure!(duration >= T::MinTrustDuration::get(), Error::<T>::DurationTooShort);
            ensure!(duration <= T::MaxTrustDuration::get(), Error::<T>::DurationTooLong);

            // Validate greve_claim_before if provided
            if let Some(claim_before) = greve_claim_before {
                ensure!(claim_before < trigger_block, Error::<T>::ClaimPeriodInvalid);
                ensure!(claim_before > current_block, Error::<T>::ClaimPeriodInvalid);
            }

            // Validate initial deposit
            ensure!(initial_deposit >= T::MinDeposit::get(), Error::<T>::DepositTooLow);

            // Check constituant has sufficient balance
            ensure!(
                T::Currency::free_balance(&constituant) >= initial_deposit,
                Error::<T>::InsufficientBalance
            );

            // Generate trust ID
            let trust_id = NextTrustId::<T>::get();
            let next_id = trust_id.checked_add(1).ok_or(Error::<T>::Overflow)?;
            NextTrustId::<T>::put(next_id);

            // Create trust
            let trust = Fideicommis {
                id: trust_id,
                name: name_bounded,
                constituant: constituant.clone(),
                fiduciary: fiduciary.clone(),
                greve: greve.clone(),
                appele: appele.clone(),
                status: FideicommisStatus::Pending,
                balance: Zero::zero(),
                created_at: current_block,
                trigger_block,
                greve_claim_before,
                greve_claimed: Zero::zero(),
                appele_claimed: Zero::zero(),
                revocable,
            };

            // Store trust
            Fideicommissa::<T>::insert(trust_id, trust);

            // Update indexes
            TrustsByConstituant::<T>::try_mutate(&constituant, |trusts| {
                trusts.try_push(trust_id).map_err(|_| Error::<T>::MaxTrustsReached)
            })?;
            TrustsByGreve::<T>::try_mutate(&greve, |trusts| {
                trusts.try_push(trust_id).map_err(|_| Error::<T>::MaxTrustsReached)
            })?;
            TrustsByAppele::<T>::try_mutate(&appele, |trusts| {
                trusts.try_push(trust_id).map_err(|_| Error::<T>::MaxTrustsReached)
            })?;

            // Add to trigger index
            TrustsByTrigger::<T>::try_mutate(trigger_block, |trusts| {
                trusts.try_push(trust_id).map_err(|_| Error::<T>::MaxTrustsReached)
            })?;

            Self::deposit_event(Event::TrustCreated {
                trust_id,
                constituant: constituant.clone(),
                greve,
                appele,
                trigger_block,
            });

            // Handle initial deposit
            Self::do_deposit(&constituant, trust_id, initial_deposit)?;

            Ok(())
        }

        /// Deposit additional funds into a trust.
        #[pallet::call_index(1)]
        #[pallet::weight(Weight::from_parts(50_000, 0))]
        pub fn deposit(
            origin: OriginFor<T>,
            trust_id: u64,
            amount: BalanceOf<T>,
        ) -> DispatchResult {
            let who = ensure_signed(origin)?;

            let trust = Fideicommissa::<T>::get(trust_id)
                .ok_or(Error::<T>::TrustNotFound)?;

            // Only constituant can deposit
            ensure!(who == trust.constituant, Error::<T>::NotAuthorized);

            // Must be Pending or Active
            ensure!(
                trust.status == FideicommisStatus::Pending ||
                trust.status == FideicommisStatus::Active,
                Error::<T>::TrustNotActive
            );

            Self::do_deposit(&who, trust_id, amount)
        }

        /// Claim funds as grevé (primary beneficiary) before trigger.
        #[pallet::call_index(2)]
        #[pallet::weight(Weight::from_parts(60_000, 0))]
        pub fn claim_as_greve(
            origin: OriginFor<T>,
            trust_id: u64,
            amount: BalanceOf<T>,
        ) -> DispatchResult {
            let who = ensure_signed(origin)?;

            let mut trust = Fideicommissa::<T>::get(trust_id)
                .ok_or(Error::<T>::TrustNotFound)?;

            // Only grevé can claim
            ensure!(who == trust.greve, Error::<T>::NotAuthorized);

            // Trust must be active
            ensure!(trust.status == FideicommisStatus::Active, Error::<T>::InvalidStatus);

            let current_block = frame_system::Pallet::<T>::block_number();

            // Check claim period
            let claim_deadline = trust.greve_claim_before.unwrap_or(trust.trigger_block);
            ensure!(current_block < claim_deadline, Error::<T>::ClaimPeriodInvalid);

            // Check sufficient balance
            let available = trust.balance.saturating_sub(trust.greve_claimed);
            ensure!(amount <= available, Error::<T>::InsufficientTrustBalance);
            ensure!(!amount.is_zero(), Error::<T>::NoFundsToClaim);

            // Transfer from reserved to grevé
            T::Currency::unreserve(&trust.constituant, amount);
            T::Currency::transfer(
                &trust.constituant,
                &who,
                amount,
                ExistenceRequirement::AllowDeath,
            )?;

            // Update trust
            trust.greve_claimed = trust.greve_claimed.saturating_add(amount);

            // Update total locked
            TotalLocked::<T>::mutate(|total| {
                *total = total.saturating_sub(amount);
            });

            let remaining = trust.balance.saturating_sub(trust.greve_claimed);
            Fideicommissa::<T>::insert(trust_id, trust);

            Self::deposit_event(Event::GreveClaimed {
                trust_id,
                claimer: who,
                amount,
                remaining,
            });

            Ok(())
        }

        /// Claim funds as appelé (substitute beneficiary) after trigger.
        #[pallet::call_index(3)]
        #[pallet::weight(Weight::from_parts(60_000, 0))]
        pub fn claim_as_appele(
            origin: OriginFor<T>,
            trust_id: u64,
        ) -> DispatchResult {
            let who = ensure_signed(origin)?;

            let mut trust = Fideicommissa::<T>::get(trust_id)
                .ok_or(Error::<T>::TrustNotFound)?;

            // Only appelé can claim
            ensure!(who == trust.appele, Error::<T>::NotAuthorized);

            let current_block = frame_system::Pallet::<T>::block_number();

            // Must be past trigger block
            ensure!(current_block >= trust.trigger_block, Error::<T>::TriggerNotReached);

            // Trigger if not already (in case on_initialize was missed)
            if trust.status == FideicommisStatus::Active {
                trust.status = FideicommisStatus::Triggered;

                let balance_for_appele = trust.balance.saturating_sub(trust.greve_claimed);

                Self::deposit_event(Event::TrustTriggered {
                    trust_id,
                    trigger_block: trust.trigger_block,
                    balance_for_appele,
                });
            }

            ensure!(trust.status == FideicommisStatus::Triggered, Error::<T>::InvalidStatus);

            // Calculate claimable amount
            let claimable = trust.balance
                .saturating_sub(trust.greve_claimed)
                .saturating_sub(trust.appele_claimed);

            ensure!(!claimable.is_zero(), Error::<T>::NoFundsToClaim);

            // Transfer from reserved to appelé
            T::Currency::unreserve(&trust.constituant, claimable);
            T::Currency::transfer(
                &trust.constituant,
                &who,
                claimable,
                ExistenceRequirement::AllowDeath,
            )?;

            // Update trust
            trust.appele_claimed = trust.appele_claimed.saturating_add(claimable);

            // Update total locked
            TotalLocked::<T>::mutate(|total| {
                *total = total.saturating_sub(claimable);
            });

            // Check if completed
            let total_claimed = trust.greve_claimed.saturating_add(trust.appele_claimed);
            if total_claimed >= trust.balance {
                trust.status = FideicommisStatus::Completed;
                ActiveCount::<T>::mutate(|c| *c = c.saturating_sub(1));

                Self::deposit_event(Event::TrustCompleted {
                    trust_id,
                    greve_total: trust.greve_claimed,
                    appele_total: trust.appele_claimed,
                });
            }

            Fideicommissa::<T>::insert(trust_id, trust.clone());

            Self::deposit_event(Event::AppeleClaimed {
                trust_id,
                claimer: who,
                amount: claimable,
            });

            Ok(())
        }

        /// Cancel a trust and return funds to constituant.
        #[pallet::call_index(4)]
        #[pallet::weight(Weight::from_parts(60_000, 0))]
        pub fn cancel(
            origin: OriginFor<T>,
            trust_id: u64,
        ) -> DispatchResult {
            // Check if ForceOrigin or signed
            let is_forced = T::ForceOrigin::try_origin(origin.clone()).is_ok();

            let canceller = if is_forced {
                let trust = Fideicommissa::<T>::get(trust_id)
                    .ok_or(Error::<T>::TrustNotFound)?;
                trust.constituant.clone()
            } else {
                ensure_signed(origin)?
            };

            let mut trust = Fideicommissa::<T>::get(trust_id)
                .ok_or(Error::<T>::TrustNotFound)?;

            // If not forced, check authorization
            if !is_forced {
                ensure!(
                    canceller == trust.constituant || canceller == trust.fiduciary,
                    Error::<T>::NotAuthorized
                );
                ensure!(trust.revocable, Error::<T>::TrustIrrevocable);
            }

            // Cannot cancel if already triggered
            let current_block = frame_system::Pallet::<T>::block_number();
            ensure!(current_block < trust.trigger_block, Error::<T>::CannotCancelTriggered);

            // Calculate amount to return
            let return_amount = trust.balance.saturating_sub(trust.greve_claimed);

            // Return remaining escrow to constituant
            if !return_amount.is_zero() {
                T::Currency::unreserve(&trust.constituant, return_amount);
            }

            // Update total locked
            TotalLocked::<T>::mutate(|total| {
                *total = total.saturating_sub(return_amount);
            });

            // Update status
            trust.status = FideicommisStatus::Cancelled;
            Fideicommissa::<T>::insert(trust_id, trust.clone());

            // Update counts
            if trust.balance > Zero::zero() {
                ActiveCount::<T>::mutate(|c| *c = c.saturating_sub(1));
            }

            Self::deposit_event(Event::TrustCancelled {
                trust_id,
                cancelled_by: canceller,
                returned_to: trust.constituant.clone(),
                amount: return_amount,
            });

            Ok(())
        }

        /// Change the fiduciary (trustee) of a trust.
        #[pallet::call_index(5)]
        #[pallet::weight(Weight::from_parts(30_000, 0))]
        pub fn change_fiduciary(
            origin: OriginFor<T>,
            trust_id: u64,
            new_fiduciary: T::AccountId,
        ) -> DispatchResult {
            let who = ensure_signed(origin)?;

            let mut trust = Fideicommissa::<T>::get(trust_id)
                .ok_or(Error::<T>::TrustNotFound)?;

            // Only constituant can change fiduciary
            ensure!(who == trust.constituant, Error::<T>::NotAuthorized);

            // Must not be cancelled/completed
            ensure!(
                trust.status != FideicommisStatus::Cancelled &&
                trust.status != FideicommisStatus::Completed,
                Error::<T>::InvalidStatus
            );

            let old_fiduciary = trust.fiduciary.clone();
            trust.fiduciary = new_fiduciary.clone();
            Fideicommissa::<T>::insert(trust_id, trust);

            Self::deposit_event(Event::FiduciaryChanged {
                trust_id,
                old_fiduciary,
                new_fiduciary,
            });

            Ok(())
        }
    }

    // ==================== HELPER FUNCTIONS ====================

    impl<T: Config> Pallet<T> {
        /// Internal deposit logic
        fn do_deposit(
            depositor: &T::AccountId,
            trust_id: u64,
            amount: BalanceOf<T>,
        ) -> DispatchResult {
            let mut trust = Fideicommissa::<T>::get(trust_id)
                .ok_or(Error::<T>::TrustNotFound)?;

            // Reserve funds
            T::Currency::reserve(depositor, amount)?;

            // Update trust balance
            let was_pending = trust.status == FideicommisStatus::Pending;
            trust.balance = trust.balance.saturating_add(amount);

            // Activate if first deposit
            if was_pending {
                trust.status = FideicommisStatus::Active;
                ActiveCount::<T>::mutate(|c| *c = c.saturating_add(1));

                Self::deposit_event(Event::TrustActivated {
                    trust_id,
                    balance: trust.balance,
                });
            }

            // Update total locked
            TotalLocked::<T>::mutate(|total| {
                *total = total.saturating_add(amount);
            });

            Fideicommissa::<T>::insert(trust_id, trust.clone());

            Self::deposit_event(Event::FundsDeposited {
                trust_id,
                depositor: depositor.clone(),
                amount,
                total_balance: trust.balance,
            });

            Ok(())
        }

        // ==================== PUBLIC QUERY HELPERS ====================

        /// Get all trusts for an account (as any role)
        pub fn get_trusts_for_account(account: &T::AccountId) -> Vec<u64> {
            let mut trusts = Vec::new();
            trusts.extend(TrustsByConstituant::<T>::get(account).to_vec());
            trusts.extend(TrustsByGreve::<T>::get(account).to_vec());
            trusts.extend(TrustsByAppele::<T>::get(account).to_vec());
            trusts.sort();
            trusts.dedup();
            trusts
        }

        /// Check if a trust is triggered
        pub fn is_triggered(trust_id: u64) -> bool {
            Fideicommissa::<T>::get(trust_id)
                .map(|t| matches!(t.status,
                    FideicommisStatus::Triggered |
                    FideicommisStatus::Completed
                ))
                .unwrap_or(false)
        }

        /// Get claimable amount for grevé
        pub fn greve_claimable(trust_id: u64) -> BalanceOf<T> {
            Fideicommissa::<T>::get(trust_id)
                .map(|trust| {
                    if trust.status != FideicommisStatus::Active {
                        return Zero::zero();
                    }
                    let current_block = frame_system::Pallet::<T>::block_number();
                    let deadline = trust.greve_claim_before.unwrap_or(trust.trigger_block);
                    if current_block >= deadline {
                        return Zero::zero();
                    }
                    trust.balance.saturating_sub(trust.greve_claimed)
                })
                .unwrap_or(Zero::zero())
        }

        /// Get claimable amount for appelé
        pub fn appele_claimable(trust_id: u64) -> BalanceOf<T> {
            Fideicommissa::<T>::get(trust_id)
                .map(|trust| {
                    let current_block = frame_system::Pallet::<T>::block_number();
                    if current_block < trust.trigger_block {
                        return Zero::zero();
                    }
                    trust.balance
                        .saturating_sub(trust.greve_claimed)
                        .saturating_sub(trust.appele_claimed)
                })
                .unwrap_or(Zero::zero())
        }
    }
}
