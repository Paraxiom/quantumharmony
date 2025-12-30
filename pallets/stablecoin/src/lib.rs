//! # QCAD Stablecoin Pallet
//!
//! Collateralized CAD stablecoin for QuantumHarmony.
//!
//! ## Overview
//!
//! QCAD is a stablecoin pegged to the Canadian Dollar, backed by QMHY tokens
//! at a minimum 150% collateralization ratio. Users open vaults to lock QMHY
//! and mint QCAD. If collateral ratio drops below 120%, vaults can be liquidated.
//!
//! ## Core Concepts
//!
//! - **Vault**: A user's collateral position (QMHY locked, QCAD debt)
//! - **Collateral Ratio**: Value of QMHY / QCAD minted (min 150%)
//! - **Liquidation**: When ratio < 120%, anyone can repay debt and claim collateral
//! - **Stability Fee**: Annual interest on minted QCAD
//! - **Oracle**: Trusted price feed for QMHY/CAD
//!
//! ## Security
//!
//! - Oracle price must be fresh (configurable staleness limit)
//! - Liquidation penalty incentivizes healthy ratios
//! - Minimum vault size prevents dust attacks
//! - Only vault owner can withdraw (except liquidation)

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
    use sp_runtime::{
        traits::{Saturating, Zero},
        FixedU128, FixedPointNumber,
    };
    use sp_std::prelude::*;

    /// Balance type for QMHY (collateral)
    pub type BalanceOf<T> =
        <<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;

    /// Price type - fixed point with 18 decimals
    pub type Price = FixedU128;

    /// Maximum vaults per account
    pub const MAX_VAULTS_PER_ACCOUNT: u32 = 50;

    /// Blocks per year (at 3s blocks)
    pub const BLOCKS_PER_YEAR: u64 = 10_512_000;

    // ==================== DATA STRUCTURES ====================

    /// Status of a vault
    #[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, TypeInfo, MaxEncodedLen, Default)]
    pub enum VaultStatus {
        /// Vault is healthy (ratio >= 150%)
        #[default]
        Active,
        /// Vault is at risk (120% <= ratio < 150%)
        AtRisk,
        /// Vault can be liquidated (ratio < 120%)
        Liquidatable,
        /// Vault has been liquidated
        Liquidated,
        /// Vault has been closed by owner
        Closed,
    }

    /// A collateral vault
    #[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
    #[scale_info(skip_type_params(T))]
    pub struct Vault<T: Config> {
        /// Unique vault ID
        pub id: u64,
        /// Vault owner
        pub owner: T::AccountId,
        /// QMHY collateral locked
        pub collateral: BalanceOf<T>,
        /// QCAD debt (minted)
        pub debt: BalanceOf<T>,
        /// Block when vault was created
        pub created_at: BlockNumberFor<T>,
        /// Last block when fees were accrued
        pub last_fee_block: BlockNumberFor<T>,
        /// Accumulated stability fees
        pub accumulated_fees: BalanceOf<T>,
        /// Vault status
        pub status: VaultStatus,
    }

    // ==================== PALLET CONFIG ====================

    #[pallet::config]
    pub trait Config: frame_system::Config {
        /// The overarching event type
        type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

        /// Currency type for QMHY collateral
        type Currency: Currency<Self::AccountId> + ReservableCurrency<Self::AccountId>;

        /// Minimum collateral ratio (e.g., 150% = 1_500_000)
        /// Stored as parts per million (1_000_000 = 100%)
        #[pallet::constant]
        type MinCollateralRatio: Get<u32>;

        /// Liquidation ratio (e.g., 120% = 1_200_000)
        #[pallet::constant]
        type LiquidationRatio: Get<u32>;

        /// Liquidation penalty (e.g., 13% = 130_000)
        #[pallet::constant]
        type LiquidationPenalty: Get<u32>;

        /// Stability fee rate per year (e.g., 2% = 20_000)
        #[pallet::constant]
        type StabilityFeeRate: Get<u32>;

        /// Minimum vault debt in QCAD (prevents dust)
        #[pallet::constant]
        type MinVaultDebt: Get<BalanceOf<Self>>;

        /// Oracle price validity period in blocks
        #[pallet::constant]
        type OracleValidityPeriod: Get<BlockNumberFor<Self>>;

        /// Origin that can update oracle price
        type OracleOrigin: EnsureOrigin<Self::RuntimeOrigin>;

        /// Origin that can force-liquidate (governance)
        type ForceOrigin: EnsureOrigin<Self::RuntimeOrigin>;
    }

    #[pallet::pallet]
    #[pallet::without_storage_info]
    pub struct Pallet<T>(_);

    // ==================== STORAGE ====================

    /// All vaults by ID
    #[pallet::storage]
    #[pallet::getter(fn vaults)]
    pub type Vaults<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        u64,
        Vault<T>,
        OptionQuery,
    >;

    /// Next vault ID
    #[pallet::storage]
    #[pallet::getter(fn next_vault_id)]
    pub type NextVaultId<T: Config> = StorageValue<_, u64, ValueQuery>;

    /// Vaults by owner
    #[pallet::storage]
    #[pallet::getter(fn vaults_by_owner)]
    pub type VaultsByOwner<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        T::AccountId,
        BoundedVec<u64, ConstU32<MAX_VAULTS_PER_ACCOUNT>>,
        ValueQuery,
    >;

    /// QCAD balances
    #[pallet::storage]
    #[pallet::getter(fn qcad_balance)]
    pub type QCADBalances<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        T::AccountId,
        BalanceOf<T>,
        ValueQuery,
    >;

    /// Total QCAD supply
    #[pallet::storage]
    #[pallet::getter(fn total_qcad_supply)]
    pub type TotalQCADSupply<T: Config> = StorageValue<_, BalanceOf<T>, ValueQuery>;

    /// QMHY price in CAD (18 decimals fixed point) and last update block
    #[pallet::storage]
    #[pallet::getter(fn qmhy_price)]
    pub type QMHYPrice<T: Config> = StorageValue<_, (Price, BlockNumberFor<T>), ValueQuery>;

    /// Total QMHY collateral locked across all vaults
    #[pallet::storage]
    #[pallet::getter(fn total_collateral)]
    pub type TotalCollateral<T: Config> = StorageValue<_, BalanceOf<T>, ValueQuery>;

    /// Total QCAD debt outstanding
    #[pallet::storage]
    #[pallet::getter(fn total_debt)]
    pub type TotalDebt<T: Config> = StorageValue<_, BalanceOf<T>, ValueQuery>;

    /// Accumulated protocol fees (from stability fees and liquidations)
    #[pallet::storage]
    #[pallet::getter(fn protocol_fees)]
    pub type ProtocolFees<T: Config> = StorageValue<_, BalanceOf<T>, ValueQuery>;

    // ==================== EVENTS ====================

    #[pallet::event]
    #[pallet::generate_deposit(pub(super) fn deposit_event)]
    pub enum Event<T: Config> {
        /// Vault opened
        VaultOpened {
            vault_id: u64,
            owner: T::AccountId,
            collateral: BalanceOf<T>,
            debt: BalanceOf<T>,
        },
        /// Collateral deposited
        CollateralDeposited {
            vault_id: u64,
            amount: BalanceOf<T>,
            new_collateral: BalanceOf<T>,
        },
        /// Collateral withdrawn
        CollateralWithdrawn {
            vault_id: u64,
            amount: BalanceOf<T>,
            new_collateral: BalanceOf<T>,
        },
        /// QCAD minted
        QCADMinted {
            vault_id: u64,
            amount: BalanceOf<T>,
            new_debt: BalanceOf<T>,
        },
        /// QCAD repaid
        QCADRepaid {
            vault_id: u64,
            amount: BalanceOf<T>,
            new_debt: BalanceOf<T>,
        },
        /// Vault closed
        VaultClosed {
            vault_id: u64,
            owner: T::AccountId,
            collateral_returned: BalanceOf<T>,
        },
        /// Vault liquidated
        VaultLiquidated {
            vault_id: u64,
            liquidator: T::AccountId,
            debt_repaid: BalanceOf<T>,
            collateral_seized: BalanceOf<T>,
        },
        /// QCAD transferred
        QCADTransferred {
            from: T::AccountId,
            to: T::AccountId,
            amount: BalanceOf<T>,
        },
        /// Oracle price updated
        PriceUpdated {
            price: Price,
            block: BlockNumberFor<T>,
        },
        /// Stability fees accrued
        FeesAccrued {
            vault_id: u64,
            fees: BalanceOf<T>,
        },
    }

    // ==================== ERRORS ====================

    #[pallet::error]
    pub enum Error<T> {
        /// Vault not found
        VaultNotFound,
        /// Not vault owner
        NotVaultOwner,
        /// Vault not active
        VaultNotActive,
        /// Collateral ratio too low
        CollateralRatioTooLow,
        /// Cannot liquidate healthy vault
        VaultNotLiquidatable,
        /// Debt below minimum
        DebtBelowMinimum,
        /// Insufficient QCAD balance
        InsufficientQCAD,
        /// Insufficient collateral
        InsufficientCollateral,
        /// Insufficient QMHY balance
        InsufficientQMHY,
        /// Oracle price stale
        OraclePriceStale,
        /// Oracle price not set
        OraclePriceNotSet,
        /// Max vaults per account reached
        MaxVaultsReached,
        /// Overflow error
        Overflow,
        /// Vault already closed
        VaultAlreadyClosed,
        /// Cannot withdraw - would make vault liquidatable
        WithdrawalWouldLiquidate,
        /// Zero amount not allowed
        ZeroAmount,
    }

    // ==================== DISPATCHABLES ====================

    #[pallet::call]
    impl<T: Config> Pallet<T> {
        /// Open a new vault with collateral and mint QCAD.
        ///
        /// ## Parameters
        /// - `collateral`: Amount of QMHY to lock
        /// - `mint_amount`: Amount of QCAD to mint
        #[pallet::call_index(0)]
        #[pallet::weight(Weight::from_parts(80_000, 0))]
        pub fn open_vault(
            origin: OriginFor<T>,
            collateral: BalanceOf<T>,
            mint_amount: BalanceOf<T>,
        ) -> DispatchResult {
            let owner = ensure_signed(origin)?;

            ensure!(!collateral.is_zero(), Error::<T>::ZeroAmount);
            ensure!(mint_amount >= T::MinVaultDebt::get(), Error::<T>::DebtBelowMinimum);

            // Check oracle price is fresh
            Self::ensure_price_fresh()?;

            // Check collateral ratio
            let ratio = Self::calculate_ratio(collateral, mint_amount)?;
            ensure!(ratio >= T::MinCollateralRatio::get(), Error::<T>::CollateralRatioTooLow);

            // Check user has enough QMHY
            ensure!(
                T::Currency::free_balance(&owner) >= collateral,
                Error::<T>::InsufficientQMHY
            );

            // Reserve collateral
            T::Currency::reserve(&owner, collateral)?;

            // Generate vault ID
            let vault_id = NextVaultId::<T>::get();
            NextVaultId::<T>::put(vault_id.saturating_add(1));

            let current_block = frame_system::Pallet::<T>::block_number();

            // Create vault
            let vault = Vault {
                id: vault_id,
                owner: owner.clone(),
                collateral,
                debt: mint_amount,
                created_at: current_block,
                last_fee_block: current_block,
                accumulated_fees: Zero::zero(),
                status: VaultStatus::Active,
            };

            // Store vault
            Vaults::<T>::insert(vault_id, vault);

            // Update index
            VaultsByOwner::<T>::try_mutate(&owner, |vaults| {
                vaults.try_push(vault_id).map_err(|_| Error::<T>::MaxVaultsReached)
            })?;

            // Mint QCAD to owner
            QCADBalances::<T>::mutate(&owner, |bal| {
                *bal = bal.saturating_add(mint_amount);
            });
            TotalQCADSupply::<T>::mutate(|s| *s = s.saturating_add(mint_amount));

            // Update totals
            TotalCollateral::<T>::mutate(|c| *c = c.saturating_add(collateral));
            TotalDebt::<T>::mutate(|d| *d = d.saturating_add(mint_amount));

            Self::deposit_event(Event::VaultOpened {
                vault_id,
                owner,
                collateral,
                debt: mint_amount,
            });

            Ok(())
        }

        /// Deposit additional collateral to a vault.
        #[pallet::call_index(1)]
        #[pallet::weight(Weight::from_parts(50_000, 0))]
        pub fn deposit_collateral(
            origin: OriginFor<T>,
            vault_id: u64,
            amount: BalanceOf<T>,
        ) -> DispatchResult {
            let who = ensure_signed(origin)?;

            ensure!(!amount.is_zero(), Error::<T>::ZeroAmount);

            let mut vault = Vaults::<T>::get(vault_id).ok_or(Error::<T>::VaultNotFound)?;
            ensure!(vault.owner == who, Error::<T>::NotVaultOwner);
            ensure!(vault.status == VaultStatus::Active || vault.status == VaultStatus::AtRisk, Error::<T>::VaultNotActive);

            // Accrue fees first
            Self::accrue_fees(&mut vault)?;

            // Reserve additional collateral
            T::Currency::reserve(&who, amount)?;

            vault.collateral = vault.collateral.saturating_add(amount);

            // Update vault status
            vault.status = Self::get_vault_status(&vault)?;

            Vaults::<T>::insert(vault_id, vault.clone());
            TotalCollateral::<T>::mutate(|c| *c = c.saturating_add(amount));

            Self::deposit_event(Event::CollateralDeposited {
                vault_id,
                amount,
                new_collateral: vault.collateral,
            });

            Ok(())
        }

        /// Withdraw collateral from a vault (if ratio stays healthy).
        #[pallet::call_index(2)]
        #[pallet::weight(Weight::from_parts(60_000, 0))]
        pub fn withdraw_collateral(
            origin: OriginFor<T>,
            vault_id: u64,
            amount: BalanceOf<T>,
        ) -> DispatchResult {
            let who = ensure_signed(origin)?;

            ensure!(!amount.is_zero(), Error::<T>::ZeroAmount);
            Self::ensure_price_fresh()?;

            let mut vault = Vaults::<T>::get(vault_id).ok_or(Error::<T>::VaultNotFound)?;
            ensure!(vault.owner == who, Error::<T>::NotVaultOwner);
            ensure!(vault.status == VaultStatus::Active, Error::<T>::VaultNotActive);

            // Accrue fees first
            Self::accrue_fees(&mut vault)?;

            ensure!(vault.collateral >= amount, Error::<T>::InsufficientCollateral);

            let new_collateral = vault.collateral.saturating_sub(amount);
            let total_debt = vault.debt.saturating_add(vault.accumulated_fees);

            // Check new ratio is still healthy
            if !total_debt.is_zero() {
                let new_ratio = Self::calculate_ratio(new_collateral, total_debt)?;
                ensure!(new_ratio >= T::MinCollateralRatio::get(), Error::<T>::WithdrawalWouldLiquidate);
            }

            // Unreserve and transfer collateral
            T::Currency::unreserve(&who, amount);

            vault.collateral = new_collateral;
            vault.status = Self::get_vault_status(&vault)?;

            Vaults::<T>::insert(vault_id, vault.clone());
            TotalCollateral::<T>::mutate(|c| *c = c.saturating_sub(amount));

            Self::deposit_event(Event::CollateralWithdrawn {
                vault_id,
                amount,
                new_collateral: vault.collateral,
            });

            Ok(())
        }

        /// Mint additional QCAD against existing collateral.
        #[pallet::call_index(3)]
        #[pallet::weight(Weight::from_parts(50_000, 0))]
        pub fn mint_qcad(
            origin: OriginFor<T>,
            vault_id: u64,
            amount: BalanceOf<T>,
        ) -> DispatchResult {
            let who = ensure_signed(origin)?;

            ensure!(!amount.is_zero(), Error::<T>::ZeroAmount);
            Self::ensure_price_fresh()?;

            let mut vault = Vaults::<T>::get(vault_id).ok_or(Error::<T>::VaultNotFound)?;
            ensure!(vault.owner == who, Error::<T>::NotVaultOwner);
            ensure!(vault.status == VaultStatus::Active, Error::<T>::VaultNotActive);

            // Accrue fees first
            Self::accrue_fees(&mut vault)?;

            let new_debt = vault.debt.saturating_add(amount);
            let total_debt = new_debt.saturating_add(vault.accumulated_fees);

            // Check ratio stays healthy
            let ratio = Self::calculate_ratio(vault.collateral, total_debt)?;
            ensure!(ratio >= T::MinCollateralRatio::get(), Error::<T>::CollateralRatioTooLow);

            vault.debt = new_debt;
            vault.status = Self::get_vault_status(&vault)?;

            Vaults::<T>::insert(vault_id, vault.clone());

            // Mint QCAD
            QCADBalances::<T>::mutate(&who, |bal| {
                *bal = bal.saturating_add(amount);
            });
            TotalQCADSupply::<T>::mutate(|s| *s = s.saturating_add(amount));
            TotalDebt::<T>::mutate(|d| *d = d.saturating_add(amount));

            Self::deposit_event(Event::QCADMinted {
                vault_id,
                amount,
                new_debt: vault.debt,
            });

            Ok(())
        }

        /// Repay QCAD debt.
        #[pallet::call_index(4)]
        #[pallet::weight(Weight::from_parts(50_000, 0))]
        pub fn repay_qcad(
            origin: OriginFor<T>,
            vault_id: u64,
            amount: BalanceOf<T>,
        ) -> DispatchResult {
            let who = ensure_signed(origin)?;

            ensure!(!amount.is_zero(), Error::<T>::ZeroAmount);

            let mut vault = Vaults::<T>::get(vault_id).ok_or(Error::<T>::VaultNotFound)?;
            ensure!(vault.owner == who, Error::<T>::NotVaultOwner);
            ensure!(
                vault.status == VaultStatus::Active ||
                vault.status == VaultStatus::AtRisk ||
                vault.status == VaultStatus::Liquidatable,
                Error::<T>::VaultNotActive
            );

            // Accrue fees first
            Self::accrue_fees(&mut vault)?;

            // Check user has enough QCAD
            let user_balance = QCADBalances::<T>::get(&who);
            ensure!(user_balance >= amount, Error::<T>::InsufficientQCAD);

            // First pay off accumulated fees, then principal
            let mut remaining = amount;

            if vault.accumulated_fees > Zero::zero() {
                let fee_payment = remaining.min(vault.accumulated_fees);
                vault.accumulated_fees = vault.accumulated_fees.saturating_sub(fee_payment);
                remaining = remaining.saturating_sub(fee_payment);

                // Fees go to protocol
                ProtocolFees::<T>::mutate(|f| *f = f.saturating_add(fee_payment));
            }

            if remaining > Zero::zero() {
                let debt_payment = remaining.min(vault.debt);
                vault.debt = vault.debt.saturating_sub(debt_payment);
                TotalDebt::<T>::mutate(|d| *d = d.saturating_sub(debt_payment));
            }

            // Burn QCAD
            QCADBalances::<T>::mutate(&who, |bal| {
                *bal = bal.saturating_sub(amount);
            });
            TotalQCADSupply::<T>::mutate(|s| *s = s.saturating_sub(amount));

            vault.status = Self::get_vault_status(&vault)?;
            Vaults::<T>::insert(vault_id, vault.clone());

            Self::deposit_event(Event::QCADRepaid {
                vault_id,
                amount,
                new_debt: vault.debt,
            });

            Ok(())
        }

        /// Close vault by repaying all debt and withdrawing collateral.
        #[pallet::call_index(5)]
        #[pallet::weight(Weight::from_parts(70_000, 0))]
        pub fn close_vault(
            origin: OriginFor<T>,
            vault_id: u64,
        ) -> DispatchResult {
            let who = ensure_signed(origin)?;

            let mut vault = Vaults::<T>::get(vault_id).ok_or(Error::<T>::VaultNotFound)?;
            ensure!(vault.owner == who, Error::<T>::NotVaultOwner);
            ensure!(vault.status != VaultStatus::Closed && vault.status != VaultStatus::Liquidated, Error::<T>::VaultAlreadyClosed);

            // Accrue fees
            Self::accrue_fees(&mut vault)?;

            let total_owed = vault.debt.saturating_add(vault.accumulated_fees);

            // Check user has enough QCAD to repay
            let user_balance = QCADBalances::<T>::get(&who);
            ensure!(user_balance >= total_owed, Error::<T>::InsufficientQCAD);

            // Burn QCAD
            QCADBalances::<T>::mutate(&who, |bal| {
                *bal = bal.saturating_sub(total_owed);
            });
            TotalQCADSupply::<T>::mutate(|s| *s = s.saturating_sub(total_owed));

            // Pay fees to protocol
            if vault.accumulated_fees > Zero::zero() {
                ProtocolFees::<T>::mutate(|f| *f = f.saturating_add(vault.accumulated_fees));
            }

            // Return collateral
            let collateral_to_return = vault.collateral;
            T::Currency::unreserve(&who, collateral_to_return);

            // Update totals
            TotalCollateral::<T>::mutate(|c| *c = c.saturating_sub(collateral_to_return));
            TotalDebt::<T>::mutate(|d| *d = d.saturating_sub(vault.debt));

            // Mark vault as closed
            vault.status = VaultStatus::Closed;
            vault.collateral = Zero::zero();
            vault.debt = Zero::zero();
            vault.accumulated_fees = Zero::zero();
            Vaults::<T>::insert(vault_id, vault);

            Self::deposit_event(Event::VaultClosed {
                vault_id,
                owner: who,
                collateral_returned: collateral_to_return,
            });

            Ok(())
        }

        /// Liquidate an unhealthy vault.
        #[pallet::call_index(6)]
        #[pallet::weight(Weight::from_parts(80_000, 0))]
        pub fn liquidate(
            origin: OriginFor<T>,
            vault_id: u64,
        ) -> DispatchResult {
            let liquidator = ensure_signed(origin)?;

            Self::ensure_price_fresh()?;

            let mut vault = Vaults::<T>::get(vault_id).ok_or(Error::<T>::VaultNotFound)?;
            ensure!(vault.status != VaultStatus::Closed && vault.status != VaultStatus::Liquidated, Error::<T>::VaultAlreadyClosed);

            // Accrue fees
            Self::accrue_fees(&mut vault)?;

            // Check vault is liquidatable
            let total_debt = vault.debt.saturating_add(vault.accumulated_fees);
            let ratio = Self::calculate_ratio(vault.collateral, total_debt)?;
            ensure!(ratio < T::LiquidationRatio::get(), Error::<T>::VaultNotLiquidatable);

            // Liquidator must have enough QCAD to repay debt
            let liquidator_balance = QCADBalances::<T>::get(&liquidator);
            ensure!(liquidator_balance >= total_debt, Error::<T>::InsufficientQCAD);

            // Calculate collateral to seize (debt value + penalty)
            let base_collateral = Self::debt_to_collateral(total_debt)?;
            let base_u128: u128 = base_collateral.try_into().map_err(|_| Error::<T>::Overflow)?;
            let penalty_multiplier = 1_000_000u64.saturating_add(T::LiquidationPenalty::get() as u64);
            let seized_u128 = base_u128
                .saturating_mul(penalty_multiplier as u128)
                / 1_000_000u128;
            let collateral_to_seize: BalanceOf<T> = seized_u128.try_into().map_err(|_| Error::<T>::Overflow)?;
            let collateral_to_seize = collateral_to_seize.min(vault.collateral);

            // Burn liquidator's QCAD
            QCADBalances::<T>::mutate(&liquidator, |bal| {
                *bal = bal.saturating_sub(total_debt);
            });
            TotalQCADSupply::<T>::mutate(|s| *s = s.saturating_sub(total_debt));

            // Transfer collateral from vault owner to liquidator
            T::Currency::unreserve(&vault.owner, collateral_to_seize);
            T::Currency::transfer(
                &vault.owner,
                &liquidator,
                collateral_to_seize,
                ExistenceRequirement::AllowDeath,
            )?;

            // Any remaining collateral stays with owner (but unreserved)
            let remaining_collateral = vault.collateral.saturating_sub(collateral_to_seize);
            if remaining_collateral > Zero::zero() {
                T::Currency::unreserve(&vault.owner, remaining_collateral);
            }

            // Update totals
            TotalCollateral::<T>::mutate(|c| *c = c.saturating_sub(vault.collateral));
            TotalDebt::<T>::mutate(|d| *d = d.saturating_sub(vault.debt));

            // Fees go to protocol
            ProtocolFees::<T>::mutate(|f| *f = f.saturating_add(vault.accumulated_fees));

            // Mark vault as liquidated
            vault.status = VaultStatus::Liquidated;
            vault.collateral = Zero::zero();
            vault.debt = Zero::zero();
            vault.accumulated_fees = Zero::zero();
            Vaults::<T>::insert(vault_id, vault);

            Self::deposit_event(Event::VaultLiquidated {
                vault_id,
                liquidator,
                debt_repaid: total_debt,
                collateral_seized: collateral_to_seize,
            });

            Ok(())
        }

        /// Transfer QCAD between accounts.
        #[pallet::call_index(7)]
        #[pallet::weight(Weight::from_parts(40_000, 0))]
        pub fn transfer_qcad(
            origin: OriginFor<T>,
            to: T::AccountId,
            amount: BalanceOf<T>,
        ) -> DispatchResult {
            let from = ensure_signed(origin)?;

            ensure!(!amount.is_zero(), Error::<T>::ZeroAmount);

            let from_balance = QCADBalances::<T>::get(&from);
            ensure!(from_balance >= amount, Error::<T>::InsufficientQCAD);

            QCADBalances::<T>::mutate(&from, |bal| {
                *bal = bal.saturating_sub(amount);
            });
            QCADBalances::<T>::mutate(&to, |bal| {
                *bal = bal.saturating_add(amount);
            });

            Self::deposit_event(Event::QCADTransferred {
                from,
                to,
                amount,
            });

            Ok(())
        }

        /// Update QMHY/CAD oracle price (oracle origin only).
        #[pallet::call_index(8)]
        #[pallet::weight(Weight::from_parts(20_000, 0))]
        pub fn update_price(
            origin: OriginFor<T>,
            price: u128,
        ) -> DispatchResult {
            T::OracleOrigin::ensure_origin(origin)?;

            let fixed_price = Price::from_inner(price);
            let current_block = frame_system::Pallet::<T>::block_number();

            QMHYPrice::<T>::put((fixed_price, current_block));

            Self::deposit_event(Event::PriceUpdated {
                price: fixed_price,
                block: current_block,
            });

            Ok(())
        }
    }

    // ==================== HELPER FUNCTIONS ====================

    impl<T: Config> Pallet<T> {
        /// Ensure oracle price is fresh
        fn ensure_price_fresh() -> DispatchResult {
            let (price, last_update) = QMHYPrice::<T>::get();
            ensure!(!price.is_zero(), Error::<T>::OraclePriceNotSet);

            let current_block = frame_system::Pallet::<T>::block_number();
            let age = current_block.saturating_sub(last_update);
            ensure!(age <= T::OracleValidityPeriod::get(), Error::<T>::OraclePriceStale);

            Ok(())
        }

        /// Calculate collateral ratio in parts per million
        fn calculate_ratio(collateral: BalanceOf<T>, debt: BalanceOf<T>) -> Result<u32, DispatchError> {
            if debt.is_zero() {
                return Ok(u32::MAX);
            }

            let (price, _) = QMHYPrice::<T>::get();

            // collateral_value = collateral * price
            // ratio = collateral_value / debt * 1_000_000
            let collateral_u128: u128 = collateral.try_into().map_err(|_| Error::<T>::Overflow)?;
            let debt_u128: u128 = debt.try_into().map_err(|_| Error::<T>::Overflow)?;

            let collateral_value = price
                .checked_mul_int(collateral_u128)
                .ok_or(Error::<T>::Overflow)?;

            let ratio = collateral_value
                .checked_mul(1_000_000)
                .ok_or(Error::<T>::Overflow)?
                .checked_div(debt_u128)
                .ok_or(Error::<T>::Overflow)?;

            Ok(ratio.min(u32::MAX as u128) as u32)
        }

        /// Convert debt amount to collateral amount at current price
        fn debt_to_collateral(debt: BalanceOf<T>) -> Result<BalanceOf<T>, DispatchError> {
            let (price, _) = QMHYPrice::<T>::get();
            let debt_u128: u128 = debt.try_into().map_err(|_| Error::<T>::Overflow)?;

            // collateral = debt / price
            let collateral_u128 = price
                .reciprocal()
                .ok_or(Error::<T>::Overflow)?
                .checked_mul_int(debt_u128)
                .ok_or(Error::<T>::Overflow)?;

            Ok(collateral_u128.try_into().map_err(|_| Error::<T>::Overflow)?)
        }

        /// Get vault status based on current collateral ratio
        fn get_vault_status(vault: &Vault<T>) -> Result<VaultStatus, DispatchError> {
            let total_debt = vault.debt.saturating_add(vault.accumulated_fees);

            if total_debt.is_zero() {
                return Ok(VaultStatus::Active);
            }

            let ratio = Self::calculate_ratio(vault.collateral, total_debt)?;

            if ratio < T::LiquidationRatio::get() {
                Ok(VaultStatus::Liquidatable)
            } else if ratio < T::MinCollateralRatio::get() {
                Ok(VaultStatus::AtRisk)
            } else {
                Ok(VaultStatus::Active)
            }
        }

        /// Accrue stability fees on a vault
        fn accrue_fees(vault: &mut Vault<T>) -> DispatchResult {
            let current_block = frame_system::Pallet::<T>::block_number();
            let blocks_elapsed: u64 = current_block
                .saturating_sub(vault.last_fee_block)
                .try_into()
                .unwrap_or(0);

            if blocks_elapsed == 0 || vault.debt.is_zero() {
                vault.last_fee_block = current_block;
                return Ok(());
            }

            // fee = debt * rate * time / BLOCKS_PER_YEAR
            let debt_u128: u128 = vault.debt.try_into().map_err(|_| Error::<T>::Overflow)?;
            let rate = T::StabilityFeeRate::get() as u128;

            let fee = debt_u128
                .checked_mul(rate)
                .ok_or(Error::<T>::Overflow)?
                .checked_mul(blocks_elapsed as u128)
                .ok_or(Error::<T>::Overflow)?
                .checked_div(1_000_000 * BLOCKS_PER_YEAR as u128)
                .unwrap_or(0);

            let fee_balance: BalanceOf<T> = fee.try_into().map_err(|_| Error::<T>::Overflow)?;

            vault.accumulated_fees = vault.accumulated_fees.saturating_add(fee_balance);
            vault.last_fee_block = current_block;

            if fee > 0 {
                Self::deposit_event(Event::FeesAccrued {
                    vault_id: vault.id,
                    fees: fee_balance,
                });
            }

            Ok(())
        }

        // ==================== PUBLIC QUERIES ====================

        /// Get all vault IDs for an account
        pub fn get_vaults_for_account(account: &T::AccountId) -> Vec<u64> {
            VaultsByOwner::<T>::get(account).into_iter().collect()
        }

        /// Check if a vault is liquidatable
        pub fn is_liquidatable(vault_id: u64) -> bool {
            Vaults::<T>::get(vault_id)
                .map(|v| {
                    Self::get_vault_status(&v)
                        .map(|s| s == VaultStatus::Liquidatable)
                        .unwrap_or(false)
                })
                .unwrap_or(false)
        }

        /// Get current QMHY price in CAD
        pub fn get_price() -> Price {
            QMHYPrice::<T>::get().0
        }
    }
}
