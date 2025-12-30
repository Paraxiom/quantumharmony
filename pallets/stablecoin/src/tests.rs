//! Unit tests for QCAD Stablecoin pallet

use crate::{self as pallet_stablecoin, *};
use frame_support::{
    assert_noop, assert_ok,
    traits::{ConstU16, ConstU32, ConstU64},
    parameter_types,
};
use sp_core::H256;
use sp_runtime::{
    traits::{BlakeTwo256, IdentityLookup},
    BuildStorage, FixedU128,
};

type Block = frame_system::mocking::MockBlock<Test>;

frame_support::construct_runtime!(
    pub enum Test
    {
        System: frame_system,
        Balances: pallet_balances,
        Stablecoin: pallet_stablecoin,
    }
);

impl frame_system::Config for Test {
    type BaseCallFilter = frame_support::traits::Everything;
    type BlockWeights = ();
    type BlockLength = ();
    type DbWeight = ();
    type RuntimeOrigin = RuntimeOrigin;
    type RuntimeCall = RuntimeCall;
    type Nonce = u64;
    type Hash = H256;
    type Hashing = BlakeTwo256;
    type AccountId = u64;
    type Lookup = IdentityLookup<Self::AccountId>;
    type Block = Block;
    type RuntimeEvent = RuntimeEvent;
    type RuntimeTask = ();
    type BlockHashCount = ConstU64<250>;
    type Version = ();
    type PalletInfo = PalletInfo;
    type AccountData = pallet_balances::AccountData<u128>;
    type OnNewAccount = ();
    type OnKilledAccount = ();
    type SystemWeightInfo = ();
    type ExtensionsWeightInfo = ();
    type SS58Prefix = ConstU16<42>;
    type OnSetCode = ();
    type MaxConsumers = ConstU32<16>;
    type SingleBlockMigrations = ();
    type MultiBlockMigrator = ();
    type PreInherents = ();
    type PostInherents = ();
    type PostTransactions = ();
}

parameter_types! {
    pub const ExistentialDeposit: u128 = 1;
}

impl pallet_balances::Config for Test {
    type MaxLocks = ConstU32<50>;
    type MaxReserves = ConstU32<50>;
    type ReserveIdentifier = [u8; 8];
    type Balance = u128;
    type RuntimeEvent = RuntimeEvent;
    type DustRemoval = ();
    type ExistentialDeposit = ExistentialDeposit;
    type AccountStore = System;
    type WeightInfo = ();
    type FreezeIdentifier = ();
    type MaxFreezes = ConstU32<0>;
    type RuntimeHoldReason = ();
    type RuntimeFreezeReason = ();
    type DoneSlashHandler = ();
}

parameter_types! {
    pub const MinCollateralRatio: u32 = 1_500_000;    // 150%
    pub const LiquidationRatio: u32 = 1_200_000;      // 120%
    pub const LiquidationPenalty: u32 = 130_000;      // 13%
    pub const StabilityFeeRate: u32 = 20_000;         // 2% annual
    pub const MinVaultDebt: u128 = 100;               // 100 QCAD
    pub const OracleValidityPeriod: u64 = 100;        // 100 blocks
}

impl Config for Test {
    type RuntimeEvent = RuntimeEvent;
    type Currency = Balances;
    type MinCollateralRatio = MinCollateralRatio;
    type LiquidationRatio = LiquidationRatio;
    type LiquidationPenalty = LiquidationPenalty;
    type StabilityFeeRate = StabilityFeeRate;
    type MinVaultDebt = MinVaultDebt;
    type OracleValidityPeriod = OracleValidityPeriod;
    type OracleOrigin = frame_system::EnsureRoot<u64>;
    type ForceOrigin = frame_system::EnsureRoot<u64>;
}

// Test accounts
const ALICE: u64 = 1;
const BOB: u64 = 2;
const ORACLE: u64 = 100;

// Price: 1 QMHY = 1 CAD (for simplicity)
const QMHY_PRICE: u128 = 1_000_000_000_000_000_000; // 1.0 in FixedU128

fn new_test_ext() -> sp_io::TestExternalities {
    let mut t = frame_system::GenesisConfig::<Test>::default()
        .build_storage()
        .unwrap();

    pallet_balances::GenesisConfig::<Test> {
        balances: vec![
            (ALICE, 10_000_000),
            (BOB, 10_000_000),
        ],
        dev_accounts: None,
    }
    .assimilate_storage(&mut t)
    .unwrap();

    let mut ext = sp_io::TestExternalities::new(t);
    ext.execute_with(|| {
        System::set_block_number(1);
        // Set initial oracle price
        assert_ok!(Stablecoin::update_price(RuntimeOrigin::root(), QMHY_PRICE));
    });
    ext
}

fn advance_blocks(n: u64) {
    for _ in 0..n {
        let current = System::block_number();
        System::set_block_number(current + 1);
    }
}

// ==================== VAULT OPENING TESTS ====================

#[test]
fn test_open_vault_success() {
    new_test_ext().execute_with(|| {
        let collateral = 1500u128;
        let debt = 1000u128;

        assert_ok!(Stablecoin::open_vault(
            RuntimeOrigin::signed(ALICE),
            collateral,
            debt,
        ));

        // Check vault was created
        let vault = Stablecoin::vaults(0).expect("Vault should exist");
        assert_eq!(vault.owner, ALICE);
        assert_eq!(vault.collateral, collateral);
        assert_eq!(vault.debt, debt);
        assert_eq!(vault.status, VaultStatus::Active);

        // Check QCAD was minted
        assert_eq!(Stablecoin::qcad_balance(ALICE), debt);
        assert_eq!(Stablecoin::total_qcad_supply(), debt);

        // Check collateral was reserved
        assert_eq!(Balances::reserved_balance(ALICE), collateral);

        // Check totals
        assert_eq!(Stablecoin::total_collateral(), collateral);
        assert_eq!(Stablecoin::total_debt(), debt);
    });
}

#[test]
fn test_open_vault_fails_ratio_too_low() {
    new_test_ext().execute_with(|| {
        // 1000 collateral for 1000 debt = 100% ratio (below 150%)
        assert_noop!(
            Stablecoin::open_vault(
                RuntimeOrigin::signed(ALICE),
                1000,
                1000,
            ),
            Error::<Test>::CollateralRatioTooLow
        );
    });
}

#[test]
fn test_open_vault_fails_debt_too_low() {
    new_test_ext().execute_with(|| {
        // Debt below minimum (100)
        assert_noop!(
            Stablecoin::open_vault(
                RuntimeOrigin::signed(ALICE),
                200,
                50, // Below MinVaultDebt
            ),
            Error::<Test>::DebtBelowMinimum
        );
    });
}

// ==================== COLLATERAL TESTS ====================

#[test]
fn test_deposit_collateral() {
    new_test_ext().execute_with(|| {
        assert_ok!(Stablecoin::open_vault(
            RuntimeOrigin::signed(ALICE),
            1500,
            1000,
        ));

        assert_ok!(Stablecoin::deposit_collateral(
            RuntimeOrigin::signed(ALICE),
            0,
            500,
        ));

        let vault = Stablecoin::vaults(0).unwrap();
        assert_eq!(vault.collateral, 2000);
        assert_eq!(Balances::reserved_balance(ALICE), 2000);
    });
}

#[test]
fn test_withdraw_collateral() {
    new_test_ext().execute_with(|| {
        // Open with extra collateral (200%)
        assert_ok!(Stablecoin::open_vault(
            RuntimeOrigin::signed(ALICE),
            2000,
            1000,
        ));

        // Withdraw some (but stay above 150%)
        assert_ok!(Stablecoin::withdraw_collateral(
            RuntimeOrigin::signed(ALICE),
            0,
            400,
        ));

        let vault = Stablecoin::vaults(0).unwrap();
        assert_eq!(vault.collateral, 1600);
    });
}

#[test]
fn test_withdraw_fails_would_liquidate() {
    new_test_ext().execute_with(|| {
        // Open at exactly 150%
        assert_ok!(Stablecoin::open_vault(
            RuntimeOrigin::signed(ALICE),
            1500,
            1000,
        ));

        // Can't withdraw any - would go below 150%
        assert_noop!(
            Stablecoin::withdraw_collateral(
                RuntimeOrigin::signed(ALICE),
                0,
                100,
            ),
            Error::<Test>::WithdrawalWouldLiquidate
        );
    });
}

// ==================== MINT/REPAY TESTS ====================

#[test]
fn test_mint_more_qcad() {
    new_test_ext().execute_with(|| {
        // Open with extra collateral
        assert_ok!(Stablecoin::open_vault(
            RuntimeOrigin::signed(ALICE),
            3000,
            1000,
        ));

        // Mint more QCAD
        assert_ok!(Stablecoin::mint_qcad(
            RuntimeOrigin::signed(ALICE),
            0,
            500,
        ));

        let vault = Stablecoin::vaults(0).unwrap();
        assert_eq!(vault.debt, 1500);
        assert_eq!(Stablecoin::qcad_balance(ALICE), 1500);
    });
}

#[test]
fn test_repay_qcad() {
    new_test_ext().execute_with(|| {
        assert_ok!(Stablecoin::open_vault(
            RuntimeOrigin::signed(ALICE),
            1500,
            1000,
        ));

        // Repay half
        assert_ok!(Stablecoin::repay_qcad(
            RuntimeOrigin::signed(ALICE),
            0,
            500,
        ));

        let vault = Stablecoin::vaults(0).unwrap();
        assert_eq!(vault.debt, 500);
        assert_eq!(Stablecoin::qcad_balance(ALICE), 500);
    });
}

// ==================== CLOSE VAULT TESTS ====================

#[test]
fn test_close_vault() {
    new_test_ext().execute_with(|| {
        let initial_balance = Balances::free_balance(ALICE);

        assert_ok!(Stablecoin::open_vault(
            RuntimeOrigin::signed(ALICE),
            1500,
            1000,
        ));

        assert_ok!(Stablecoin::close_vault(
            RuntimeOrigin::signed(ALICE),
            0,
        ));

        let vault = Stablecoin::vaults(0).unwrap();
        assert_eq!(vault.status, VaultStatus::Closed);
        assert_eq!(vault.collateral, 0);
        assert_eq!(vault.debt, 0);

        // Collateral returned
        assert_eq!(Balances::free_balance(ALICE), initial_balance);
        assert_eq!(Balances::reserved_balance(ALICE), 0);

        // QCAD burned
        assert_eq!(Stablecoin::qcad_balance(ALICE), 0);
    });
}

// ==================== LIQUIDATION TESTS ====================

#[test]
fn test_liquidation() {
    new_test_ext().execute_with(|| {
        // Alice opens vault at 150%
        assert_ok!(Stablecoin::open_vault(
            RuntimeOrigin::signed(ALICE),
            1500,
            1000,
        ));

        // Bob opens his vault BEFORE price drop to get QCAD
        assert_ok!(Stablecoin::open_vault(
            RuntimeOrigin::signed(BOB),
            3000,
            1500,
        ));

        let bob_initial_qmhy = Balances::free_balance(BOB);

        // Price drops - now 1 QMHY = 0.7 CAD
        // Alice's collateral value = 1500 * 0.7 = 1050 CAD
        // Alice's ratio = 1050 / 1000 = 105% (below 120% liquidation threshold)
        // Bob's ratio = (3000 * 0.7) / 1500 = 140% (still above 120%, safe but at risk)
        let new_price = 700_000_000_000_000_000u128; // 0.7
        assert_ok!(Stablecoin::update_price(RuntimeOrigin::root(), new_price));

        // Bob liquidates Alice's vault
        assert_ok!(Stablecoin::liquidate(
            RuntimeOrigin::signed(BOB),
            0, // Alice's vault
        ));

        // Check Alice's vault is liquidated
        let vault = Stablecoin::vaults(0).unwrap();
        assert_eq!(vault.status, VaultStatus::Liquidated);
        assert_eq!(vault.collateral, 0);
        assert_eq!(vault.debt, 0);

        // Bob should have received collateral (minus his QCAD payment)
        // He paid 1000 QCAD, gets collateral + 13% penalty
        assert!(Balances::free_balance(BOB) > bob_initial_qmhy);
    });
}

#[test]
fn test_cannot_liquidate_healthy_vault() {
    new_test_ext().execute_with(|| {
        assert_ok!(Stablecoin::open_vault(
            RuntimeOrigin::signed(ALICE),
            1500,
            1000,
        ));

        // Give Bob QCAD
        assert_ok!(Stablecoin::open_vault(
            RuntimeOrigin::signed(BOB),
            3000,
            1500,
        ));

        // Try to liquidate healthy vault
        assert_noop!(
            Stablecoin::liquidate(RuntimeOrigin::signed(BOB), 0),
            Error::<Test>::VaultNotLiquidatable
        );
    });
}

// ==================== TRANSFER TESTS ====================

#[test]
fn test_transfer_qcad() {
    new_test_ext().execute_with(|| {
        assert_ok!(Stablecoin::open_vault(
            RuntimeOrigin::signed(ALICE),
            1500,
            1000,
        ));

        assert_ok!(Stablecoin::transfer_qcad(
            RuntimeOrigin::signed(ALICE),
            BOB,
            400,
        ));

        assert_eq!(Stablecoin::qcad_balance(ALICE), 600);
        assert_eq!(Stablecoin::qcad_balance(BOB), 400);
    });
}

// ==================== ORACLE TESTS ====================

#[test]
fn test_oracle_price_update() {
    new_test_ext().execute_with(|| {
        let new_price = 2_000_000_000_000_000_000u128; // 2.0
        assert_ok!(Stablecoin::update_price(RuntimeOrigin::root(), new_price));

        let (price, _) = Stablecoin::qmhy_price();
        assert_eq!(price, FixedU128::from_inner(new_price));
    });
}

#[test]
fn test_stale_price_fails() {
    new_test_ext().execute_with(|| {
        // Advance past oracle validity period
        advance_blocks(150);

        // Try to open vault with stale price
        assert_noop!(
            Stablecoin::open_vault(
                RuntimeOrigin::signed(ALICE),
                1500,
                1000,
            ),
            Error::<Test>::OraclePriceStale
        );
    });
}
