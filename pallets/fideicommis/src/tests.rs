//! Unit tests for Fideicommis pallet
//!
//! Tests cover:
//! 1. Trust creation with all parameters
//! 2. Deposit and activation
//! 3. Grevé claiming before trigger
//! 4. Appelé claiming after trigger
//! 5. Trust cancellation
//! 6. Error cases and authorization

use crate::{self as pallet_fideicommis, *};
use frame_support::{
    assert_noop, assert_ok,
    traits::{ConstU16, ConstU32, ConstU64, ConstU128, Hooks},
    parameter_types,
};
use sp_core::H256;
use sp_runtime::{
    traits::{BlakeTwo256, IdentityLookup},
    BuildStorage,
};

type Block = frame_system::mocking::MockBlock<Test>;

// Configure a mock runtime to test the pallet
frame_support::construct_runtime!(
    pub enum Test
    {
        System: frame_system,
        Balances: pallet_balances,
        Fideicommis: pallet_fideicommis,
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
    pub const MinTrustDuration: u64 = 10;
    pub const MaxTrustDuration: u64 = 1_000_000;
    pub const MinDeposit: u128 = 100;
}

impl Config for Test {
    type RuntimeEvent = RuntimeEvent;
    type Currency = Balances;
    type MinTrustDuration = MinTrustDuration;
    type MaxTrustDuration = MaxTrustDuration;
    type MinDeposit = MinDeposit;
    type ForceOrigin = frame_system::EnsureRoot<u64>;
}

// Helper function to create test environment
fn new_test_ext() -> sp_io::TestExternalities {
    let mut t = frame_system::GenesisConfig::<Test>::default()
        .build_storage()
        .unwrap();

    pallet_balances::GenesisConfig::<Test> {
        balances: vec![
            (ALICE, 10_000),
            (BOB, 10_000),
            (CHARLIE, 10_000),
            (DAVE, 10_000),
        ],
        dev_accounts: None,
    }
    .assimilate_storage(&mut t)
    .unwrap();

    let mut ext = sp_io::TestExternalities::new(t);
    ext.execute_with(|| System::set_block_number(1));
    ext
}

// Helper to advance blocks
fn advance_blocks(n: u64) {
    for _ in 0..n {
        let current = System::block_number();
        System::set_block_number(current + 1);
    }
}

// Helper to run on_initialize for triggering trusts
fn run_to_block(n: u64) {
    while System::block_number() < n {
        let current = System::block_number() + 1;
        System::set_block_number(current);
        Fideicommis::on_initialize(current);
    }
}

// Test accounts
const ALICE: u64 = 1;   // Constituant (creator)
const BOB: u64 = 2;     // Grevé (primary beneficiary)
const CHARLIE: u64 = 3; // Appelé (substitute beneficiary)
const DAVE: u64 = 4;    // Fiduciary

// ==================== TRUST CREATION TESTS ====================

#[test]
fn test_create_trust_success() {
    new_test_ext().execute_with(|| {
        let trigger_block = 100u64;
        let initial_deposit = 1000u128;

        assert_ok!(Fideicommis::create(
            RuntimeOrigin::signed(ALICE),
            b"Family Trust".to_vec(),
            DAVE,                    // fiduciary
            BOB,                     // greve
            CHARLIE,                 // appele
            trigger_block,
            None,                    // greve_claim_before
            initial_deposit,
            true,                    // revocable
        ));

        // Verify trust was created
        let trust = Fideicommis::fideicommis(0).expect("Trust should exist");
        assert_eq!(trust.id, 0);
        assert_eq!(trust.constituant, ALICE);
        assert_eq!(trust.fiduciary, DAVE);
        assert_eq!(trust.greve, BOB);
        assert_eq!(trust.appele, CHARLIE);
        assert_eq!(trust.status, FideicommisStatus::Active); // Active after deposit
        assert_eq!(trust.balance, initial_deposit);
        assert_eq!(trust.trigger_block, trigger_block);
        assert_eq!(trust.revocable, true);

        // Verify funds were reserved
        assert_eq!(Balances::reserved_balance(ALICE), initial_deposit);
        assert_eq!(Balances::free_balance(ALICE), 10_000 - initial_deposit);

        // Verify indexes updated
        assert!(Fideicommis::trusts_by_constituant(ALICE).contains(&0));
        assert!(Fideicommis::trusts_by_greve(BOB).contains(&0));
        assert!(Fideicommis::trusts_by_appele(CHARLIE).contains(&0));

        // Verify total locked
        assert_eq!(Fideicommis::total_locked(), initial_deposit);
        assert_eq!(Fideicommis::active_count(), 1);
    });
}

#[test]
fn test_create_trust_fails_same_beneficiary() {
    new_test_ext().execute_with(|| {
        assert_noop!(
            Fideicommis::create(
                RuntimeOrigin::signed(ALICE),
                b"Bad Trust".to_vec(),
                DAVE,
                BOB,
                BOB,  // Same as greve!
                100,
                None,
                1000,
                true,
            ),
            Error::<Test>::SameBeneficiary
        );
    });
}

#[test]
fn test_create_trust_fails_duration_too_short() {
    new_test_ext().execute_with(|| {
        assert_noop!(
            Fideicommis::create(
                RuntimeOrigin::signed(ALICE),
                b"Short Trust".to_vec(),
                DAVE,
                BOB,
                CHARLIE,
                5,  // Less than MinTrustDuration (10)
                None,
                1000,
                true,
            ),
            Error::<Test>::DurationTooShort
        );
    });
}

#[test]
fn test_create_trust_fails_deposit_too_low() {
    new_test_ext().execute_with(|| {
        assert_noop!(
            Fideicommis::create(
                RuntimeOrigin::signed(ALICE),
                b"Low Deposit Trust".to_vec(),
                DAVE,
                BOB,
                CHARLIE,
                100,
                None,
                50,  // Less than MinDeposit (100)
                true,
            ),
            Error::<Test>::DepositTooLow
        );
    });
}

// ==================== DEPOSIT TESTS ====================

#[test]
fn test_deposit_additional_funds() {
    new_test_ext().execute_with(|| {
        // Create trust
        assert_ok!(Fideicommis::create(
            RuntimeOrigin::signed(ALICE),
            b"Test Trust".to_vec(),
            DAVE, BOB, CHARLIE, 100, None, 1000, true,
        ));

        // Deposit more
        assert_ok!(Fideicommis::deposit(
            RuntimeOrigin::signed(ALICE),
            0,
            500,
        ));

        let trust = Fideicommis::fideicommis(0).unwrap();
        assert_eq!(trust.balance, 1500);
        assert_eq!(Balances::reserved_balance(ALICE), 1500);
    });
}

#[test]
fn test_deposit_fails_not_constituant() {
    new_test_ext().execute_with(|| {
        assert_ok!(Fideicommis::create(
            RuntimeOrigin::signed(ALICE),
            b"Test Trust".to_vec(),
            DAVE, BOB, CHARLIE, 100, None, 1000, true,
        ));

        // BOB tries to deposit (not constituant)
        assert_noop!(
            Fideicommis::deposit(RuntimeOrigin::signed(BOB), 0, 500),
            Error::<Test>::NotAuthorized
        );
    });
}

// ==================== GREVE CLAIM TESTS ====================

#[test]
fn test_greve_claim_before_trigger() {
    new_test_ext().execute_with(|| {
        // Create trust (trigger at block 100)
        assert_ok!(Fideicommis::create(
            RuntimeOrigin::signed(ALICE),
            b"Test Trust".to_vec(),
            DAVE, BOB, CHARLIE, 100, None, 1000, true,
        ));

        let bob_initial = Balances::free_balance(BOB);

        // Grevé claims half
        assert_ok!(Fideicommis::claim_as_greve(
            RuntimeOrigin::signed(BOB),
            0,
            500,
        ));

        // Verify balances
        assert_eq!(Balances::free_balance(BOB), bob_initial + 500);

        let trust = Fideicommis::fideicommis(0).unwrap();
        assert_eq!(trust.greve_claimed, 500);
        assert_eq!(Fideicommis::total_locked(), 500); // 1000 - 500 claimed
    });
}

#[test]
fn test_greve_cannot_claim_after_trigger() {
    new_test_ext().execute_with(|| {
        // Create trust (trigger at block 50)
        assert_ok!(Fideicommis::create(
            RuntimeOrigin::signed(ALICE),
            b"Test Trust".to_vec(),
            DAVE, BOB, CHARLIE, 50, None, 1000, true,
        ));

        // Advance past trigger block
        run_to_block(51);

        // Grevé tries to claim - trust status changes after trigger, so InvalidStatus is returned
        assert_noop!(
            Fideicommis::claim_as_greve(RuntimeOrigin::signed(BOB), 0, 500),
            Error::<Test>::InvalidStatus
        );
    });
}

#[test]
fn test_greve_cannot_claim_more_than_available() {
    new_test_ext().execute_with(|| {
        assert_ok!(Fideicommis::create(
            RuntimeOrigin::signed(ALICE),
            b"Test Trust".to_vec(),
            DAVE, BOB, CHARLIE, 100, None, 1000, true,
        ));

        assert_noop!(
            Fideicommis::claim_as_greve(RuntimeOrigin::signed(BOB), 0, 2000),
            Error::<Test>::InsufficientTrustBalance
        );
    });
}

// ==================== APPELE CLAIM TESTS ====================

#[test]
fn test_appele_claim_after_trigger() {
    new_test_ext().execute_with(|| {
        // Create trust (trigger at block 50)
        assert_ok!(Fideicommis::create(
            RuntimeOrigin::signed(ALICE),
            b"Test Trust".to_vec(),
            DAVE, BOB, CHARLIE, 50, None, 1000, true,
        ));

        let charlie_initial = Balances::free_balance(CHARLIE);

        // Advance to trigger
        run_to_block(50);

        // Verify trust was triggered
        let trust = Fideicommis::fideicommis(0).unwrap();
        assert_eq!(trust.status, FideicommisStatus::Triggered);

        // Appelé claims
        assert_ok!(Fideicommis::claim_as_appele(
            RuntimeOrigin::signed(CHARLIE),
            0,
        ));

        // Verify balances
        assert_eq!(Balances::free_balance(CHARLIE), charlie_initial + 1000);

        // Verify trust completed
        let trust = Fideicommis::fideicommis(0).unwrap();
        assert_eq!(trust.status, FideicommisStatus::Completed);
        assert_eq!(trust.appele_claimed, 1000);
    });
}

#[test]
fn test_appele_cannot_claim_before_trigger() {
    new_test_ext().execute_with(|| {
        assert_ok!(Fideicommis::create(
            RuntimeOrigin::signed(ALICE),
            b"Test Trust".to_vec(),
            DAVE, BOB, CHARLIE, 100, None, 1000, true,
        ));

        // Try to claim before trigger
        assert_noop!(
            Fideicommis::claim_as_appele(RuntimeOrigin::signed(CHARLIE), 0),
            Error::<Test>::TriggerNotReached
        );
    });
}

#[test]
fn test_appele_gets_remainder_after_greve_claims() {
    new_test_ext().execute_with(|| {
        assert_ok!(Fideicommis::create(
            RuntimeOrigin::signed(ALICE),
            b"Test Trust".to_vec(),
            DAVE, BOB, CHARLIE, 50, None, 1000, true,
        ));

        // Grevé claims 300 before trigger
        assert_ok!(Fideicommis::claim_as_greve(RuntimeOrigin::signed(BOB), 0, 300));

        let charlie_initial = Balances::free_balance(CHARLIE);

        // Advance to trigger
        run_to_block(50);

        // Appelé claims remainder
        assert_ok!(Fideicommis::claim_as_appele(RuntimeOrigin::signed(CHARLIE), 0));

        // Appelé should get 700 (1000 - 300)
        assert_eq!(Balances::free_balance(CHARLIE), charlie_initial + 700);

        let trust = Fideicommis::fideicommis(0).unwrap();
        assert_eq!(trust.greve_claimed, 300);
        assert_eq!(trust.appele_claimed, 700);
        assert_eq!(trust.status, FideicommisStatus::Completed);
    });
}

// ==================== CANCEL TESTS ====================

#[test]
fn test_cancel_revocable_trust() {
    new_test_ext().execute_with(|| {
        let initial_balance = Balances::free_balance(ALICE);

        assert_ok!(Fideicommis::create(
            RuntimeOrigin::signed(ALICE),
            b"Revocable Trust".to_vec(),
            DAVE, BOB, CHARLIE, 100, None, 1000, true, // revocable
        ));

        assert_eq!(Balances::free_balance(ALICE), initial_balance - 1000);

        // Cancel
        assert_ok!(Fideicommis::cancel(RuntimeOrigin::signed(ALICE), 0));

        // Verify funds returned
        assert_eq!(Balances::free_balance(ALICE), initial_balance);

        let trust = Fideicommis::fideicommis(0).unwrap();
        assert_eq!(trust.status, FideicommisStatus::Cancelled);
    });
}

#[test]
fn test_cancel_fails_irrevocable_trust() {
    new_test_ext().execute_with(|| {
        assert_ok!(Fideicommis::create(
            RuntimeOrigin::signed(ALICE),
            b"Irrevocable Trust".to_vec(),
            DAVE, BOB, CHARLIE, 100, None, 1000, false, // NOT revocable
        ));

        assert_noop!(
            Fideicommis::cancel(RuntimeOrigin::signed(ALICE), 0),
            Error::<Test>::TrustIrrevocable
        );
    });
}

#[test]
fn test_cancel_fails_after_trigger() {
    new_test_ext().execute_with(|| {
        assert_ok!(Fideicommis::create(
            RuntimeOrigin::signed(ALICE),
            b"Test Trust".to_vec(),
            DAVE, BOB, CHARLIE, 50, None, 1000, true,
        ));

        // Advance past trigger
        run_to_block(51);

        assert_noop!(
            Fideicommis::cancel(RuntimeOrigin::signed(ALICE), 0),
            Error::<Test>::CannotCancelTriggered
        );
    });
}

// ==================== FIDUCIARY TESTS ====================

#[test]
fn test_change_fiduciary() {
    new_test_ext().execute_with(|| {
        assert_ok!(Fideicommis::create(
            RuntimeOrigin::signed(ALICE),
            b"Test Trust".to_vec(),
            DAVE, BOB, CHARLIE, 100, None, 1000, true,
        ));

        // Change fiduciary
        assert_ok!(Fideicommis::change_fiduciary(
            RuntimeOrigin::signed(ALICE),
            0,
            BOB, // New fiduciary
        ));

        let trust = Fideicommis::fideicommis(0).unwrap();
        assert_eq!(trust.fiduciary, BOB);
    });
}

#[test]
fn test_change_fiduciary_fails_not_constituant() {
    new_test_ext().execute_with(|| {
        assert_ok!(Fideicommis::create(
            RuntimeOrigin::signed(ALICE),
            b"Test Trust".to_vec(),
            DAVE, BOB, CHARLIE, 100, None, 1000, true,
        ));

        // BOB tries to change fiduciary
        assert_noop!(
            Fideicommis::change_fiduciary(RuntimeOrigin::signed(BOB), 0, CHARLIE),
            Error::<Test>::NotAuthorized
        );
    });
}

// ==================== HELPER FUNCTION TESTS ====================

#[test]
fn test_query_helpers() {
    new_test_ext().execute_with(|| {
        assert_ok!(Fideicommis::create(
            RuntimeOrigin::signed(ALICE),
            b"Test Trust".to_vec(),
            DAVE, BOB, CHARLIE, 100, None, 1000, true,
        ));

        // Test get_trusts_for_account
        let alice_trusts = Fideicommis::get_trusts_for_account(&ALICE);
        assert!(alice_trusts.contains(&0));

        let bob_trusts = Fideicommis::get_trusts_for_account(&BOB);
        assert!(bob_trusts.contains(&0));

        // Test greve_claimable
        assert_eq!(Fideicommis::greve_claimable(0), 1000);

        // Test appele_claimable (should be 0 before trigger)
        assert_eq!(Fideicommis::appele_claimable(0), 0);

        // Advance past trigger
        run_to_block(100);

        // Now appelé can claim
        assert_eq!(Fideicommis::appele_claimable(0), 1000);
        assert_eq!(Fideicommis::greve_claimable(0), 0); // Grevé can no longer claim
    });
}
