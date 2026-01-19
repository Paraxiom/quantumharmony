//! Unit tests for Oracle pallet

use crate::{self as pallet_oracle};
use frame_support::{
    assert_ok,
    traits::{ConstU16, ConstU32, ConstU64, ConstU128},
    parameter_types,
};
use sp_core::H256;
use sp_runtime::{
    traits::{BlakeTwo256, IdentityLookup},
    BuildStorage,
};

type Block = frame_system::mocking::MockBlock<Test>;

frame_support::construct_runtime!(
    pub enum Test {
        System: frame_system,
        Balances: pallet_balances,
        Oracle: pallet_oracle,
    }
);

parameter_types! {
    pub const BlockHashCount: u64 = 250;
}

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
    type BlockHashCount = BlockHashCount;
    type Version = ();
    type PalletInfo = PalletInfo;
    type AccountData = pallet_balances::AccountData<u128>;
    type OnNewAccount = ();
    type OnKilledAccount = ();
    type SystemWeightInfo = ();
    type SS58Prefix = ConstU16<42>;
    type OnSetCode = ();
    type MaxConsumers = ConstU32<16>;
    type RuntimeTask = ();
    type SingleBlockMigrations = ();
    type MultiBlockMigrator = ();
    type PreInherents = ();
    type PostInherents = ();
    type PostTransactions = ();
    type ExtensionsWeightInfo = ();
}

impl pallet_balances::Config for Test {
    type MaxLocks = ConstU32<50>;
    type MaxReserves = ();
    type ReserveIdentifier = [u8; 8];
    type Balance = u128;
    type RuntimeEvent = RuntimeEvent;
    type DustRemoval = ();
    type ExistentialDeposit = ConstU128<1>;
    type AccountStore = System;
    type WeightInfo = ();
    type FreezeIdentifier = ();
    type MaxFreezes = ();
    type RuntimeHoldReason = ();
    type RuntimeFreezeReason = ();
    type DoneSlashHandler = ();
}

parameter_types! {
    pub const MinReporterStake: u128 = 100;
    pub const MaxPriceDeviation: u32 = 50_000; // 5%
    pub const AggregationPeriod: u64 = 10;
    pub const SlashPercent: u32 = 100_000; // 10%
}

impl pallet_oracle::Config for Test {
    type RuntimeEvent = RuntimeEvent;
    type Currency = Balances;
    type MinReporterStake = MinReporterStake;
    type MaxPriceDeviation = MaxPriceDeviation;
    type AggregationPeriod = AggregationPeriod;
    type SlashPercent = SlashPercent;
    type ForceOrigin = frame_system::EnsureRoot<u64>;
    type AdminOrigin = frame_system::EnsureRoot<u64>;
}

fn new_test_ext() -> sp_io::TestExternalities {
    let mut t = frame_system::GenesisConfig::<Test>::default()
        .build_storage()
        .unwrap();

    pallet_balances::GenesisConfig::<Test> {
        balances: vec![(1, 10000), (2, 10000), (3, 10000)],
        dev_accounts: None,
    }
    .assimilate_storage(&mut t)
    .unwrap();

    t.into()
}

#[test]
fn oracle_pallet_compiles() {
    new_test_ext().execute_with(|| {
        // Basic compilation test
        assert_eq!(System::block_number(), 0);
    });
}

// ==================== REPORTER APPROVAL TESTS ====================

#[test]
fn propose_reporter_works() {
    new_test_ext().execute_with(|| {
        // Account 1 proposes account 2 as a reporter
        assert_ok!(Oracle::propose_reporter(
            RuntimeOrigin::signed(1),
            2, // candidate
            100, // stake (min required)
            vec![0, 1] // CAD/USD and QMHY/USD feeds
        ));

        // Check proposal was created
        let proposal = Oracle::reporter_proposals(0).expect("Proposal should exist");
        assert_eq!(proposal.candidate, 2);
        assert_eq!(proposal.stake, 100);
        assert_eq!(proposal.yes_votes, 0);
        assert_eq!(proposal.no_votes, 0);
        assert!(!proposal.finalized);

        // Check stake was reserved from candidate
        assert_eq!(Balances::reserved_balance(2), 100);
    });
}

#[test]
fn propose_reporter_fails_insufficient_stake() {
    new_test_ext().execute_with(|| {
        // Try to propose with less than minimum stake
        assert!(Oracle::propose_reporter(
            RuntimeOrigin::signed(1),
            2,
            50, // less than MinReporterStake (100)
            vec![0]
        ).is_err());
    });
}

#[test]
fn vote_on_reporter_requires_active_reporter() {
    new_test_ext().execute_with(|| {
        // First create a proposal
        assert_ok!(Oracle::propose_reporter(
            RuntimeOrigin::signed(1),
            2,
            100,
            vec![0]
        ));

        // Account 3 is not a reporter, should fail to vote
        assert!(Oracle::vote_on_reporter(
            RuntimeOrigin::signed(3),
            0, // proposal_id
            true
        ).is_err());
    });
}

#[test]
fn vote_and_finalize_reporter_proposal() {
    new_test_ext().execute_with(|| {
        // First, register account 1 as a reporter (using old direct registration for setup)
        assert_ok!(Oracle::register_reporter(
            RuntimeOrigin::signed(1),
            100,
            vec![0]
        ));

        // Register account 3 as a reporter too
        assert_ok!(Oracle::register_reporter(
            RuntimeOrigin::signed(3),
            100,
            vec![0]
        ));

        // Now propose account 2 as a reporter
        assert_ok!(Oracle::propose_reporter(
            RuntimeOrigin::signed(1),
            2,
            100,
            vec![0, 1]
        ));

        // Account 1 (active reporter) votes yes
        assert_ok!(Oracle::vote_on_reporter(
            RuntimeOrigin::signed(1),
            0,
            true
        ));

        // Account 3 (active reporter) votes yes
        assert_ok!(Oracle::vote_on_reporter(
            RuntimeOrigin::signed(3),
            0,
            true
        ));

        // Check votes recorded
        let proposal = Oracle::reporter_proposals(0).unwrap();
        assert_eq!(proposal.yes_votes, 2);
        assert_eq!(proposal.no_votes, 0);

        // Advance past voting period
        System::set_block_number(101);

        // Finalize the proposal
        assert_ok!(Oracle::finalize_reporter_proposal(
            RuntimeOrigin::signed(1),
            0
        ));

        // Check proposal finalized and approved
        let proposal = Oracle::reporter_proposals(0).unwrap();
        assert!(proposal.finalized);
        assert!(proposal.approved);

        // Check account 2 is now a registered reporter
        let reporter = Oracle::reporters(2).expect("Reporter should exist");
        assert_eq!(reporter.account, 2);
        assert_eq!(reporter.reputation, 50); // Initial reputation
    });
}

#[test]
fn rejected_proposal_returns_stake() {
    new_test_ext().execute_with(|| {
        // Setup: register account 1 and 3 as reporters
        assert_ok!(Oracle::register_reporter(RuntimeOrigin::signed(1), 100, vec![0]));
        assert_ok!(Oracle::register_reporter(RuntimeOrigin::signed(3), 100, vec![0]));

        // Propose account 2
        assert_ok!(Oracle::propose_reporter(RuntimeOrigin::signed(1), 2, 100, vec![0]));

        // Check stake reserved
        assert_eq!(Balances::reserved_balance(2), 100);

        // Vote NO
        assert_ok!(Oracle::vote_on_reporter(RuntimeOrigin::signed(1), 0, false));
        assert_ok!(Oracle::vote_on_reporter(RuntimeOrigin::signed(3), 0, false));

        // Advance and finalize
        System::set_block_number(101);
        assert_ok!(Oracle::finalize_reporter_proposal(RuntimeOrigin::signed(1), 0));

        // Check proposal rejected
        let proposal = Oracle::reporter_proposals(0).unwrap();
        assert!(proposal.finalized);
        assert!(!proposal.approved);

        // Check stake returned to candidate
        assert_eq!(Balances::reserved_balance(2), 0);
        assert_eq!(Balances::free_balance(2), 10000); // Original balance
    });
}

#[test]
fn cannot_vote_twice() {
    new_test_ext().execute_with(|| {
        // Setup
        assert_ok!(Oracle::register_reporter(RuntimeOrigin::signed(1), 100, vec![0]));
        assert_ok!(Oracle::propose_reporter(RuntimeOrigin::signed(1), 2, 100, vec![0]));

        // First vote succeeds
        assert_ok!(Oracle::vote_on_reporter(RuntimeOrigin::signed(1), 0, true));

        // Second vote fails
        assert!(Oracle::vote_on_reporter(RuntimeOrigin::signed(1), 0, true).is_err());
    });
}

#[test]
fn cannot_finalize_before_voting_period_ends() {
    new_test_ext().execute_with(|| {
        assert_ok!(Oracle::register_reporter(RuntimeOrigin::signed(1), 100, vec![0]));
        assert_ok!(Oracle::propose_reporter(RuntimeOrigin::signed(1), 2, 100, vec![0]));

        // Try to finalize immediately (voting period is 100 blocks)
        assert!(Oracle::finalize_reporter_proposal(RuntimeOrigin::signed(1), 0).is_err());
    });
}
