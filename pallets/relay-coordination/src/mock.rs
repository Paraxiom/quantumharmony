//! Mock runtime for pallet-relay-coordination tests

use crate as pallet_relay_coordination;
use frame_support::{
    derive_impl, parameter_types,
    traits::{ConstU16, ConstU32, ConstU64, ValidatorSet},
};
use sp_runtime::{
    testing::H256,
    traits::{BlakeTwo256, IdentityLookup},
    BuildStorage, Perbill,
};

type Block = frame_system::mocking::MockBlock<Test>;

// Configure a mock runtime to test the pallet.
frame_support::construct_runtime!(
    pub enum Test
    {
        System: frame_system,
        Balances: pallet_balances,
        RelayCoordination: pallet_relay_coordination,
    }
);

#[derive_impl(frame_system::config_preludes::TestDefaultConfig)]
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
    type BlockHashCount = ConstU64<250>;
    type Version = ();
    type PalletInfo = PalletInfo;
    type AccountData = pallet_balances::AccountData<u128>;
    type OnNewAccount = ();
    type OnKilledAccount = ();
    type SystemWeightInfo = ();
    type SS58Prefix = ConstU16<42>;
    type OnSetCode = ();
    type MaxConsumers = ConstU32<16>;
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
    type MaxFreezes = ();
    type RuntimeHoldReason = ();
    type RuntimeFreezeReason = ();
    type DoneSlashHandler = ();
}

parameter_types! {
    pub const MinRelayStake: u128 = 1000;
    pub const RelayElectionInterval: u64 = 100;
    pub const MaxRelayCandidates: u32 = 100;
    pub const MaxElectedRelaysPerRegion: u32 = 10;
    pub const MinUptimePercentage: u8 = 80;
    pub const SlashPercentage: Perbill = Perbill::from_percent(10);
}

/// Mock ValidatorSet implementation
pub struct MockValidatorSet;

impl ValidatorSet<u64> for MockValidatorSet {
    type ValidatorId = u64;
    type ValidatorIdOf = sp_runtime::traits::ConvertInto;

    fn session_index() -> u32 {
        0
    }

    fn validators() -> Vec<Self::ValidatorId> {
        vec![1, 2, 3]
    }
}

impl pallet_relay_coordination::Config for Test {
    type RuntimeEvent = RuntimeEvent;
    type Currency = Balances;
    type MinRelayStake = MinRelayStake;
    type RelayElectionInterval = RelayElectionInterval;
    type MaxRelayCandidates = MaxRelayCandidates;
    type MaxElectedRelaysPerRegion = MaxElectedRelaysPerRegion;
    type MinUptimePercentage = MinUptimePercentage;
    type SlashPercentage = SlashPercentage;
    type ValidatorSet = MockValidatorSet;
    type WeightInfo = ();
}

// Implement unsigned transaction support for off-chain workers
impl frame_system::offchain::CreateTransactionBase<pallet_relay_coordination::Call<Test>> for Test {
    type Extrinsic = sp_runtime::testing::TestXt<RuntimeCall, ()>;
    type RuntimeCall = RuntimeCall;
}

impl frame_system::offchain::CreateBare<pallet_relay_coordination::Call<Test>> for Test {
    fn create_bare(call: RuntimeCall) -> sp_runtime::testing::TestXt<RuntimeCall, ()> {
        sp_runtime::testing::TestXt::new_bare(call)
    }
}

// Build genesis storage according to the mock runtime.
pub fn new_test_ext() -> sp_io::TestExternalities {
    let mut storage = frame_system::GenesisConfig::<Test>::default()
        .build_storage()
        .unwrap();

    pallet_balances::GenesisConfig::<Test> {
        balances: vec![
            (1, 10000),
            (2, 10000),
            (3, 10000),
        ],
        ..Default::default()
    }
    .assimilate_storage(&mut storage)
    .unwrap();

    storage.into()
}
