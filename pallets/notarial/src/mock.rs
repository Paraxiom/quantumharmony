//! Mock runtime for Notarial pallet tests

use crate as pallet_notarial;
use frame_support::{
    derive_impl,
    parameter_types,
    traits::ConstU32,
};
use sp_runtime::BuildStorage;

type Block = frame_system::mocking::MockBlock<Test>;

// Test accounts
pub const ALICE: u64 = 1;
pub const BOB: u64 = 2;
pub const CHARLIE: u64 = 3;

// Configure mock runtime
frame_support::construct_runtime!(
    pub enum Test {
        System: frame_system,
        Notarial: pallet_notarial,
    }
);

#[derive_impl(frame_system::config_preludes::TestDefaultConfig)]
impl frame_system::Config for Test {
    type Block = Block;
}

parameter_types! {
    pub const MinWitnesses: u32 = 2;
    pub const DefaultValidityPeriod: u64 = 0; // Permanent by default
}

impl pallet_notarial::Config for Test {
    type RuntimeEvent = RuntimeEvent;
    type MinWitnesses = MinWitnesses;
    type DefaultValidityPeriod = DefaultValidityPeriod;
}

// Build test externalities
pub fn new_test_ext() -> sp_io::TestExternalities {
    let t = frame_system::GenesisConfig::<Test>::default()
        .build_storage()
        .unwrap();

    let mut ext = sp_io::TestExternalities::new(t);
    ext.execute_with(|| System::set_block_number(1));
    ext
}
