//! Mock runtime for Academic Vouch pallet tests

use crate as pallet_academic_vouch;
use frame_support::{
    derive_impl,
    parameter_types,
};
use sp_runtime::BuildStorage;

type Block = frame_system::mocking::MockBlock<Test>;

// Test accounts
pub const ALICE: u64 = 1;
pub const BOB: u64 = 2;
pub const CHARLIE: u64 = 3;
pub const DAVE: u64 = 4;
pub const EVE: u64 = 5;

// Configure mock runtime
frame_support::construct_runtime!(
    pub enum Test {
        System: frame_system,
        AcademicVouch: pallet_academic_vouch,
    }
);

#[derive_impl(frame_system::config_preludes::TestDefaultConfig)]
impl frame_system::Config for Test {
    type Block = Block;
}

parameter_types! {
    pub const RequiredVouches: u32 = 2;
    pub const AcademicVotingPeriod: u64 = 10;
    pub const MinimumAcademicApprovals: u32 = 1;
}

impl pallet_academic_vouch::Config for Test {
    type RuntimeEvent = RuntimeEvent;
    type RequiredVouches = RequiredVouches;
    type AcademicVotingPeriod = AcademicVotingPeriod;
    type MinimumAcademicApprovals = MinimumAcademicApprovals;
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

// Helper to register an academic directly (bypassing proposal for simpler tests)
pub fn register_academic_directly(account: u64, institution: &[u8]) {
    use crate::pallet::{Academic, Academics};
    use frame_support::BoundedVec;

    let bounded_institution: BoundedVec<u8, frame_support::traits::ConstU32<256>> =
        institution.to_vec().try_into().unwrap();

    let academic = Academic::<Test> {
        account,
        institution: bounded_institution,
        credential_hash: [0u8; 32],
        registered_at: 1,
        vouches_given: 0,
        active: true,
    };

    Academics::<Test>::insert(account, academic);
}

#[test]
fn mock_runtime_initializes() {
    new_test_ext().execute_with(|| {
        assert_eq!(System::block_number(), 1);
    });
}
