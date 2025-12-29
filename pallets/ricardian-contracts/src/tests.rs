//! Unit tests for Ricardian Contracts pallet
//!
//! Tests cover:
//! 1. Contract creation (all types)
//! 2. Party management (add, validate)
//! 3. Multi-party signing workflow
//! 4. Amendment proposal and approval
//! 5. Contract lifecycle (draft -> active -> executed/terminated)
//! 6. Error cases and edge conditions
//! 7. Expiration handling

use crate::{self as pallet_ricardian_contracts, *};
use frame_support::{
    assert_noop, assert_ok,
    traits::{ConstU16, ConstU32, ConstU64},
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
        RicardianContracts: pallet_ricardian_contracts,
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
    type AccountData = ();
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

impl Config for Test {
    type RuntimeEvent = RuntimeEvent;
    type MinContractDuration = ConstU64<10>;
}

// Helper function to create test environment
fn new_test_ext() -> sp_io::TestExternalities {
    let t = frame_system::GenesisConfig::<Test>::default()
        .build_storage()
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

// Test accounts
const ALICE: u64 = 1;
const BOB: u64 = 2;
const CHARLIE: u64 = 3;
const DAVE: u64 = 4;

// Test document hash
fn test_document_hash() -> [u8; 32] {
    [0xAB; 32]
}

fn test_term_hash() -> [u8; 32] {
    [0xCD; 32]
}

fn test_amendment_hash() -> [u8; 32] {
    [0xEF; 32]
}

// ==================== CONTRACT CREATION TESTS ====================

#[test]
fn test_create_contract_success() {
    new_test_ext().execute_with(|| {
        assert_ok!(RicardianContracts::create_contract(
            RuntimeOrigin::signed(ALICE),
            b"Test Partnership Agreement".to_vec(),
            1, // Partnership
            test_document_hash(),
            Some(100), // expires at block 100
            None,
        ));

        // Verify contract was created
        let contract = RicardianContracts::contracts(0).expect("Contract should exist");
        assert_eq!(contract.id, 0);
        assert_eq!(contract.creator, ALICE);
        assert_eq!(contract.contract_type, ContractType::Partnership);
        assert_eq!(contract.status, ContractStatus::Draft);
        assert_eq!(contract.party_count, 0);
        assert_eq!(contract.signatures_collected, 0);

        // Verify next contract ID incremented
        assert_eq!(RicardianContracts::next_contract_id(), 1);
    });
}

#[test]
fn test_create_contract_all_types() {
    new_test_ext().execute_with(|| {
        let types = vec![
            (0u8, ContractType::AcademicProgram),
            (1, ContractType::Partnership),
            (2, ContractType::Service),
            (3, ContractType::NDA),
            (4, ContractType::Employment),
            (5, ContractType::License),
            (6, ContractType::Custom),
        ];

        for (type_id, expected_type) in types {
            assert_ok!(RicardianContracts::create_contract(
                RuntimeOrigin::signed(ALICE),
                format!("Contract Type {}", type_id).into_bytes(),
                type_id,
                test_document_hash(),
                Some(100),
                None,
            ));

            let contract_id = RicardianContracts::next_contract_id() - 1;
            let contract = RicardianContracts::contracts(contract_id).unwrap();
            assert_eq!(contract.contract_type, expected_type);
        }
    });
}

#[test]
fn test_create_contract_with_academic_program() {
    new_test_ext().execute_with(|| {
        assert_ok!(RicardianContracts::create_contract(
            RuntimeOrigin::signed(ALICE),
            b"PhD Agreement".to_vec(),
            0, // AcademicProgram
            test_document_hash(),
            Some(100),
            Some(42), // academic_program_id
        ));

        let contract = RicardianContracts::contracts(0).unwrap();
        assert_eq!(contract.academic_program_id, Some(42));
    });
}

#[test]
fn test_create_contract_title_too_long() {
    new_test_ext().execute_with(|| {
        let long_title = vec![b'X'; 200]; // Exceeds MAX_TITLE_LENGTH (128)

        assert_noop!(
            RicardianContracts::create_contract(
                RuntimeOrigin::signed(ALICE),
                long_title,
                1,
                test_document_hash(),
                Some(100),
                None,
            ),
            Error::<Test>::TitleTooLong
        );
    });
}

#[test]
fn test_create_contract_expiration_too_soon() {
    new_test_ext().execute_with(|| {
        // MinContractDuration is 10, current block is 1
        // So expires_at must be >= 11
        assert_noop!(
            RicardianContracts::create_contract(
                RuntimeOrigin::signed(ALICE),
                b"Short Contract".to_vec(),
                1,
                test_document_hash(),
                Some(5), // Too soon
                None,
            ),
            Error::<Test>::ExpirationTooSoon
        );
    });
}

#[test]
fn test_create_contract_no_expiration() {
    new_test_ext().execute_with(|| {
        assert_ok!(RicardianContracts::create_contract(
            RuntimeOrigin::signed(ALICE),
            b"Perpetual Contract".to_vec(),
            1,
            test_document_hash(),
            None, // No expiration
            None,
        ));

        let contract = RicardianContracts::contracts(0).unwrap();
        assert_eq!(contract.expires_at, None);
    });
}

// ==================== PARTY MANAGEMENT TESTS ====================

#[test]
fn test_add_party_success() {
    new_test_ext().execute_with(|| {
        // Create contract
        assert_ok!(RicardianContracts::create_contract(
            RuntimeOrigin::signed(ALICE),
            b"Partnership".to_vec(),
            1,
            test_document_hash(),
            Some(100),
            None,
        ));

        // Add party
        assert_ok!(RicardianContracts::add_party(
            RuntimeOrigin::signed(ALICE),
            0,
            BOB,
            b"Partner".to_vec(),
        ));

        // Verify party was added
        let parties = RicardianContracts::parties(0);
        assert_eq!(parties.len(), 1);
        assert_eq!(parties[0].account, BOB);
        assert!(!parties[0].signed);

        // Verify contract party_count updated
        let contract = RicardianContracts::contracts(0).unwrap();
        assert_eq!(contract.party_count, 1);

        // Verify party's contract list updated
        let bob_contracts = RicardianContracts::contracts_by_party(&BOB);
        assert!(bob_contracts.contains(&0));
    });
}

#[test]
fn test_add_multiple_parties() {
    new_test_ext().execute_with(|| {
        assert_ok!(RicardianContracts::create_contract(
            RuntimeOrigin::signed(ALICE),
            b"Multi-party Agreement".to_vec(),
            1,
            test_document_hash(),
            Some(100),
            None,
        ));

        // Add multiple parties
        assert_ok!(RicardianContracts::add_party(
            RuntimeOrigin::signed(ALICE),
            0,
            BOB,
            b"Party A".to_vec(),
        ));
        assert_ok!(RicardianContracts::add_party(
            RuntimeOrigin::signed(ALICE),
            0,
            CHARLIE,
            b"Party B".to_vec(),
        ));
        assert_ok!(RicardianContracts::add_party(
            RuntimeOrigin::signed(ALICE),
            0,
            DAVE,
            b"Party C".to_vec(),
        ));

        let parties = RicardianContracts::parties(0);
        assert_eq!(parties.len(), 3);

        let contract = RicardianContracts::contracts(0).unwrap();
        assert_eq!(contract.party_count, 3);
    });
}

#[test]
fn test_add_party_not_creator() {
    new_test_ext().execute_with(|| {
        assert_ok!(RicardianContracts::create_contract(
            RuntimeOrigin::signed(ALICE),
            b"Partnership".to_vec(),
            1,
            test_document_hash(),
            Some(100),
            None,
        ));

        // BOB tries to add party (not authorized)
        assert_noop!(
            RicardianContracts::add_party(
                RuntimeOrigin::signed(BOB),
                0,
                CHARLIE,
                b"Unauthorized".to_vec(),
            ),
            Error::<Test>::NotAuthorized
        );
    });
}

#[test]
fn test_add_party_role_too_long() {
    new_test_ext().execute_with(|| {
        assert_ok!(RicardianContracts::create_contract(
            RuntimeOrigin::signed(ALICE),
            b"Partnership".to_vec(),
            1,
            test_document_hash(),
            Some(100),
            None,
        ));

        let long_role = vec![b'R'; 100]; // Exceeds 64 bytes

        assert_noop!(
            RicardianContracts::add_party(
                RuntimeOrigin::signed(ALICE),
                0,
                BOB,
                long_role,
            ),
            Error::<Test>::RoleTooLong
        );
    });
}

#[test]
fn test_add_party_contract_not_found() {
    new_test_ext().execute_with(|| {
        assert_noop!(
            RicardianContracts::add_party(
                RuntimeOrigin::signed(ALICE),
                999, // Non-existent
                BOB,
                b"Role".to_vec(),
            ),
            Error::<Test>::ContractNotFound
        );
    });
}

// ==================== TERMS TESTS ====================

#[test]
fn test_add_term_success() {
    new_test_ext().execute_with(|| {
        assert_ok!(RicardianContracts::create_contract(
            RuntimeOrigin::signed(ALICE),
            b"Contract with Terms".to_vec(),
            2, // Service
            test_document_hash(),
            Some(100),
            None,
        ));

        assert_ok!(RicardianContracts::add_term(
            RuntimeOrigin::signed(ALICE),
            0,
            test_term_hash(),
            true, // mandatory
        ));

        let terms = RicardianContracts::terms(0);
        assert_eq!(terms.len(), 1);
        assert_eq!(terms[0].number, 1);
        assert_eq!(terms[0].content_hash, test_term_hash());
        assert!(terms[0].mandatory);

        let contract = RicardianContracts::contracts(0).unwrap();
        assert_eq!(contract.term_count, 1);
    });
}

#[test]
fn test_add_multiple_terms() {
    new_test_ext().execute_with(|| {
        assert_ok!(RicardianContracts::create_contract(
            RuntimeOrigin::signed(ALICE),
            b"Multi-term Contract".to_vec(),
            2,
            test_document_hash(),
            Some(100),
            None,
        ));

        for i in 0..5 {
            let mut hash = test_term_hash();
            hash[0] = i as u8;
            assert_ok!(RicardianContracts::add_term(
                RuntimeOrigin::signed(ALICE),
                0,
                hash,
                i % 2 == 0, // alternate mandatory
            ));
        }

        let terms = RicardianContracts::terms(0);
        assert_eq!(terms.len(), 5);

        let contract = RicardianContracts::contracts(0).unwrap();
        assert_eq!(contract.term_count, 5);
    });
}

// ==================== SIGNING WORKFLOW TESTS ====================

#[test]
fn test_sign_contract_success() {
    new_test_ext().execute_with(|| {
        // Create contract and add party
        assert_ok!(RicardianContracts::create_contract(
            RuntimeOrigin::signed(ALICE),
            b"NDA".to_vec(),
            3,
            test_document_hash(),
            Some(100),
            None,
        ));
        assert_ok!(RicardianContracts::add_party(
            RuntimeOrigin::signed(ALICE),
            0,
            BOB,
            b"Signatory".to_vec(),
        ));

        // Sign
        assert_ok!(RicardianContracts::sign_contract(
            RuntimeOrigin::signed(BOB),
            0,
        ));

        // Verify signature recorded
        let parties = RicardianContracts::parties(0);
        assert!(parties[0].signed);
        assert!(parties[0].signed_at.is_some());

        let contract = RicardianContracts::contracts(0).unwrap();
        assert_eq!(contract.signatures_collected, 1);
    });
}

#[test]
fn test_sign_contract_activates_when_all_signed() {
    new_test_ext().execute_with(|| {
        assert_ok!(RicardianContracts::create_contract(
            RuntimeOrigin::signed(ALICE),
            b"Partnership".to_vec(),
            1,
            test_document_hash(),
            Some(100),
            None,
        ));
        assert_ok!(RicardianContracts::add_party(
            RuntimeOrigin::signed(ALICE),
            0,
            BOB,
            b"Partner 1".to_vec(),
        ));
        assert_ok!(RicardianContracts::add_party(
            RuntimeOrigin::signed(ALICE),
            0,
            CHARLIE,
            b"Partner 2".to_vec(),
        ));

        // First signature
        assert_ok!(RicardianContracts::sign_contract(
            RuntimeOrigin::signed(BOB),
            0,
        ));
        let contract = RicardianContracts::contracts(0).unwrap();
        assert_eq!(contract.status, ContractStatus::Draft);

        // Second signature - should activate
        assert_ok!(RicardianContracts::sign_contract(
            RuntimeOrigin::signed(CHARLIE),
            0,
        ));
        let contract = RicardianContracts::contracts(0).unwrap();
        assert_eq!(contract.status, ContractStatus::Active);
    });
}

#[test]
fn test_sign_contract_not_a_party() {
    new_test_ext().execute_with(|| {
        assert_ok!(RicardianContracts::create_contract(
            RuntimeOrigin::signed(ALICE),
            b"NDA".to_vec(),
            3,
            test_document_hash(),
            Some(100),
            None,
        ));
        assert_ok!(RicardianContracts::add_party(
            RuntimeOrigin::signed(ALICE),
            0,
            BOB,
            b"Signatory".to_vec(),
        ));

        // CHARLIE is not a party
        assert_noop!(
            RicardianContracts::sign_contract(RuntimeOrigin::signed(CHARLIE), 0),
            Error::<Test>::NotAParty
        );
    });
}

#[test]
fn test_sign_contract_already_signed() {
    new_test_ext().execute_with(|| {
        assert_ok!(RicardianContracts::create_contract(
            RuntimeOrigin::signed(ALICE),
            b"NDA".to_vec(),
            3,
            test_document_hash(),
            Some(100),
            None,
        ));
        // Add TWO parties so first signature doesn't activate contract
        assert_ok!(RicardianContracts::add_party(
            RuntimeOrigin::signed(ALICE),
            0,
            BOB,
            b"Signatory 1".to_vec(),
        ));
        assert_ok!(RicardianContracts::add_party(
            RuntimeOrigin::signed(ALICE),
            0,
            CHARLIE,
            b"Signatory 2".to_vec(),
        ));

        // First signature (contract stays in Draft)
        assert_ok!(RicardianContracts::sign_contract(
            RuntimeOrigin::signed(BOB),
            0,
        ));

        // Verify still in draft
        let contract = RicardianContracts::contracts(0).unwrap();
        assert_eq!(contract.status, ContractStatus::Draft);

        // Try to sign again
        assert_noop!(
            RicardianContracts::sign_contract(RuntimeOrigin::signed(BOB), 0),
            Error::<Test>::AlreadySigned
        );
    });
}

#[test]
fn test_sign_expired_contract() {
    new_test_ext().execute_with(|| {
        assert_ok!(RicardianContracts::create_contract(
            RuntimeOrigin::signed(ALICE),
            b"Short-lived".to_vec(),
            1,
            test_document_hash(),
            Some(15), // Expires at block 15
            None,
        ));
        assert_ok!(RicardianContracts::add_party(
            RuntimeOrigin::signed(ALICE),
            0,
            BOB,
            b"Party".to_vec(),
        ));

        // Advance past expiration
        advance_blocks(20);

        assert_noop!(
            RicardianContracts::sign_contract(RuntimeOrigin::signed(BOB), 0),
            Error::<Test>::ContractExpired
        );
    });
}

// ==================== AMENDMENT TESTS ====================

#[test]
fn test_propose_amendment_success() {
    new_test_ext().execute_with(|| {
        // Create and activate contract
        assert_ok!(RicardianContracts::create_contract(
            RuntimeOrigin::signed(ALICE),
            b"Partnership".to_vec(),
            1,
            test_document_hash(),
            Some(100),
            None,
        ));
        assert_ok!(RicardianContracts::add_party(
            RuntimeOrigin::signed(ALICE),
            0,
            BOB,
            b"Partner".to_vec(),
        ));
        assert_ok!(RicardianContracts::sign_contract(
            RuntimeOrigin::signed(BOB),
            0,
        ));

        // Propose amendment
        assert_ok!(RicardianContracts::propose_amendment(
            RuntimeOrigin::signed(BOB),
            0,
            test_amendment_hash(),
        ));

        let amendments = RicardianContracts::amendments(0);
        assert_eq!(amendments.len(), 1);
        assert_eq!(amendments[0].number, 1);
        assert_eq!(amendments[0].proposed_by, BOB);
        assert_eq!(amendments[0].approvals, 1); // Proposer auto-approves
        assert!(!amendments[0].approved);
    });
}

#[test]
fn test_propose_amendment_not_active() {
    new_test_ext().execute_with(|| {
        assert_ok!(RicardianContracts::create_contract(
            RuntimeOrigin::signed(ALICE),
            b"Draft Contract".to_vec(),
            1,
            test_document_hash(),
            Some(100),
            None,
        ));
        assert_ok!(RicardianContracts::add_party(
            RuntimeOrigin::signed(ALICE),
            0,
            BOB,
            b"Partner".to_vec(),
        ));
        // Not signed - still draft

        assert_noop!(
            RicardianContracts::propose_amendment(
                RuntimeOrigin::signed(BOB),
                0,
                test_amendment_hash(),
            ),
            Error::<Test>::NotActive
        );
    });
}

#[test]
fn test_approve_amendment_success() {
    new_test_ext().execute_with(|| {
        // Setup: create contract with 2 parties, activate
        assert_ok!(RicardianContracts::create_contract(
            RuntimeOrigin::signed(ALICE),
            b"Partnership".to_vec(),
            1,
            test_document_hash(),
            Some(100),
            None,
        ));
        assert_ok!(RicardianContracts::add_party(
            RuntimeOrigin::signed(ALICE),
            0,
            BOB,
            b"Partner 1".to_vec(),
        ));
        assert_ok!(RicardianContracts::add_party(
            RuntimeOrigin::signed(ALICE),
            0,
            CHARLIE,
            b"Partner 2".to_vec(),
        ));
        assert_ok!(RicardianContracts::sign_contract(RuntimeOrigin::signed(BOB), 0));
        assert_ok!(RicardianContracts::sign_contract(RuntimeOrigin::signed(CHARLIE), 0));

        // BOB proposes amendment (auto-approves)
        assert_ok!(RicardianContracts::propose_amendment(
            RuntimeOrigin::signed(BOB),
            0,
            test_amendment_hash(),
        ));

        // CHARLIE approves
        assert_ok!(RicardianContracts::approve_amendment(
            RuntimeOrigin::signed(CHARLIE),
            0,
            1,
        ));

        let amendments = RicardianContracts::amendments(0);
        assert_eq!(amendments[0].approvals, 2);
        assert!(amendments[0].approved); // All parties approved
    });
}

#[test]
fn test_approve_amendment_already_approved() {
    new_test_ext().execute_with(|| {
        // Setup active contract
        assert_ok!(RicardianContracts::create_contract(
            RuntimeOrigin::signed(ALICE),
            b"Partnership".to_vec(),
            1,
            test_document_hash(),
            Some(100),
            None,
        ));
        assert_ok!(RicardianContracts::add_party(
            RuntimeOrigin::signed(ALICE),
            0,
            BOB,
            b"Partner".to_vec(),
        ));
        assert_ok!(RicardianContracts::sign_contract(RuntimeOrigin::signed(BOB), 0));

        assert_ok!(RicardianContracts::propose_amendment(
            RuntimeOrigin::signed(BOB),
            0,
            test_amendment_hash(),
        ));

        // BOB already approved (proposer auto-approves)
        assert_noop!(
            RicardianContracts::approve_amendment(RuntimeOrigin::signed(BOB), 0, 1),
            Error::<Test>::AmendmentAlreadyApproved
        );
    });
}

// ==================== EXECUTION AND TERMINATION TESTS ====================

#[test]
fn test_execute_contract_success() {
    new_test_ext().execute_with(|| {
        assert_ok!(RicardianContracts::create_contract(
            RuntimeOrigin::signed(ALICE),
            b"Service Agreement".to_vec(),
            2,
            test_document_hash(),
            Some(100),
            None,
        ));
        assert_ok!(RicardianContracts::add_party(
            RuntimeOrigin::signed(ALICE),
            0,
            BOB,
            b"Provider".to_vec(),
        ));
        assert_ok!(RicardianContracts::sign_contract(RuntimeOrigin::signed(BOB), 0));

        // Execute
        assert_ok!(RicardianContracts::execute_contract(
            RuntimeOrigin::signed(BOB),
            0,
        ));

        let contract = RicardianContracts::contracts(0).unwrap();
        assert_eq!(contract.status, ContractStatus::Executed);
    });
}

#[test]
fn test_execute_contract_not_active() {
    new_test_ext().execute_with(|| {
        assert_ok!(RicardianContracts::create_contract(
            RuntimeOrigin::signed(ALICE),
            b"Draft".to_vec(),
            2,
            test_document_hash(),
            Some(100),
            None,
        ));
        assert_ok!(RicardianContracts::add_party(
            RuntimeOrigin::signed(ALICE),
            0,
            BOB,
            b"Party".to_vec(),
        ));

        // Try to execute draft contract
        assert_noop!(
            RicardianContracts::execute_contract(RuntimeOrigin::signed(BOB), 0),
            Error::<Test>::NotActive
        );
    });
}

#[test]
fn test_terminate_contract_by_creator() {
    new_test_ext().execute_with(|| {
        assert_ok!(RicardianContracts::create_contract(
            RuntimeOrigin::signed(ALICE),
            b"Cancellable".to_vec(),
            1,
            test_document_hash(),
            Some(100),
            None,
        ));

        assert_ok!(RicardianContracts::terminate_contract(
            RuntimeOrigin::signed(ALICE),
            0,
            b"No longer needed".to_vec(),
        ));

        let contract = RicardianContracts::contracts(0).unwrap();
        assert_eq!(contract.status, ContractStatus::Terminated);
    });
}

#[test]
fn test_terminate_contract_by_party() {
    new_test_ext().execute_with(|| {
        assert_ok!(RicardianContracts::create_contract(
            RuntimeOrigin::signed(ALICE),
            b"Partnership".to_vec(),
            1,
            test_document_hash(),
            Some(100),
            None,
        ));
        assert_ok!(RicardianContracts::add_party(
            RuntimeOrigin::signed(ALICE),
            0,
            BOB,
            b"Partner".to_vec(),
        ));

        // Party can terminate
        assert_ok!(RicardianContracts::terminate_contract(
            RuntimeOrigin::signed(BOB),
            0,
            b"Mutual termination".to_vec(),
        ));

        let contract = RicardianContracts::contracts(0).unwrap();
        assert_eq!(contract.status, ContractStatus::Terminated);
    });
}

#[test]
fn test_terminate_contract_not_authorized() {
    new_test_ext().execute_with(|| {
        assert_ok!(RicardianContracts::create_contract(
            RuntimeOrigin::signed(ALICE),
            b"Restricted".to_vec(),
            1,
            test_document_hash(),
            Some(100),
            None,
        ));

        // CHARLIE is neither creator nor party
        assert_noop!(
            RicardianContracts::terminate_contract(
                RuntimeOrigin::signed(CHARLIE),
                0,
                b"Unauthorized attempt".to_vec(),
            ),
            Error::<Test>::NotAuthorized
        );
    });
}

// ==================== HELPER FUNCTION TESTS ====================

#[test]
fn test_get_contract_status() {
    new_test_ext().execute_with(|| {
        assert_ok!(RicardianContracts::create_contract(
            RuntimeOrigin::signed(ALICE),
            b"Test".to_vec(),
            1,
            test_document_hash(),
            Some(100),
            None,
        ));

        assert_eq!(
            RicardianContracts::get_contract_status(0),
            Some(ContractStatus::Draft)
        );
        assert_eq!(RicardianContracts::get_contract_status(999), None);
    });
}

#[test]
fn test_is_active() {
    new_test_ext().execute_with(|| {
        assert_ok!(RicardianContracts::create_contract(
            RuntimeOrigin::signed(ALICE),
            b"Test".to_vec(),
            1,
            test_document_hash(),
            Some(100),
            None,
        ));
        assert_ok!(RicardianContracts::add_party(
            RuntimeOrigin::signed(ALICE),
            0,
            BOB,
            b"Party".to_vec(),
        ));

        assert!(!RicardianContracts::is_active(0)); // Draft

        assert_ok!(RicardianContracts::sign_contract(RuntimeOrigin::signed(BOB), 0));

        assert!(RicardianContracts::is_active(0)); // Active
    });
}

#[test]
fn test_is_party() {
    new_test_ext().execute_with(|| {
        assert_ok!(RicardianContracts::create_contract(
            RuntimeOrigin::signed(ALICE),
            b"Test".to_vec(),
            1,
            test_document_hash(),
            Some(100),
            None,
        ));
        assert_ok!(RicardianContracts::add_party(
            RuntimeOrigin::signed(ALICE),
            0,
            BOB,
            b"Party".to_vec(),
        ));

        assert!(RicardianContracts::is_party(0, &BOB));
        assert!(!RicardianContracts::is_party(0, &CHARLIE));
    });
}

#[test]
fn test_get_contracts_for_account() {
    new_test_ext().execute_with(|| {
        // Create multiple contracts and add BOB to some
        for i in 0..5 {
            assert_ok!(RicardianContracts::create_contract(
                RuntimeOrigin::signed(ALICE),
                format!("Contract {}", i).into_bytes(),
                1,
                test_document_hash(),
                Some(100),
                None,
            ));
            if i % 2 == 0 {
                assert_ok!(RicardianContracts::add_party(
                    RuntimeOrigin::signed(ALICE),
                    i,
                    BOB,
                    b"Party".to_vec(),
                ));
            }
        }

        let bob_contracts = RicardianContracts::get_contracts_for_account(&BOB);
        assert_eq!(bob_contracts.len(), 3); // 0, 2, 4
        assert!(bob_contracts.contains(&0));
        assert!(bob_contracts.contains(&2));
        assert!(bob_contracts.contains(&4));
    });
}

// ==================== FULL WORKFLOW TEST ====================

#[test]
fn test_complete_contract_lifecycle() {
    new_test_ext().execute_with(|| {
        // 1. Create contract
        assert_ok!(RicardianContracts::create_contract(
            RuntimeOrigin::signed(ALICE),
            b"Complete Lifecycle Test".to_vec(),
            1, // Partnership
            test_document_hash(),
            Some(100),
            None,
        ));

        // 2. Add terms
        assert_ok!(RicardianContracts::add_term(
            RuntimeOrigin::signed(ALICE),
            0,
            [0x11; 32],
            true,
        ));
        assert_ok!(RicardianContracts::add_term(
            RuntimeOrigin::signed(ALICE),
            0,
            [0x22; 32],
            false,
        ));

        // 3. Add parties
        assert_ok!(RicardianContracts::add_party(
            RuntimeOrigin::signed(ALICE),
            0,
            BOB,
            b"Partner A".to_vec(),
        ));
        assert_ok!(RicardianContracts::add_party(
            RuntimeOrigin::signed(ALICE),
            0,
            CHARLIE,
            b"Partner B".to_vec(),
        ));

        // Verify draft state
        let contract = RicardianContracts::contracts(0).unwrap();
        assert_eq!(contract.status, ContractStatus::Draft);
        assert_eq!(contract.party_count, 2);
        assert_eq!(contract.term_count, 2);

        // 4. Sign contract
        assert_ok!(RicardianContracts::sign_contract(RuntimeOrigin::signed(BOB), 0));
        assert_ok!(RicardianContracts::sign_contract(RuntimeOrigin::signed(CHARLIE), 0));

        // Verify active state
        let contract = RicardianContracts::contracts(0).unwrap();
        assert_eq!(contract.status, ContractStatus::Active);

        // 5. Propose and approve amendment
        assert_ok!(RicardianContracts::propose_amendment(
            RuntimeOrigin::signed(BOB),
            0,
            test_amendment_hash(),
        ));
        assert_ok!(RicardianContracts::approve_amendment(
            RuntimeOrigin::signed(CHARLIE),
            0,
            1,
        ));

        // Verify amendment applied
        let amendments = RicardianContracts::amendments(0);
        assert!(amendments[0].approved);

        // 6. Execute contract
        assert_ok!(RicardianContracts::execute_contract(
            RuntimeOrigin::signed(BOB),
            0,
        ));

        // Verify executed state
        let contract = RicardianContracts::contracts(0).unwrap();
        assert_eq!(contract.status, ContractStatus::Executed);
    });
}
