//! Tests for the Axiom Attestation pallet
//!
//! Comprehensive test coverage for anchoring, deduplication, revocation,
//! querying, rate limiting, and edge cases.

use crate::{mock::*, Error, Event};
use frame_support::{assert_noop, assert_ok};

/// Helper: create a task hash from a seed
fn task_hash(seed: u8) -> [u8; 32] {
    let mut hash = [0u8; 32];
    hash[0] = seed;
    hash[31] = seed;
    hash
}

/// Helper: create a description hash
fn desc_hash(seed: u8) -> [u8; 32] {
    let mut hash = [0u8; 32];
    hash[0] = seed;
    hash[1] = 0xDE;
    hash
}

/// Helper: create an audit chain hash
fn audit_hash(seed: u8) -> [u8; 32] {
    let mut hash = [0u8; 32];
    hash[0] = seed;
    hash[2] = 0xAC;
    hash
}

/// Helper: a valid fingerprint
fn fingerprint() -> Vec<u8> {
    b"7b:a7:b6:01:02".to_vec()
}

/// Helper: a valid signature (fake but non-empty)
fn signature() -> Vec<u8> {
    vec![0xFA; 100] // 100 bytes of fake Falcon sig
}

/// Helper: a valid provider string
fn provider() -> Vec<u8> {
    b"claude-code".to_vec()
}

// ==================== ANCHOR ATTESTATION TESTS ====================

#[test]
fn anchor_attestation_works() {
    new_test_ext().execute_with(|| {
        let th = task_hash(1);
        let dh = desc_hash(1);
        let ah = audit_hash(1);

        assert_ok!(AxiomAttestation::anchor_attestation(
            RuntimeOrigin::signed(ALICE),
            th, dh, 5,
            fingerprint(), signature(), ah,
            provider(),
        ));

        // Verify attestation was created
        let attestation = AxiomAttestation::task_attestations(0).expect("Should exist");
        assert_eq!(attestation.id, 0);
        assert_eq!(attestation.task_hash, th);
        assert_eq!(attestation.description_hash, dh);
        assert_eq!(attestation.step_count, 5);
        assert_eq!(attestation.audit_chain_hash, ah);
        assert_eq!(attestation.attester, ALICE);
        assert_eq!(attestation.anchored_at, 1);
        assert!(!attestation.revoked);

        // Verify lookup by task hash
        assert_eq!(AxiomAttestation::attestation_by_task_hash(th), Some(0));

        // Verify account tracking
        let account_attestations = AxiomAttestation::attestations_by_account(ALICE);
        assert!(account_attestations.contains(&0));

        // Verify global stats
        assert_eq!(AxiomAttestation::total_attestations(), 1);
        assert_eq!(AxiomAttestation::total_steps_attested(), 5);

        // Verify next ID
        assert_eq!(AxiomAttestation::next_attestation_id(), 1);

        // Verify event
        System::assert_has_event(Event::TaskAttestationAnchored {
            attestation_id: 0,
            task_hash: th,
            step_count: 5,
            attester: ALICE,
        }.into());
    });
}

#[test]
fn anchor_attestation_increments_ids() {
    new_test_ext().execute_with(|| {
        for i in 0u8..5 {
            assert_ok!(AxiomAttestation::anchor_attestation(
                RuntimeOrigin::signed(ALICE),
                task_hash(10 + i), desc_hash(10 + i), i as u32,
                fingerprint(), signature(), audit_hash(10 + i),
                provider(),
            ));
            assert_eq!(AxiomAttestation::next_attestation_id(), (i + 1) as u64);
        }
        assert_eq!(AxiomAttestation::total_attestations(), 5);
    });
}

#[test]
fn anchor_attestation_accumulates_steps() {
    new_test_ext().execute_with(|| {
        assert_ok!(AxiomAttestation::anchor_attestation(
            RuntimeOrigin::signed(ALICE),
            task_hash(20), desc_hash(20), 10,
            fingerprint(), signature(), audit_hash(20),
            provider(),
        ));
        assert_ok!(AxiomAttestation::anchor_attestation(
            RuntimeOrigin::signed(ALICE),
            task_hash(21), desc_hash(21), 7,
            fingerprint(), signature(), audit_hash(21),
            provider(),
        ));
        assert_eq!(AxiomAttestation::total_steps_attested(), 17);
    });
}

#[test]
fn anchor_attestation_multiple_accounts() {
    new_test_ext().execute_with(|| {
        assert_ok!(AxiomAttestation::anchor_attestation(
            RuntimeOrigin::signed(ALICE),
            task_hash(30), desc_hash(30), 3,
            fingerprint(), signature(), audit_hash(30),
            provider(),
        ));
        assert_ok!(AxiomAttestation::anchor_attestation(
            RuntimeOrigin::signed(BOB),
            task_hash(31), desc_hash(31), 8,
            fingerprint(), signature(), audit_hash(31),
            provider(),
        ));

        assert_eq!(AxiomAttestation::attestations_by_account(ALICE).len(), 1);
        assert_eq!(AxiomAttestation::attestations_by_account(BOB).len(), 1);
        assert_eq!(AxiomAttestation::total_attestations(), 2);
    });
}

// ==================== DEDUP TESTS ====================

#[test]
fn anchor_attestation_fails_duplicate_task_hash() {
    new_test_ext().execute_with(|| {
        let th = task_hash(40);

        assert_ok!(AxiomAttestation::anchor_attestation(
            RuntimeOrigin::signed(ALICE),
            th, desc_hash(40), 5,
            fingerprint(), signature(), audit_hash(40),
            provider(),
        ));

        // Same task hash from different account should fail
        assert_noop!(
            AxiomAttestation::anchor_attestation(
                RuntimeOrigin::signed(BOB),
                th, desc_hash(41), 3,
                fingerprint(), signature(), audit_hash(41),
                provider(),
            ),
            Error::<Test>::TaskAlreadyAttested
        );
    });
}

// ==================== VALIDATION TESTS ====================

#[test]
fn anchor_attestation_fails_empty_signature() {
    new_test_ext().execute_with(|| {
        assert_noop!(
            AxiomAttestation::anchor_attestation(
                RuntimeOrigin::signed(ALICE),
                task_hash(50), desc_hash(50), 5,
                fingerprint(),
                vec![], // empty signature
                audit_hash(50),
                provider(),
            ),
            Error::<Test>::InvalidSignature
        );
    });
}

#[test]
fn anchor_attestation_fails_empty_fingerprint() {
    new_test_ext().execute_with(|| {
        assert_noop!(
            AxiomAttestation::anchor_attestation(
                RuntimeOrigin::signed(ALICE),
                task_hash(51), desc_hash(51), 5,
                vec![], // empty fingerprint
                signature(),
                audit_hash(51),
                provider(),
            ),
            Error::<Test>::InvalidFingerprint
        );
    });
}

#[test]
fn anchor_attestation_fails_fingerprint_too_long() {
    new_test_ext().execute_with(|| {
        assert_noop!(
            AxiomAttestation::anchor_attestation(
                RuntimeOrigin::signed(ALICE),
                task_hash(52), desc_hash(52), 5,
                vec![0xAB; 50], // > 48 bytes
                signature(),
                audit_hash(52),
                provider(),
            ),
            Error::<Test>::InvalidFingerprint
        );
    });
}

#[test]
fn anchor_attestation_fails_signature_too_long() {
    new_test_ext().execute_with(|| {
        assert_noop!(
            AxiomAttestation::anchor_attestation(
                RuntimeOrigin::signed(ALICE),
                task_hash(53), desc_hash(53), 5,
                fingerprint(),
                vec![0xFA; 1500], // > 1400 bytes
                audit_hash(53),
                provider(),
            ),
            Error::<Test>::InvalidSignature
        );
    });
}

#[test]
fn anchor_attestation_fails_provider_too_long() {
    new_test_ext().execute_with(|| {
        assert_noop!(
            AxiomAttestation::anchor_attestation(
                RuntimeOrigin::signed(ALICE),
                task_hash(54), desc_hash(54), 5,
                fingerprint(), signature(), audit_hash(54),
                vec![b'x'; 40], // > 32 bytes
            ),
            Error::<Test>::ProviderTooLong
        );
    });
}

// ==================== RATE LIMIT TESTS ====================

#[test]
fn anchor_attestation_rate_limit() {
    new_test_ext().execute_with(|| {
        // MaxAttestationsPerBlock = 10
        for i in 0u8..10 {
            assert_ok!(AxiomAttestation::anchor_attestation(
                RuntimeOrigin::signed(ALICE),
                task_hash(60 + i), desc_hash(60 + i), 1,
                fingerprint(), signature(), audit_hash(60 + i),
                provider(),
            ));
        }

        // 11th should fail
        assert_noop!(
            AxiomAttestation::anchor_attestation(
                RuntimeOrigin::signed(ALICE),
                task_hash(70), desc_hash(70), 1,
                fingerprint(), signature(), audit_hash(70),
                provider(),
            ),
            Error::<Test>::MaxAttestationsPerBlock
        );
    });
}

// ==================== REVOKE TESTS ====================

#[test]
fn revoke_attestation_works() {
    new_test_ext().execute_with(|| {
        let th = task_hash(80);

        assert_ok!(AxiomAttestation::anchor_attestation(
            RuntimeOrigin::signed(ALICE),
            th, desc_hash(80), 3,
            fingerprint(), signature(), audit_hash(80),
            provider(),
        ));

        assert_ok!(AxiomAttestation::revoke_attestation(
            RuntimeOrigin::signed(ALICE),
            0,
            b"task was incorrect".to_vec(),
        ));

        let attestation = AxiomAttestation::task_attestations(0).expect("Should exist");
        assert!(attestation.revoked);
    });
}

#[test]
fn revoke_attestation_fails_not_owner() {
    new_test_ext().execute_with(|| {
        assert_ok!(AxiomAttestation::anchor_attestation(
            RuntimeOrigin::signed(ALICE),
            task_hash(81), desc_hash(81), 3,
            fingerprint(), signature(), audit_hash(81),
            provider(),
        ));

        assert_noop!(
            AxiomAttestation::revoke_attestation(
                RuntimeOrigin::signed(BOB),
                0,
                b"unauthorized".to_vec(),
            ),
            Error::<Test>::NotOwner
        );
    });
}

#[test]
fn revoke_attestation_fails_not_found() {
    new_test_ext().execute_with(|| {
        assert_noop!(
            AxiomAttestation::revoke_attestation(
                RuntimeOrigin::signed(ALICE),
                999,
                b"not found".to_vec(),
            ),
            Error::<Test>::AttestationNotFound
        );
    });
}

// ==================== QUERY / HELPER TESTS ====================

#[test]
fn verify_task_works() {
    new_test_ext().execute_with(|| {
        let th = task_hash(90);

        assert_ok!(AxiomAttestation::anchor_attestation(
            RuntimeOrigin::signed(ALICE),
            th, desc_hash(90), 12,
            fingerprint(), signature(), audit_hash(90),
            provider(),
        ));

        let result = AxiomAttestation::verify_task(th);
        assert!(result.is_some());

        let (id, block, steps) = result.unwrap();
        assert_eq!(id, 0);
        assert_eq!(block, 1);
        assert_eq!(steps, 12);

        // Non-existent task
        assert!(AxiomAttestation::verify_task(task_hash(99)).is_none());
    });
}

#[test]
fn get_attestation_works() {
    new_test_ext().execute_with(|| {
        assert_ok!(AxiomAttestation::anchor_attestation(
            RuntimeOrigin::signed(BOB),
            task_hash(91), desc_hash(91), 7,
            fingerprint(), signature(), audit_hash(91),
            b"anthropic".to_vec(),
        ));

        let att = AxiomAttestation::get_attestation(0).expect("Should exist");
        assert_eq!(att.attester, BOB);
        assert_eq!(att.step_count, 7);
        assert_eq!(att.provider.into_inner(), b"anthropic".to_vec());

        assert!(AxiomAttestation::get_attestation(999).is_none());
    });
}

#[test]
fn get_attestations_for_account_works() {
    new_test_ext().execute_with(|| {
        // Alice submits 3 attestations
        for i in 0u8..3 {
            assert_ok!(AxiomAttestation::anchor_attestation(
                RuntimeOrigin::signed(ALICE),
                task_hash(100 + i), desc_hash(100 + i), 1,
                fingerprint(), signature(), audit_hash(100 + i),
                provider(),
            ));
        }

        let ids = AxiomAttestation::get_attestations_for_account(&ALICE);
        assert_eq!(ids, vec![0, 1, 2]);

        // Bob has none
        let bob_ids = AxiomAttestation::get_attestations_for_account(&BOB);
        assert!(bob_ids.is_empty());
    });
}

// ==================== CONFIG UPDATE TEST ====================

#[test]
fn set_max_attestations_requires_root() {
    new_test_ext().execute_with(|| {
        // Signed origin should fail
        assert_noop!(
            AxiomAttestation::set_max_attestations_per_block(
                RuntimeOrigin::signed(ALICE),
                20,
            ),
            sp_runtime::DispatchError::BadOrigin
        );

        // Root should work
        assert_ok!(AxiomAttestation::set_max_attestations_per_block(
            RuntimeOrigin::root(),
            20,
        ));

        System::assert_has_event(Event::ConfigUpdated {
            max_per_block: 20,
        }.into());
    });
}

// ==================== ZERO STEP COUNT ====================

#[test]
fn anchor_attestation_zero_steps() {
    new_test_ext().execute_with(|| {
        // Zero steps is valid (e.g., a failed-then-retried task)
        assert_ok!(AxiomAttestation::anchor_attestation(
            RuntimeOrigin::signed(ALICE),
            task_hash(110), desc_hash(110), 0,
            fingerprint(), signature(), audit_hash(110),
            provider(),
        ));

        let att = AxiomAttestation::task_attestations(0).expect("Should exist");
        assert_eq!(att.step_count, 0);
        assert_eq!(AxiomAttestation::total_steps_attested(), 0);
    });
}
