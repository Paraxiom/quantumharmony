//! Tests for Academic Vouch pallet

use crate::{
    mock::*,
    pallet::{ApplicantStatus, Error, Event},
};
use frame_support::{assert_noop, assert_ok};

// ==================== HELPER FUNCTIONS ====================

fn credential_hash(seed: u8) -> [u8; 32] {
    let mut hash = [0u8; 32];
    hash[0] = seed;
    hash[31] = seed;
    hash
}

fn institution(name: &str) -> Vec<u8> {
    name.as_bytes().to_vec()
}

fn reason(text: &str) -> Vec<u8> {
    text.as_bytes().to_vec()
}

// ==================== PROPOSE ACADEMIC TESTS ====================

#[test]
fn propose_academic_works() {
    new_test_ext().execute_with(|| {
        assert_ok!(AcademicVouch::propose_academic(
            RuntimeOrigin::signed(ALICE),
            institution("MIT"),
            credential_hash(1),
        ));

        // Check event
        System::assert_has_event(Event::AcademicProposed {
            proposal_id: 0,
            account: ALICE,
            institution: institution("MIT"),
        }.into());

        // Check proposal exists
        let proposal = AcademicVouch::academic_proposals(0).expect("Proposal should exist");
        assert_eq!(proposal.account, ALICE);
        assert_eq!(proposal.institution.to_vec(), institution("MIT"));
        assert_eq!(proposal.approvals, 0);
        assert_eq!(proposal.rejections, 0);
        assert!(!proposal.finalized);
    });
}

#[test]
fn propose_academic_fails_already_registered() {
    new_test_ext().execute_with(|| {
        register_academic_directly(ALICE, b"Harvard");

        assert_noop!(
            AcademicVouch::propose_academic(
                RuntimeOrigin::signed(ALICE),
                institution("MIT"),
                credential_hash(1),
            ),
            Error::<Test>::AlreadyRegistered
        );
    });
}

#[test]
fn propose_academic_fails_credential_too_long() {
    new_test_ext().execute_with(|| {
        let long_institution = vec![b'a'; 300]; // > 256 max

        assert_noop!(
            AcademicVouch::propose_academic(
                RuntimeOrigin::signed(ALICE),
                long_institution,
                credential_hash(1),
            ),
            Error::<Test>::CredentialTooLong
        );
    });
}

#[test]
fn proposal_id_increments() {
    new_test_ext().execute_with(|| {
        assert_ok!(AcademicVouch::propose_academic(
            RuntimeOrigin::signed(ALICE),
            institution("MIT"),
            credential_hash(1),
        ));

        assert_ok!(AcademicVouch::propose_academic(
            RuntimeOrigin::signed(BOB),
            institution("Stanford"),
            credential_hash(2),
        ));

        assert!(AcademicVouch::academic_proposals(0).is_some());
        assert!(AcademicVouch::academic_proposals(1).is_some());
        assert_eq!(AcademicVouch::next_academic_proposal_id(), 2);
    });
}

// ==================== VOTE ACADEMIC PROPOSAL TESTS ====================

#[test]
fn vote_academic_proposal_works() {
    new_test_ext().execute_with(|| {
        // Register existing academic to vote
        register_academic_directly(BOB, b"Harvard");

        // Create proposal
        assert_ok!(AcademicVouch::propose_academic(
            RuntimeOrigin::signed(ALICE),
            institution("MIT"),
            credential_hash(1),
        ));

        // Vote
        assert_ok!(AcademicVouch::vote_academic_proposal(
            RuntimeOrigin::signed(BOB),
            0,
            true, // approve
        ));

        // Check event
        System::assert_has_event(Event::AcademicVoteCast {
            proposal_id: 0,
            voter: BOB,
            approve: true,
        }.into());

        // Check vote recorded
        let proposal = AcademicVouch::academic_proposals(0).unwrap();
        assert_eq!(proposal.approvals, 1);
        assert_eq!(proposal.rejections, 0);
    });
}

#[test]
fn vote_academic_proposal_rejection() {
    new_test_ext().execute_with(|| {
        register_academic_directly(BOB, b"Harvard");

        assert_ok!(AcademicVouch::propose_academic(
            RuntimeOrigin::signed(ALICE),
            institution("MIT"),
            credential_hash(1),
        ));

        assert_ok!(AcademicVouch::vote_academic_proposal(
            RuntimeOrigin::signed(BOB),
            0,
            false, // reject
        ));

        let proposal = AcademicVouch::academic_proposals(0).unwrap();
        assert_eq!(proposal.approvals, 0);
        assert_eq!(proposal.rejections, 1);
    });
}

#[test]
fn vote_academic_proposal_fails_not_academic() {
    new_test_ext().execute_with(|| {
        assert_ok!(AcademicVouch::propose_academic(
            RuntimeOrigin::signed(ALICE),
            institution("MIT"),
            credential_hash(1),
        ));

        // BOB is not an academic
        assert_noop!(
            AcademicVouch::vote_academic_proposal(
                RuntimeOrigin::signed(BOB),
                0,
                true,
            ),
            Error::<Test>::NotAnAcademic
        );
    });
}

#[test]
fn vote_academic_proposal_fails_already_voted() {
    new_test_ext().execute_with(|| {
        register_academic_directly(BOB, b"Harvard");

        assert_ok!(AcademicVouch::propose_academic(
            RuntimeOrigin::signed(ALICE),
            institution("MIT"),
            credential_hash(1),
        ));

        assert_ok!(AcademicVouch::vote_academic_proposal(
            RuntimeOrigin::signed(BOB),
            0,
            true,
        ));

        assert_noop!(
            AcademicVouch::vote_academic_proposal(
                RuntimeOrigin::signed(BOB),
                0,
                false,
            ),
            Error::<Test>::AlreadyVoted
        );
    });
}

#[test]
fn vote_academic_proposal_fails_not_found() {
    new_test_ext().execute_with(|| {
        register_academic_directly(BOB, b"Harvard");

        assert_noop!(
            AcademicVouch::vote_academic_proposal(
                RuntimeOrigin::signed(BOB),
                99, // non-existent
                true,
            ),
            Error::<Test>::ProposalNotFound
        );
    });
}

#[test]
fn vote_academic_proposal_fails_voting_period_ended() {
    new_test_ext().execute_with(|| {
        register_academic_directly(BOB, b"Harvard");

        assert_ok!(AcademicVouch::propose_academic(
            RuntimeOrigin::signed(ALICE),
            institution("MIT"),
            credential_hash(1),
        ));

        // Advance past voting period (10 blocks)
        System::set_block_number(15);

        assert_noop!(
            AcademicVouch::vote_academic_proposal(
                RuntimeOrigin::signed(BOB),
                0,
                true,
            ),
            Error::<Test>::VotingPeriodEnded
        );
    });
}

// ==================== FINALIZE ACADEMIC PROPOSAL TESTS ====================

#[test]
fn finalize_academic_proposal_approved() {
    new_test_ext().execute_with(|| {
        register_academic_directly(BOB, b"Harvard");
        register_academic_directly(CHARLIE, b"Stanford");

        assert_ok!(AcademicVouch::propose_academic(
            RuntimeOrigin::signed(ALICE),
            institution("MIT"),
            credential_hash(1),
        ));

        // Vote approval
        assert_ok!(AcademicVouch::vote_academic_proposal(
            RuntimeOrigin::signed(BOB),
            0,
            true,
        ));

        // Advance past voting period
        System::set_block_number(15);

        // Finalize
        assert_ok!(AcademicVouch::finalize_academic_proposal(
            RuntimeOrigin::signed(CHARLIE),
            0,
        ));

        // Check ALICE is now an academic
        assert!(AcademicVouch::is_academic(&ALICE));

        System::assert_has_event(Event::AcademicRegistered {
            account: ALICE,
            institution: institution("MIT"),
        }.into());
    });
}

#[test]
fn finalize_academic_proposal_rejected() {
    new_test_ext().execute_with(|| {
        register_academic_directly(BOB, b"Harvard");

        assert_ok!(AcademicVouch::propose_academic(
            RuntimeOrigin::signed(ALICE),
            institution("MIT"),
            credential_hash(1),
        ));

        // Vote rejection
        assert_ok!(AcademicVouch::vote_academic_proposal(
            RuntimeOrigin::signed(BOB),
            0,
            false, // reject
        ));

        // Advance past voting period
        System::set_block_number(15);

        // Finalize
        assert_ok!(AcademicVouch::finalize_academic_proposal(
            RuntimeOrigin::signed(CHARLIE),
            0,
        ));

        // Check ALICE is NOT an academic
        assert!(!AcademicVouch::is_academic(&ALICE));

        System::assert_has_event(Event::AcademicRejected {
            account: ALICE,
        }.into());
    });
}

#[test]
fn finalize_academic_proposal_fails_voting_not_ended() {
    new_test_ext().execute_with(|| {
        assert_ok!(AcademicVouch::propose_academic(
            RuntimeOrigin::signed(ALICE),
            institution("MIT"),
            credential_hash(1),
        ));

        // Try to finalize immediately (voting still open)
        assert_noop!(
            AcademicVouch::finalize_academic_proposal(
                RuntimeOrigin::signed(BOB),
                0,
            ),
            Error::<Test>::VotingPeriodNotEnded
        );
    });
}

#[test]
fn finalize_academic_proposal_fails_already_finalized() {
    new_test_ext().execute_with(|| {
        register_academic_directly(BOB, b"Harvard");

        assert_ok!(AcademicVouch::propose_academic(
            RuntimeOrigin::signed(ALICE),
            institution("MIT"),
            credential_hash(1),
        ));

        assert_ok!(AcademicVouch::vote_academic_proposal(
            RuntimeOrigin::signed(BOB),
            0,
            true,
        ));

        System::set_block_number(15);

        assert_ok!(AcademicVouch::finalize_academic_proposal(
            RuntimeOrigin::signed(CHARLIE),
            0,
        ));

        // Try to finalize again
        assert_noop!(
            AcademicVouch::finalize_academic_proposal(
                RuntimeOrigin::signed(CHARLIE),
                0,
            ),
            Error::<Test>::AlreadyFinalized
        );
    });
}

// ==================== APPLY FOR PROGRAM TESTS ====================

#[test]
fn apply_for_program_works() {
    new_test_ext().execute_with(|| {
        assert_ok!(AcademicVouch::apply_for_program(
            RuntimeOrigin::signed(ALICE),
        ));

        System::assert_has_event(Event::ApplicationSubmitted {
            applicant: ALICE,
        }.into());

        let applicant = AcademicVouch::applicants(ALICE).expect("Applicant should exist");
        assert_eq!(applicant.account, ALICE);
        assert_eq!(applicant.status, ApplicantStatus::Pending);
        assert_eq!(applicant.vouch_count, 0);
    });
}

#[test]
fn apply_for_program_fails_already_applied() {
    new_test_ext().execute_with(|| {
        assert_ok!(AcademicVouch::apply_for_program(
            RuntimeOrigin::signed(ALICE),
        ));

        assert_noop!(
            AcademicVouch::apply_for_program(
                RuntimeOrigin::signed(ALICE),
            ),
            Error::<Test>::AlreadyApplied
        );
    });
}

// ==================== VOUCH FOR APPLICANT TESTS ====================

#[test]
fn vouch_for_applicant_works() {
    new_test_ext().execute_with(|| {
        register_academic_directly(BOB, b"Harvard");

        assert_ok!(AcademicVouch::apply_for_program(
            RuntimeOrigin::signed(ALICE),
        ));

        assert_ok!(AcademicVouch::vouch_for_applicant(
            RuntimeOrigin::signed(BOB),
            ALICE,
            reason("Excellent candidate"),
            None,
        ));

        System::assert_has_event(Event::VouchGiven {
            academic: BOB,
            applicant: ALICE,
        }.into());

        // Check vouch count
        assert_eq!(AcademicVouch::get_vouch_count(&ALICE), 1);

        // Check academic's vouch count
        let academic = AcademicVouch::academics(BOB).unwrap();
        assert_eq!(academic.vouches_given, 1);
    });
}

#[test]
fn vouch_triggers_vouches_complete() {
    new_test_ext().execute_with(|| {
        register_academic_directly(BOB, b"Harvard");
        register_academic_directly(CHARLIE, b"Stanford");

        assert_ok!(AcademicVouch::apply_for_program(
            RuntimeOrigin::signed(ALICE),
        ));

        // First vouch
        assert_ok!(AcademicVouch::vouch_for_applicant(
            RuntimeOrigin::signed(BOB),
            ALICE,
            reason("Great"),
            None,
        ));

        // Second vouch (reaches required threshold of 2)
        assert_ok!(AcademicVouch::vouch_for_applicant(
            RuntimeOrigin::signed(CHARLIE),
            ALICE,
            reason("Excellent"),
            None,
        ));

        // Check VouchesComplete event
        System::assert_has_event(Event::VouchesComplete {
            applicant: ALICE,
            vouch_count: 2,
        }.into());

        // Check status changed
        let applicant = AcademicVouch::applicants(ALICE).unwrap();
        assert_eq!(applicant.status, ApplicantStatus::VouchesComplete);
    });
}

#[test]
fn vouch_for_applicant_fails_not_academic() {
    new_test_ext().execute_with(|| {
        assert_ok!(AcademicVouch::apply_for_program(
            RuntimeOrigin::signed(ALICE),
        ));

        assert_noop!(
            AcademicVouch::vouch_for_applicant(
                RuntimeOrigin::signed(BOB),
                ALICE,
                reason("Good"),
                None,
            ),
            Error::<Test>::NotAnAcademic
        );
    });
}

#[test]
fn vouch_for_applicant_fails_self_vouch() {
    new_test_ext().execute_with(|| {
        register_academic_directly(ALICE, b"MIT");

        assert_ok!(AcademicVouch::apply_for_program(
            RuntimeOrigin::signed(ALICE),
        ));

        assert_noop!(
            AcademicVouch::vouch_for_applicant(
                RuntimeOrigin::signed(ALICE),
                ALICE,
                reason("I'm great"),
                None,
            ),
            Error::<Test>::CannotVouchForSelf
        );
    });
}

#[test]
fn vouch_for_applicant_fails_already_vouched() {
    new_test_ext().execute_with(|| {
        register_academic_directly(BOB, b"Harvard");

        assert_ok!(AcademicVouch::apply_for_program(
            RuntimeOrigin::signed(ALICE),
        ));

        assert_ok!(AcademicVouch::vouch_for_applicant(
            RuntimeOrigin::signed(BOB),
            ALICE,
            reason("Good"),
            None,
        ));

        assert_noop!(
            AcademicVouch::vouch_for_applicant(
                RuntimeOrigin::signed(BOB),
                ALICE,
                reason("Still good"),
                None,
            ),
            Error::<Test>::AlreadyVouched
        );
    });
}

#[test]
fn vouch_for_applicant_fails_applicant_not_found() {
    new_test_ext().execute_with(|| {
        register_academic_directly(BOB, b"Harvard");

        // ALICE hasn't applied
        assert_noop!(
            AcademicVouch::vouch_for_applicant(
                RuntimeOrigin::signed(BOB),
                ALICE,
                reason("Good"),
                None,
            ),
            Error::<Test>::ApplicantNotFound
        );
    });
}

#[test]
fn vouch_for_applicant_fails_reason_too_long() {
    new_test_ext().execute_with(|| {
        register_academic_directly(BOB, b"Harvard");

        assert_ok!(AcademicVouch::apply_for_program(
            RuntimeOrigin::signed(ALICE),
        ));

        let long_reason = vec![b'x'; 600]; // > 512 max

        assert_noop!(
            AcademicVouch::vouch_for_applicant(
                RuntimeOrigin::signed(BOB),
                ALICE,
                long_reason,
                None,
            ),
            Error::<Test>::ReasonTooLong
        );
    });
}

// ==================== ACCEPT APPLICANT TESTS ====================

#[test]
fn accept_applicant_works() {
    new_test_ext().execute_with(|| {
        register_academic_directly(BOB, b"Harvard");
        register_academic_directly(CHARLIE, b"Stanford");

        assert_ok!(AcademicVouch::apply_for_program(
            RuntimeOrigin::signed(ALICE),
        ));

        // Get required vouches
        assert_ok!(AcademicVouch::vouch_for_applicant(
            RuntimeOrigin::signed(BOB),
            ALICE,
            reason("Great"),
            None,
        ));
        assert_ok!(AcademicVouch::vouch_for_applicant(
            RuntimeOrigin::signed(CHARLIE),
            ALICE,
            reason("Excellent"),
            None,
        ));

        // Accept with contract
        assert_ok!(AcademicVouch::accept_applicant(
            RuntimeOrigin::signed(DAVE),
            ALICE,
            42, // contract_id
        ));

        System::assert_has_event(Event::ApplicantAccepted {
            applicant: ALICE,
            contract_id: 42,
        }.into());

        let applicant = AcademicVouch::applicants(ALICE).unwrap();
        assert_eq!(applicant.status, ApplicantStatus::Accepted);
        assert_eq!(applicant.contract_id, Some(42));
    });
}

#[test]
fn accept_applicant_fails_wrong_status() {
    new_test_ext().execute_with(|| {
        assert_ok!(AcademicVouch::apply_for_program(
            RuntimeOrigin::signed(ALICE),
        ));

        // Status is still Pending (no vouches)
        assert_noop!(
            AcademicVouch::accept_applicant(
                RuntimeOrigin::signed(DAVE),
                ALICE,
                42,
            ),
            Error::<Test>::InvalidStatusTransition
        );
    });
}

#[test]
fn accept_applicant_fails_not_found() {
    new_test_ext().execute_with(|| {
        assert_noop!(
            AcademicVouch::accept_applicant(
                RuntimeOrigin::signed(DAVE),
                ALICE,
                42,
            ),
            Error::<Test>::ApplicantNotFound
        );
    });
}

// ==================== REJECT APPLICANT TESTS ====================

#[test]
fn reject_applicant_works() {
    new_test_ext().execute_with(|| {
        assert_ok!(AcademicVouch::apply_for_program(
            RuntimeOrigin::signed(ALICE),
        ));

        assert_ok!(AcademicVouch::reject_applicant(
            RuntimeOrigin::signed(DAVE),
            ALICE,
            reason("Not qualified"),
        ));

        System::assert_has_event(Event::ApplicantRejected {
            applicant: ALICE,
            reason: reason("Not qualified"),
        }.into());

        let applicant = AcademicVouch::applicants(ALICE).unwrap();
        assert_eq!(applicant.status, ApplicantStatus::Rejected);
    });
}

#[test]
fn reject_applicant_fails_not_found() {
    new_test_ext().execute_with(|| {
        assert_noop!(
            AcademicVouch::reject_applicant(
                RuntimeOrigin::signed(DAVE),
                ALICE,
                reason("Not qualified"),
            ),
            Error::<Test>::ApplicantNotFound
        );
    });
}

// ==================== HELPER FUNCTION TESTS ====================

#[test]
fn is_academic_works() {
    new_test_ext().execute_with(|| {
        assert!(!AcademicVouch::is_academic(&ALICE));

        register_academic_directly(ALICE, b"MIT");

        assert!(AcademicVouch::is_academic(&ALICE));
    });
}

#[test]
fn get_vouch_count_works() {
    new_test_ext().execute_with(|| {
        register_academic_directly(BOB, b"Harvard");
        register_academic_directly(CHARLIE, b"Stanford");

        assert_eq!(AcademicVouch::get_vouch_count(&ALICE), 0);

        assert_ok!(AcademicVouch::apply_for_program(
            RuntimeOrigin::signed(ALICE),
        ));

        assert_ok!(AcademicVouch::vouch_for_applicant(
            RuntimeOrigin::signed(BOB),
            ALICE,
            reason("Good"),
            None,
        ));

        assert_eq!(AcademicVouch::get_vouch_count(&ALICE), 1);

        assert_ok!(AcademicVouch::vouch_for_applicant(
            RuntimeOrigin::signed(CHARLIE),
            ALICE,
            reason("Great"),
            None,
        ));

        assert_eq!(AcademicVouch::get_vouch_count(&ALICE), 2);
    });
}

#[test]
fn has_enough_vouches_works() {
    new_test_ext().execute_with(|| {
        register_academic_directly(BOB, b"Harvard");
        register_academic_directly(CHARLIE, b"Stanford");

        assert_ok!(AcademicVouch::apply_for_program(
            RuntimeOrigin::signed(ALICE),
        ));

        assert!(!AcademicVouch::has_enough_vouches(&ALICE));

        assert_ok!(AcademicVouch::vouch_for_applicant(
            RuntimeOrigin::signed(BOB),
            ALICE,
            reason("Good"),
            None,
        ));

        assert!(!AcademicVouch::has_enough_vouches(&ALICE)); // Still need 2

        assert_ok!(AcademicVouch::vouch_for_applicant(
            RuntimeOrigin::signed(CHARLIE),
            ALICE,
            reason("Great"),
            None,
        ));

        assert!(AcademicVouch::has_enough_vouches(&ALICE)); // Now has 2
    });
}

// ==================== VOUCH WITH CONTRACT REFERENCE TESTS ====================

#[test]
fn vouch_with_contract_id() {
    new_test_ext().execute_with(|| {
        register_academic_directly(BOB, b"Harvard");

        assert_ok!(AcademicVouch::apply_for_program(
            RuntimeOrigin::signed(ALICE),
        ));

        assert_ok!(AcademicVouch::vouch_for_applicant(
            RuntimeOrigin::signed(BOB),
            ALICE,
            reason("Good candidate"),
            Some(123), // contract reference
        ));

        let vouches = AcademicVouch::vouches(ALICE);
        assert_eq!(vouches.len(), 1);
        assert_eq!(vouches[0].contract_id, Some(123));
    });
}
