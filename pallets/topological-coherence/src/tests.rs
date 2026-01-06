//! Tests for the Topological Coherence pallet
//!
//! Comprehensive test coverage for entity registration, transition validation,
//! coherence tracking, and account flagging.

use crate::{mock::*, pallet::*, Error, Event};
use frame_support::{assert_noop, assert_ok};

// ==================== REGISTER ENTITY TESTS ====================

#[test]
fn register_entity_works() {
    new_test_ext().execute_with(|| {
        let position = ToroidalPosition::new(3, 5);

        assert_ok!(TopologicalCoherence::register_entity(
            RuntimeOrigin::signed(ALICE),
            0,
            position,
        ));

        // Verify tracker was created
        let tracker = TopologicalCoherence::tracker(ALICE, 0).expect("Tracker should exist");
        assert_eq!(tracker.position, position);
        assert_eq!(tracker.transitions, 0);
        assert_eq!(tracker.violations, 0);

        // Verify entity count
        assert_eq!(TopologicalCoherence::entity_count(ALICE), 1);

        // Verify event
        System::assert_has_event(
            Event::EntityRegistered {
                account: ALICE,
                entity_id: 0,
                position,
            }
            .into(),
        );
    });
}

#[test]
fn register_entity_fails_duplicate() {
    new_test_ext().execute_with(|| {
        let position = ToroidalPosition::new(0, 0);

        assert_ok!(TopologicalCoherence::register_entity(
            RuntimeOrigin::signed(ALICE),
            0,
            position,
        ));

        assert_noop!(
            TopologicalCoherence::register_entity(RuntimeOrigin::signed(ALICE), 0, position,),
            Error::<Test>::EntityAlreadyExists
        );
    });
}

#[test]
fn register_entity_fails_invalid_position() {
    new_test_ext().execute_with(|| {
        // Default grid size is 12, so position (12, 0) is out of bounds
        let invalid_position = ToroidalPosition::new(12, 0);

        assert_noop!(
            TopologicalCoherence::register_entity(
                RuntimeOrigin::signed(ALICE),
                0,
                invalid_position,
            ),
            Error::<Test>::InvalidPosition
        );
    });
}

#[test]
fn register_entity_fails_too_many() {
    new_test_ext().execute_with(|| {
        // MaxEntitiesPerAccount is 10 in mock
        for i in 0..10 {
            assert_ok!(TopologicalCoherence::register_entity(
                RuntimeOrigin::signed(ALICE),
                i,
                ToroidalPosition::new(0, 0),
            ));
        }

        assert_noop!(
            TopologicalCoherence::register_entity(
                RuntimeOrigin::signed(ALICE),
                10,
                ToroidalPosition::new(0, 0),
            ),
            Error::<Test>::TooManyEntities
        );
    });
}

#[test]
fn register_multiple_entities() {
    new_test_ext().execute_with(|| {
        assert_ok!(TopologicalCoherence::register_entity(
            RuntimeOrigin::signed(ALICE),
            0,
            ToroidalPosition::new(0, 0),
        ));

        assert_ok!(TopologicalCoherence::register_entity(
            RuntimeOrigin::signed(ALICE),
            1,
            ToroidalPosition::new(5, 5),
        ));

        assert_ok!(TopologicalCoherence::register_entity(
            RuntimeOrigin::signed(BOB),
            0,
            ToroidalPosition::new(3, 3),
        ));

        assert_eq!(TopologicalCoherence::entity_count(ALICE), 2);
        assert_eq!(TopologicalCoherence::entity_count(BOB), 1);
    });
}

// ==================== SUBMIT TRANSITION TESTS ====================

#[test]
fn submit_transition_works() {
    new_test_ext().execute_with(|| {
        let start = ToroidalPosition::new(5, 5);
        let end = ToroidalPosition::new(6, 5); // distance = 1

        assert_ok!(TopologicalCoherence::register_entity(
            RuntimeOrigin::signed(ALICE),
            0,
            start,
        ));

        assert_ok!(TopologicalCoherence::submit_transition(
            RuntimeOrigin::signed(ALICE),
            0,
            end,
        ));

        let tracker = TopologicalCoherence::tracker(ALICE, 0).expect("Tracker should exist");
        assert_eq!(tracker.position, end);
        assert_eq!(tracker.transitions, 1);
        assert_eq!(tracker.violations, 0); // distance 1 <= threshold 2

        System::assert_has_event(
            Event::TransitionRecorded {
                account: ALICE,
                entity_id: 0,
                from: start,
                to: end,
                distance: 1,
                is_violation: false,
            }
            .into(),
        );
    });
}

#[test]
fn submit_transition_violation() {
    new_test_ext().execute_with(|| {
        let start = ToroidalPosition::new(0, 0);
        let end = ToroidalPosition::new(5, 5); // distance = 10, > threshold 2

        assert_ok!(TopologicalCoherence::register_entity(
            RuntimeOrigin::signed(ALICE),
            0,
            start,
        ));

        assert_ok!(TopologicalCoherence::submit_transition(
            RuntimeOrigin::signed(ALICE),
            0,
            end,
        ));

        let tracker = TopologicalCoherence::tracker(ALICE, 0).expect("Tracker should exist");
        assert_eq!(tracker.violations, 1);

        System::assert_has_event(
            Event::TransitionRecorded {
                account: ALICE,
                entity_id: 0,
                from: start,
                to: end,
                distance: 10,
                is_violation: true,
            }
            .into(),
        );
    });
}

#[test]
fn submit_transition_fails_entity_not_found() {
    new_test_ext().execute_with(|| {
        assert_noop!(
            TopologicalCoherence::submit_transition(
                RuntimeOrigin::signed(ALICE),
                999,
                ToroidalPosition::new(0, 0),
            ),
            Error::<Test>::EntityNotFound
        );
    });
}

#[test]
fn submit_transition_fails_invalid_position() {
    new_test_ext().execute_with(|| {
        assert_ok!(TopologicalCoherence::register_entity(
            RuntimeOrigin::signed(ALICE),
            0,
            ToroidalPosition::new(0, 0),
        ));

        assert_noop!(
            TopologicalCoherence::submit_transition(
                RuntimeOrigin::signed(ALICE),
                0,
                ToroidalPosition::new(15, 0), // out of bounds
            ),
            Error::<Test>::InvalidPosition
        );
    });
}

#[test]
fn submit_transition_fails_flagged_account() {
    new_test_ext().execute_with(|| {
        assert_ok!(TopologicalCoherence::register_entity(
            RuntimeOrigin::signed(ALICE),
            0,
            ToroidalPosition::new(0, 0),
        ));

        // Manually flag the account
        Flagged::<Test>::insert(ALICE, true);

        assert_noop!(
            TopologicalCoherence::submit_transition(
                RuntimeOrigin::signed(ALICE),
                0,
                ToroidalPosition::new(1, 0),
            ),
            Error::<Test>::AccountFlagged
        );
    });
}

// ==================== ACCOUNT FLAGGING TESTS ====================

#[test]
fn account_gets_flagged_on_excessive_violations() {
    new_test_ext().execute_with(|| {
        assert_ok!(TopologicalCoherence::register_entity(
            RuntimeOrigin::signed(ALICE),
            0,
            ToroidalPosition::new(0, 0),
        ));

        // Default config: min_transitions = 10, max_violation_rate = 100 (10%)
        // So we need > 10% violation rate after 10 transitions

        // Make 10 transitions, all violations (100% violation rate)
        for i in 0..10 {
            let pos = ToroidalPosition::new((i % 6) as u8, ((i + 3) % 6) as u8);
            // Create large jumps (violations)
            let new_pos = ToroidalPosition::new(((i + 5) % 12) as u8, ((i + 7) % 12) as u8);

            // Set current position
            Trackers::<Test>::mutate(ALICE, 0, |t| {
                if let Some(tracker) = t {
                    tracker.position = pos;
                }
            });

            assert_ok!(TopologicalCoherence::submit_transition(
                RuntimeOrigin::signed(ALICE),
                0,
                new_pos,
            ));
        }

        // Account should be flagged
        assert!(TopologicalCoherence::flagged(ALICE));

        // Verify flagging event was emitted
        let events = System::events();
        let flagged_event = events.iter().find(|e| {
            matches!(
                e.event,
                RuntimeEvent::TopologicalCoherence(Event::AccountFlagged { .. })
            )
        });
        assert!(flagged_event.is_some());
    });
}

#[test]
fn account_not_flagged_below_min_transitions() {
    new_test_ext().execute_with(|| {
        assert_ok!(TopologicalCoherence::register_entity(
            RuntimeOrigin::signed(ALICE),
            0,
            ToroidalPosition::new(0, 0),
        ));

        // Make 5 violations (below min_transitions = 10)
        for _ in 0..5 {
            assert_ok!(TopologicalCoherence::submit_transition(
                RuntimeOrigin::signed(ALICE),
                0,
                ToroidalPosition::new(10, 10), // large jump = violation
            ));

            // Reset position for next violation
            Trackers::<Test>::mutate(ALICE, 0, |t| {
                if let Some(tracker) = t {
                    tracker.position = ToroidalPosition::new(0, 0);
                }
            });
        }

        // Account should NOT be flagged (below min_transitions)
        assert!(!TopologicalCoherence::flagged(ALICE));
    });
}

// ==================== UPDATE CONFIG TESTS ====================

#[test]
fn update_config_works() {
    new_test_ext().execute_with(|| {
        let new_config = CoherenceConfig {
            grid_size: 16,
            drift_threshold: 3,
            max_violation_rate: 200,
            min_transitions: 20,
        };

        assert_ok!(TopologicalCoherence::update_config(
            RuntimeOrigin::root(),
            new_config,
        ));

        assert_eq!(TopologicalCoherence::config(), new_config);

        System::assert_has_event(Event::ConfigUpdated { config: new_config }.into());
    });
}

#[test]
fn update_config_fails_not_root() {
    new_test_ext().execute_with(|| {
        let new_config = CoherenceConfig::default();

        assert_noop!(
            TopologicalCoherence::update_config(RuntimeOrigin::signed(ALICE), new_config,),
            sp_runtime::DispatchError::BadOrigin
        );
    });
}

// ==================== UNFLAG ACCOUNT TESTS ====================

#[test]
fn unflag_account_works() {
    new_test_ext().execute_with(|| {
        // Manually flag
        Flagged::<Test>::insert(ALICE, true);
        assert!(TopologicalCoherence::flagged(ALICE));

        assert_ok!(TopologicalCoherence::unflag_account(
            RuntimeOrigin::root(),
            ALICE,
        ));

        assert!(!TopologicalCoherence::flagged(ALICE));

        System::assert_has_event(Event::AccountUnflagged { account: ALICE }.into());
    });
}

#[test]
fn unflag_account_fails_not_root() {
    new_test_ext().execute_with(|| {
        Flagged::<Test>::insert(ALICE, true);

        assert_noop!(
            TopologicalCoherence::unflag_account(RuntimeOrigin::signed(BOB), ALICE,),
            sp_runtime::DispatchError::BadOrigin
        );
    });
}

// ==================== TOROIDAL DISTANCE TESTS ====================

#[test]
fn toroidal_distance_wraps_correctly() {
    new_test_ext().execute_with(|| {
        // Test wraparound: distance from (0,0) to (11,11) should be 2 on 12x12 torus
        let pos_a = ToroidalPosition::new(0, 0);
        let pos_b = ToroidalPosition::new(11, 11);

        // 11 -> wraps to 1, so distance is 1 + 1 = 2
        assert_eq!(pos_a.distance_to(&pos_b), 2);

        // Distance from (0,0) to (6,6) = 6 + 6 = 12, but wrapped = 6 + 6 = 12
        let pos_c = ToroidalPosition::new(6, 6);
        assert_eq!(pos_a.distance_to(&pos_c), 12);

        // Distance from (0,0) to (7,0) = 5 (wraps around)
        let pos_d = ToroidalPosition::new(7, 0);
        assert_eq!(pos_a.distance_to(&pos_d), 5);
    });
}

#[test]
fn toroidal_distance_symmetric() {
    new_test_ext().execute_with(|| {
        let pos_a = ToroidalPosition::new(3, 7);
        let pos_b = ToroidalPosition::new(9, 2);

        assert_eq!(pos_a.distance_to(&pos_b), pos_b.distance_to(&pos_a));
    });
}

// ==================== COHERENCE TRACKER TESTS ====================

#[test]
fn violation_rate_calculation() {
    new_test_ext().execute_with(|| {
        let tracker = CoherenceTracker {
            position: ToroidalPosition::new(0, 0),
            transitions: 100,
            violations: 15,
            last_update: 1,
        };

        // 15/100 = 0.15 = 150 per mille
        assert_eq!(tracker.violation_rate_scaled(), 150);
    });
}

#[test]
fn is_coherent_check() {
    new_test_ext().execute_with(|| {
        let config = CoherenceConfig::default(); // max_violation_rate = 100, min_transitions = 10

        // Below min_transitions - always coherent
        let tracker1 = CoherenceTracker {
            position: ToroidalPosition::new(0, 0),
            transitions: 5,
            violations: 5, // 100% violations but below threshold
            last_update: 1,
        };
        assert!(tracker1.is_coherent(&config));

        // Above min_transitions, below max_violation_rate
        let tracker2 = CoherenceTracker {
            position: ToroidalPosition::new(0, 0),
            transitions: 20,
            violations: 1, // 5% violation rate
            last_update: 1,
        };
        assert!(tracker2.is_coherent(&config));

        // Above min_transitions, above max_violation_rate
        let tracker3 = CoherenceTracker {
            position: ToroidalPosition::new(0, 0),
            transitions: 20,
            violations: 5, // 25% violation rate > 10%
            last_update: 1,
        };
        assert!(!tracker3.is_coherent(&config));
    });
}

// ==================== EDGE CASES ====================

#[test]
fn zero_transitions_no_panic() {
    new_test_ext().execute_with(|| {
        let tracker = CoherenceTracker::default();
        assert_eq!(tracker.violation_rate_scaled(), 0);
    });
}

#[test]
fn boundary_positions_work() {
    new_test_ext().execute_with(|| {
        // Test all corners of 12x12 grid
        let corners = [
            ToroidalPosition::new(0, 0),
            ToroidalPosition::new(0, 11),
            ToroidalPosition::new(11, 0),
            ToroidalPosition::new(11, 11),
        ];

        for (i, &pos) in corners.iter().enumerate() {
            assert_ok!(TopologicalCoherence::register_entity(
                RuntimeOrigin::signed(ALICE),
                i as u32,
                pos,
            ));
        }

        assert_eq!(TopologicalCoherence::entity_count(ALICE), 4);
    });
}

#[test]
fn same_position_transition() {
    new_test_ext().execute_with(|| {
        let pos = ToroidalPosition::new(5, 5);

        assert_ok!(TopologicalCoherence::register_entity(
            RuntimeOrigin::signed(ALICE),
            0,
            pos,
        ));

        // Transition to same position (distance = 0)
        assert_ok!(TopologicalCoherence::submit_transition(
            RuntimeOrigin::signed(ALICE),
            0,
            pos,
        ));

        let tracker = TopologicalCoherence::tracker(ALICE, 0).expect("Tracker should exist");
        assert_eq!(tracker.transitions, 1);
        assert_eq!(tracker.violations, 0);
    });
}
