//! Unit tests for pallet-relay-coordination

use crate::{mock::*, Error, Event, Region, RelayStatus, Pallet as RelayCoordination};
use frame_support::{assert_noop, assert_ok};

#[test]
fn volunteer_as_relay_works() {
    new_test_ext().execute_with(|| {
        // Initialize block number to 1 so events are emitted
        System::set_block_number(1);

        let relay_account = 1;
        let region = Region::Asia;
        let max_bandwidth = 1_000_000u64;
        let ssh_key = vec![1u8; 32];

        // Volunteer as relay
        assert_ok!(RelayCoordination::<Test>::volunteer_as_relay(
            RuntimeOrigin::signed(relay_account),
            region.clone(),
            max_bandwidth,
            ssh_key.clone(),
            b"https://relay.example.com".to_vec(),
        ));

        // Verify storage
        let relay_info = RelayCoordination::<Test>::relay_candidates(relay_account).unwrap();
        assert_eq!(relay_info.region, region);
        assert_eq!(relay_info.max_bandwidth, max_bandwidth);
        assert_eq!(relay_info.status, RelayStatus::Candidate);
        assert_eq!(relay_info.stake, 1000); // MinRelayStake

        // Verify event
        System::assert_last_event(
            Event::RelayVolunteered {
                relay: relay_account,
                region,
                stake: 1000,
                max_bandwidth,
            }
            .into(),
        );
    });
}

#[test]
fn volunteer_as_relay_fails_when_already_registered() {
    new_test_ext().execute_with(|| {
        let relay_account = 1;

        // Register first time
        assert_ok!(RelayCoordination::<Test>::volunteer_as_relay(
            RuntimeOrigin::signed(relay_account),
            Region::Asia,
            1_000_000u64,
            vec![1u8; 32],
            b"https://relay1.example.com".to_vec(),
        ));

        // Try to register again
        assert_noop!(
            RelayCoordination::<Test>::volunteer_as_relay(
                RuntimeOrigin::signed(relay_account),
                Region::Europe,
                1_000_000u64,
                vec![2u8; 32],
                b"https://relay2.example.com".to_vec(),
            ),
            Error::<Test>::AlreadyRegistered
        );
    });
}

#[test]
fn volunteer_as_relay_fails_with_invalid_ssh_key() {
    new_test_ext().execute_with(|| {
        // Empty SSH key
        assert_noop!(
            RelayCoordination::<Test>::volunteer_as_relay(
                RuntimeOrigin::signed(1),
                Region::Asia,
                1_000_000u64,
                vec![],
                b"https://relay.example.com".to_vec(),
            ),
            Error::<Test>::InvalidSshPublicKey
        );

        // SSH key too long (> 256 bytes)
        assert_noop!(
            RelayCoordination::<Test>::volunteer_as_relay(
                RuntimeOrigin::signed(1),
                Region::Asia,
                1_000_000u64,
                vec![1u8; 257],
                b"https://relay.example.com".to_vec(),
            ),
            Error::<Test>::InvalidSshPublicKey
        );
    });
}

#[test]
fn volunteer_as_relay_fails_with_insufficient_balance() {
    new_test_ext().execute_with(|| {
        let poor_account = 99; // Account not in genesis config

        assert_noop!(
            RelayCoordination::<Test>::volunteer_as_relay(
                RuntimeOrigin::signed(poor_account),
                Region::Asia,
                1_000_000u64,
                vec![1u8; 32],
                b"https://relay.example.com".to_vec(),
            ),
            Error::<Test>::InsufficientStake
        );
    });
}

#[test]
fn deregister_relay_works() {
    new_test_ext().execute_with(|| {
        // Initialize block number to 1 so events are emitted
        System::set_block_number(1);

        let relay_account = 1;

        // Register first
        assert_ok!(RelayCoordination::<Test>::volunteer_as_relay(
            RuntimeOrigin::signed(relay_account),
            Region::Asia,
            1_000_000u64,
            vec![1u8; 32],
            b"https://relay.example.com".to_vec(),
        ));

        // Deregister
        assert_ok!(RelayCoordination::<Test>::deregister_relay(
            RuntimeOrigin::signed(relay_account)
        ));

        // Verify removed
        assert!(RelayCoordination::<Test>::relay_candidates(relay_account).is_none());

        // Verify event
        System::assert_last_event(
            Event::RelayDeregistered {
                relay: relay_account,
            }
            .into(),
        );
    });
}

#[test]
fn deregister_relay_fails_when_not_registered() {
    new_test_ext().execute_with(|| {
        assert_noop!(
            RelayCoordination::<Test>::deregister_relay(RuntimeOrigin::signed(1)),
            Error::<Test>::NotRegistered
        );
    });
}

#[test]
fn report_relay_metrics_works() {
    new_test_ext().execute_with(|| {
        // Initialize block number to 1 so events are emitted
        System::set_block_number(1);

        let relay_account = 1;

        // Register relay first
        assert_ok!(RelayCoordination::<Test>::volunteer_as_relay(
            RuntimeOrigin::signed(relay_account),
            Region::Asia,
            1_000_000u64,
            vec![1u8; 32],
            b"https://relay.example.com".to_vec(),
        ));

        // Report metrics (relay reports its own metrics)
        assert_ok!(RelayCoordination::<Test>::report_relay_metrics(
            RuntimeOrigin::signed(relay_account),
            relay_account,
            100, // successful_connections
            5,   // failed_connections
            95,  // uptime_percentage
        ));

        // Verify metrics updated
        let relay_info = RelayCoordination::<Test>::relay_candidates(relay_account).unwrap();
        assert_eq!(relay_info.total_connections, 100);
        assert_eq!(relay_info.failed_connections, 5);
        assert_eq!(relay_info.uptime_percentage, 95);

        // Verify event
        System::assert_last_event(
            Event::RelayMetricsUpdated {
                relay: relay_account,
                uptime_percentage: 95,
                total_connections: 100,
            }
            .into(),
        );
    });
}

#[test]
fn report_relay_metrics_fails_when_not_registered() {
    new_test_ext().execute_with(|| {
        let unregistered_relay = 99;
        assert_noop!(
            RelayCoordination::<Test>::report_relay_metrics(
                RuntimeOrigin::signed(unregistered_relay),
                unregistered_relay, // unregistered relay
                100,
                5,
                95,
            ),
            Error::<Test>::NotRegistered
        );
    });
}

#[test]
fn low_uptime_triggers_slash() {
    new_test_ext().execute_with(|| {
        // Initialize block number to 1 so events are emitted
        System::set_block_number(1);

        let relay_account = 1;

        // Register relay
        assert_ok!(RelayCoordination::<Test>::volunteer_as_relay(
            RuntimeOrigin::signed(relay_account),
            Region::Asia,
            1_000_000u64,
            vec![1u8; 32],
            b"https://relay.example.com".to_vec(),
        ));

        // Report low uptime (< MinUptimePercentage of 80%) - relay reports its own metrics
        assert_ok!(RelayCoordination::<Test>::report_relay_metrics(
            RuntimeOrigin::signed(relay_account),
            relay_account,
            50,
            50,
            50, // 50% uptime
        ));

        // Verify relay was slashed
        let relay_info = RelayCoordination::<Test>::relay_candidates(relay_account).unwrap();
        assert_eq!(relay_info.status, RelayStatus::Slashed);

        // Verify slash event was emitted
        let events = System::events();
        assert!(events.iter().any(|e| matches!(
            e.event,
            RuntimeEvent::RelayCoordination(Event::RelaySlashed { .. })
        )));
    });
}

#[test]
fn multiple_relays_can_volunteer() {
    new_test_ext().execute_with(|| {
        // Register relay 1 in Asia
        assert_ok!(RelayCoordination::<Test>::volunteer_as_relay(
            RuntimeOrigin::signed(1),
            Region::Asia,
            1_000_000u64,
            vec![1u8; 32],
            b"https://relay1.example.com".to_vec(),
        ));

        // Register relay 2 in Europe
        assert_ok!(RelayCoordination::<Test>::volunteer_as_relay(
            RuntimeOrigin::signed(2),
            Region::Europe,
            2_000_000u64,
            vec![2u8; 32],
            b"https://relay2.example.com".to_vec(),
        ));

        // Verify both registered
        assert!(RelayCoordination::<Test>::relay_candidates(1).is_some());
        assert!(RelayCoordination::<Test>::relay_candidates(2).is_some());

        let relay1 = RelayCoordination::<Test>::relay_candidates(1).unwrap();
        let relay2 = RelayCoordination::<Test>::relay_candidates(2).unwrap();

        assert_eq!(relay1.region, Region::Asia);
        assert_eq!(relay2.region, Region::Europe);
        assert_eq!(relay1.max_bandwidth, 1_000_000);
        assert_eq!(relay2.max_bandwidth, 2_000_000);
    });
}

#[test]
fn is_active_relay_works() {
    new_test_ext().execute_with(|| {
        let relay_account = 1;

        // Not active initially
        assert!(!RelayCoordination::<Test>::is_active_relay(&relay_account));

        // Register relay
        assert_ok!(RelayCoordination::<Test>::volunteer_as_relay(
            RuntimeOrigin::signed(relay_account),
            Region::Asia,
            1_000_000u64,
            vec![1u8; 32],
            b"https://relay.example.com".to_vec(),
        ));

        // Still not active (status is Candidate, not Active)
        assert!(!RelayCoordination::<Test>::is_active_relay(&relay_account));

        // Manually set to Active status for testing
        crate::RelayCandidates::<Test>::mutate(relay_account, |maybe_info| {
            if let Some(info) = maybe_info {
                info.status = RelayStatus::Active;
            }
        });

        // Now is active
        assert!(RelayCoordination::<Test>::is_active_relay(&relay_account));
    });
}
