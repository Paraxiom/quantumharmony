//! Benchmarking for pallet-topological-coherence

#![cfg(feature = "runtime-benchmarks")]

use super::*;
use crate::Pallet as TopologicalCoherence;
use frame_benchmarking::v2::*;
use frame_system::RawOrigin;

#[benchmarks]
mod benchmarks {
    use super::*;

    #[benchmark]
    fn register_entity() {
        let caller: T::AccountId = whitelisted_caller();
        let entity_id = 0u32;
        let position = ToroidalPosition::new(5, 7);

        #[extrinsic_call]
        _(RawOrigin::Signed(caller.clone()), entity_id, position);

        // Verify the entity was registered
        assert!(Trackers::<T>::contains_key(&caller, entity_id));
        assert_eq!(EntityCount::<T>::get(&caller), 1);
    }

    #[benchmark]
    fn submit_transition() {
        let caller: T::AccountId = whitelisted_caller();
        let entity_id = 0u32;
        let initial_position = ToroidalPosition::new(0, 0);
        let new_position = ToroidalPosition::new(1, 1);

        // Setup: register an entity first
        TopologicalCoherence::<T>::register_entity(
            RawOrigin::Signed(caller.clone()).into(),
            entity_id,
            initial_position,
        )
        .unwrap();

        #[extrinsic_call]
        _(RawOrigin::Signed(caller.clone()), entity_id, new_position);

        // Verify the transition was recorded
        let tracker = Trackers::<T>::get(&caller, entity_id).unwrap();
        assert_eq!(tracker.position, new_position);
        assert_eq!(tracker.transitions, 1);
    }

    #[benchmark]
    fn submit_transition_violation() {
        let caller: T::AccountId = whitelisted_caller();
        let entity_id = 0u32;
        let initial_position = ToroidalPosition::new(0, 0);
        // Large jump that exceeds drift threshold (default = 2)
        let new_position = ToroidalPosition::new(6, 6);

        // Setup: register an entity first
        TopologicalCoherence::<T>::register_entity(
            RawOrigin::Signed(caller.clone()).into(),
            entity_id,
            initial_position,
        )
        .unwrap();

        #[extrinsic_call]
        submit_transition(RawOrigin::Signed(caller.clone()), entity_id, new_position);

        // Verify the violation was recorded
        let tracker = Trackers::<T>::get(&caller, entity_id).unwrap();
        assert_eq!(tracker.violations, 1);
    }

    #[benchmark]
    fn update_config() {
        let new_config = CoherenceConfig {
            grid_size: 16,
            drift_threshold: 3,
            max_violation_rate: 150,
            min_transitions: 20,
        };

        #[extrinsic_call]
        _(RawOrigin::Root, new_config);

        // Verify config was updated
        assert_eq!(GlobalConfig::<T>::get(), new_config);
    }

    #[benchmark]
    fn unflag_account() {
        let account: T::AccountId = whitelisted_caller();

        // Setup: flag the account first
        Flagged::<T>::insert(&account, true);

        #[extrinsic_call]
        _(RawOrigin::Root, account.clone());

        // Verify account was unflagged
        assert!(!Flagged::<T>::get(&account));
    }

    impl_benchmark_test_suite!(
        TopologicalCoherence,
        crate::mock::new_test_ext(),
        crate::mock::Test
    );
}
