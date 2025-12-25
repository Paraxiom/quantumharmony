//! Benchmarking for pallet-relay-coordination

#![cfg(feature = "runtime-benchmarks")]

use super::*;
use crate::Pallet as RelayCoordination;
use frame_benchmarking::v2::*;
use frame_support::traits::Currency;
use frame_system::RawOrigin;
use sp_std::vec;

#[benchmarks]
mod benchmarks {
    use super::*;

    #[benchmark]
    fn volunteer_as_relay() {
        let caller: T::AccountId = whitelisted_caller();

        // Give the caller enough balance to stake
        let stake = T::MinRelayStake::get();
        let balance = stake * 10u32.into();
        T::Currency::make_free_balance_be(&caller, balance);

        // Prepare test data
        let region = Region::Asia;
        let max_bandwidth = 1_000_000u64;
        let ssh_public_key = vec![1u8; 32];

        #[extrinsic_call]
        _(RawOrigin::Signed(caller.clone()), region, max_bandwidth, ssh_public_key);

        // Verify the relay was registered
        assert!(RelayCandidates::<T>::contains_key(&caller));
    }

    #[benchmark]
    fn deregister_relay() {
        let caller: T::AccountId = whitelisted_caller();

        // Setup: register a relay first
        let stake = T::MinRelayStake::get();
        let balance = stake * 10u32.into();
        T::Currency::make_free_balance_be(&caller, balance);

        RelayCoordination::<T>::volunteer_as_relay(
            RawOrigin::Signed(caller.clone()).into(),
            Region::Asia,
            1_000_000u64,
            vec![1u8; 32],
        ).unwrap();

        #[extrinsic_call]
        _(RawOrigin::Signed(caller.clone()));

        // Verify the relay was removed
        assert!(!RelayCandidates::<T>::contains_key(&caller));
    }

    #[benchmark]
    fn report_relay_metrics() {
        let caller: T::AccountId = whitelisted_caller();
        let relay: T::AccountId = account("relay", 0, 0);

        // Setup: register a relay first
        let stake = T::MinRelayStake::get();
        let balance = stake * 10u32.into();
        T::Currency::make_free_balance_be(&relay, balance);

        RelayCoordination::<T>::volunteer_as_relay(
            RawOrigin::Signed(relay.clone()).into(),
            Region::Asia,
            1_000_000u64,
            vec![1u8; 32],
        ).unwrap();

        let successful_connections = 100u32;
        let failed_connections = 5u32;
        let uptime_percentage = 95u8;

        #[extrinsic_call]
        _(RawOrigin::Signed(caller), relay.clone(), successful_connections, failed_connections, uptime_percentage);

        // Verify metrics were updated
        let info = RelayCandidates::<T>::get(&relay).unwrap();
        assert!(info.total_connections > 0);
    }

    impl_benchmark_test_suite!(
        RelayCoordination,
        crate::mock::new_test_ext(),
        crate::mock::Test
    );
}
