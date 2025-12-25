//! Benchmarking for pallet-validator-entropy

#![cfg(feature = "runtime-benchmarks")]

use super::*;
use crate::Pallet as ValidatorEntropy;
use frame_benchmarking::v2::*;
use frame_system::RawOrigin;
use sp_std::vec;

#[benchmarks]
mod benchmarks {
    use super::*;

    #[benchmark]
    fn register_entropy_config() {
        let caller: T::AccountId = whitelisted_caller();

        // Prepare test data
        let source_type = EntropySourceType::QKD;
        let devices = vec![DeviceType::ToshibaQKD, DeviceType::Crypto4A];
        let threshold_k = 2u8;

        #[extrinsic_call]
        _(RawOrigin::Signed(caller.clone()), source_type, devices, threshold_k);

        // Verify the config was registered
        assert!(ValidatorConfigs::<T>::contains_key(&caller));
    }

    #[benchmark]
    fn remove_entropy_config() {
        let caller: T::AccountId = whitelisted_caller();

        // Setup: register a config first
        let source_type = EntropySourceType::QKD;
        let devices = vec![DeviceType::ToshibaQKD];
        ValidatorEntropy::<T>::register_entropy_config(
            RawOrigin::Signed(caller.clone()).into(),
            source_type,
            devices,
            1u8,
        ).unwrap();

        #[extrinsic_call]
        _(RawOrigin::Signed(caller.clone()));

        // Verify the config was removed
        assert!(!ValidatorConfigs::<T>::contains_key(&caller));
    }

    impl_benchmark_test_suite!(
        ValidatorEntropy,
        crate::mock::new_test_ext(),
        crate::mock::Test
    );
}
