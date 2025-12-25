//! Unit tests for pallet-validator-entropy

use crate::{mock::*, Error, Event, EntropySourceType, DeviceType};
use frame_support::{assert_noop, assert_ok};

#[test]
fn register_entropy_config_works() {
    new_test_ext().execute_with(|| {
        // Initialize block number to 1 so events are emitted
        System::set_block_number(1);

        // Register entropy config
        assert_ok!(ValidatorEntropy::register_entropy_config(
            RuntimeOrigin::signed(1),
            EntropySourceType::QKD,
            vec![DeviceType::ToshibaQKD, DeviceType::Crypto4A],
            2,
        ));

        // Verify storage
        let config = ValidatorEntropy::validator_configs(1).unwrap();
        assert_eq!(config.source_type, EntropySourceType::QKD);
        assert_eq!(config.devices.len(), 2);
        assert_eq!(config.threshold_k, 2);
        assert_eq!(config.total_devices, 2);

        // Verify event
        System::assert_last_event(
            Event::EntropyConfigRegistered {
                validator: 1,
                source_type: EntropySourceType::QKD,
                threshold_k: 2,
                total_devices: 2,
            }
            .into(),
        );
    });
}

#[test]
fn register_entropy_config_can_update() {
    new_test_ext().execute_with(|| {
        // Register first time
        assert_ok!(ValidatorEntropy::register_entropy_config(
            RuntimeOrigin::signed(1),
            EntropySourceType::QKD,
            vec![DeviceType::ToshibaQKD],
            1,
        ));

        // Update registration (this is allowed - it updates existing config)
        assert_ok!(ValidatorEntropy::register_entropy_config(
            RuntimeOrigin::signed(1),
            EntropySourceType::Hybrid,
            vec![DeviceType::IdQuantiqueQKD, DeviceType::Crypto4A],
            2,
        ));

        // Verify updated config
        let config = ValidatorEntropy::validator_configs(1).unwrap();
        assert_eq!(config.source_type, EntropySourceType::Hybrid);
        assert_eq!(config.devices.len(), 2);
    });
}

#[test]
fn register_entropy_config_fails_with_too_many_devices() {
    new_test_ext().execute_with(|| {
        // Try to register with more devices than MaxDevices (10)
        let too_many_devices = vec![DeviceType::ToshibaQKD; 11];

        assert_noop!(
            ValidatorEntropy::register_entropy_config(
                RuntimeOrigin::signed(1),
                EntropySourceType::QKD,
                too_many_devices,
                2,
            ),
            Error::<Test>::TooManyDevices
        );
    });
}

#[test]
fn register_entropy_config_fails_with_invalid_threshold() {
    new_test_ext().execute_with(|| {
        // Threshold = 0
        assert_noop!(
            ValidatorEntropy::register_entropy_config(
                RuntimeOrigin::signed(1),
                EntropySourceType::QKD,
                vec![DeviceType::ToshibaQKD],
                0,
            ),
            Error::<Test>::ZeroThreshold
        );

        // Threshold > device count
        assert_noop!(
            ValidatorEntropy::register_entropy_config(
                RuntimeOrigin::signed(1),
                EntropySourceType::QKD,
                vec![DeviceType::ToshibaQKD],
                2,
            ),
            Error::<Test>::InvalidThreshold
        );
    });
}

#[test]
fn remove_entropy_config_works() {
    new_test_ext().execute_with(|| {
        // Initialize block number to 1 so events are emitted
        System::set_block_number(1);

        // Register first
        assert_ok!(ValidatorEntropy::register_entropy_config(
            RuntimeOrigin::signed(1),
            EntropySourceType::QKD,
            vec![DeviceType::ToshibaQKD],
            1,
        ));

        // Remove
        assert_ok!(ValidatorEntropy::remove_entropy_config(
            RuntimeOrigin::signed(1)
        ));

        // Verify removed
        assert!(ValidatorEntropy::validator_configs(1).is_none());

        // Verify event
        System::assert_last_event(
            Event::EntropyConfigRemoved { validator: 1 }.into(),
        );
    });
}

#[test]
fn remove_entropy_config_fails_when_not_registered() {
    new_test_ext().execute_with(|| {
        assert_noop!(
            ValidatorEntropy::remove_entropy_config(RuntimeOrigin::signed(1)),
            Error::<Test>::ConfigNotFound
        );
    });
}

#[test]
fn multiple_validators_can_register() {
    new_test_ext().execute_with(|| {
        // Register validator 1
        assert_ok!(ValidatorEntropy::register_entropy_config(
            RuntimeOrigin::signed(1),
            EntropySourceType::QKD,
            vec![DeviceType::ToshibaQKD],
            1,
        ));

        // Register validator 2
        assert_ok!(ValidatorEntropy::register_entropy_config(
            RuntimeOrigin::signed(2),
            EntropySourceType::HardwareRNG,
            vec![DeviceType::Crypto4A, DeviceType::EntropyKey],
            2,
        ));

        // Verify both registered
        assert!(ValidatorEntropy::validator_configs(1).is_some());
        assert!(ValidatorEntropy::validator_configs(2).is_some());

        let config1 = ValidatorEntropy::validator_configs(1).unwrap();
        let config2 = ValidatorEntropy::validator_configs(2).unwrap();

        assert_eq!(config1.source_type, EntropySourceType::QKD);
        assert_eq!(config2.source_type, EntropySourceType::HardwareRNG);
    });
}
