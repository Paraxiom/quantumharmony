//! Benchmarking for pallet-sphincs-keystore

#![cfg(feature = "runtime-benchmarks")]

use super::*;
use crate::Pallet as SphincsKeystore;
use frame_benchmarking::v2::*;
use frame_system::RawOrigin;
use sp_core::sphincs::Pair as SphincsPair;

#[benchmarks]
mod benchmarks {
    use super::*;

    /// Benchmark for register_key extrinsic
    /// This stores a SPHINCS+ public key mapping for an account
    #[benchmark]
    fn register_key() {
        // Generate a SPHINCS+ keypair
        let (pair, _seed) = SphincsPair::generate();
        let public_key = pair.public();

        // Derive the account ID from the public key
        let account = SphincsKeystore::<T>::derive_account_id(&public_key);

        #[extrinsic_call]
        _(RawOrigin::Signed(account.clone()), public_key);

        // Verify the key was registered
        assert!(PublicKeys::<T>::contains_key(&account));
    }

    /// Benchmark for mark_hsm_anchored extrinsic
    /// This marks a registered key as anchored to an HSM
    #[benchmark]
    fn mark_hsm_anchored() {
        // Setup: first register a key
        let (pair, _seed) = SphincsPair::generate();
        let public_key = pair.public();
        let account = SphincsKeystore::<T>::derive_account_id(&public_key);

        // Register the key first
        PublicKeys::<T>::insert(&account, public_key);

        // Prepare HSM key ID
        let hsm_key_id = vec![1u8; 32];
        let bounded_key_id =
            BoundedVec::<u8, MaxHsmKeyIdLen>::try_from(hsm_key_id.clone()).unwrap();

        // Set initial anchor status
        let status = HsmAnchorStatus {
            anchored: false,
            hsm_key_id: None,
            last_sync: 0,
        };
        HsmAnchors::<T>::insert(&account, status);

        #[extrinsic_call]
        _(RawOrigin::Root, account.clone(), hsm_key_id);

        // Verify the key was marked as anchored
        let stored_status = HsmAnchors::<T>::get(&account);
        assert!(stored_status.anchored);
        assert!(stored_status.hsm_key_id.is_some());
    }

    impl_benchmark_test_suite!(
        SphincsKeystore,
        crate::tests::new_test_ext(),
        crate::tests::Test
    );
}
        crate::tests::Test
    );
}
