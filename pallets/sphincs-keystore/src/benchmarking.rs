//! Benchmarking setup for pallet-sphincs-keystore
//!
//! Measures weight of:
//! - `register_key`: SPHINCS+ public key registration (Keccak-256 hash + StorageMap insert)
//! - `mark_hsm_anchored`: HSM anchor status update (root-only, StorageMap insert)

use super::*;
use frame_benchmarking::{benchmarks, whitelisted_caller};
use frame_system::RawOrigin;
use sp_core::sphincs::Pair as SphincsPair;
use sp_core::Pair;

#[allow(unused)]
use crate::Pallet as SphincsKeystore;

benchmarks! {
	register_key {
		// Generate a real SPHINCS+ keypair so the Keccak-256 derivation matches
		let (pair, _seed) = SphincsPair::generate();
		let public_key = pair.public();
		let caller = Pallet::<T>::derive_account_id(&public_key);
		// Whitelist the caller account for DB read/write cost exclusion
		frame_system::Pallet::<T>::inc_providers(&caller);
	}: _(RawOrigin::Signed(caller.clone()), public_key)
	verify {
		assert!(PublicKeys::<T>::contains_key(&caller));
	}

	mark_hsm_anchored {
		// Setup: register a key first so mark_hsm_anchored doesn't fail
		let (pair, _seed) = SphincsPair::generate();
		let public_key = pair.public();
		let account = Pallet::<T>::derive_account_id(&public_key);
		frame_system::Pallet::<T>::inc_providers(&account);
		Pallet::<T>::register_key(
			RawOrigin::Signed(account.clone()).into(),
			public_key,
		)?;
		let hsm_key_id = b"hsm-bench-key-001".to_vec();
	}: _(RawOrigin::Root, account.clone(), hsm_key_id)
	verify {
		let status = HsmAnchors::<T>::get(&account);
		assert!(status.anchored);
	}

	impl_benchmark_test_suite!(SphincsKeystore, crate::tests::new_test_ext(), crate::tests::Test);
}
