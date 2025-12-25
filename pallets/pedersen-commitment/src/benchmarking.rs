//! Benchmarking setup for pallet-pedersen-commitment

use super::*;
use frame_benchmarking::{benchmarks, whitelisted_caller};
use frame_system::RawOrigin;

#[allow(unused)]
use crate::Pallet as PedersenCommitment;

benchmarks! {
	commit {
		let caller: T::AccountId = whitelisted_caller();
		let commitment_id = [1u8; 32];
		let entropy = [42u8; 32];
		let blinding = [99u8; 32];
		let commitment_point = Pallet::<T>::create_commitment_point(&entropy, &blinding);
		let commitment_bytes = commitment_point.to_compressed();
	}: _(RawOrigin::Signed(caller.clone()), commitment_id, commitment_bytes)
	verify {
		assert!(Commitments::<T>::contains_key(&caller, &commitment_id));
	}

	reveal {
		let caller: T::AccountId = whitelisted_caller();
		let commitment_id = [1u8; 32];
		let entropy = [42u8; 32];
		let blinding = [99u8; 32];

		// Setup: create commitment first
		let commitment_point = Pallet::<T>::create_commitment_point(&entropy, &blinding);
		let commitment_bytes = commitment_point.to_compressed();

		PedersenCommitment::<T>::commit(
			RawOrigin::Signed(caller.clone()).into(),
			commitment_id,
			commitment_bytes
		)?;

		// Advance block
		frame_system::Pallet::<T>::set_block_number(2u32.into());
	}: _(RawOrigin::Signed(caller.clone()), commitment_id, entropy, blinding)
	verify {
		assert!(Reveals::<T>::contains_key(&caller, &commitment_id));
	}

	impl_benchmark_test_suite!(PedersenCommitment, crate::tests::new_test_ext(), crate::tests::Test);
}
