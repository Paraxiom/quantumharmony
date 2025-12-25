//! Unit tests for Pedersen commitment pallet
//!
//! Tests cover:
//! 1. Commitment creation and storage
//! 2. Reveal verification (correct and incorrect)
//! 3. Information-theoretic hiding property
//! 4. Binding property
//! 5. Timing constraints (reveal must be after commit)
//! 6. Edge cases (invalid inputs, double commits, etc.)

use crate::{self as pallet_pedersen_commitment, *};
use frame_support::{
	assert_noop, assert_ok,
	traits::{ConstU16, ConstU32, ConstU64},
};
use sp_core::H256;
use sp_runtime::{
	traits::{BlakeTwo256, IdentityLookup},
	BuildStorage,
};

type Block = frame_system::mocking::MockBlock<Test>;

// Configure a mock runtime to test the pallet
frame_support::construct_runtime!(
	pub enum Test
	{
		System: frame_system,
		PedersenCommitment: pallet_pedersen_commitment,
	}
);

impl frame_system::Config for Test {
	type BaseCallFilter = frame_support::traits::Everything;
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = ();
	type RuntimeOrigin = RuntimeOrigin;
	type RuntimeCall = RuntimeCall;
	type Nonce = u64;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Block = Block;
	type RuntimeEvent = RuntimeEvent;
	type BlockHashCount = ConstU64<250>;
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = ();
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ConstU16<42>;
	type OnSetCode = ();
	type MaxConsumers = ConstU32<16>;
}

impl Config for Test {
	type RuntimeEvent = RuntimeEvent;
}

// Helper function to create test environment
fn new_test_ext() -> sp_io::TestExternalities {
	let t = frame_system::GenesisConfig::<Test>::default()
		.build_storage()
		.unwrap();
	let mut ext = sp_io::TestExternalities::new(t);
	ext.execute_with(|| System::set_block_number(1));
	ext
}

// Helper to advance blocks
fn advance_blocks(n: u64) {
	for _ in 0..n {
		let current = System::block_number();
		System::set_block_number(current + 1);
	}
}

#[test]
fn test_create_commitment_point_deterministic() {
	new_test_ext().execute_with(|| {
		// Test that create_commitment_point is deterministic
		let entropy = [42u8; 32];
		let blinding = [99u8; 32];

		let commitment1 = Pallet::<Test>::create_commitment_point(&entropy, &blinding);
		let commitment2 = Pallet::<Test>::create_commitment_point(&entropy, &blinding);

		assert_eq!(
			commitment1, commitment2,
			"Same entropy and blinding should produce same commitment"
		);
	});
}

#[test]
fn test_create_commitment_point_different_entropy() {
	new_test_ext().execute_with(|| {
		// Different entropy should produce different commitments
		let entropy1 = [42u8; 32];
		let entropy2 = [43u8; 32];
		let blinding = [99u8; 32];

		let commitment1 = Pallet::<Test>::create_commitment_point(&entropy1, &blinding);
		let commitment2 = Pallet::<Test>::create_commitment_point(&entropy2, &blinding);

		assert_ne!(
			commitment1, commitment2,
			"Different entropy should produce different commitments"
		);
	});
}

#[test]
fn test_create_commitment_point_different_blinding() {
	new_test_ext().execute_with(|| {
		// Different blinding should produce different commitments
		let entropy = [42u8; 32];
		let blinding1 = [99u8; 32];
		let blinding2 = [100u8; 32];

		let commitment1 = Pallet::<Test>::create_commitment_point(&entropy, &blinding1);
		let commitment2 = Pallet::<Test>::create_commitment_point(&entropy, &blinding2);

		assert_ne!(
			commitment1, commitment2,
			"Different blinding should produce different commitments"
		);
	});
}

#[test]
fn test_commit_and_store() {
	new_test_ext().execute_with(|| {
		let validator = 1u64;
		let commitment_id = [1u8; 32];
		let entropy = [42u8; 32];
		let blinding = [99u8; 32];

		// Create commitment
		let commitment_point = Pallet::<Test>::create_commitment_point(&entropy, &blinding);
		let commitment_bytes = commitment_point.to_compressed();

		// Submit commitment
		assert_ok!(PedersenCommitment::commit(
			RuntimeOrigin::signed(validator),
			commitment_id,
			commitment_bytes
		));

		// Verify storage
		let stored_commitment = Commitments::<Test>::get(validator, commitment_id);
		assert!(stored_commitment.is_some(), "Commitment should be stored");
		assert_eq!(
			stored_commitment.unwrap().commitment,
			commitment_bytes,
			"Stored commitment should match"
		);

		// Verify block number stored
		let stored_block = CommitmentBlocks::<Test>::get(validator, commitment_id);
		assert_eq!(stored_block, Some(1), "Block number should be stored");
	});
}

#[test]
fn test_commit_duplicate_fails() {
	new_test_ext().execute_with(|| {
		let validator = 1u64;
		let commitment_id = [1u8; 32];
		let entropy = [42u8; 32];
		let blinding = [99u8; 32];

		let commitment_point = Pallet::<Test>::create_commitment_point(&entropy, &blinding);
		let commitment_bytes = commitment_point.to_compressed();

		// First commit succeeds
		assert_ok!(PedersenCommitment::commit(
			RuntimeOrigin::signed(validator),
			commitment_id,
			commitment_bytes
		));

		// Second commit with same ID fails
		assert_noop!(
			PedersenCommitment::commit(
				RuntimeOrigin::signed(validator),
				commitment_id,
				commitment_bytes
			),
			Error::<Test>::CommitmentAlreadyExists
		);
	});
}

#[test]
fn test_verify_commitment_correct() {
	new_test_ext().execute_with(|| {
		let entropy = [42u8; 32];
		let blinding = [99u8; 32];

		// Create commitment
		let commitment_point = Pallet::<Test>::create_commitment_point(&entropy, &blinding);
		let commitment_bytes = commitment_point.to_compressed();

		// Verify should succeed
		let is_valid = Pallet::<Test>::verify_commitment(&commitment_bytes, &entropy, &blinding);
		assert!(is_valid, "Valid reveal should verify correctly");
	});
}

#[test]
fn test_verify_commitment_wrong_entropy() {
	new_test_ext().execute_with(|| {
		let entropy = [42u8; 32];
		let wrong_entropy = [43u8; 32];
		let blinding = [99u8; 32];

		// Create commitment with correct entropy
		let commitment_point = Pallet::<Test>::create_commitment_point(&entropy, &blinding);
		let commitment_bytes = commitment_point.to_compressed();

		// Verify with wrong entropy should fail
		let is_valid =
			Pallet::<Test>::verify_commitment(&commitment_bytes, &wrong_entropy, &blinding);
		assert!(!is_valid, "Wrong entropy should fail verification");
	});
}

#[test]
fn test_verify_commitment_wrong_blinding() {
	new_test_ext().execute_with(|| {
		let entropy = [42u8; 32];
		let blinding = [99u8; 32];
		let wrong_blinding = [100u8; 32];

		// Create commitment with correct blinding
		let commitment_point = Pallet::<Test>::create_commitment_point(&entropy, &blinding);
		let commitment_bytes = commitment_point.to_compressed();

		// Verify with wrong blinding should fail
		let is_valid =
			Pallet::<Test>::verify_commitment(&commitment_bytes, &entropy, &wrong_blinding);
		assert!(!is_valid, "Wrong blinding should fail verification");
	});
}

#[test]
fn test_reveal_success() {
	new_test_ext().execute_with(|| {
		let validator = 1u64;
		let commitment_id = [1u8; 32];
		let entropy = [42u8; 32];
		let blinding = [99u8; 32];

		// Create and submit commitment
		let commitment_point = Pallet::<Test>::create_commitment_point(&entropy, &blinding);
		let commitment_bytes = commitment_point.to_compressed();

		assert_ok!(PedersenCommitment::commit(
			RuntimeOrigin::signed(validator),
			commitment_id,
			commitment_bytes
		));

		// Advance at least 1 block
		advance_blocks(1);

		// Reveal should succeed
		assert_ok!(PedersenCommitment::reveal(
			RuntimeOrigin::signed(validator),
			commitment_id,
			entropy,
			blinding
		));

		// Verify reveal stored
		let stored_reveal = Reveals::<Test>::get(validator, commitment_id);
		assert!(stored_reveal.is_some(), "Reveal should be stored");
		let reveal = stored_reveal.unwrap();
		assert_eq!(reveal.entropy, entropy, "Entropy should match");
		assert_eq!(reveal.blinding, blinding, "Blinding should match");
	});
}

#[test]
fn test_reveal_too_early_fails() {
	new_test_ext().execute_with(|| {
		let validator = 1u64;
		let commitment_id = [1u8; 32];
		let entropy = [42u8; 32];
		let blinding = [99u8; 32];

		// Create and submit commitment
		let commitment_point = Pallet::<Test>::create_commitment_point(&entropy, &blinding);
		let commitment_bytes = commitment_point.to_compressed();

		assert_ok!(PedersenCommitment::commit(
			RuntimeOrigin::signed(validator),
			commitment_id,
			commitment_bytes
		));

		// Try to reveal in same block (should fail)
		assert_noop!(
			PedersenCommitment::reveal(
				RuntimeOrigin::signed(validator),
				commitment_id,
				entropy,
				blinding
			),
			Error::<Test>::RevealTooEarly
		);
	});
}

#[test]
fn test_reveal_nonexistent_commitment_fails() {
	new_test_ext().execute_with(|| {
		let validator = 1u64;
		let commitment_id = [1u8; 32];
		let entropy = [42u8; 32];
		let blinding = [99u8; 32];

		// Try to reveal without committing first
		assert_noop!(
			PedersenCommitment::reveal(
				RuntimeOrigin::signed(validator),
				commitment_id,
				entropy,
				blinding
			),
			Error::<Test>::CommitmentNotFound
		);
	});
}

#[test]
fn test_reveal_wrong_entropy_fails() {
	new_test_ext().execute_with(|| {
		let validator = 1u64;
		let commitment_id = [1u8; 32];
		let entropy = [42u8; 32];
		let wrong_entropy = [43u8; 32];
		let blinding = [99u8; 32];

		// Create and submit commitment with correct entropy
		let commitment_point = Pallet::<Test>::create_commitment_point(&entropy, &blinding);
		let commitment_bytes = commitment_point.to_compressed();

		assert_ok!(PedersenCommitment::commit(
			RuntimeOrigin::signed(validator),
			commitment_id,
			commitment_bytes
		));

		advance_blocks(1);

		// Try to reveal with wrong entropy (should fail)
		assert_noop!(
			PedersenCommitment::reveal(
				RuntimeOrigin::signed(validator),
				commitment_id,
				wrong_entropy,
				blinding
			),
			Error::<Test>::RevealMismatch
		);
	});
}

#[test]
fn test_reveal_wrong_blinding_fails() {
	new_test_ext().execute_with(|| {
		let validator = 1u64;
		let commitment_id = [1u8; 32];
		let entropy = [42u8; 32];
		let blinding = [99u8; 32];
		let wrong_blinding = [100u8; 32];

		// Create and submit commitment with correct blinding
		let commitment_point = Pallet::<Test>::create_commitment_point(&entropy, &blinding);
		let commitment_bytes = commitment_point.to_compressed();

		assert_ok!(PedersenCommitment::commit(
			RuntimeOrigin::signed(validator),
			commitment_id,
			commitment_bytes
		));

		advance_blocks(1);

		// Try to reveal with wrong blinding (should fail)
		assert_noop!(
			PedersenCommitment::reveal(
				RuntimeOrigin::signed(validator),
				commitment_id,
				entropy,
				wrong_blinding
			),
			Error::<Test>::RevealMismatch
		);
	});
}

#[test]
fn test_double_reveal_fails() {
	new_test_ext().execute_with(|| {
		let validator = 1u64;
		let commitment_id = [1u8; 32];
		let entropy = [42u8; 32];
		let blinding = [99u8; 32];

		// Create and submit commitment
		let commitment_point = Pallet::<Test>::create_commitment_point(&entropy, &blinding);
		let commitment_bytes = commitment_point.to_compressed();

		assert_ok!(PedersenCommitment::commit(
			RuntimeOrigin::signed(validator),
			commitment_id,
			commitment_bytes
		));

		advance_blocks(1);

		// First reveal succeeds
		assert_ok!(PedersenCommitment::reveal(
			RuntimeOrigin::signed(validator),
			commitment_id,
			entropy,
			blinding
		));

		advance_blocks(1);

		// Second reveal fails
		assert_noop!(
			PedersenCommitment::reveal(
				RuntimeOrigin::signed(validator),
				commitment_id,
				entropy,
				blinding
			),
			Error::<Test>::AlreadyRevealed
		);
	});
}

#[test]
fn test_multiple_validators_same_commitment_id() {
	new_test_ext().execute_with(|| {
		let validator1 = 1u64;
		let validator2 = 2u64;
		let commitment_id = [1u8; 32]; // Same ID
		let entropy1 = [42u8; 32];
		let entropy2 = [43u8; 32];
		let blinding1 = [99u8; 32];
		let blinding2 = [100u8; 32];

		// Validator 1 commits
		let commitment1 = Pallet::<Test>::create_commitment_point(&entropy1, &blinding1);
		assert_ok!(PedersenCommitment::commit(
			RuntimeOrigin::signed(validator1),
			commitment_id,
			commitment1.to_compressed()
		));

		// Validator 2 can commit with same ID (different validator)
		let commitment2 = Pallet::<Test>::create_commitment_point(&entropy2, &blinding2);
		assert_ok!(PedersenCommitment::commit(
			RuntimeOrigin::signed(validator2),
			commitment_id,
			commitment2.to_compressed()
		));

		advance_blocks(1);

		// Both can reveal independently
		assert_ok!(PedersenCommitment::reveal(
			RuntimeOrigin::signed(validator1),
			commitment_id,
			entropy1,
			blinding1
		));

		assert_ok!(PedersenCommitment::reveal(
			RuntimeOrigin::signed(validator2),
			commitment_id,
			entropy2,
			blinding2
		));
	});
}

#[test]
fn test_information_theoretic_hiding() {
	new_test_ext().execute_with(|| {
		// Two different (entropy, blinding) pairs should produce different commitments
		// This demonstrates that without the blinding factor, entropy is hidden

		let entropy1 = [42u8; 32];
		let blinding1 = [99u8; 32];

		let entropy2 = [42u8; 32]; // Same entropy
		let blinding2 = [100u8; 32]; // Different blinding

		let commitment1 = Pallet::<Test>::create_commitment_point(&entropy1, &blinding1);
		let commitment2 = Pallet::<Test>::create_commitment_point(&entropy2, &blinding2);

		assert_ne!(
			commitment1, commitment2,
			"Same entropy with different blinding should produce different commitments (hiding property)"
		);
	});
}

#[test]
fn test_binding_property() {
	new_test_ext().execute_with(|| {
		// Once committed, validator cannot reveal different entropy
		let entropy_original = [42u8; 32];
		let entropy_fake = [99u8; 32];
		let blinding = [88u8; 32];

		// Create commitment with original entropy
		let commitment = Pallet::<Test>::create_commitment_point(&entropy_original, &blinding);
		let commitment_bytes = commitment.to_compressed();

		// Try to verify with fake entropy (should fail)
		let is_valid = Pallet::<Test>::verify_commitment(&commitment_bytes, &entropy_fake, &blinding);
		assert!(
			!is_valid,
			"Cannot reveal different entropy than committed (binding property)"
		);

		// Verify with original entropy (should succeed)
		let is_valid_original =
			Pallet::<Test>::verify_commitment(&commitment_bytes, &entropy_original, &blinding);
		assert!(is_valid_original, "Original entropy should verify");
	});
}

#[test]
fn test_bytes_to_scalar_consistency() {
	new_test_ext().execute_with(|| {
		let bytes = [42u8; 32];
		let scalar1 = Pallet::<Test>::bytes_to_scalar(&bytes);
		let scalar2 = Pallet::<Test>::bytes_to_scalar(&bytes);

		assert_eq!(
			scalar1, scalar2,
			"bytes_to_scalar should be deterministic"
		);
	});
}

#[test]
fn test_hash_to_g1_deterministic() {
	new_test_ext().execute_with(|| {
		let domain1 = b"test_domain";
		let domain2 = b"test_domain";
		let domain3 = b"different_domain";

		let point1 = Pallet::<Test>::hash_to_g1(domain1);
		let point2 = Pallet::<Test>::hash_to_g1(domain2);
		let point3 = Pallet::<Test>::hash_to_g1(domain3);

		assert_eq!(
			point1, point2,
			"Same domain should produce same point"
		);
		assert_ne!(
			point1, point3,
			"Different domains should produce different points"
		);
	});
}

#[test]
fn test_full_commit_reveal_workflow() {
	new_test_ext().execute_with(|| {
		let validator = 1u64;
		let commitment_id = [1u8; 32];
		let entropy = [42u8; 32];
		let blinding = [99u8; 32];

		// Step 1: Create commitment off-chain
		let commitment_point = Pallet::<Test>::create_commitment_point(&entropy, &blinding);
		let commitment_bytes = commitment_point.to_compressed();

		// Step 2: Submit commitment on-chain (Block N)
		assert_ok!(PedersenCommitment::commit(
			RuntimeOrigin::signed(validator),
			commitment_id,
			commitment_bytes
		));

		// Step 3: Wait for next block (Block N+1)
		advance_blocks(1);

		// Step 4: Reveal entropy
		assert_ok!(PedersenCommitment::reveal(
			RuntimeOrigin::signed(validator),
			commitment_id,
			entropy,
			blinding
		));

		// Step 5: Verify reveal is stored correctly
		let stored_reveal = Reveals::<Test>::get(validator, commitment_id).unwrap();
		assert_eq!(stored_reveal.entropy, entropy);
		assert_eq!(stored_reveal.blinding, blinding);
	});
}

#[test]
fn test_events_emitted() {
	new_test_ext().execute_with(|| {
		let validator = 1u64;
		let commitment_id = [1u8; 32];
		let entropy = [42u8; 32];
		let blinding = [99u8; 32];

		let commitment_point = Pallet::<Test>::create_commitment_point(&entropy, &blinding);
		let commitment_bytes = commitment_point.to_compressed();

		// Commit and check event
		assert_ok!(PedersenCommitment::commit(
			RuntimeOrigin::signed(validator),
			commitment_id,
			commitment_bytes
		));

		System::assert_has_event(
			Event::CommitmentCreated {
				validator,
				commitment_id,
				block_number: 1,
			}
			.into(),
		);

		advance_blocks(1);

		// Reveal and check events
		assert_ok!(PedersenCommitment::reveal(
			RuntimeOrigin::signed(validator),
			commitment_id,
			entropy,
			blinding
		));

		System::assert_has_event(
			Event::EntropyRevealed {
				validator,
				commitment_id,
				entropy,
			}
			.into(),
		);

		System::assert_has_event(
			Event::CommitmentVerified {
				validator,
				commitment_id,
			}
			.into(),
		);
	});
}
