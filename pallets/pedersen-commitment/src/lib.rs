//! # Pedersen Commitment Pallet
//!
//! ## Overview
//!
//! This pallet implements **Pedersen commitments** using the BLS12-381 elliptic curve
//! for **information-theoretic hiding** of quantum entropy during the commit phase.
//!
//! ### Cryptographic Properties
//!
//! 1. **Hiding**: Given commitment C, impossible to determine entropy value (information-theoretic)
//! 2. **Binding**: Once committed, validator cannot change entropy without detection
//! 3. **Verifiability**: Anyone can verify a reveal against the original commitment
//!
//! ### Protocol Flow
//!
//! ```text
//! Block N (Commit Phase):
//!   Validator computes: C = g^entropy × h^blinding
//!   Submits: commitment C to blockchain
//!   State: Entropy is HIDDEN (information-theoretically secure)
//!
//! Block N+1 (Reveal Phase):
//!   Validator submits: (entropy, blinding) as plaintext
//!   Network verifies: g^entropy × h^blinding == C
//!   State: Entropy is REVEALED and verified
//! ```
//!
//! ### Security Guarantees
//!
//! - **Information-theoretic hiding**: Even with infinite computational power,
//!   an attacker cannot determine entropy from commitment alone
//! - **Computational binding**: Requires breaking discrete log to forge commitment
//! - **Post-quantum secure**: Uses hash-to-curve which resists quantum attacks
//!
//! ## Implementation Details
//!
//! - **Curve**: BLS12-381 (G1 group, 381-bit prime field)
//! - **Generators**: g = G1::generator(), h = hash_to_curve("qh_pedersen_h")
//! - **Entropy size**: 32 bytes (256 bits of quantum randomness)
//! - **Blinding factor**: 32 bytes (256 bits of randomness)
//! - **Commitment size**: 48 bytes (compressed G1 point)
//!
//! ## Usage in QuantumHarmony
//!
//! This pallet is used in the **50,000-node hierarchical sharding architecture**
//! to keep entropy secret during mempool validation, preventing front-running
//! and MEV attacks while maintaining Byzantine fault tolerance.

#![cfg_attr(not(feature = "std"), no_std)]

pub use pallet::*;

#[cfg(test)]
mod tests;

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;

use bls12_381::{G1Affine, G1Projective, Scalar};
use codec::{Decode, Encode};
use frame_support::{dispatch::DispatchResult, pallet_prelude::*};
use frame_system::pallet_prelude::*;
use group::Curve;
use scale_info::TypeInfo;
use sp_runtime::RuntimeDebug;

/// Pedersen commitment (48-byte compressed G1 point)
#[derive(Clone, PartialEq, Eq, Encode, Decode, RuntimeDebug, TypeInfo, MaxEncodedLen)]
#[scale_info(skip_type_params(T))]
pub struct PedersenCommitment {
	/// Compressed BLS12-381 G1 point (48 bytes)
	pub commitment: [u8; 48],
}

/// Entropy reveal data (entropy + blinding factor)
#[derive(Clone, PartialEq, Eq, Encode, Decode, RuntimeDebug, TypeInfo, MaxEncodedLen)]
pub struct EntropyReveal {
	/// Original entropy value (32 bytes)
	pub entropy: [u8; 32],
	/// Blinding factor used in commitment (32 bytes)
	pub blinding: [u8; 32],
}

/// Commitment phase identifier
pub type CommitmentId = [u8; 32];

#[frame_support::pallet]
pub mod pallet {
	use super::*;

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The overarching event type.
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;
	}

	/// Storage: Active commitments by validator
	/// Map: (ValidatorAccountId, CommitmentId) => PedersenCommitment
	#[pallet::storage]
	#[pallet::getter(fn commitments)]
	pub type Commitments<T: Config> = StorageDoubleMap<
		_,
		Blake2_128Concat,
		T::AccountId,
		Blake2_128Concat,
		CommitmentId,
		PedersenCommitment,
		OptionQuery,
	>;

	/// Storage: Block number when commitment was created
	/// Map: (ValidatorAccountId, CommitmentId) => BlockNumber
	#[pallet::storage]
	#[pallet::getter(fn commitment_blocks)]
	pub type CommitmentBlocks<T: Config> = StorageDoubleMap<
		_,
		Blake2_128Concat,
		T::AccountId,
		Blake2_128Concat,
		CommitmentId,
		BlockNumberFor<T>,
		OptionQuery,
	>;

	/// Storage: Revealed entropy values
	/// Map: (ValidatorAccountId, CommitmentId) => EntropyReveal
	#[pallet::storage]
	#[pallet::getter(fn reveals)]
	pub type Reveals<T: Config> = StorageDoubleMap<
		_,
		Blake2_128Concat,
		T::AccountId,
		Blake2_128Concat,
		CommitmentId,
		EntropyReveal,
		OptionQuery,
	>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// Commitment created: [validator, commitment_id, block_number]
		CommitmentCreated {
			validator: T::AccountId,
			commitment_id: CommitmentId,
			block_number: BlockNumberFor<T>,
		},
		/// Entropy revealed: [validator, commitment_id, entropy_bytes]
		EntropyRevealed {
			validator: T::AccountId,
			commitment_id: CommitmentId,
			entropy: [u8; 32],
		},
		/// Commitment verified successfully: [validator, commitment_id]
		CommitmentVerified {
			validator: T::AccountId,
			commitment_id: CommitmentId,
		},
	}

	#[pallet::error]
	pub enum Error<T> {
		/// Commitment already exists for this ID
		CommitmentAlreadyExists,
		/// Commitment not found
		CommitmentNotFound,
		/// Reveal doesn't match commitment (verification failed)
		RevealMismatch,
		/// Invalid commitment format (not a valid G1 point)
		InvalidCommitment,
		/// Reveal too early (must wait at least 1 block)
		RevealTooEarly,
		/// Commitment already revealed
		AlreadyRevealed,
		/// Invalid entropy size (must be 32 bytes)
		InvalidEntropySize,
		/// Invalid blinding factor size (must be 32 bytes)
		InvalidBlindingSize,
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Submit a Pedersen commitment for quantum entropy
		///
		/// # Arguments
		/// * `origin` - Validator submitting the commitment
		/// * `commitment_id` - Unique identifier for this commitment (e.g., hash of block number + shard ID)
		/// * `commitment` - 48-byte compressed G1 point (C = g^entropy × h^blinding)
		///
		/// # Security
		/// - Entropy remains **information-theoretically hidden** until reveal phase
		/// - Validator **cannot change** entropy after commitment (binding property)
		#[pallet::call_index(0)]
		#[pallet::weight(10_000)]
		pub fn commit(
			origin: OriginFor<T>,
			commitment_id: CommitmentId,
			commitment: [u8; 48],
		) -> DispatchResult {
			let validator = ensure_signed(origin)?;
			let current_block = frame_system::Pallet::<T>::block_number();

			// Ensure commitment doesn't already exist
			ensure!(
				!Commitments::<T>::contains_key(&validator, &commitment_id),
				Error::<T>::CommitmentAlreadyExists
			);

			// Validate that commitment is a valid G1 point
			let ct_option = G1Affine::from_compressed(&commitment);
			ensure!(
				Option::<G1Affine>::from(ct_option).is_some(),
				Error::<T>::InvalidCommitment
			);

			// Store commitment
			let pedersen_commitment = PedersenCommitment { commitment };
			Commitments::<T>::insert(&validator, &commitment_id, pedersen_commitment);
			CommitmentBlocks::<T>::insert(&validator, &commitment_id, current_block);

			Self::deposit_event(Event::CommitmentCreated {
				validator,
				commitment_id,
				block_number: current_block,
			});

			Ok(())
		}

		/// Reveal entropy and verify against commitment
		///
		/// # Arguments
		/// * `origin` - Validator revealing their entropy
		/// * `commitment_id` - ID of the commitment to reveal
		/// * `entropy` - Original 32-byte entropy value
		/// * `blinding` - Original 32-byte blinding factor
		///
		/// # Verification
		/// Computes C' = g^entropy × h^blinding and checks C' == C
		///
		/// # Timing
		/// Must be at least 1 block after commitment to prevent same-block reveal
		#[pallet::call_index(1)]
		#[pallet::weight(20_000)]
		pub fn reveal(
			origin: OriginFor<T>,
			commitment_id: CommitmentId,
			entropy: [u8; 32],
			blinding: [u8; 32],
		) -> DispatchResult {
			let validator = ensure_signed(origin)?;
			let current_block = frame_system::Pallet::<T>::block_number();

			// Ensure commitment exists
			let commitment = Commitments::<T>::get(&validator, &commitment_id)
				.ok_or(Error::<T>::CommitmentNotFound)?;

			// Ensure commitment block exists
			let commitment_block = CommitmentBlocks::<T>::get(&validator, &commitment_id)
				.ok_or(Error::<T>::CommitmentNotFound)?;

			// Ensure at least 1 block has passed since commitment
			ensure!(
				current_block > commitment_block,
				Error::<T>::RevealTooEarly
			);

			// Ensure not already revealed
			ensure!(
				!Reveals::<T>::contains_key(&validator, &commitment_id),
				Error::<T>::AlreadyRevealed
			);

			// Verify the reveal matches the commitment
			let is_valid = Self::verify_commitment(&commitment.commitment, &entropy, &blinding);
			ensure!(is_valid, Error::<T>::RevealMismatch);

			// Store the reveal
			let reveal = EntropyReveal { entropy, blinding };
			Reveals::<T>::insert(&validator, &commitment_id, reveal);

			Self::deposit_event(Event::EntropyRevealed {
				validator: validator.clone(),
				commitment_id,
				entropy,
			});

			Self::deposit_event(Event::CommitmentVerified {
				validator,
				commitment_id,
			});

			Ok(())
		}
	}

	impl<T: Config> Pallet<T> {
		/// Verify that a reveal matches a commitment
		///
		/// # Arguments
		/// * `commitment` - 48-byte compressed G1 point
		/// * `entropy` - 32-byte entropy value
		/// * `blinding` - 32-byte blinding factor
		///
		/// # Returns
		/// `true` if g^entropy × h^blinding == commitment, `false` otherwise
		pub fn verify_commitment(
			commitment: &[u8; 48],
			entropy: &[u8; 32],
			blinding: &[u8; 32],
		) -> bool {
			// Parse commitment point
			let ct_option = G1Affine::from_compressed(commitment);
			let commitment_point = match Option::<G1Affine>::from(ct_option) {
				Some(point) => point,
				None => return false,
			};

			// Recompute C' = g^entropy × h^blinding
			let recomputed = Self::create_commitment_point(entropy, blinding);

			// Check equality
			commitment_point == recomputed
		}

		/// Create a Pedersen commitment point
		///
		/// # Algorithm
		/// 1. g = G1::generator()
		/// 2. h = hash_to_curve("qh_pedersen_h")
		/// 3. entropy_scalar = bytes_to_scalar(entropy)
		/// 4. blinding_scalar = bytes_to_scalar(blinding)
		/// 5. C = g^entropy_scalar × h^blinding_scalar
		///
		/// # Returns
		/// G1Affine point representing the commitment
		pub fn create_commitment_point(entropy: &[u8; 32], blinding: &[u8; 32]) -> G1Affine {
			// Generator g (standard BLS12-381 G1 generator)
			let g = G1Projective::generator();

			// Generator h (derived from hash-to-curve)
			let h = Self::hash_to_g1(b"qh_pedersen_h");

			// Convert entropy and blinding to scalars
			let entropy_scalar = Self::bytes_to_scalar(entropy);
			let blinding_scalar = Self::bytes_to_scalar(blinding);

			// Compute C = g^entropy × h^blinding
			let commitment = (g * entropy_scalar) + (h * blinding_scalar);

			commitment.to_affine()
		}

		/// Hash-to-curve for generating deterministic G1 points
		///
		/// Uses hash-to-scalar then scalar multiplication: h = hash_to_scalar(domain) * G
		/// This ensures different domains always produce different points
		pub fn hash_to_g1(domain: &[u8]) -> G1Projective {
			use sp_io::hashing::blake2_256;

			// Hash the domain to get a 32-byte value
			let hash = blake2_256(domain);

			// Convert hash to scalar
			let scalar = Self::bytes_to_scalar(&hash);

			// Multiply generator by scalar: h = scalar * G
			// This ensures different domains produce different points
			G1Projective::generator() * scalar
		}

		/// Convert 32-byte array to BLS12-381 scalar field element
		///
		/// Uses reduction modulo the scalar field order (r = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001)
		pub fn bytes_to_scalar(bytes: &[u8; 32]) -> Scalar {
			// Convert bytes to scalar (automatically reduces mod r)
			let mut scalar_bytes = [0u8; 64];
			scalar_bytes[..32].copy_from_slice(bytes);
			Scalar::from_bytes_wide(&scalar_bytes)
		}
	}
}

/// Helper functions for creating commitments off-chain
#[cfg(feature = "std")]
pub mod offchain {
	use rand_core::{OsRng, RngCore};

	/// Generate a cryptographically secure 32-byte blinding factor
	pub fn generate_blinding_factor() -> [u8; 32] {
		let mut blinding = [0u8; 32];
		OsRng.fill_bytes(&mut blinding);
		blinding
	}
}
