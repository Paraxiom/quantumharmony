//! QKD Client for Quantum Harmony blockchain
//!
//! This crate provides interfaces to quantum key distribution hardware
//! for secure random number generation and quantum entropy.
//!
//! IMPORTANT: For on-chain (runtime) usage, always use `get_deterministic_random_bytes()`
//! with a seed derived from block hash to ensure consensus. The `get_quantum_random_bytes()`
//! function is ONLY safe for off-chain workers.

#![cfg_attr(not(feature = "std"), no_std)]

use sp_core::H256;
use sp_std::prelude::*;

/// Generates deterministic random bytes from a seed.
///
/// CRITICAL: This function MUST be used for all on-chain randomness needs.
/// It uses a simple but deterministic PRNG (xorshift-based) that will produce
/// identical output on all nodes given the same seed.
///
/// # Arguments
///
/// * `seed` - A seed derived from deterministic on-chain data (e.g., block hash)
/// * `length` - The number of bytes to generate
///
/// # Returns
///
/// A vector of deterministically-generated random bytes
pub fn get_deterministic_random_bytes(seed: &[u8], length: usize) -> Vec<u8> {
    // Create initial state from seed using a simple hash-like mixing
    let mut state: [u64; 4] = [0; 4];

    // Mix seed bytes into state
    for (i, chunk) in seed.chunks(8).enumerate() {
        let mut bytes = [0u8; 8];
        for (j, &b) in chunk.iter().enumerate() {
            bytes[j] = b;
        }
        state[i % 4] ^= u64::from_le_bytes(bytes);
    }

    // Ensure non-zero state (xorshift requires this)
    if state.iter().all(|&x| x == 0) {
        state[0] = 0x853c49e6748fea9b;
        state[1] = 0xda3e39cb94b95bdb;
        state[2] = 0x7c9e8f9a6b5c4d3e;
        state[3] = 0x1a2b3c4d5e6f7a8b;
    }

    let mut result = Vec::with_capacity(length);

    // Generate bytes using xorshift128+ algorithm (deterministic)
    while result.len() < length {
        // xorshift128+ step
        let t = state[0];
        let s = state[3];
        state[3] = state[2];
        state[2] = state[1];
        state[1] = state[0];
        let t = t ^ (t << 23);
        let t = t ^ (t >> 18);
        let t = t ^ s ^ (s >> 5);
        state[0] = t;

        // Extract bytes from result
        let value = t.wrapping_add(s);
        for byte in value.to_le_bytes() {
            if result.len() < length {
                result.push(byte);
            }
        }
    }

    result
}

/// Retrieves quantum random bytes from the QKD device.
///
/// WARNING: This function is NON-DETERMINISTIC and must ONLY be used in:
/// - Off-chain workers
/// - Tests
/// - Initial key generation (before chain starts)
///
/// For on-chain consensus-critical code, use `get_deterministic_random_bytes()` instead!
///
/// # Arguments
///
/// * `length` - The number of bytes to retrieve
///
/// # Returns
///
/// A vector of random bytes from the quantum source
pub fn get_quantum_random_bytes(length: usize) -> Vec<u8> {
    #[cfg(feature = "std")]
    {
        // In a real implementation, this would interact with actual QKD hardware
        // For now, use rand for testing purposes
        use rand::Rng;
        let mut rng = rand::thread_rng();
        let mut result = Vec::with_capacity(length);
        for _ in 0..length {
            result.push(rng.gen::<u8>());
        }
        result
    }

    #[cfg(not(feature = "std"))]
    {
        // In no_std environment, return a predictable sequence for compilation
        // This should never be used in production!
        let mut result = Vec::with_capacity(length);
        for i in 0..length {
            result.push(i as u8);
        }
        result
    }
}

/// Retrieves a quantum-derived hash for blockchain usage
///
/// # Returns
///
/// An H256 hash derived from quantum entropy
pub fn get_quantum_hash() -> H256 {
    let random_bytes = get_quantum_random_bytes(32);
    H256::from_slice(&random_bytes)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_get_quantum_random_bytes_length() {
        // Test various lengths
        for length in [0, 1, 16, 32, 64, 128, 256, 1024] {
            let bytes = get_quantum_random_bytes(length);
            assert_eq!(bytes.len(), length, "Expected {} bytes, got {}", length, bytes.len());
        }
    }

    #[test]
    fn test_get_quantum_random_bytes_non_deterministic() {
        #[cfg(feature = "std")]
        {
            // Generate two sequences and verify they're different (probabilistic test)
            let bytes1 = get_quantum_random_bytes(32);
            let bytes2 = get_quantum_random_bytes(32);

            // With 32 bytes of random data, probability of collision is negligible
            assert_ne!(bytes1, bytes2, "Two random sequences should be different");
        }
    }

    #[test]
    fn test_get_quantum_random_bytes_distribution() {
        #[cfg(feature = "std")]
        {
            // Test that bytes are reasonably distributed (not all zeros, not all same value)
            let bytes = get_quantum_random_bytes(256);

            // Check not all zeros
            assert!(bytes.iter().any(|&b| b != 0), "Random bytes should not all be zero");

            // Check not all same value
            let first_byte = bytes[0];
            assert!(bytes.iter().any(|&b| b != first_byte), "Random bytes should have variety");

            // Basic entropy check: count unique values
            let mut unique_values = std::collections::HashSet::new();
            for &b in &bytes {
                unique_values.insert(b);
            }

            // With 256 bytes, we expect to see many different values
            // (at least 50% of possible byte values should appear)
            assert!(unique_values.len() >= 128,
                "Expected at least 128 unique byte values, got {}", unique_values.len());
        }
    }

    #[test]
    fn test_get_quantum_hash_length() {
        let hash = get_quantum_hash();
        assert_eq!(hash.as_bytes().len(), 32, "H256 should be 32 bytes");
    }

    #[test]
    fn test_get_quantum_hash_non_deterministic() {
        #[cfg(feature = "std")]
        {
            // Generate two hashes and verify they're different
            let hash1 = get_quantum_hash();
            let hash2 = get_quantum_hash();

            assert_ne!(hash1, hash2, "Two quantum hashes should be different");
        }
    }

    #[test]
    fn test_get_quantum_hash_valid_h256() {
        let hash = get_quantum_hash();

        // Verify it's a valid H256 by converting to bytes and back
        let bytes = hash.as_bytes();
        let reconstructed = H256::from_slice(bytes);

        assert_eq!(hash, reconstructed, "H256 should round-trip correctly");
    }

    #[test]
    fn test_edge_case_zero_length() {
        let bytes = get_quantum_random_bytes(0);
        assert_eq!(bytes.len(), 0);
        assert!(bytes.is_empty());
    }

    #[test]
    fn test_edge_case_single_byte() {
        let bytes = get_quantum_random_bytes(1);
        assert_eq!(bytes.len(), 1);
    }

    #[test]
    fn test_large_request() {
        // Test that large requests work
        let bytes = get_quantum_random_bytes(10_000);
        assert_eq!(bytes.len(), 10_000);
    }

    #[cfg(not(feature = "std"))]
    #[test]
    fn test_no_std_predictable_sequence() {
        // In no_std, bytes should be a predictable sequence (for testing only!)
        let bytes = get_quantum_random_bytes(10);
        let expected: Vec<u8> = (0..10).map(|i| i as u8).collect();
        assert_eq!(bytes, expected, "no_std implementation should return predictable sequence");
    }

    #[test]
    fn test_multiple_calls_different_results() {
        #[cfg(feature = "std")]
        {
            // Call multiple times and ensure we get different results
            let mut results = Vec::new();
            for _ in 0..5 {
                results.push(get_quantum_random_bytes(16));
            }

            // Verify not all results are the same
            let first = &results[0];
            assert!(results.iter().any(|r| r != first),
                "Multiple calls should produce different results");
        }
    }

    #[test]
    fn test_quantum_hash_covers_full_range() {
        #[cfg(feature = "std")]
        {
            // Generate multiple hashes and verify they cover different parts of the hash space
            let mut hashes = Vec::new();
            for _ in 0..10 {
                hashes.push(get_quantum_hash());
            }

            // Verify all hashes are unique
            let unique_count = hashes.iter().collect::<std::collections::HashSet<_>>().len();
            assert_eq!(unique_count, 10, "All 10 hashes should be unique");
        }
    }
}
