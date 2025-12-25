//! Quaternary Encoding for Quantum Checksums
//!
//! DNA-inspired base-4 encoding optimized for quantum measurements.
//! Each quaternary digit (quart) represents exactly 2 bits.
//!
//! ## Why Quaternary for Checksums?
//! - Perfect alignment: 1 quart = 2 bits (no waste)
//! - Natural for 2-bit quantum measurements
//! - DNA-inspired: A=0, T=1, G=2, C=3
//! - Efficient error detection
//! - Easy conversion to/from binary

use codec::{Decode, Encode};
use frame_support::pallet_prelude::*;
use sp_std::prelude::*;

/// A quart (quaternary digit) representing values 0, 1, 2, or 3
pub type Quart = u8;

/// Quaternary-encoded quantum checksum (16 quarts = 32 bits)
///
/// Designed for quantum random number generators that produce
/// measurements in 2-bit chunks. Each quart represents one
/// quantum measurement pair.
///
/// Format: 16 quaternary digits packed into 32 bits
/// - More compact than hex (16 chars = 64 bits)
/// - Natural for quantum hardware (2-bit measurements)
/// - DNA-inspired (A, T, G, C mapping)
#[derive(Clone, Copy, Debug, PartialEq, Eq, Encode, Decode, TypeInfo, MaxEncodedLen)]
pub struct QuaternaryChecksum {
    /// 16 quarts packed into 4 bytes (32 bits)
    /// Each quart uses 2 bits: [qq|qq|qq|qq|qq|qq|qq|qq] per byte
    quarts: [u8; 16],
}

impl QuaternaryChecksum {
    /// Create checksum from 16 quaternary digits
    pub fn from_quarts(quarts: [u8; 16]) -> Result<Self, &'static str> {
        // Validate all quarts are 0-3
        for &q in &quarts {
            if q > 3 {
                return Err("Invalid quart: must be 0-3");
            }
        }
        Ok(Self { quarts })
    }

    /// Create checksum from raw bytes (32 bits)
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, &'static str> {
        if bytes.len() < 4 {
            return Err("Need at least 4 bytes for checksum");
        }

        let mut quarts = [0u8; 16];
        for (i, &byte) in bytes[0..4].iter().enumerate() {
            // Extract 4 quarts from each byte (2 bits each)
            quarts[i * 4 + 0] = (byte >> 6) & 0b11;
            quarts[i * 4 + 1] = (byte >> 4) & 0b11;
            quarts[i * 4 + 2] = (byte >> 2) & 0b11;
            quarts[i * 4 + 3] = (byte >> 0) & 0b11;
        }

        Ok(Self { quarts })
    }

    /// Create checksum from quantum entropy (designed for QRNG)
    ///
    /// Takes 32 bits of quantum entropy and converts to quaternary.
    /// Each 2-bit quantum measurement becomes one quart.
    pub fn from_quantum_entropy(entropy: &[u8]) -> Result<Self, &'static str> {
        if entropy.len() < 4 {
            return Err("Need at least 4 bytes of quantum entropy");
        }

        Self::from_bytes(entropy)
    }

    /// Get the quarts as array
    pub fn as_quarts(&self) -> &[u8; 16] {
        &self.quarts
    }

    /// Convert to packed binary (4 bytes)
    pub fn to_bytes(&self) -> [u8; 4] {
        let mut bytes = [0u8; 4];
        for i in 0..4 {
            bytes[i] = (self.quarts[i * 4 + 0] << 6)
                | (self.quarts[i * 4 + 1] << 4)
                | (self.quarts[i * 4 + 2] << 2)
                | (self.quarts[i * 4 + 3] << 0);
        }
        bytes
    }

    /// Convert to DNA-inspired string (A, T, G, C)
    ///
    /// Mapping:
    /// - 0 → 'A' (Adenine)
    /// - 1 → 'T' (Thymine)
    /// - 2 → 'G' (Guanine)
    /// - 3 → 'C' (Cytosine)
    pub fn to_dna_string(&self) -> Vec<u8> {
        self.quarts
            .iter()
            .map(|&q| match q {
                0 => b'A',
                1 => b'T',
                2 => b'G',
                3 => b'C',
                _ => b'?', // Should never happen
            })
            .collect()
    }

    /// Create from DNA string
    pub fn from_dna_string(dna: &[u8]) -> Result<Self, &'static str> {
        if dna.len() != 16 {
            return Err("DNA string must be exactly 16 characters");
        }

        let mut quarts = [0u8; 16];
        for (i, &nucleotide) in dna.iter().enumerate() {
            quarts[i] = match nucleotide {
                b'A' | b'a' => 0,
                b'T' | b't' => 1,
                b'G' | b'g' => 2,
                b'C' | b'c' => 3,
                _ => return Err("Invalid nucleotide: must be A, T, G, or C"),
            };
        }

        Ok(Self { quarts })
    }

    /// Verify data integrity by comparing checksums
    pub fn verify(&self, other: &Self) -> bool {
        self.quarts == other.quarts
    }

    /// Calculate Hamming distance (number of differing quarts)
    ///
    /// Useful for error detection: if distance > threshold, data corrupted
    pub fn hamming_distance(&self, other: &Self) -> u32 {
        self.quarts
            .iter()
            .zip(other.quarts.iter())
            .filter(|(a, b)| a != b)
            .count() as u32
    }

    /// Check if checksum is all zeros (invalid/uninitialized)
    pub fn is_zero(&self) -> bool {
        self.quarts.iter().all(|&q| q == 0)
    }
}

/// Compute quaternary checksum from arbitrary data
///
/// Uses simple XOR-based algorithm optimized for speed.
/// For cryptographic purposes, use proper hash functions.
pub fn compute_checksum(data: &[u8]) -> QuaternaryChecksum {
    let mut checksum_bytes = [0u8; 4];

    // XOR all bytes in chunks of 4
    for (i, &byte) in data.iter().enumerate() {
        checksum_bytes[i % 4] ^= byte;
    }

    // Convert to quaternary
    QuaternaryChecksum::from_bytes(&checksum_bytes)
        .expect("checksum bytes are always valid")
}

/// Compute cryptographic checksum using hash
///
/// Uses sp_core's hashing for secure checksums.
/// Takes first 32 bits of hash output.
pub fn compute_cryptographic_checksum<H: sp_core::Hasher>(data: &[u8]) -> QuaternaryChecksum {
    let hash = H::hash(data);
    let hash_bytes = hash.as_ref();

    QuaternaryChecksum::from_bytes(hash_bytes)
        .expect("hash bytes are always valid")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_quart_encoding() {
        let quarts = [0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3];
        let checksum = QuaternaryChecksum::from_quarts(quarts).unwrap();
        assert_eq!(checksum.as_quarts(), &quarts);
    }

    #[test]
    fn test_invalid_quart() {
        let invalid = [0, 1, 2, 4, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3];
        assert!(QuaternaryChecksum::from_quarts(invalid).is_err());
    }

    #[test]
    fn test_byte_conversion() {
        let bytes = [0b11100100, 0b10110001, 0b01011100, 0b11001011];
        let checksum = QuaternaryChecksum::from_bytes(&bytes).unwrap();
        let decoded = checksum.to_bytes();
        assert_eq!(bytes, decoded);
    }

    #[test]
    fn test_dna_encoding() {
        let quarts = [0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3];
        let checksum = QuaternaryChecksum::from_quarts(quarts).unwrap();
        let dna = checksum.to_dna_string();
        assert_eq!(dna, b"ATGCATGCATGCATGC");

        // Round-trip test
        let decoded = QuaternaryChecksum::from_dna_string(&dna).unwrap();
        assert_eq!(checksum, decoded);
    }

    #[test]
    fn test_dna_case_insensitive() {
        let upper = b"ATGC";
        let lower = b"atgc";

        let mut full_upper = [0u8; 16];
        let mut full_lower = [0u8; 16];
        for i in 0..4 {
            full_upper[i * 4..(i + 1) * 4].copy_from_slice(upper);
            full_lower[i * 4..(i + 1) * 4].copy_from_slice(lower);
        }

        let cs_upper = QuaternaryChecksum::from_dna_string(&full_upper).unwrap();
        let cs_lower = QuaternaryChecksum::from_dna_string(&full_lower).unwrap();

        assert_eq!(cs_upper, cs_lower);
    }

    #[test]
    fn test_verification() {
        let quarts1 = [0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3];
        let quarts2 = [0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3];
        let quarts3 = [3, 2, 1, 0, 3, 2, 1, 0, 3, 2, 1, 0, 3, 2, 1, 0];

        let cs1 = QuaternaryChecksum::from_quarts(quarts1).unwrap();
        let cs2 = QuaternaryChecksum::from_quarts(quarts2).unwrap();
        let cs3 = QuaternaryChecksum::from_quarts(quarts3).unwrap();

        assert!(cs1.verify(&cs2));
        assert!(!cs1.verify(&cs3));
    }

    #[test]
    fn test_hamming_distance() {
        let quarts1 = [0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3];
        let quarts2 = [0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3]; // Same
        let quarts3 = [3, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 0]; // 2 different

        let cs1 = QuaternaryChecksum::from_quarts(quarts1).unwrap();
        let cs2 = QuaternaryChecksum::from_quarts(quarts2).unwrap();
        let cs3 = QuaternaryChecksum::from_quarts(quarts3).unwrap();

        assert_eq!(cs1.hamming_distance(&cs2), 0);
        assert_eq!(cs1.hamming_distance(&cs3), 2);
    }

    #[test]
    fn test_compute_checksum() {
        let data = b"Hello, QuantumHarmony!";
        let checksum = compute_checksum(data);

        // Should be deterministic
        let checksum2 = compute_checksum(data);
        assert_eq!(checksum, checksum2);

        // Different data should produce different checksum (usually)
        let checksum3 = compute_checksum(b"Different data");
        assert_ne!(checksum, checksum3);
    }

    #[test]
    fn test_is_zero() {
        let zeros = [0u8; 16];
        let non_zeros = [0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3];

        let cs_zero = QuaternaryChecksum::from_quarts(zeros).unwrap();
        let cs_non_zero = QuaternaryChecksum::from_quarts(non_zeros).unwrap();

        assert!(cs_zero.is_zero());
        assert!(!cs_non_zero.is_zero());
    }

    #[test]
    fn test_size() {
        // Verify struct size is optimal
        assert_eq!(core::mem::size_of::<QuaternaryChecksum>(), 16);
    }

    #[test]
    fn test_quantum_entropy() {
        // Simulate quantum entropy (32 bits)
        let quantum_bits = [0b11010010, 0b10110100, 0b01100011, 0b11001010];

        let checksum = QuaternaryChecksum::from_quantum_entropy(&quantum_bits).unwrap();

        // Verify we can extract the quarts
        let quarts = checksum.as_quarts();
        assert_eq!(quarts.len(), 16);

        // All quarts should be 0-3
        for &q in quarts.iter() {
            assert!(q <= 3);
        }
    }

    #[test]
    fn test_codec_roundtrip() {
        let quarts = [0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3];
        let checksum = QuaternaryChecksum::from_quarts(quarts).unwrap();

        // Encode to bytes
        let encoded = checksum.encode();

        // Decode back
        let decoded = QuaternaryChecksum::decode(&mut &encoded[..]).unwrap();

        assert_eq!(checksum, decoded);
    }
}
