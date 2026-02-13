//! Quantum-resistant hasher for runtime
//!
//! This module provides Keccak-256 (SHA3) as the default hasher for the runtime,
//! replacing Blake2 which has reduced quantum resistance.
//!
//! The quantum aspect comes from:
//! 1. QRNG entropy feeding into SPHINCS+/Falcon key generation and signing
//! 2. Keccak-256's quantum-resistant properties (128-bit security against Grover's algorithm)
//! 3. Sponge construction with 1600-bit internal state

use sp_runtime::traits::{Hash as HashT};
use sp_core::{H256, Hasher};
use scale_info::TypeInfo;
use sp_runtime::StateVersion;
use sp_std::vec::Vec;
use scale_codec::{Encode, Decode};
use serde::{Serialize, Deserialize};

/// Quantum-resistant hasher using Keccak-256 (SHA3)
#[derive(Clone, Debug, Eq, PartialEq, TypeInfo, Encode, Decode, Serialize, Deserialize)]
pub struct QuantumHasher;

impl Hasher for QuantumHasher {
    type Out = H256;
    type StdHasher = hash256_std_hasher::Hash256StdHasher;
    const LENGTH: usize = 32;

    fn hash(data: &[u8]) -> Self::Out {
        sp_io::hashing::keccak_256(data).into()
    }
}

impl HashT for QuantumHasher {
    type Output = H256;

    fn trie_root(input: Vec<(Vec<u8>, Vec<u8>)>, version: StateVersion) -> Self::Output {
        sp_io::trie::keccak_256_root(input, version)
    }

    fn ordered_trie_root(input: Vec<Vec<u8>>, version: StateVersion) -> Self::Output {
        sp_io::trie::keccak_256_ordered_root(input, version)
    }
}
