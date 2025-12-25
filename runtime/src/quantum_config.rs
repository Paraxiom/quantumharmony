// runtime/src/quantum_config.rs
//! Configuration for quantum pallets in the QuantumHarmony runtime

use crate::{Runtime, RuntimeEvent, Balances, Balance};
use frame_support::parameter_types;
use sp_runtime::traits::ConstU32;

extern crate alloc;
use alloc::vec::Vec;

// ====== Quantum Crypto Configuration ======

parameter_types! {
    /// QKD endpoint for local KIRQ entropy receiver
    /// Initialize empty, can be set via governance
    pub QkdEndpointValue: Option<Vec<u8>> = None;
}

// HWRNG INTEGRATION POINT: Runtime Randomness (VRF)
//
// This stub implementation currently returns zero randomness.
// To integrate HWRNG quantum entropy:
//
// 1. **Runtime Host Function Approach** (Recommended):
//    - Define a custom host function in sp-io for quantum entropy
//    - Implement the host function in the node using QuantumEntropyProvider
//    - Call from runtime via sp_io::crypto::quantum_entropy()
//
// 2. **Off-Chain Worker Approach** (Alternative):
//    - Use off-chain workers to fetch quantum entropy from PQTG
//    - Store in off-chain storage indexed by block number
//    - Read from on-chain randomness calls
//
// 3. **Entropy Pool Approach** (Future):
//    - Populate an on-chain entropy pool with quantum randomness
//    - Runtime randomness derives from pool + block hash
//    - Validators submit quantum entropy via inherents
//
// For now, we use a deterministic fallback based on block hash.
// This ensures functionality while HWRNG infrastructure is being built.
//
// TODO: Implement custom host function for quantum_entropy()
// TODO: Register host function in node/src/service.rs executor
// TODO: Update this implementation to call sp_io::crypto::quantum_entropy()

pub struct QuantumRandomness;
impl frame_support::traits::Randomness<sp_core::H256, u32> for QuantumRandomness {
    fn random(subject: &[u8]) -> (sp_core::H256, u32) {
        // Deterministic randomness from PARENT block hash + subject
        // IMPORTANT: We use the parent block hash because the current block's
        // hash is not known during block execution - it's only computed after
        // the block is finalized. Using current block hash would cause
        // non-determinism between block production and import.
        use frame_support::sp_runtime::traits::Hash;
        use crate::Runtime;

        let block_number = frame_system::Pallet::<Runtime>::block_number();

        // Use parent block hash (block_number - 1, or genesis hash for block 1)
        let parent_number = block_number.saturating_sub(1);
        let parent_hash = frame_system::Pallet::<Runtime>::block_hash(parent_number);

        // Combine parent hash with subject for deterministic randomness
        let mut data = parent_hash.as_ref().to_vec();
        data.extend_from_slice(subject);
        data.extend_from_slice(&block_number.to_le_bytes());

        let hash = <Runtime as frame_system::Config>::Hashing::hash(&data);

        (hash, block_number)
    }
}

impl pallet_quantum_crypto::Config for Runtime {
    type RuntimeEvent = RuntimeEvent;
    type MyRandomness = QuantumRandomness;
    type MaxEntropyPoolSize = ConstU32<1_048_576>;  // 1MB
    type QkdEndpoint = QkdEndpointValue;
    type MinSecureQber = ConstU32<1100>;  // 11% QBER
    type MaxMeasurementsPerProof = ConstU32<1000>;
    type MaxProofSize = ConstU32<262_144>;  // 256KB
    type MaxCertificateSize = ConstU32<65_536>;  // 64KB
}

// ====== Proof of Coherence Configuration ======

parameter_types! {
    /// Reward for maintaining coherence: 10 QHMY
    pub const CoherenceReward: Balance = 10 * 10u128.pow(18);

    /// Slash for losing coherence: 1 QHMY
    pub const CoherenceSlash: Balance = 1 * 10u128.pow(18);
}

impl pallet_proof_of_coherence::Config for Runtime {
    type RuntimeEvent = RuntimeEvent;
    type Currency = Balances;
    type MinimumCoherenceScore = ConstU32<7000>;  // 70%
    type MaxValidators = ConstU32<100>;
    type CoherencePeriod = ConstU32<100>;  // ~10 minutes
    type CoherenceReward = CoherenceReward;
    type CoherenceSlash = CoherenceSlash;
}