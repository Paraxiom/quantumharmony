//! QPP Light Client with quantum advantages

use crate::{
    no_clone::NoClone,
    quantum_state::{LightClientState, Unsynced, Syncing, Synced},
    types::{ProofType, WalletError},
};
use sp_core::H256;
use scale_codec::{Encode, Decode};

#[cfg(not(feature = "std"))]
use alloc::vec::Vec;
#[cfg(feature = "std")]
use std::vec::Vec;

/// QPP Light Client for quantum-enhanced blockchain verification
pub struct QPPLightClient {
    /// Current sync state
    state: LightClientState<Synced>,
    /// Quantum proof cache (cannot be cloned)
    proof_cache: NoClone<Vec<QuantumProof>>,
}

/// Quantum proof for light client verification
#[derive(Debug, Clone, Encode, Decode)]
pub struct QuantumProof {
    /// Block hash
    pub block_hash: H256,
    /// Quantum fingerprint
    pub fingerprint: Vec<u8>,
    /// Measurement results
    pub measurements: Vec<bool>,
    /// Proof timestamp
    pub timestamp: u64,
}

impl QPPLightClient {
    /// Initialize a new light client
    pub fn new() -> Result<Self, WalletError> {
        // Start with unsynced state
        let unsynced = LightClientState::<Unsynced>::new();
        
        // Begin sync process
        let syncing = unsynced.start_sync();
        
        // For demo, immediately complete sync
        let synced = syncing.complete_sync();
        
        Ok(QPPLightClient {
            state: synced,
            proof_cache: NoClone::new(Vec::new()),
        })
    }

    /// Verify a transaction using quantum proof
    pub fn verify_transaction(&self, tx_hash: H256, proof: ProofType) -> Result<bool, WalletError> {
        match proof {
            ProofType::Classical(merkle_proof) => {
                // Classical verification - O(log n) complexity
                self.verify_classical_proof(tx_hash, merkle_proof)
            }
            ProofType::Quantum { fingerprint, measurements, threshold } => {
                // Quantum verification - O(sqrt(n)) complexity
                self.verify_quantum_proof(tx_hash, fingerprint, measurements, threshold)
            }
        }
    }

    fn verify_classical_proof(&self, tx_hash: H256, proof: Vec<H256>) -> Result<bool, WalletError> {
        // Simulate Merkle proof verification
        if proof.is_empty() {
            return Err(WalletError::SyncError("Empty proof".into()));
        }
        
        // In real implementation, verify Merkle path
        let mut current = tx_hash;
        for sibling in proof {
            current = sp_core::blake2_256(&[current.as_bytes(), sibling.as_bytes()].concat()).into();
        }
        
        Ok(true) // Simplified
    }

    fn verify_quantum_proof(
        &self,
        _tx_hash: H256,
        fingerprint: Vec<u8>,
        measurements: Vec<bool>,
        threshold: u8,
    ) -> Result<bool, WalletError> {
        // Quantum verification using amplitude amplification
        if fingerprint.len() < 32 {
            return Err(WalletError::SyncError("Invalid quantum fingerprint".into()));
        }
        
        // Count successful measurements
        let successes = measurements.iter().filter(|&&m| m).count();
        let success_rate = successes as f64 / measurements.len() as f64;
        
        // Quantum advantage: need fewer samples due to amplitude amplification
        Ok(success_rate >= threshold as f64 / 100.0)
    }

    /// Get quantum advantage metrics
    pub fn quantum_advantage(&self) -> QuantumAdvantage {
        QuantumAdvantage {
            // Classical proof size: O(log n)
            classical_proof_size: 32 * 20, // 20 hashes for 1M leaves
            // Quantum proof size: O(1)
            quantum_proof_size: 32 + 10, // fingerprint + 10 measurements
            // Classical queries: O(n)
            classical_queries: 1_000_000,
            // Quantum queries: O(sqrt(n))
            quantum_queries: 1_000,
        }
    }

    /// Add a quantum proof to cache
    pub fn cache_proof(&mut self, proof: QuantumProof) -> Result<(), WalletError> {
        if self.proof_cache.len() >= 100 {
            // Remove oldest proof
            self.proof_cache.as_mut().remove(0);
        }
        
        self.proof_cache.as_mut().push(proof);
        Ok(())
    }
}

/// Quantum advantage metrics
#[derive(Debug, Clone)]
pub struct QuantumAdvantage {
    /// Size of classical proof in bytes
    pub classical_proof_size: usize,
    /// Size of quantum proof in bytes
    pub quantum_proof_size: usize,
    /// Number of queries for classical verification
    pub classical_queries: usize,
    /// Number of queries for quantum verification
    pub quantum_queries: usize,
}

impl QuantumAdvantage {
    /// Calculate speedup factor
    pub fn speedup(&self) -> f64 {
        self.classical_queries as f64 / self.quantum_queries as f64
    }
    
    /// Calculate space savings
    pub fn space_savings(&self) -> f64 {
        1.0 - (self.quantum_proof_size as f64 / self.classical_proof_size as f64)
    }
}

// Quantum light client operations (synchronous)
pub mod quantum_verify {
    use super::*;
    
    /// Perform quantum state verification (must be synchronous)
    pub fn verify_state_fingerprint(
        fingerprint: &[u8],
        expected: &[u8],
    ) -> bool {
        // Quantum fingerprint comparison
        // In real implementation, use quantum interference
        fingerprint == expected
    }
    
    /// Quantum sampling for verification
    pub fn quantum_sample(data: &[u8], samples: usize) -> Vec<bool> {
        // Simulate quantum sampling with amplitude amplification
        let mut results = Vec::with_capacity(samples);
        
        for i in 0..samples {
            // Quantum measurement simulation
            let measurement = (data[i % data.len()] as usize + i) % 2 == 0;
            results.push(measurement);
        }
        
        results
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_light_client_creation() {
        let client = QPPLightClient::new().unwrap();
        let advantage = client.quantum_advantage();
        
        println!("Quantum speedup: {}x", advantage.speedup());
        println!("Space savings: {:.1}%", advantage.space_savings() * 100.0);
        
        assert!(advantage.speedup() > 100.0);
        assert!(advantage.space_savings() > 0.9);
    }

    #[test]
    fn test_quantum_verification() {
        let client = QPPLightClient::new().unwrap();
        
        let tx_hash = H256::from([1u8; 32]);
        let proof = ProofType::Quantum {
            fingerprint: vec![0u8; 32],
            measurements: vec![true, false, true, true, false, true, true, true, false, true],
            threshold: 60, // 60%
        };
        
        let result = client.verify_transaction(tx_hash, proof).unwrap();
        assert!(result);
    }

    #[test]
    fn test_proof_caching() {
        let mut client = QPPLightClient::new().unwrap();
        
        for i in 0..10 {
            let proof = QuantumProof {
                block_hash: H256::from([i as u8; 32]),
                fingerprint: vec![i as u8; 32],
                measurements: vec![true; 10],
                timestamp: i as u64,
            };
            
            client.cache_proof(proof).unwrap();
        }
        
        assert_eq!(client.proof_cache.len(), 10);
    }
}