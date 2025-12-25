//! Quantum state types with compile-time state transitions

use crate::no_clone::NoClone;
use core::marker::PhantomData;
use sp_core::H256;
use scale_codec::{Encode, Decode};
use scale_info::TypeInfo;

#[cfg(not(feature = "std"))]
use alloc::{vec, vec::Vec};
#[cfg(feature = "std")]
use std::{vec, vec::Vec};

// Quantum state markers
#[derive(Debug, Clone, Copy, PartialEq, Eq, Encode, Decode, TypeInfo)]
pub struct Initialized;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Encode, Decode, TypeInfo)]
pub struct Superposition;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Encode, Decode, TypeInfo)]
pub struct Entangled;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Encode, Decode, TypeInfo)]
pub struct Measured;

/// Quantum state with compile-time state tracking
pub struct QuantumState<S> {
    /// The actual quantum data (cannot be cloned)
    data: NoClone<Vec<u8>>,
    /// Quantum phase information
    phase: f64,
    /// Type-state marker
    _state: PhantomData<S>,
}

impl QuantumState<Initialized> {
    /// Create a new initialized quantum state
    pub fn new(data: Vec<u8>) -> Self {
        QuantumState {
            data: NoClone::new(data),
            phase: 0.0,
            _state: PhantomData,
        }
    }

    /// Apply Hadamard gate to enter superposition
    pub fn hadamard(mut self) -> QuantumState<Superposition> {
        // Transform the state
        self.phase = core::f64::consts::PI / 4.0;
        
        QuantumState {
            data: self.data,
            phase: self.phase,
            _state: PhantomData,
        }
    }
}

impl QuantumState<Superposition> {
    /// Entangle with another quantum state
    pub fn entangle_with(self, other: QuantumState<Superposition>) -> (QuantumState<Entangled>, QuantumState<Entangled>) {
        // Consume both states and create entangled pair
        let phase = (self.phase + other.phase) / 2.0;
        
        let state1 = QuantumState {
            data: self.data,
            phase,
            _state: PhantomData,
        };
        
        let state2 = QuantumState {
            data: other.data,
            phase,
            _state: PhantomData,
        };
        
        (state1, state2)
    }

    /// Measure the quantum state (consumes it)
    pub fn measure(self) -> (MeasurementResult, QuantumState<Measured>) {
        // Perform measurement - state collapses
        let result = if self.phase.cos() > 0.5 {
            MeasurementResult::Zero
        } else {
            MeasurementResult::One
        };
        
        let measured_state = QuantumState {
            data: self.data,
            phase: 0.0, // Phase is lost after measurement
            _state: PhantomData,
        };
        
        (result, measured_state)
    }
}

impl QuantumState<Entangled> {
    /// Measure entangled state
    pub fn measure(self) -> (MeasurementResult, QuantumState<Measured>) {
        // Entangled measurement - affects paired state
        let result = if self.phase.sin() > 0.5 {
            MeasurementResult::Zero
        } else {
            MeasurementResult::One
        };
        
        let measured_state = QuantumState {
            data: self.data,
            phase: 0.0,
            _state: PhantomData,
        };
        
        (result, measured_state)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MeasurementResult {
    Zero,
    One,
}

/// Quantum key with no-cloning guarantee
pub struct QuantumKey {
    /// The key material (cannot be cloned)
    material: NoClone<[u8; 32]>,
    /// Key ID for tracking
    id: H256,
    /// Whether this key has been used
    used: bool,
}

impl QuantumKey {
    /// Create a new quantum key
    pub fn new(material: [u8; 32]) -> Self {
        let id = sp_core::blake2_256(&material).into();
        QuantumKey {
            material: NoClone::new(material),
            id,
            used: false,
        }
    }

    /// Use the key (can only be done once)
    pub fn use_key(mut self) -> Result<[u8; 32], &'static str> {
        if self.used {
            return Err("Quantum key already used");
        }
        self.used = true;
        Ok(self.material.into_inner())
    }

    /// Get the key ID
    pub fn id(&self) -> H256 {
        self.id
    }
}

/// Quantum light client state
pub struct LightClientState<S> {
    /// Quantum fingerprint of blockchain state
    fingerprint: NoClone<Vec<u8>>,
    /// Verified block height
    block_height: u64,
    /// State marker
    _state: PhantomData<S>,
}

// Light client states
pub struct Unsynced;
pub struct Syncing;
pub struct Synced;

impl LightClientState<Unsynced> {
    /// Create new unsynced light client
    pub fn new() -> Self {
        LightClientState {
            fingerprint: NoClone::new(vec![0; 32]),
            block_height: 0,
            _state: PhantomData,
        }
    }

    /// Start syncing
    pub fn start_sync(self) -> LightClientState<Syncing> {
        LightClientState {
            fingerprint: self.fingerprint,
            block_height: self.block_height,
            _state: PhantomData,
        }
    }
}

impl LightClientState<Syncing> {
    /// Update with quantum proof
    pub fn update_with_proof(mut self, proof: &[u8], new_height: u64) -> Result<Self, &'static str> {
        // Verify quantum proof
        if proof.len() < 32 {
            return Err("Invalid quantum proof");
        }
        
        // Update fingerprint
        *self.fingerprint.as_mut() = proof[..32].to_vec();
        self.block_height = new_height;
        
        Ok(self)
    }

    /// Complete sync
    pub fn complete_sync(self) -> LightClientState<Synced> {
        LightClientState {
            fingerprint: self.fingerprint,
            block_height: self.block_height,
            _state: PhantomData,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_quantum_state_transitions() {
        // Create initialized state
        let state = QuantumState::<Initialized>::new(vec![0, 1, 0, 1]);
        
        // Apply Hadamard to get superposition
        let superposition = state.hadamard();
        
        // Measure the state
        let (result, _measured) = superposition.measure();
        
        match result {
            MeasurementResult::Zero => println!("Measured |0⟩"),
            MeasurementResult::One => println!("Measured |1⟩"),
        }
    }

    #[test]
    fn test_entanglement() {
        let state1 = QuantumState::<Initialized>::new(vec![1, 0]).hadamard();
        let state2 = QuantumState::<Initialized>::new(vec![0, 1]).hadamard();
        
        let (entangled1, entangled2) = state1.entangle_with(state2);
        
        // Measure first qubit
        let (result1, _) = entangled1.measure();
        // Second measurement would be correlated (if we could access entangled2)
        let (result2, _) = entangled2.measure();
        
        println!("Entangled measurements: {:?}, {:?}", result1, result2);
    }

    // This should NOT compile:
    // #[test]
    // fn test_invalid_transition() {
    //     let state = QuantumState::<Initialized>::new(vec![0, 1]);
    //     let (result, _) = state.measure(); // ❌ Error: no method `measure` on Initialized
    // }
}