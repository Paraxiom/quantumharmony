//! QPP Wallet implementation with compile-time quantum guarantees

use crate::{
    no_clone::NoClone,
    quantum_state::{QuantumKey, QuantumState, Initialized, Superposition, MeasurementResult},
    qpp_enforcement::{QuantumEntropy, QuantumKeyGenerator, QuantumAccountCreator},
    types::*,
};
use core::marker::PhantomData;
use sp_core::{H256, Pair, crypto::AccountId32};
use sp_core::sr25519;
use scale_codec::{Encode, Decode};

#[cfg(not(feature = "std"))]
use alloc::vec::Vec;
#[cfg(feature = "std")]
use std::{sync::{Arc, Mutex}, vec::Vec};
#[cfg(feature = "std")]
use tokio::sync::mpsc;

// Wallet states
pub struct Locked;
pub struct Unlocked;
pub struct Syncing;

/// QPP Wallet with type-state pattern
pub struct QPPWallet<S> {
    /// Wallet data (protected from cloning)
    data: NoClone<WalletData>,
    /// State marker
    _state: PhantomData<S>,
}

struct WalletData {
    /// Account information
    accounts: Vec<AccountType>,
    /// Current account index
    current_account: Option<usize>,
    /// Quantum keys (one-time use)
    quantum_keys: Vec<QuantumKey>,
    /// Quantum key generator with enforced entropy consumption
    key_generator: Option<QuantumKeyGenerator>,
    /// Sync state
    sync_height: u64,
}

// Wallet state for external use
#[derive(Debug, Clone)]
pub struct WalletState {
    pub accounts: Vec<AccountType>,
    pub current_account: Option<AccountType>,
    pub sync_height: u64,
    pub quantum_keys_available: usize,
}

impl QPPWallet<Locked> {
    /// Create a new locked wallet
    pub fn new() -> Self {
        QPPWallet {
            data: NoClone::new(WalletData {
                accounts: Vec::new(),
                current_account: None,
                quantum_keys: Vec::new(),
                key_generator: None,
                sync_height: 0,
            }),
            _state: PhantomData,
        }
    }

    /// Unlock wallet with password (consumes locked wallet)
    pub fn unlock(mut self, _password: &str) -> Result<QPPWallet<Unlocked>, WalletError> {
        // In real implementation, decrypt wallet data with password
        
        // Initialize quantum key generator on unlock
        self.data.key_generator = Some(QuantumKeyGenerator::new());
        
        Ok(QPPWallet {
            data: self.data,
            _state: PhantomData,
        })
    }
}

impl QPPWallet<Unlocked> {
    /// Create a new account
    pub fn create_account(&mut self, account_type: &str) -> Result<AccountType, WalletError> {
        match account_type {
            "classical" => self.create_classical_account(),
            "quantum" => self.create_quantum_account(),
            "hybrid" => self.create_hybrid_account(),
            _ => Err(WalletError::AccountNotFound(format!("Unknown account type: {}", account_type))),
        }
    }

    fn create_classical_account(&mut self) -> Result<AccountType, WalletError> {
        // Create quantum entropy for account generation
        let entropy = QuantumEntropy::from_qrng(64)?;
        let creator = QuantumAccountCreator::new(entropy);
        
        // Create account using quantum entropy (consumes the creator)
        let account_id = creator.create_classical_account()?;
        let account = AccountType::Classical(account_id);
        
        self.data.accounts.push(account.clone());
        Ok(account)
    }

    fn create_quantum_account(&mut self) -> Result<AccountType, WalletError> {
        // Create quantum entropy for account generation
        let entropy = QuantumEntropy::from_qrng(64)?;
        let creator = QuantumAccountCreator::new(entropy);
        
        // Create quantum account using QPP-enforced entropy (consumes the creator)
        let quantum_id = creator.create_quantum_account()?;
        let account = AccountType::Quantum(quantum_id);
        
        self.data.accounts.push(account.clone());
        Ok(account)
    }

    fn create_hybrid_account(&mut self) -> Result<AccountType, WalletError> {
        // Create both account types
        let classical = match self.create_classical_account()? {
            AccountType::Classical(acc) => acc,
            _ => unreachable!(),
        };
        
        let quantum = match self.create_quantum_account()? {
            AccountType::Quantum(acc) => acc,
            _ => unreachable!(),
        };
        
        let account = AccountType::Hybrid { classical, quantum };
        
        // Remove the individual accounts we just created
        self.data.accounts.pop();
        self.data.accounts.pop();
        
        // Add the hybrid account
        self.data.accounts.push(account.clone());
        Ok(account)
    }

    /// Generate quantum keys for one-time use
    pub fn generate_quantum_keys(&mut self, count: usize) -> Result<usize, WalletError> {
        // Get or create key generator
        let mut generator = self.data.key_generator
            .take()
            .unwrap_or_else(QuantumKeyGenerator::new);
        
        // Add entropy to the generator
        for _ in 0..count {
            let entropy = QuantumEntropy::from_qrng(32)?;
            generator.add_entropy(entropy);
        }
        
        // Generate keys (each consumes entropy)
        for _ in 0..count {
            let (key, new_generator) = generator.generate_key()?;
            generator = new_generator;
            self.data.quantum_keys.push(key);
        }
        
        // Store the generator back
        self.data.key_generator = Some(generator);
        
        Ok(self.data.quantum_keys.len())
    }

    /// Use a quantum key (consumes it)
    pub fn use_quantum_key(&mut self) -> Result<[u8; 32], WalletError> {
        self.data.quantum_keys
            .pop()
            .ok_or_else(|| WalletError::QuantumStateError("No quantum keys available".into()))?
            .use_key()
            .map_err(|e| WalletError::QuantumStateError(e.into()))
    }
    
    /// List all accounts in the wallet
    pub fn list_accounts(&self) -> Vec<AccountType> {
        self.data.accounts.clone()
    }

    /// Start syncing (transitions to syncing state)
    pub fn start_sync(self) -> QPPWallet<Syncing> {
        QPPWallet {
            data: self.data,
            _state: PhantomData,
        }
    }

    /// Get current wallet state (safe to share)
    pub fn get_state(&self) -> WalletState {
        WalletState {
            accounts: self.data.accounts.clone(),
            current_account: self.data.current_account
                .and_then(|i| self.data.accounts.get(i))
                .cloned(),
            sync_height: self.data.sync_height,
            quantum_keys_available: self.data.quantum_keys.len(),
        }
    }
}

impl QPPWallet<Syncing> {
    /// Update sync progress
    pub fn update_sync(&mut self, new_height: u64) -> Result<(), WalletError> {
        if new_height > self.data.sync_height {
            self.data.sync_height = new_height;
            Ok(())
        } else {
            Err(WalletError::SyncError("Invalid block height".into()))
        }
    }

    /// Complete sync and return to unlocked state
    pub fn complete_sync(self) -> QPPWallet<Unlocked> {
        QPPWallet {
            data: self.data,
            _state: PhantomData,
        }
    }
}

// Quantum operations (always synchronous)
pub mod quantum_ops {
    use super::*;

    /// Perform quantum measurement (synchronous only!)
    pub fn measure_quantum_state(state: QuantumState<Superposition>) -> MeasurementResult {
        let (result, _measured) = state.measure();
        result
    }

    /// Generate quantum random number (synchronous)
    pub fn quantum_random() -> [u8; 32] {
        // In real implementation, this would interface with quantum hardware
        let mut random = [0u8; 32];
        // Get quantum entropy from QRNG service
        #[cfg(feature = "std")]
        {
            use crate::qrng_client::fill_quantum_bytes;
            fill_quantum_bytes(&mut random)
                .unwrap_or_else(|_| {
                    log::warn!("QRNG unavailable, using fallback");
                    // Fallback only if QRNG is down
                    use rand::RngCore;
                    rand::thread_rng().fill_bytes(&mut random);
                });
        }
        #[cfg(not(feature = "std"))]
        {
            // In no_std environment, we can't access QRNG
            // This should only be used in WASM runtime
            compile_error!("Wallet requires std feature for QRNG access");
        }
        random
    }
}

// Async I/O operations (separate from quantum ops)
#[cfg(feature = "std")]
pub mod async_io {
    use super::*;

    /// Channel for quantum measurements
    pub type QuantumChannel = mpsc::Sender<MeasurementResult>;

    /// Async task for storing measurements
    pub async fn store_measurements(
        mut rx: mpsc::Receiver<MeasurementResult>,
    ) -> Result<(), WalletError> {
        while let Some(measurement) = rx.recv().await {
            // Store to database, send over network, etc.
            println!("Storing measurement: {:?}", measurement);
            
            // Simulate async I/O
            tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
        }
        Ok(())
    }

    /// Async task for syncing with network
    pub async fn sync_with_network(
        wallet_state: Arc<Mutex<WalletState>>,
    ) -> Result<(), WalletError> {
        loop {
            // Fetch latest block height from network
            let new_height = fetch_latest_height().await?;
            
            // Update wallet state
            {
                let mut state = wallet_state.lock().unwrap();
                state.sync_height = new_height;
            }
            
            tokio::time::sleep(tokio::time::Duration::from_secs(5)).await;
        }
    }

    async fn fetch_latest_height() -> Result<u64, WalletError> {
        // Simulate network request
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
        Ok(12345)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_wallet_state_transitions() {
        // Create locked wallet
        let wallet = QPPWallet::<Locked>::new();
        
        // Unlock wallet
        let mut wallet = wallet.unlock("password").unwrap();
        
        // Create accounts
        let classical = wallet.create_account("classical").unwrap();
        let quantum = wallet.create_account("quantum").unwrap();
        let hybrid = wallet.create_account("hybrid").unwrap();
        
        // Generate quantum keys
        let key_count = wallet.generate_quantum_keys(5).unwrap();
        assert_eq!(key_count, 5);
        
        // Use a quantum key
        let key = wallet.use_quantum_key().unwrap();
        assert_eq!(key.len(), 32);
        
        // Check state
        let state = wallet.get_state();
        assert_eq!(state.accounts.len(), 3);
        assert_eq!(state.quantum_keys_available, 4);
    }

    #[test]
    fn test_sync_state() {
        let wallet = QPPWallet::<Locked>::new();
        let wallet = wallet.unlock("password").unwrap();
        
        // Start syncing
        let mut syncing_wallet = wallet.start_sync();
        
        // Update sync
        syncing_wallet.update_sync(1000).unwrap();
        
        // Complete sync
        let wallet = syncing_wallet.complete_sync();
        
        let state = wallet.get_state();
        assert_eq!(state.sync_height, 1000);
    }

    // This should NOT compile:
    // #[test]
    // fn test_invalid_state_access() {
    //     let wallet = QPPWallet::<Locked>::new();
    //     wallet.create_account("classical"); // ❌ Error: method not found for Locked state
    // }
}