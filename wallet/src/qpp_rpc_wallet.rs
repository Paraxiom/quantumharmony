//! RPC Wallet with QPP enforcement
//! 
//! This module extends the RPC wallet with quantum preservation patterns
//! to ensure quantum safety in all operations.

use crate::{
    no_clone::NoClone,
    qpp_enforcement::{
        QuantumEntropy, QuantumSigner, QuantumTransactionBuilder,
        QuantumTransaction, QuantumSignature,
    },
    types::{WalletError, AccountType},
};
use sp_core::{
    crypto::{Ss58Codec, AccountId32},
    sr25519::{Pair as Sr25519Pair, Public as Sr25519Public},
    H256, Pair,
};
use std::collections::HashMap;
use scale_codec::Encode;

/// RPC client for blockchain interaction
pub use crate::rpc_wallet::RpcClient;

/// QPP-enforced RPC wallet states
pub struct QPPLocked;
pub struct QPPUnlocked;
pub struct QPPSigning;

/// QPP-enforced RPC wallet
pub struct QPPRpcWallet<S> {
    /// Wallet data (protected from cloning)
    data: NoClone<QPPWalletData>,
    /// RPC client
    rpc: RpcClient,
    /// State marker
    _state: std::marker::PhantomData<S>,
}

struct QPPWalletData {
    /// Account keypairs (classical)
    accounts: HashMap<String, Sr25519Pair>,
    /// Quantum signer for transactions
    quantum_signer: Option<QuantumSigner>,
    /// Current nonce tracker (single-use)
    nonce_tracker: HashMap<String, NoClone<u64>>,
}

impl QPPRpcWallet<QPPLocked> {
    /// Create new QPP-enforced RPC wallet
    pub fn new(rpc_endpoint: String) -> Self {
        QPPRpcWallet {
            data: NoClone::new(QPPWalletData {
                accounts: HashMap::new(),
                quantum_signer: None,
                nonce_tracker: HashMap::new(),
            }),
            rpc: RpcClient::new(rpc_endpoint),
            _state: std::marker::PhantomData,
        }
    }
    
    /// Unlock wallet (transitions to unlocked state)
    pub fn unlock(mut self, _password: &str) -> Result<QPPRpcWallet<QPPUnlocked>, WalletError> {
        // In production, decrypt wallet data
        // Initialize quantum signer on unlock
        self.data.quantum_signer = Some(QuantumSigner::new(Vec::new()));
        
        Ok(QPPRpcWallet {
            data: self.data,
            rpc: self.rpc,
            _state: std::marker::PhantomData,
        })
    }
}

impl QPPRpcWallet<QPPUnlocked> {
    /// Create account with quantum entropy
    pub fn create_account(&mut self, name: &str) -> Result<String, WalletError> {
        // Get quantum entropy for key generation
        let entropy = QuantumEntropy::from_qrng(64)?;
        let entropy_data = entropy.consume()?;
        
        // Generate keypair with quantum seed
        let pair = Sr25519Pair::from_seed_slice(&entropy_data)
            .map_err(|_| WalletError::CryptoError("Failed to create keypair".into()))?;
        
        let address = pair.public().to_ss58check();
        self.data.accounts.insert(address.clone(), pair);
        
        // Initialize nonce tracker for this account
        self.data.nonce_tracker.insert(address.clone(), NoClone::new(0));
        
        Ok(address)
    }
    
    /// Add quantum keys for signing
    pub fn add_quantum_keys(&mut self, count: usize) -> Result<(), WalletError> {
        let mut keys = Vec::new();
        
        for _ in 0..count {
            let entropy = QuantumEntropy::from_qrng(32)?;
            let key_data = entropy.consume()?;
            
            let mut key_bytes = [0u8; 32];
            key_bytes.copy_from_slice(&key_data[..32]);
            
            keys.push(crate::quantum_state::QuantumKey::new(key_bytes));
        }
        
        // Replace signer with new keys
        self.data.quantum_signer = Some(QuantumSigner::new(keys));
        
        Ok(())
    }
    
    /// Start building a transaction (transitions to signing state)
    pub fn start_transaction(self, from: &str) -> Result<QPPRpcWallet<QPPSigning>, WalletError> {
        // Verify account exists
        if !self.data.accounts.contains_key(from) {
            return Err(WalletError::AccountNotFound(from.to_string()));
        }
        
        Ok(QPPRpcWallet {
            data: self.data,
            rpc: self.rpc,
            _state: std::marker::PhantomData,
        })
    }
    
    /// Get account balance
    pub async fn get_balance(&self, account: &str) -> Result<u128, WalletError> {
        self.rpc.get_balance(account).await
    }
}

impl QPPRpcWallet<QPPSigning> {
    /// Build and sign transaction with QPP enforcement
    pub async fn build_and_sign_transaction(
        mut self,
        from: &str,
        to: &str,
        amount: u128,
    ) -> Result<(String, QPPRpcWallet<QPPUnlocked>), WalletError> {
        // Get account
        let pair = self.data.accounts.get(from)
            .ok_or(WalletError::AccountNotFound(from.to_string()))?;
        
        // Create transaction builder
        // SPHINCS+ public keys need explicit byte conversion
        let from_public = pair.public();
        let from_bytes: &[u8] = from_public.as_ref();
        let from_account_id = AccountId32::from(<[u8; 32]>::try_from(&from_bytes[..32])
            .map_err(|_| WalletError::CryptoError("Invalid public key length".into()))?);
        let from_account = AccountType::Classical(from_account_id);

        // Parse to address
        let to_public = Sr25519Public::from_ss58check(to)
            .map_err(|_| WalletError::InvalidAddress(to.to_string()))?;
        let to_bytes: &[u8] = to_public.as_ref();
        let to_account_id = AccountId32::from(<[u8; 32]>::try_from(&to_bytes[..32])
            .map_err(|_| WalletError::CryptoError("Invalid public key length".into()))?);
        let to_account = AccountType::Classical(to_account_id);
        
        // Get and consume nonce
        let nonce = self.data.nonce_tracker
            .remove(from)
            .ok_or(WalletError::InvalidTransaction("No nonce available".into()))?
            .into_inner();
        
        // Build transaction with QPP enforcement
        let builder = QuantumTransactionBuilder::new(from_account)
            .to(to_account)
            .amount(amount)
            .with_nonce(nonce);
        
        let ready = builder.finalize()?;
        
        // Sign with quantum key
        let signer = self.data.quantum_signer.as_mut()
            .ok_or(WalletError::QuantumStateError("No quantum signer available".into()))?;
        
        let signed = ready.sign(signer)?;
        let transaction = signed.build()?;
        
        // Encode and submit
        let encoded_tx = transaction.encode_for_submission();
        let tx_hash = self.rpc.submit_extrinsic(encoded_tx).await?;
        
        // Update nonce for next transaction
        self.data.nonce_tracker.insert(from.to_string(), NoClone::new(nonce + 1));
        
        // Return to unlocked state
        Ok((tx_hash, QPPRpcWallet {
            data: self.data,
            rpc: self.rpc,
            _state: std::marker::PhantomData,
        }))
    }
    
    /// Cancel transaction and return to unlocked state
    pub fn cancel(self) -> QPPRpcWallet<QPPUnlocked> {
        QPPRpcWallet {
            data: self.data,
            rpc: self.rpc,
            _state: std::marker::PhantomData,
        }
    }
}

/// Create QPP-enforced production wallet
pub fn create_qpp_production_wallet(endpoint: &str) -> QPPRpcWallet<QPPLocked> {
    QPPRpcWallet::new(endpoint.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_qpp_wallet_state_transitions() {
        // Create locked wallet
        let wallet = create_qpp_production_wallet("ws://localhost:9933");
        
        // Unlock wallet
        let mut wallet = wallet.unlock("password").unwrap();
        
        // Create account with quantum entropy
        let account = wallet.create_account("alice").unwrap();
        assert!(!account.is_empty());
        
        // Add quantum keys
        wallet.add_quantum_keys(5).unwrap();
    }
    
    // This should NOT compile:
    // #[test]
    // fn test_invalid_state_access() {
    //     let wallet = create_qpp_production_wallet("ws://localhost:9933");
    //     wallet.create_account("alice"); // ❌ Error: method not found for QPPLocked
    // }
}