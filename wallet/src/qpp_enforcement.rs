//! QPP (Quantum Preservation Pattern) enforcement for wallet operations
//!
//! This module enforces the quantum no-cloning theorem at the type system level
//! for all critical wallet operations including:
//! - Key generation (keys can only be generated once)
//! - Signature creation (keys must be consumed after use)
//! - Transaction building (prevents quantum state cloning)
//! - QRNG usage (entropy is consumed, not reused)

use crate::{
    no_clone::NoClone,
    quantum_state::{QuantumKey, QuantumState, Initialized, Superposition, Measured},
    types::{WalletError, AccountType, QuantumAccountId},
};
#[cfg(feature = "std")]
use crate::qrng_client;

use sp_core::{H256, Pair, crypto::AccountId32};
use sp_core::sr25519;
use scale_codec::{Encode, Decode};
use core::marker::PhantomData;

#[cfg(not(feature = "std"))]
use alloc::{vec, vec::Vec};
#[cfg(feature = "std")]
use std::{vec, vec::Vec};

/// Quantum entropy that can only be used once
pub struct QuantumEntropy {
    /// The entropy data (protected from cloning)
    pub(crate) data: NoClone<Vec<u8>>,
    /// Entropy ID for tracking
    pub(crate) id: H256,
    /// Marker to ensure single use
    pub(crate) consumed: bool,
}

impl QuantumEntropy {
    /// Create new quantum entropy (consumes QRNG output)
    pub fn from_qrng(size: usize) -> Result<Self, WalletError> {
        let mut entropy_data = vec![0u8; size];
        
        #[cfg(feature = "std")]
        {
            qrng_client::fill_quantum_bytes(&mut entropy_data)?;
        }
        #[cfg(not(feature = "std"))]
        {
            return Err(WalletError::CryptoError("QRNG requires std feature".into()));
        }
        
        let id = sp_core::blake2_256(&entropy_data).into();
        
        Ok(QuantumEntropy {
            data: NoClone::new(entropy_data),
            id,
            consumed: false,
        })
    }
    
    /// Consume the entropy (can only be done once)
    pub fn consume(mut self) -> Result<Vec<u8>, WalletError> {
        if self.consumed {
            return Err(WalletError::QuantumStateError("Entropy already consumed".into()));
        }
        self.consumed = true;
        Ok(self.data.into_inner())
    }
    
    /// Get entropy ID
    pub fn id(&self) -> H256 {
        self.id
    }
}

/// Quantum key generation with enforced single use
pub struct QuantumKeyGenerator {
    /// Generator state (cannot be cloned)
    state: NoClone<GeneratorState>,
}

struct GeneratorState {
    /// Available entropy packets
    pub(crate) entropy_pool: Vec<QuantumEntropy>,
    /// Generation counter
    pub(crate) generation_count: u64,
}

impl QuantumKeyGenerator {
    /// Create new key generator
    pub fn new() -> Self {
        QuantumKeyGenerator {
            state: NoClone::new(GeneratorState {
                entropy_pool: Vec::new(),
                generation_count: 0,
            }),
        }
    }
    
    /// Add quantum entropy to the pool
    pub fn add_entropy(&mut self, entropy: QuantumEntropy) {
        self.state.entropy_pool.push(entropy);
    }
    
    /// Generate a new quantum key (consumes entropy)
    pub fn generate_key(mut self) -> Result<(QuantumKey, Self), WalletError> {
        let entropy = self.state.entropy_pool
            .pop()
            .ok_or(WalletError::QuantumStateError("No entropy available".into()))?;
        
        let key_material = entropy.consume()?;
        
        if key_material.len() < 32 {
            return Err(WalletError::CryptoError("Insufficient entropy".into()));
        }
        
        let mut key_bytes = [0u8; 32];
        key_bytes.copy_from_slice(&key_material[..32]);
        
        let quantum_key = QuantumKey::new(key_bytes);
        self.state.generation_count += 1;
        
        Ok((quantum_key, self))
    }
    
    /// Get generation count
    pub fn generation_count(&self) -> u64 {
        self.state.generation_count
    }
}

/// Quantum signature with enforced single use
pub struct QuantumSignature {
    /// The signature data (protected from cloning)
    data: NoClone<Vec<u8>>,
    /// Key ID that was used
    key_id: H256,
    /// Message hash that was signed
    message_hash: H256,
}

impl QuantumSignature {
    /// Get signature bytes (consumes the signature)
    pub fn into_bytes(self) -> Vec<u8> {
        self.data.into_inner()
    }
    
    /// Get key ID
    pub fn key_id(&self) -> H256 {
        self.key_id
    }
    
    /// Get message hash
    pub fn message_hash(&self) -> H256 {
        self.message_hash
    }
}

/// Quantum signer that enforces key consumption
pub struct QuantumSigner {
    /// Available quantum keys
    keys: NoClone<Vec<QuantumKey>>,
}

impl QuantumSigner {
    /// Create new signer with quantum keys
    pub fn new(keys: Vec<QuantumKey>) -> Self {
        QuantumSigner {
            keys: NoClone::new(keys),
        }
    }
    
    /// Sign a message (consumes a quantum key)
    pub fn sign_message(&mut self, message: &[u8]) -> Result<QuantumSignature, WalletError> {
        let key = self.keys.as_mut()
            .pop()
            .ok_or(WalletError::QuantumStateError("No quantum keys available".into()))?;
        
        let key_id = key.id();
        let key_material = key.use_key()
            .map_err(|e| WalletError::QuantumStateError(e.into()))?;
        
        // Create signature using quantum key material
        // In real implementation, this would use SPHINCS+ or similar
        let message_hash: H256 = sp_core::blake2_256(message).into();
        
        // Combine key material with message hash for signature
        let mut sig_input = Vec::new();
        sig_input.extend_from_slice(&key_material);
        sig_input.extend_from_slice(message_hash.as_bytes());
        
        let signature_data = sp_core::blake2_256(&sig_input).to_vec();
        
        Ok(QuantumSignature {
            data: NoClone::new(signature_data),
            key_id,
            message_hash,
        })
    }
    
    /// Get remaining key count
    pub fn remaining_keys(&self) -> usize {
        self.keys.as_ref().len()
    }
}

/// Transaction builder with quantum state protection
pub struct QuantumTransactionBuilder<S> {
    /// Transaction data (protected from cloning)
    data: NoClone<TransactionData>,
    /// State marker
    _state: PhantomData<S>,
}

// Transaction states
pub struct Building;
pub struct ReadyToSign;
pub struct Signed;

struct TransactionData {
    /// From account
    pub(crate) from: AccountType,
    /// To account
    pub(crate) to: Option<AccountType>,
    /// Amount
    pub(crate) amount: Option<u128>,
    /// Call data
    pub(crate) call_data: Vec<u8>,
    /// Signature (if signed)
    pub(crate) signature: Option<QuantumSignature>,
    /// Nonce (consumed on use)
    pub(crate) nonce: Option<NoClone<u64>>,
}

impl QuantumTransactionBuilder<Building> {
    /// Create new transaction builder
    pub fn new(from: AccountType) -> Self {
        QuantumTransactionBuilder {
            data: NoClone::new(TransactionData {
                from,
                to: None,
                amount: None,
                call_data: Vec::new(),
                signature: None,
                nonce: None,
            }),
            _state: PhantomData,
        }
    }
    
    /// Set recipient
    pub fn to(mut self, to: AccountType) -> Self {
        self.data.to = Some(to);
        self
    }
    
    /// Set amount
    pub fn amount(mut self, amount: u128) -> Self {
        self.data.amount = Some(amount);
        self
    }
    
    /// Set call data
    pub fn call_data(mut self, data: Vec<u8>) -> Self {
        self.data.call_data = data;
        self
    }
    
    /// Add nonce (quantum-protected)
    pub fn with_nonce(mut self, nonce: u64) -> Self {
        self.data.nonce = Some(NoClone::new(nonce));
        self
    }
    
    /// Finalize for signing
    pub fn finalize(self) -> Result<QuantumTransactionBuilder<ReadyToSign>, WalletError> {
        // Validate transaction
        if self.data.to.is_none() && self.data.call_data.is_empty() {
            return Err(WalletError::InvalidTransaction("Missing recipient or call data".into()));
        }
        
        Ok(QuantumTransactionBuilder {
            data: self.data,
            _state: PhantomData,
        })
    }
}

impl QuantumTransactionBuilder<ReadyToSign> {
    /// Sign the transaction (consumes the builder and a quantum key)
    pub fn sign(mut self, signer: &mut QuantumSigner) -> Result<QuantumTransactionBuilder<Signed>, WalletError> {
        // Encode transaction data
        let mut tx_data = Vec::new();
        tx_data.extend_from_slice(&self.data.from.encode());
        if let Some(ref to) = self.data.to {
            tx_data.extend_from_slice(&to.encode());
        }
        if let Some(amount) = self.data.amount {
            tx_data.extend_from_slice(&amount.encode());
        }
        tx_data.extend_from_slice(&self.data.call_data);
        
        // Consume nonce if present
        if let Some(nonce_wrapper) = self.data.nonce.take() {
            let nonce = nonce_wrapper.into_inner();
            tx_data.extend_from_slice(&nonce.encode());
        }
        
        // Sign with quantum key
        let signature = signer.sign_message(&tx_data)?;
        self.data.signature = Some(signature);
        
        Ok(QuantumTransactionBuilder {
            data: self.data,
            _state: PhantomData,
        })
    }
}

impl QuantumTransactionBuilder<Signed> {
    /// Build the final transaction (consumes the builder)
    pub fn build(self) -> Result<QuantumTransaction, WalletError> {
        let data = self.data.into_inner();
        let signature = data.signature
            .ok_or(WalletError::InvalidTransaction("Missing signature".into()))?;
        
        Ok(QuantumTransaction {
            from: data.from,
            to: data.to,
            amount: data.amount,
            call_data: data.call_data,
            signature,
        })
    }
}

/// Final quantum transaction (immutable)
pub struct QuantumTransaction {
    pub from: AccountType,
    pub to: Option<AccountType>,
    pub amount: Option<u128>,
    pub call_data: Vec<u8>,
    pub signature: QuantumSignature,
}

impl QuantumTransaction {
    /// Encode for submission (consumes the transaction)
    pub fn encode_for_submission(self) -> Vec<u8> {
        let mut encoded = Vec::new();
        encoded.extend_from_slice(&self.from.encode());
        if let Some(to) = self.to {
            encoded.extend_from_slice(&to.encode());
        }
        if let Some(amount) = self.amount {
            encoded.extend_from_slice(&amount.encode());
        }
        encoded.extend_from_slice(&self.call_data);
        encoded.extend_from_slice(&self.signature.into_bytes());
        encoded
    }
}

/// Quantum account creator with enforced entropy consumption
pub struct QuantumAccountCreator {
    /// Entropy for account creation
    entropy: NoClone<QuantumEntropy>,
}

impl QuantumAccountCreator {
    /// Create new account creator with quantum entropy
    pub fn new(entropy: QuantumEntropy) -> Self {
        QuantumAccountCreator {
            entropy: NoClone::new(entropy),
        }
    }
    
    /// Create a quantum account (consumes the creator)
    pub fn create_quantum_account(self) -> Result<QuantumAccountId, WalletError> {
        let entropy_data = self.entropy.into_inner().consume()?;
        
        if entropy_data.len() < 32 {
            return Err(WalletError::CryptoError("Insufficient entropy for account".into()));
        }
        
        let mut hash = [0u8; 32];
        hash.copy_from_slice(&entropy_data[..32]);
        
        Ok(QuantumAccountId {
            hash: H256::from(hash),
            variant: crate::types::SphincsVariant::Medium,
        })
    }
    
    /// Create a classical account with quantum entropy (consumes the creator)
    pub fn create_classical_account(self) -> Result<AccountId32, WalletError> {
        let entropy_data = self.entropy.into_inner().consume()?;
        
        // Use quantum entropy as seed for classical key generation
        let pair = sr25519::Pair::from_seed_slice(&entropy_data)
            .map_err(|_| WalletError::CryptoError("Failed to create keypair".into()))?;

        // SPHINCS+ public keys need explicit byte conversion
        let public_key = pair.public();
        let pub_bytes: &[u8] = public_key.as_ref();
        let account_bytes = <[u8; 32]>::try_from(&pub_bytes[..32])
            .map_err(|_| WalletError::CryptoError("Invalid public key length".into()))?;
        Ok(AccountId32::from(account_bytes))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_quantum_entropy_single_use() {
        // Create quantum entropy
        let entropy = QuantumEntropy {
            data: NoClone::new(vec![1, 2, 3, 4]),
            id: H256::default(),
            consumed: false,
        };
        
        // Consume it once
        let data = entropy.consume().unwrap();
        assert_eq!(data, vec![1, 2, 3, 4]);
        
        // Second consume would fail (can't test because entropy is moved)
    }
    
    #[test]
    fn test_quantum_key_generation() {
        // Create generator
        let mut generator = QuantumKeyGenerator::new();
        
        // Add entropy
        let entropy = QuantumEntropy {
            data: NoClone::new(vec![0u8; 32]),
            id: H256::default(),
            consumed: false,
        };
        generator.add_entropy(entropy);
        
        // Generate key (consumes generator)
        let (key, new_generator) = generator.generate_key().unwrap();
        assert_eq!(new_generator.generation_count(), 1);
    }
    
    #[test]
    fn test_transaction_builder_state_transitions() {
        // Create account
        let from = AccountType::Classical(AccountId32::from([0u8; 32]));
        let to = AccountType::Classical(AccountId32::from([1u8; 32]));
        
        // Build transaction
        let builder = QuantumTransactionBuilder::<Building>::new(from.clone())
            .to(to)
            .amount(1000)
            .with_nonce(1);
        
        // Finalize for signing
        let ready = builder.finalize().unwrap();
        
        // Would need a signer to test signing
        // let signed = ready.sign(&mut signer).unwrap();
        // let tx = signed.build().unwrap();
    }
    
    // This should NOT compile:
    // #[test]
    // fn test_invalid_state_transition() {
    //     let from = AccountType::Classical(AccountId32::from([0u8; 32]));
    //     let builder = QuantumTransactionBuilder::<Building>::new(from);
    //     let tx = builder.build(); // ❌ Error: no method `build` on Building state
    // }
}