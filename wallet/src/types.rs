//! Common types for QPP wallet

use scale_codec::{Encode, Decode};
use scale_info::TypeInfo;
use serde::{Serialize, Deserialize};
use sp_core::{H256, crypto::AccountId32};

#[cfg(not(feature = "std"))]
use alloc::{vec::Vec, string::String, format};
#[cfg(feature = "std")]
use std::{vec::Vec, string::String};

/// Account type that can be either classical or quantum
#[derive(Debug, Clone, PartialEq, Eq, Encode, Decode, TypeInfo, Serialize, Deserialize)]
pub enum AccountType {
    /// Classical Ed25519/Sr25519 account
    Classical(AccountId32),
    /// Quantum SPHINCS+ account
    Quantum(QuantumAccountId),
    /// Hybrid account with both key types
    Hybrid {
        classical: AccountId32,
        quantum: QuantumAccountId,
    },
}

/// Quantum account identifier
#[derive(Debug, Clone, PartialEq, Eq, Encode, Decode, TypeInfo, Serialize, Deserialize)]
pub struct QuantumAccountId {
    /// SPHINCS+ public key hash
    pub hash: H256,
    /// Key size variant
    pub variant: SphincsVariant,
}

/// SPHINCS+ key size variants
#[derive(Debug, Clone, Copy, PartialEq, Eq, Encode, Decode, TypeInfo, Serialize, Deserialize)]
pub enum SphincsVariant {
    /// Small variant (fast, less secure)
    Small,
    /// Medium variant (balanced)
    Medium,
    /// Large variant (slow, most secure)
    Large,
}

/// Balance information for dual-system
#[derive(Debug, Clone, PartialEq, Eq, Encode, Decode, TypeInfo, Serialize, Deserialize)]
pub struct Balance {
    /// Classical balance (standard transactions)
    pub classical: u128,
    /// Quantum balance (quantum-secured transactions)
    pub quantum: u128,
    /// Locked balance (in bridge)
    pub locked: u128,
}

/// Transaction type
#[derive(Debug, Clone, PartialEq, Eq, Encode, Decode, TypeInfo, Serialize, Deserialize)]
pub enum TransactionType {
    /// Standard classical transaction
    Classical,
    /// Quantum-secured transaction
    Quantum {
        /// Enable zero-knowledge privacy
        privacy: bool,
        /// Time-lock using quantum uncertainty
        time_lock: Option<u64>,
    },
    /// Bridge transaction
    Bridge(BridgeDirection),
}

/// Bridge direction
#[derive(Debug, Clone, Copy, PartialEq, Eq, Encode, Decode, TypeInfo, Serialize, Deserialize)]
pub enum BridgeDirection {
    /// Lock classical tokens, mint quantum tokens
    ClassicalToQuantum,
    /// Burn quantum tokens, unlock classical tokens
    QuantumToClassical,
}

/// Light client proof type
#[derive(Debug, Clone, PartialEq, Eq, Encode, Decode, TypeInfo)]
pub enum ProofType {
    /// Classical Merkle proof
    Classical(Vec<H256>),
    /// Quantum fingerprint proof
    Quantum {
        /// Quantum state fingerprint
        fingerprint: Vec<u8>,
        /// Measurement results
        measurements: Vec<bool>,
        /// Verification threshold (as percentage 0-100)
        threshold: u8,
    },
}

/// Wallet error types
#[derive(Debug, thiserror::Error)]
pub enum WalletError {
    #[error("Account not found: {0}")]
    AccountNotFound(String),
    
    #[error("Insufficient balance: required {required}, available {available}")]
    InsufficientBalance { required: u128, available: u128 },
    
    #[error("Quantum state error: {0}")]
    QuantumStateError(String),
    
    #[error("Bridge error: {0}")]
    BridgeError(String),
    
    #[error("Sync error: {0}")]
    SyncError(String),
    
    #[error("Cryptographic error: {0}")]
    CryptoError(String),
    
    #[error("Connection error: {0}")]
    ConnectionError(String),
    
    #[error("Invalid address: {0}")]
    InvalidAddress(String),
    
    #[error("Invalid input: {0}")]
    InvalidInput(String),
    
    #[error("Resource exhausted: {0}")]
    ResourceExhausted(String),
    
    #[error("Invalid context: {0}")]
    InvalidContext(String),
    
    #[error("No available context: {0}")]
    NoAvailableContext(String),
    
    #[error("Invalid transaction: {0}")]
    InvalidTransaction(String),

    #[error("RPC error: {0}")]
    RpcError(String),
}