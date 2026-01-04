//! Error types for the PQ-Triple-Ratchet protocol.

use thiserror::Error;

/// Result type alias for this crate.
pub type Result<T> = std::result::Result<T, Error>;

/// Errors that can occur during protocol operations.
#[derive(Error, Debug)]
pub enum Error {
    /// Key generation failed
    #[error("key generation failed: {0}")]
    KeyGeneration(String),

    /// Key exchange failed
    #[error("key exchange failed: {0}")]
    KeyExchange(String),

    /// Encryption failed
    #[error("encryption failed: {0}")]
    Encryption(String),

    /// Decryption failed (bad key, corrupted ciphertext, or replay attack)
    #[error("decryption failed: {0}")]
    Decryption(String),

    /// Signature verification failed
    #[error("signature verification failed")]
    SignatureVerification,

    /// Invalid prekey bundle
    #[error("invalid prekey bundle: {0}")]
    InvalidPreKeyBundle(String),

    /// Ratchet state error
    #[error("ratchet state error: {0}")]
    RatchetState(String),

    /// Message too large
    #[error("message too large: {size} bytes (max {max})")]
    MessageTooLarge { size: usize, max: usize },

    /// Message replay detected (duplicate message counter)
    #[error("message replay detected")]
    ReplayDetected,

    /// Session not established
    #[error("session not established - perform key exchange first")]
    SessionNotEstablished,

    /// ZK proof verification failed
    #[error("ZK membership proof verification failed")]
    ZkProofVerification,

    /// ZK proof generation failed
    #[error("ZK proof generation failed: {0}")]
    ZkProofGeneration(String),

    /// Serialization error
    #[error("serialization error: {0}")]
    Serialization(String),

    /// Invalid protocol version
    #[error("invalid protocol version: got {got}, expected {expected}")]
    InvalidVersion { got: u8, expected: u8 },
}

impl From<bincode::Error> for Error {
    fn from(e: bincode::Error) -> Self {
        Error::Serialization(e.to_string())
    }
}
