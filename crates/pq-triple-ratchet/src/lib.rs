//! # PQ-Triple-Ratchet
//!
//! Post-quantum secure messaging protocol for QuantumHarmony validator coordination.
//!
//! ## Security Properties
//!
//! - **Post-Quantum Key Exchange**: ML-KEM-768/1024 (NIST standard, configurable)
//! - **Post-Quantum Signatures**: SPHINCS+-SHA2-256f
//! - **Forward Secrecy**: Double Ratchet with PQ-KEM ratchet
//! - **Post-Compromise Security**: Automatic healing after key compromise
//! - **Anonymous Authentication**: ZK proofs of validator set membership
//! - **Configurable Security Level**: ML-KEM-768 (Level 3) or ML-KEM-1024 (Level 5)
//!
//! ## Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────┐
//! │                    Message                          │
//! ├─────────────────────────────────────────────────────┤
//! │  ZK Membership Proof (optional)                     │
//! │  "I am a validator" without revealing identity      │
//! ├─────────────────────────────────────────────────────┤
//! │  Triple Ratchet Encryption                          │
//! │  X3DH (X25519 || ML-KEM-768/1024) + Double Ratchet │
//! ├─────────────────────────────────────────────────────┤
//! │  ChaCha20-Poly1305 AEAD                             │
//! └─────────────────────────────────────────────────────┘
//! ```
//!
//! ## ML-KEM Security Levels
//!
//! The crate supports two ML-KEM security levels:
//!
//! | Level | Variant | NIST Security | Quantum Security | Key Sizes |
//! |-------|---------|---------------|-----------------|-----------|
//! | Level 3 | ML-KEM-768 | 128-bit | 128-bit | PK: 1184, SK: 2400, CT: 1088 |
//! | Level 5 | ML-KEM-1024 | 256-bit | 256-bit | PK: 1568, SK: 3168, CT: 1568 |
//!
//! Use [`KemSecurityLevel`] to configure the security level for your application.
//! The default is ML-KEM-768 (Level 3) for backward compatibility.

#![forbid(unsafe_code)]
#![warn(missing_docs, rust_2018_idioms)]

pub mod crypto;
pub mod error;
pub mod keys;
pub mod message;
pub mod ratchet;
pub mod x3dh;

#[cfg(feature = "zk-membership")]
pub mod zk;

pub use crypto::{
    detect_kem_level,
    detect_kem_level_from_ciphertext,
    detect_kem_level_from_secret,
    kem_sizes,
    mlkem1024_decapsulate,
    mlkem1024_encapsulate,
    mlkem768_decapsulate,
    mlkem768_encapsulate,
    mlkem_decapsulate_ex,
    mlkem_decapsulate_ex as mlkem_decapsulate, // backward compat
    mlkem_encapsulate_ex,
    mlkem_encapsulate_ex as mlkem_encapsulate, // backward compat
    KemSecurityLevel,
    KemSecurityLevel::*,
};
pub use error::{Error, Result};
pub use keys::{IdentityKeyPair, PreKeyBundle, SignedPreKey};
pub use message::{EncryptedMessage, PlaintextMessage};
pub use ratchet::RatchetState;
pub use x3dh::X3DHSession;

/// Protocol version for wire compatibility
///
/// Version 1: ML-KEM-768 only
/// Version 2: ML-KEM-768/1024 configurable (current)
pub const PROTOCOL_VERSION: u8 = 2;

/// Maximum message size (64KB)
pub const MAX_MESSAGE_SIZE: usize = 65536;

/// Ratchet key rotation interval (messages)
pub const RATCHET_INTERVAL: u32 = 100;
