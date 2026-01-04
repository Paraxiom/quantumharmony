//! # PQ-Triple-Ratchet
//!
//! Post-quantum secure messaging protocol for QuantumHarmony validator coordination.
//!
//! ## Security Properties
//!
//! - **Post-Quantum Key Exchange**: ML-KEM-768 (NIST standard)
//! - **Post-Quantum Signatures**: SPHINCS+-SHA2-256f
//! - **Forward Secrecy**: Double Ratchet with PQ-KEM ratchet
//! - **Post-Compromise Security**: Automatic healing after key compromise
//! - **Anonymous Authentication**: ZK proofs of validator set membership
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
//! │  X3DH (X25519 || ML-KEM-768) + Double Ratchet       │
//! ├─────────────────────────────────────────────────────┤
//! │  ChaCha20-Poly1305 AEAD                             │
//! └─────────────────────────────────────────────────────┘
//! ```

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

pub use error::{Error, Result};
pub use keys::{IdentityKeyPair, PreKeyBundle, SignedPreKey};
pub use message::{EncryptedMessage, PlaintextMessage};
pub use ratchet::RatchetState;
pub use x3dh::X3DHSession;

/// Protocol version for wire compatibility
pub const PROTOCOL_VERSION: u8 = 1;

/// Maximum message size (64KB)
pub const MAX_MESSAGE_SIZE: usize = 65536;

/// Ratchet key rotation interval (messages)
pub const RATCHET_INTERVAL: u32 = 100;
