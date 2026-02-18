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

/// ML-KEM security level for the protocol.
///
/// Controls which ML-KEM parameter set is used for post-quantum key
/// encapsulation. Both levels provide defense-in-depth when combined
/// with classical X25519 DH.
///
/// # Migration Path (Issue #5)
///
/// 1. **Current default**: `Level3` (ML-KEM-768, NIST Level 3)
/// 2. **Upgrade path**: `Level5` (ML-KEM-1024, NIST Level 5)
/// 3. **Wire format**: The security level is encoded in the prekey bundle,
///    so peers can negotiate the highest common level.
///
/// # Key Sizes
///
/// | Parameter       | Level3 (768) | Level5 (1024) |
/// |-----------------|-------------|---------------|
/// | Public key      | 1,184 bytes | 1,568 bytes   |
/// | Secret key      | 2,400 bytes | 3,168 bytes   |
/// | Ciphertext      | 1,088 bytes | 1,568 bytes   |
/// | Shared secret   | 32 bytes    | 32 bytes      |
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum MlKemSecurityLevel {
    /// ML-KEM-768 (NIST Level 3, ~128-bit PQ security). Default.
    Level3,
    /// ML-KEM-1024 (NIST Level 5, ~192-bit PQ security). Recommended for
    /// high-value validator-to-validator channels.
    Level5,
}

impl Default for MlKemSecurityLevel {
    fn default() -> Self {
        MlKemSecurityLevel::Level3
    }
}

impl MlKemSecurityLevel {
    /// Public key size in bytes.
    pub const fn public_key_size(&self) -> usize {
        match self {
            MlKemSecurityLevel::Level3 => 1184,
            MlKemSecurityLevel::Level5 => 1568,
        }
    }

    /// Secret key size in bytes.
    pub const fn secret_key_size(&self) -> usize {
        match self {
            MlKemSecurityLevel::Level3 => 2400,
            MlKemSecurityLevel::Level5 => 3168,
        }
    }

    /// Ciphertext size in bytes.
    pub const fn ciphertext_size(&self) -> usize {
        match self {
            MlKemSecurityLevel::Level3 => 1088,
            MlKemSecurityLevel::Level5 => 1568,
        }
    }
}
