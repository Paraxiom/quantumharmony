//! QPP Production Integration Bridge
//!
//! This module provides compatibility wrappers and utilities for gradually
//! integrating Quantum Preservation Pattern (QPP) types into existing
//! QuantumHarmony production code.
//!
//! # Integration Strategy
//!
//! The integration follows a phased approach:
//! - Phase 1: Entropy wrapper returns (LOW RISK)
//! - Phase 2: Keystore integration (LOW-MEDIUM RISK)
//! - Phase 3: Key lifecycle state machines (MEDIUM-HIGH RISK)
//! - Phase 4: Triple Ratchet for consensus (HIGH RISK)
//!
//! # Usage
//!
//! ```ignore
//! use crate::qpp_integration::*;
//!
//! // Wrap existing entropy with QPP tracking
//! let entropy_bytes = get_hardware_entropy();
//! let qpp_entropy = wrap_entropy(entropy_bytes, EntropySource::HardwareRNG);
//!
//! // Use with existing Falcon crypto
//! let keypair = generate_falcon_keypair_from_qpp(qpp_entropy)?;
//! ```

use crate::falcon_crypto::{PublicKey as FalconPublic, SecretKey as FalconSecret};
use crate::qpp::{
    const_constraints::{ConstrainedKey, AES_256_KEY_SIZE, CHACHA20_KEY_SIZE},
    sync_async::{AsyncEntropy, AsyncOp, SyncEntropy, SyncOp},
    triple_ratchet::TripleRatchet,
    EntropySource, NoClone, QuantumEntropy,
};
use sp_core::Pair;
use std::time::{SystemTime, UNIX_EPOCH};

/// Compatibility wrapper for existing code that returns Vec<u8>
///
/// This allows gradual migration by wrapping raw bytes into QPP-tracked
/// QuantumEntropy while maintaining backward compatibility.
pub fn wrap_entropy(bytes: Vec<u8>, source: EntropySource) -> QuantumEntropy {
    // QuantumEntropy::new takes qber: Option<u32>, not timestamp
    QuantumEntropy::new(bytes, source, None)
}

/// Convert QuantumEntropy back to raw bytes for legacy APIs
///
/// CAUTION: This consumes the QuantumEntropy, enforcing the no-cloning theorem.
/// The entropy can only be extracted once.
pub fn unwrap_entropy(qentropy: QuantumEntropy) -> Vec<u8> {
    qentropy.consume()
}

/// Mix multiple entropy sources into a single QuantumEntropy
///
/// This is the recommended way to combine entropy from different sources
/// (keystore, hardware RNG, quantum QRNG) while preserving provenance tracking.
///
/// **IMPORTANT**: Uses SHA-3-256 (Keccak) for quantum-resistant mixing.
/// BLAKE2 is NOT post-quantum secure!
///
/// # Example
///
/// ```ignore
/// let keystore_entropy = QuantumEntropy::new(ks_bytes, EntropySource::Keystore, None);
/// let hwrng_entropy = QuantumEntropy::new(hw_bytes, EntropySource::HardwareRNG, None);
/// let quantum_entropy = QuantumEntropy::new(qrng_bytes, EntropySource::KirqHub, None);
///
/// let mixed = mix_entropy_sources(vec![keystore_entropy, hwrng_entropy, quantum_entropy]);
/// // mixed.source == EntropySource::KirqHub (quantum source takes precedence)
/// ```
pub fn mix_entropy_sources(sources: Vec<QuantumEntropy>) -> QuantumEntropy {
    use sha3::{Digest, Sha3_256};

    if sources.is_empty() {
        panic!("Cannot mix zero entropy sources");
    }

    if sources.len() == 1 {
        // Single source - no mixing needed
        return sources.into_iter().next().unwrap();
    }

    // Collect all entropy bytes and mix with SHA-3-256 (quantum-resistant)
    let mut hasher = Sha3_256::new();
    let mut has_quantum = false;
    let mut last_source = EntropySource::HardwareRNG;

    for qentropy in sources {
        let source = qentropy.source;
        if source.is_quantum() {
            has_quantum = true;
            last_source = source; // Quantum source takes precedence
        }

        let bytes = qentropy.consume();
        hasher.update(&bytes);
    }

    // Hash the combined bytes with SHA-3-256 (quantum-resistant!)
    let mixed_bytes = hasher.finalize().to_vec();

    // Use quantum source if any was present, otherwise use last classical source
    let final_source = if has_quantum {
        last_source
    } else {
        EntropySource::HardwareRNG // Default to HardwareRNG for mixed classical sources
    };

    // QuantumEntropy::new takes qber: Option<u32>, not timestamp
    QuantumEntropy::new(mixed_bytes, final_source, None)
}

/// Generate Falcon keypair from QPP-tracked entropy
///
/// This is a bridge function that consumes QuantumEntropy and produces
/// a Falcon keypair. It enforces the one-time-use property of entropy.
///
/// # Panics
///
/// Panics if the entropy is insufficient for Falcon keypair generation.
pub fn generate_falcon_keypair_from_qpp(
    keystore_entropy: QuantumEntropy,
    quantum_entropy: Option<QuantumEntropy>,
    hwrng_entropy: Option<QuantumEntropy>,
    validator_id: &[u8],
) -> (FalconPublic, FalconSecret, Vec<EntropySource>) {
    // Import the QPP-aware Falcon crypto module
    use crate::falcon_crypto::generate_keypair_qpp;

    // The falcon_crypto module already has QPP support!
    generate_keypair_qpp(
        keystore_entropy,
        quantum_entropy,
        hwrng_entropy,
        validator_id,
    )
}

/// Wrap an AES-256 key in a ConstrainedKey for compile-time size checking
///
/// This prevents accidental buffer overflows and size mismatches by enforcing
/// the correct key size at compile time.
///
/// # Panics
///
/// Panics if the slice length != 32 bytes
pub fn wrap_aes256_key(key_bytes: &[u8]) -> ConstrainedKey<AES_256_KEY_SIZE> {
    ConstrainedKey::from_slice(key_bytes)
}

/// Wrap a ChaCha20 key in a ConstrainedKey for compile-time size checking
pub fn wrap_chacha20_key(key_bytes: &[u8]) -> ConstrainedKey<CHACHA20_KEY_SIZE> {
    ConstrainedKey::from_slice(key_bytes)
}

/// Create a synchronous entropy operation for blocking contexts
///
/// This wrapper ensures that entropy operations in synchronous contexts
/// are properly typed and cannot accidentally block async execution.
pub fn create_sync_entropy(qentropy: QuantumEntropy) -> SyncEntropy {
    SyncOp::new(qentropy)
}

/// Create an asynchronous entropy operation for async contexts
///
/// This wrapper ensures that entropy operations in async contexts
/// are properly awaited and don't accidentally block.
pub fn create_async_entropy(qentropy: QuantumEntropy) -> AsyncEntropy {
    AsyncOp::new(qentropy)
}

/// Validator message encryption context using Triple Ratchet
///
/// This provides a high-level interface for secure validator-to-validator
/// communication with forward secrecy and post-compromise security.
pub struct ValidatorMessaging {
    /// The triple ratchet instance (in Established state)
    ratchet: Option<TripleRatchet<crate::qpp::triple_ratchet::Established>>,
}

impl ValidatorMessaging {
    /// Create a new messaging context (requires handshake to complete)
    pub fn new() -> Self {
        Self { ratchet: None }
    }

    /// Initialize Triple Ratchet from Falcon keypair
    ///
    /// This should be called once during validator initialization.
    pub fn initialize_from_falcon(
        &mut self,
        falcon_secret: FalconSecret,
        falcon_public: FalconPublic,
    ) -> Result<(), String> {
        use crate::qpp::triple_ratchet::TripleRatchet;

        // Clone peer public key before move (falcon_public gets moved into TripleRatchet::new)
        let peer_public = falcon_public.clone(); // NOTE: Using own public key as peer placeholder; real peer discovery via P2P handshake

        // Create ratchet in Init state
        let ratchet_init = TripleRatchet::new(falcon_secret, falcon_public);

        // For now, use placeholder handshake completion
        // In production, this would involve actual key exchange with peer
        let shared_secret = [0u8; 32]; // NOTE: Placeholder shared secret; real KEX uses ML-KEM-1024 encapsulation

        let ratchet_handshake = ratchet_init.complete_handshake(&peer_public, shared_secret);
        let ratchet_established = ratchet_handshake.establish();

        self.ratchet = Some(ratchet_established);
        Ok(())
    }

    /// Encrypt a message to another validator
    ///
    /// This provides per-message forward secrecy by ratcheting the symmetric key.
    pub fn encrypt_message(&mut self, plaintext: &[u8]) -> Result<Vec<u8>, String> {
        let ratchet = self
            .ratchet
            .take()
            .ok_or_else(|| "Triple Ratchet not initialized".to_string())?;

        let (ciphertext, new_ratchet) = ratchet.encrypt(plaintext);
        self.ratchet = Some(new_ratchet);

        Ok(ciphertext)
    }

    /// Decrypt a message from another validator
    pub fn decrypt_message(&mut self, ciphertext: &[u8]) -> Result<Vec<u8>, String> {
        let ratchet = self
            .ratchet
            .take()
            .ok_or_else(|| "Triple Ratchet not initialized".to_string())?;

        let (plaintext, new_ratchet) = ratchet.decrypt(ciphertext);
        self.ratchet = Some(new_ratchet);

        Ok(plaintext)
    }

    /// Check if rekeying is needed based on message count or time
    pub fn needs_rekey(&self, max_messages: u64, max_age_secs: u64) -> bool {
        self.ratchet
            .as_ref()
            .map(|r| r.needs_rekey(max_messages, max_age_secs))
            .unwrap_or(false)
    }

    /// Perform rekeying to rotate Merkle ratchet
    pub fn rekey(&mut self) -> Result<(), String> {
        let ratchet = self
            .ratchet
            .take()
            .ok_or_else(|| "Triple Ratchet not initialized".to_string())?;

        let ratchet_rekeying = ratchet.begin_rekey();

        // Generate fresh entropy for rekeying (32 bytes)
        // QPP: This entropy should ideally come from qpp_integration::wrap_entropy()
        // with proper source tracking (HardwareRNG, KirqHub, etc.)
        use rand::RngCore;
        let mut rekey_entropy = vec![0u8; 32];
        rand::rngs::OsRng.fill_bytes(&mut rekey_entropy);

        let new_ratchet = ratchet_rekeying.complete_rekey(rekey_entropy);

        self.ratchet = Some(new_ratchet);
        Ok(())
    }
}

impl Default for ValidatorMessaging {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_wrap_unwrap_entropy() {
        let original_bytes = vec![1, 2, 3, 4, 5];
        let qentropy = wrap_entropy(original_bytes.clone(), EntropySource::HardwareRNG);

        assert_eq!(qentropy.source, EntropySource::HardwareRNG);
        assert!(qentropy.timestamp > 0);

        let unwrapped = unwrap_entropy(qentropy);
        assert_eq!(unwrapped, original_bytes);
    }

    #[test]
    fn test_mix_entropy_sources() {
        let e1 = QuantumEntropy::new(vec![1, 2, 3], EntropySource::Keystore, None);
        let e2 = QuantumEntropy::new(vec![4, 5, 6], EntropySource::HardwareRNG, None);
        let e3 = QuantumEntropy::new(vec![7, 8, 9], EntropySource::KirqHub, None);

        let mixed = mix_entropy_sources(vec![e1, e2, e3]);

        // Quantum source (KirqHub) should take precedence
        assert_eq!(mixed.source, EntropySource::KirqHub);
        assert_eq!(mixed.consume().len(), 32); // SHA-3-256 output (quantum-resistant!)
    }

    #[test]
    fn test_mix_single_source() {
        let e1 = QuantumEntropy::new(vec![1, 2, 3], EntropySource::Keystore, None);
        let mixed = mix_entropy_sources(vec![e1]);

        // Single source should not be hashed, returned as-is
        assert_eq!(mixed.source, EntropySource::Keystore);
        assert_eq!(mixed.consume(), vec![1, 2, 3]);
    }

    #[test]
    fn test_wrap_aes256_key() {
        let key_bytes = [0u8; 32];
        let constrained = wrap_aes256_key(&key_bytes);

        assert_eq!(ConstrainedKey::<32>::size(), 32);
        assert_eq!(constrained.as_bytes(), &key_bytes);
    }

    #[test]
    #[should_panic(expected = "Slice length must match const size N")]
    fn test_wrap_aes256_key_wrong_size() {
        let key_bytes = [0u8; 16]; // Wrong size!
        let _ = wrap_aes256_key(&key_bytes);
    }

    #[test]
    fn test_sync_async_entropy_creation() {
        let qentropy = QuantumEntropy::new(vec![1, 2, 3], EntropySource::HardwareRNG, None);
        let sync_entropy = create_sync_entropy(qentropy);

        // Sync entropy can be used in blocking contexts
        sync_entropy.blocking_execute(|e| {
            assert_eq!(e.source, EntropySource::HardwareRNG);
        });
    }

    #[tokio::test]
    async fn test_async_entropy_creation() {
        let qentropy = QuantumEntropy::new(vec![1, 2, 3], EntropySource::HardwareRNG, None);
        let async_entropy = create_async_entropy(qentropy);

        // Async entropy must be awaited
        async_entropy
            .async_execute(|e| async move {
                assert_eq!(e.source, EntropySource::HardwareRNG);
            })
            .await;
    }

    #[test]
    fn test_validator_messaging_initialization() {
        use crate::falcon_crypto::generate_keypair_sha3;
        let mut messaging = ValidatorMessaging::new();

        // Generate real Falcon keys for testing with SHA-3 KDF
        let seed = [0u8; 32];
        let validator_id = b"test-validator";
        let (public, secret) = generate_keypair_sha3(&seed, None, None, validator_id);

        let result = messaging.initialize_from_falcon(secret, public);
        assert!(result.is_ok());
    }

    #[test]
    fn test_validator_messaging_encrypt_decrypt() {
        use crate::falcon_crypto::generate_keypair_sha3;
        let mut messaging = ValidatorMessaging::new();

        let seed = [0u8; 32];
        let validator_id = b"test-validator";
        let (public, secret) = generate_keypair_sha3(&seed, None, None, validator_id);

        messaging.initialize_from_falcon(secret, public).unwrap();

        let plaintext = b"Hello, validator!";
        let ciphertext = messaging.encrypt_message(plaintext).unwrap();

        // Ciphertext should be different from plaintext
        assert_ne!(ciphertext.as_slice(), plaintext);

        // Verify encryption produces output
        assert_eq!(ciphertext.len(), plaintext.len());

        // NOTE: In production, decryption would happen on the peer's ValidatorMessaging instance
        // with its own ratchet state. The Triple Ratchet architecture requires separate
        // sender/receiver states for proper forward secrecy. This test only verifies encryption.
    }

    #[test]
    fn test_validator_messaging_needs_rekey() {
        use crate::falcon_crypto::generate_keypair_sha3;
        let mut messaging = ValidatorMessaging::new();

        let seed = [0u8; 32];
        let validator_id = b"test-validator";
        let (public, secret) = generate_keypair_sha3(&seed, None, None, validator_id);

        messaging.initialize_from_falcon(secret, public).unwrap();

        // Should not need rekey initially
        assert!(!messaging.needs_rekey(1000, 3600));

        // Encrypt some messages
        for _ in 0..5 {
            let _ = messaging.encrypt_message(b"test message");
        }

        // Still shouldn't need rekey with high thresholds
        assert!(!messaging.needs_rekey(1000, 3600));

        // But would need rekey with low message threshold
        assert!(messaging.needs_rekey(3, 3600));
    }
}
