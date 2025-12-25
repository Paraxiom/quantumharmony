// node/src/quantum_p2p/transport.rs
//
// Quantum-secured transport layer using ML-KEM-1024 for key exchange
// and AES-256-GCM for authenticated encryption.

use crate::quantum_p2p::identity::{FalconIdentity, FalconIdentityError, KEM_CIPHERTEXT_SIZE};
use aes_gcm::{
    aead::{Aead, KeyInit},
    Aes256Gcm, Nonce,
};
use rand::RngCore;
use sp_core::H256;
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

/// Nonce size for AES-256-GCM (96 bits)
pub const NONCE_SIZE: usize = 12;

/// Key size for AES-256-GCM
pub const AES_KEY_SIZE: usize = 32;

/// Default key rotation interval (1 hour)
pub const DEFAULT_KEY_ROTATION_INTERVAL: Duration = Duration::from_secs(3600);

/// Cached session key for a peer
#[derive(Clone)]
struct SessionKey {
    /// The symmetric key derived from ML-KEM
    key: [u8; AES_KEY_SIZE],
    /// When this key was established
    established_at: Instant,
    /// The KEM ciphertext (needed for the other party to derive the same key)
    ciphertext: Vec<u8>,
    /// Message counter for nonce generation (prevents nonce reuse)
    message_counter: u64,
}

/// Transport layer that uses ML-KEM-1024 for key exchange and AES-256-GCM for encryption
pub struct QkdTransport {
    /// Our identity for signing and key exchange
    identity: Arc<Mutex<FalconIdentity>>,
    /// Session keys cached per peer (keyed by their node ID)
    session_keys: Mutex<HashMap<H256, SessionKey>>,
    /// Key rotation interval
    key_rotation_interval: Duration,
}

impl QkdTransport {
    /// Create a new QKD transport
    pub fn new(identity: Arc<Mutex<FalconIdentity>>) -> Self {
        Self {
            identity,
            session_keys: Mutex::new(HashMap::new()),
            key_rotation_interval: DEFAULT_KEY_ROTATION_INTERVAL,
        }
    }

    /// Create with custom key rotation interval
    pub fn with_rotation_interval(mut self, interval: Duration) -> Self {
        self.key_rotation_interval = interval;
        self
    }

    /// Establish a session key with a peer using their ML-KEM public key
    ///
    /// Returns the ciphertext that must be sent to the peer so they can derive the same key
    pub fn establish_session(
        &self,
        peer_id: &H256,
        peer_kem_pubkey: &[u8],
    ) -> Result<Vec<u8>, QkdTransportError> {
        // Use ML-KEM to encapsulate a shared secret
        let (ciphertext, shared_secret) = FalconIdentity::encapsulate(peer_kem_pubkey)
            .map_err(|e| QkdTransportError::KeyExchangeFailed(e.to_string()))?;

        // Derive AES key from shared secret (it's already 32 bytes from ML-KEM-1024)
        let mut key = [0u8; AES_KEY_SIZE];
        key.copy_from_slice(&shared_secret[..AES_KEY_SIZE]);

        let session_key = SessionKey {
            key,
            established_at: Instant::now(),
            ciphertext: ciphertext.clone(),
            message_counter: 0,
        };

        let mut cache = self.session_keys.lock().unwrap();
        cache.insert(*peer_id, session_key);

        log::debug!("Established quantum session with peer {:?}", peer_id);

        Ok(ciphertext)
    }

    /// Accept a session from a peer using the ciphertext they sent
    pub fn accept_session(
        &self,
        peer_id: &H256,
        ciphertext: &[u8],
    ) -> Result<(), QkdTransportError> {
        let identity = self.identity.lock().unwrap();

        // Decapsulate to get the shared secret
        let shared_secret = identity
            .decapsulate(ciphertext)
            .map_err(|e| QkdTransportError::KeyExchangeFailed(e.to_string()))?;

        // Derive AES key from shared secret
        let mut key = [0u8; AES_KEY_SIZE];
        key.copy_from_slice(&shared_secret[..AES_KEY_SIZE]);

        let session_key = SessionKey {
            key,
            established_at: Instant::now(),
            ciphertext: ciphertext.to_vec(),
            message_counter: 0,
        };

        let mut cache = self.session_keys.lock().unwrap();
        cache.insert(*peer_id, session_key);

        log::debug!("Accepted quantum session from peer {:?}", peer_id);

        Ok(())
    }

    /// Encrypt data for a peer using AES-256-GCM
    ///
    /// Returns: [nonce (12 bytes)][ciphertext + auth tag]
    pub fn encrypt(&self, peer_id: &H256, plaintext: &[u8]) -> Result<Vec<u8>, QkdTransportError> {
        let mut cache = self.session_keys.lock().unwrap();

        let session = cache
            .get_mut(peer_id)
            .ok_or(QkdTransportError::NoSessionKey)?;

        // Check if key needs rotation
        if session.established_at.elapsed() > self.key_rotation_interval {
            return Err(QkdTransportError::KeyExpired);
        }

        // Generate nonce from counter (prevents reuse)
        let mut nonce_bytes = [0u8; NONCE_SIZE];
        let counter_bytes = session.message_counter.to_le_bytes();
        nonce_bytes[..8].copy_from_slice(&counter_bytes);
        // Add some randomness to remaining bytes
        rand::thread_rng().fill_bytes(&mut nonce_bytes[8..]);

        session.message_counter += 1;

        let cipher = Aes256Gcm::new_from_slice(&session.key)
            .map_err(|e| QkdTransportError::EncryptionFailed(e.to_string()))?;

        let nonce = Nonce::from_slice(&nonce_bytes);
        let ciphertext = cipher
            .encrypt(nonce, plaintext)
            .map_err(|e| QkdTransportError::EncryptionFailed(e.to_string()))?;

        // Format: [nonce][ciphertext + auth tag]
        let mut result = Vec::with_capacity(NONCE_SIZE + ciphertext.len());
        result.extend_from_slice(&nonce_bytes);
        result.extend_from_slice(&ciphertext);

        Ok(result)
    }

    /// Decrypt data from a peer using AES-256-GCM
    ///
    /// Input format: [nonce (12 bytes)][ciphertext + auth tag]
    pub fn decrypt(&self, peer_id: &H256, encrypted: &[u8]) -> Result<Vec<u8>, QkdTransportError> {
        if encrypted.len() < NONCE_SIZE + 16 {
            // 16 = auth tag size
            return Err(QkdTransportError::DecryptionFailed(
                "Data too short".to_string(),
            ));
        }

        let cache = self.session_keys.lock().unwrap();

        let session = cache.get(peer_id).ok_or(QkdTransportError::NoSessionKey)?;

        // Check if key needs rotation
        if session.established_at.elapsed() > self.key_rotation_interval {
            return Err(QkdTransportError::KeyExpired);
        }

        let nonce_bytes = &encrypted[..NONCE_SIZE];
        let ciphertext = &encrypted[NONCE_SIZE..];

        let cipher = Aes256Gcm::new_from_slice(&session.key)
            .map_err(|e| QkdTransportError::DecryptionFailed(e.to_string()))?;

        let nonce = Nonce::from_slice(nonce_bytes);
        let plaintext = cipher
            .decrypt(nonce, ciphertext)
            .map_err(|e| QkdTransportError::DecryptionFailed(e.to_string()))?;

        Ok(plaintext)
    }

    /// Check if we have an active session with a peer
    pub fn has_session(&self, peer_id: &H256) -> bool {
        let cache = self.session_keys.lock().unwrap();
        if let Some(session) = cache.get(peer_id) {
            session.established_at.elapsed() <= self.key_rotation_interval
        } else {
            false
        }
    }

    /// Remove a session with a peer
    pub fn remove_session(&self, peer_id: &H256) {
        let mut cache = self.session_keys.lock().unwrap();
        cache.remove(peer_id);
        log::debug!("Removed session with peer {:?}", peer_id);
    }

    /// Get the number of active sessions
    pub fn active_session_count(&self) -> usize {
        let cache = self.session_keys.lock().unwrap();
        cache
            .values()
            .filter(|s| s.established_at.elapsed() <= self.key_rotation_interval)
            .count()
    }

    /// Clean up expired sessions
    pub fn cleanup_expired_sessions(&self) -> usize {
        let mut cache = self.session_keys.lock().unwrap();
        let before = cache.len();
        cache.retain(|_, session| session.established_at.elapsed() <= self.key_rotation_interval);
        let removed = before - cache.len();
        if removed > 0 {
            log::debug!("Cleaned up {} expired sessions", removed);
        }
        removed
    }
}

/// Errors that can occur with QkdTransport operations
#[derive(Debug, Clone)]
pub enum QkdTransportError {
    KeyExchangeFailed(String),
    NoSessionKey,
    KeyExpired,
    EncryptionFailed(String),
    DecryptionFailed(String),
}

impl std::fmt::Display for QkdTransportError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::KeyExchangeFailed(msg) => write!(f, "Key exchange failed: {}", msg),
            Self::NoSessionKey => write!(f, "No session key established with peer"),
            Self::KeyExpired => write!(f, "Session key has expired"),
            Self::EncryptionFailed(msg) => write!(f, "Encryption failed: {}", msg),
            Self::DecryptionFailed(msg) => write!(f, "Decryption failed: {}", msg),
        }
    }
}

impl std::error::Error for QkdTransportError {}

#[cfg(test)]
mod tests {
    use super::*;

    fn create_test_transport() -> (QkdTransport, Arc<Mutex<FalconIdentity>>) {
        let mut identity = FalconIdentity::new();
        identity.generate_keypair().unwrap();
        let identity = Arc::new(Mutex::new(identity));
        let transport = QkdTransport::new(identity.clone());
        (transport, identity)
    }

    #[test]
    fn test_session_establishment() {
        let (transport_a, identity_a) = create_test_transport();
        let (transport_b, identity_b) = create_test_transport();

        let node_id_a = identity_a.lock().unwrap().node_id().unwrap();
        let node_id_b = identity_b.lock().unwrap().node_id().unwrap();

        // A establishes session with B
        let kem_pubkey_b = identity_b
            .lock()
            .unwrap()
            .kem_public_key()
            .unwrap()
            .to_vec();
        let ciphertext = transport_a
            .establish_session(&node_id_b, &kem_pubkey_b)
            .expect("Session establishment failed");

        // B accepts the session
        transport_b
            .accept_session(&node_id_a, &ciphertext)
            .expect("Session acceptance failed");

        assert!(transport_a.has_session(&node_id_b));
        assert!(transport_b.has_session(&node_id_a));
    }

    #[test]
    fn test_encrypt_decrypt_roundtrip() {
        let (transport_a, identity_a) = create_test_transport();
        let (transport_b, identity_b) = create_test_transport();

        let node_id_a = identity_a.lock().unwrap().node_id().unwrap();
        let node_id_b = identity_b.lock().unwrap().node_id().unwrap();

        // Establish session
        let kem_pubkey_b = identity_b
            .lock()
            .unwrap()
            .kem_public_key()
            .unwrap()
            .to_vec();
        let ciphertext = transport_a
            .establish_session(&node_id_b, &kem_pubkey_b)
            .unwrap();
        transport_b
            .accept_session(&node_id_a, &ciphertext)
            .unwrap();

        // A encrypts message for B
        let message = b"Hello, quantum-secured world!";
        let encrypted = transport_a
            .encrypt(&node_id_b, message)
            .expect("Encryption failed");

        // B decrypts message from A
        let decrypted = transport_b
            .decrypt(&node_id_a, &encrypted)
            .expect("Decryption failed");

        assert_eq!(decrypted, message);
    }

    #[test]
    fn test_bidirectional_communication() {
        let (transport_a, identity_a) = create_test_transport();
        let (transport_b, identity_b) = create_test_transport();

        let node_id_a = identity_a.lock().unwrap().node_id().unwrap();
        let node_id_b = identity_b.lock().unwrap().node_id().unwrap();

        // Establish session A -> B
        let kem_pubkey_b = identity_b
            .lock()
            .unwrap()
            .kem_public_key()
            .unwrap()
            .to_vec();
        let ciphertext_ab = transport_a
            .establish_session(&node_id_b, &kem_pubkey_b)
            .unwrap();
        transport_b
            .accept_session(&node_id_a, &ciphertext_ab)
            .unwrap();

        // Establish session B -> A (for B to send to A)
        let kem_pubkey_a = identity_a
            .lock()
            .unwrap()
            .kem_public_key()
            .unwrap()
            .to_vec();
        let ciphertext_ba = transport_b
            .establish_session(&node_id_a, &kem_pubkey_a)
            .unwrap();
        transport_a
            .accept_session(&node_id_b, &ciphertext_ba)
            .unwrap();

        // A -> B
        let msg_a = b"Message from A to B";
        let encrypted_a = transport_a.encrypt(&node_id_b, msg_a).unwrap();
        let decrypted_a = transport_b.decrypt(&node_id_a, &encrypted_a).unwrap();
        assert_eq!(decrypted_a, msg_a);

        // B -> A
        let msg_b = b"Message from B to A";
        let encrypted_b = transport_b.encrypt(&node_id_a, msg_b).unwrap();
        let decrypted_b = transport_a.decrypt(&node_id_b, &encrypted_b).unwrap();
        assert_eq!(decrypted_b, msg_b);
    }

    #[test]
    fn test_tampered_ciphertext_fails() {
        let (transport_a, identity_a) = create_test_transport();
        let (transport_b, identity_b) = create_test_transport();

        let node_id_a = identity_a.lock().unwrap().node_id().unwrap();
        let node_id_b = identity_b.lock().unwrap().node_id().unwrap();

        // Establish session
        let kem_pubkey_b = identity_b
            .lock()
            .unwrap()
            .kem_public_key()
            .unwrap()
            .to_vec();
        let ciphertext = transport_a
            .establish_session(&node_id_b, &kem_pubkey_b)
            .unwrap();
        transport_b
            .accept_session(&node_id_a, &ciphertext)
            .unwrap();

        // Encrypt a message
        let message = b"Secret message";
        let mut encrypted = transport_a.encrypt(&node_id_b, message).unwrap();

        // Tamper with the ciphertext
        if encrypted.len() > NONCE_SIZE + 5 {
            encrypted[NONCE_SIZE + 5] ^= 0xFF;
        }

        // Decryption should fail due to authentication
        let result = transport_b.decrypt(&node_id_a, &encrypted);
        assert!(result.is_err());
    }

    #[test]
    fn test_no_session_key_fails() {
        let (transport, _identity) = create_test_transport();
        let fake_peer_id = H256::from_slice(&[1u8; 32]);

        let result = transport.encrypt(&fake_peer_id, b"test");
        assert!(matches!(result, Err(QkdTransportError::NoSessionKey)));
    }

    #[test]
    fn test_session_removal() {
        let (transport_a, identity_a) = create_test_transport();
        let (_transport_b, identity_b) = create_test_transport();

        let node_id_b = identity_b.lock().unwrap().node_id().unwrap();

        // Establish session
        let kem_pubkey_b = identity_b
            .lock()
            .unwrap()
            .kem_public_key()
            .unwrap()
            .to_vec();
        transport_a
            .establish_session(&node_id_b, &kem_pubkey_b)
            .unwrap();

        assert!(transport_a.has_session(&node_id_b));
        assert_eq!(transport_a.active_session_count(), 1);

        transport_a.remove_session(&node_id_b);

        assert!(!transport_a.has_session(&node_id_b));
        assert_eq!(transport_a.active_session_count(), 0);
    }

    #[test]
    fn test_key_expiration() {
        let mut identity = FalconIdentity::new();
        identity.generate_keypair().unwrap();
        let identity = Arc::new(Mutex::new(identity));

        // Create transport with very short rotation interval
        let transport =
            QkdTransport::new(identity.clone()).with_rotation_interval(Duration::from_millis(1));

        let mut peer_identity = FalconIdentity::new();
        peer_identity.generate_keypair().unwrap();
        let peer_id = peer_identity.node_id().unwrap();

        // Establish session
        let kem_pubkey = peer_identity.kem_public_key().unwrap().to_vec();
        transport.establish_session(&peer_id, &kem_pubkey).unwrap();

        // Wait for key to expire
        std::thread::sleep(Duration::from_millis(10));

        // Encryption should fail due to expired key
        let result = transport.encrypt(&peer_id, b"test");
        assert!(matches!(result, Err(QkdTransportError::KeyExpired)));
    }

    #[test]
    fn test_multiple_messages_different_nonces() {
        let (transport_a, identity_a) = create_test_transport();
        let (transport_b, identity_b) = create_test_transport();

        let node_id_a = identity_a.lock().unwrap().node_id().unwrap();
        let node_id_b = identity_b.lock().unwrap().node_id().unwrap();

        // Establish session
        let kem_pubkey_b = identity_b
            .lock()
            .unwrap()
            .kem_public_key()
            .unwrap()
            .to_vec();
        let ciphertext = transport_a
            .establish_session(&node_id_b, &kem_pubkey_b)
            .unwrap();
        transport_b
            .accept_session(&node_id_a, &ciphertext)
            .unwrap();

        // Send multiple messages
        let messages: Vec<&[u8]> = vec![b"Message 1", b"Message 2", b"Message 3"];
        let mut encrypted_messages = Vec::new();

        for msg in &messages {
            let encrypted = transport_a.encrypt(&node_id_b, msg).unwrap();
            encrypted_messages.push(encrypted);
        }

        // Verify nonces are different (first 12 bytes)
        for i in 0..encrypted_messages.len() {
            for j in (i + 1)..encrypted_messages.len() {
                let nonce_i = &encrypted_messages[i][..NONCE_SIZE];
                let nonce_j = &encrypted_messages[j][..NONCE_SIZE];
                assert_ne!(nonce_i, nonce_j, "Nonces should be unique");
            }
        }

        // All messages should decrypt correctly
        for (encrypted, original) in encrypted_messages.iter().zip(messages.iter()) {
            let decrypted = transport_b.decrypt(&node_id_a, encrypted).unwrap();
            assert_eq!(&decrypted[..], *original);
        }
    }

    #[test]
    fn test_cleanup_expired_sessions() {
        let mut identity = FalconIdentity::new();
        identity.generate_keypair().unwrap();
        let identity = Arc::new(Mutex::new(identity));

        // Use a longer expiration to avoid timing issues during session establishment
        let transport =
            QkdTransport::new(identity.clone()).with_rotation_interval(Duration::from_millis(100));

        // Create some peers and establish sessions
        let mut peer_keys = Vec::new();
        for i in 0..5 {
            let mut peer = FalconIdentity::new();
            peer.generate_keypair().unwrap();
            peer_keys.push(peer.kem_public_key().unwrap().to_vec());
        }

        // Establish sessions with unique peer IDs
        for (i, kem_pubkey) in peer_keys.iter().enumerate() {
            let mut peer_id_bytes = [0u8; 32];
            peer_id_bytes[0] = i as u8;
            peer_id_bytes[31] = (i * 17) as u8; // Make IDs more unique
            let peer_id = H256::from_slice(&peer_id_bytes);
            transport.establish_session(&peer_id, kem_pubkey).unwrap();
        }

        assert_eq!(transport.active_session_count(), 5);

        // Wait for expiration
        std::thread::sleep(Duration::from_millis(150));

        // Active count should be 0 (all expired)
        assert_eq!(transport.active_session_count(), 0);

        // Cleanup should remove all
        let removed = transport.cleanup_expired_sessions();
        assert_eq!(removed, 5);
    }
}
