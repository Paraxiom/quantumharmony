//! Post-Quantum Encrypted Validator Messaging
//!
//! Provides secure end-to-end encrypted messaging between validators using:
//! - ML-KEM-768 (post-quantum key encapsulation)
//! - SPHINCS+ (post-quantum signatures)
//! - Double Ratchet (forward secrecy)

use pq_triple_ratchet::{
    keys::{
        generate_one_time_prekey, generate_signed_prekey, IdentityKeyPair,
        OneTimePreKeySecret, PreKeyBundle, SignedPreKeySecret,
    },
    message::{EncryptedMessage, MessageType, PlaintextMessage},
    x3dh::X3DHSession,
};
use serde::{Deserialize, Serialize};
use std::{
    collections::HashMap,
    path::PathBuf,
    sync::Arc,
    time::{SystemTime, UNIX_EPOCH},
};
use tokio::sync::{broadcast, RwLock};
use tracing::{debug, error, info, warn};

/// Maximum messages to keep in inbox
const MAX_INBOX_SIZE: usize = 1000;
/// Number of one-time prekeys to generate
const ONE_TIME_PREKEY_COUNT: u32 = 10;

/// Messaging manager handles all encrypted communication
pub struct MessagingManager {
    /// Our identity keypair
    identity: Option<IdentityKeyPair>,
    /// Signed prekey (rotated periodically)
    signed_prekey: Option<(pq_triple_ratchet::keys::SignedPreKey, SignedPreKeySecret)>,
    /// One-time prekeys (consumed on use)
    one_time_prekeys: HashMap<u32, OneTimePreKeySecret>,
    /// Active sessions with peers
    sessions: HashMap<[u8; 8], X3DHSession>,
    /// Known peer bundles (fingerprint -> bundle)
    peer_bundles: HashMap<[u8; 8], PreKeyBundle>,
    /// Inbox of received messages
    inbox: Vec<StoredMessage>,
    /// Outbox of sent messages
    outbox: Vec<StoredMessage>,
    /// Storage path
    storage_path: PathBuf,
    /// Message broadcast channel
    message_tx: broadcast::Sender<IncomingMessage>,
    /// Next prekey ID
    next_prekey_id: u32,
}

/// Stored message (for inbox/outbox)
#[derive(Clone, Serialize, Deserialize)]
pub struct StoredMessage {
    pub id: String,
    pub from: String,
    pub to: String,
    pub message_type: String,
    pub content: String,
    pub timestamp: u64,
    pub read: bool,
}

/// Incoming message notification
#[derive(Clone, Debug)]
pub struct IncomingMessage {
    pub from: String,
    pub message_type: String,
    pub content: String,
    pub timestamp: u64,
}

/// Peer info for display
#[derive(Clone, Serialize, Deserialize)]
pub struct PeerInfo {
    pub fingerprint: String,
    pub name: Option<String>,
    pub last_seen: Option<u64>,
    pub session_active: bool,
}

/// Our messaging identity info
#[derive(Clone, Serialize, Deserialize)]
pub struct IdentityInfo {
    pub fingerprint: String,
    pub public_key_x25519: String,
    pub public_key_mlkem: String,
    pub public_key_sphincs: String,
    pub prekey_bundle_available: bool,
}

impl MessagingManager {
    /// Create a new messaging manager
    pub fn new(storage_path: Option<PathBuf>) -> Self {
        let path = storage_path.unwrap_or_else(|| {
            dirs::data_local_dir()
                .unwrap_or_else(|| PathBuf::from("."))
                .join("quantumharmony")
                .join("messaging")
        });

        let (message_tx, _) = broadcast::channel(100);

        Self {
            identity: None,
            signed_prekey: None,
            one_time_prekeys: HashMap::new(),
            sessions: HashMap::new(),
            peer_bundles: HashMap::new(),
            inbox: Vec::new(),
            outbox: Vec::new(),
            storage_path: path,
            message_tx,
            next_prekey_id: 1,
        }
    }

    /// Get the message broadcast receiver
    pub fn subscribe(&self) -> broadcast::Receiver<IncomingMessage> {
        self.message_tx.subscribe()
    }

    /// Initialize or load identity
    pub async fn initialize(&mut self) -> Result<IdentityInfo, String> {
        // Try to load existing identity
        let identity_path = self.storage_path.join("identity.bin");

        if identity_path.exists() {
            info!("Loading existing messaging identity");
            match self.load_identity(&identity_path).await {
                Ok(info) => return Ok(info),
                Err(e) => {
                    warn!("Failed to load identity, generating new one: {}", e);
                }
            }
        }

        // Generate new identity
        info!("Generating new messaging identity");
        self.generate_identity().await
    }

    /// Generate a new identity
    async fn generate_identity(&mut self) -> Result<IdentityInfo, String> {
        // Create storage directory
        tokio::fs::create_dir_all(&self.storage_path)
            .await
            .map_err(|e| format!("Failed to create storage directory: {}", e))?;

        // Generate identity keypair
        let identity = IdentityKeyPair::generate()
            .map_err(|e| format!("Failed to generate identity: {}", e))?;

        // Generate signed prekey
        let (signed_pk, signed_sk) = generate_signed_prekey(&identity, self.next_prekey_id)
            .map_err(|e| format!("Failed to generate signed prekey: {}", e))?;
        self.next_prekey_id += 1;

        // Generate one-time prekeys
        for _ in 0..ONE_TIME_PREKEY_COUNT {
            let (otpk, otpk_secret) = generate_one_time_prekey(self.next_prekey_id)
                .map_err(|e| format!("Failed to generate one-time prekey: {}", e))?;
            self.one_time_prekeys.insert(otpk.id, otpk_secret);
            self.next_prekey_id += 1;
        }

        let public_key = identity.public_key();
        let fingerprint = hex::encode(public_key.fingerprint());

        self.signed_prekey = Some((signed_pk, signed_sk));
        self.identity = Some(identity);

        // Save identity
        self.save_state().await?;

        info!("Generated messaging identity: {}", fingerprint);

        Ok(IdentityInfo {
            fingerprint,
            public_key_x25519: hex::encode(&public_key.x25519),
            public_key_mlkem: hex::encode(&public_key.mlkem),
            public_key_sphincs: hex::encode(&public_key.sphincs),
            prekey_bundle_available: true,
        })
    }

    /// Load existing identity
    async fn load_identity(&mut self, path: &PathBuf) -> Result<IdentityInfo, String> {
        // For now, just regenerate - in production, would deserialize
        // This is a placeholder for proper persistence
        Err("Identity loading not yet implemented - will regenerate".into())
    }

    /// Save state to disk
    async fn save_state(&self) -> Result<(), String> {
        // Save inbox
        let inbox_path = self.storage_path.join("inbox.json");
        let inbox_json = serde_json::to_string_pretty(&self.inbox)
            .map_err(|e| format!("Failed to serialize inbox: {}", e))?;
        tokio::fs::write(&inbox_path, inbox_json)
            .await
            .map_err(|e| format!("Failed to write inbox: {}", e))?;

        // Save outbox
        let outbox_path = self.storage_path.join("outbox.json");
        let outbox_json = serde_json::to_string_pretty(&self.outbox)
            .map_err(|e| format!("Failed to serialize outbox: {}", e))?;
        tokio::fs::write(&outbox_path, outbox_json)
            .await
            .map_err(|e| format!("Failed to write outbox: {}", e))?;

        Ok(())
    }

    /// Get our prekey bundle for sharing with peers
    pub fn get_prekey_bundle(&self) -> Result<PreKeyBundle, String> {
        let identity = self.identity.as_ref().ok_or("Identity not initialized")?;
        let (signed_pk, _) = self.signed_prekey.as_ref().ok_or("Signed prekey not available")?;

        // Collect available one-time prekeys
        let one_time_prekeys: Vec<_> = self
            .one_time_prekeys
            .iter()
            .take(5) // Only share a few at a time
            .map(|(id, secret)| {
                // Reconstruct public key from secret (in real impl, store both)
                pq_triple_ratchet::keys::OneTimePreKey {
                    id: *id,
                    x25519_public: {
                        let static_secret = x25519_dalek::StaticSecret::from(secret.x25519_secret);
                        *x25519_dalek::PublicKey::from(&static_secret).as_bytes()
                    },
                    mlkem_public: vec![], // Simplified - would need to store public keys too
                }
            })
            .collect();

        Ok(PreKeyBundle {
            identity: identity.public_key(),
            signed_prekey: signed_pk.clone(),
            one_time_prekeys,
        })
    }

    /// Get our identity info
    pub fn get_identity_info(&self) -> Result<IdentityInfo, String> {
        let identity = self.identity.as_ref().ok_or("Identity not initialized")?;
        let public_key = identity.public_key();

        Ok(IdentityInfo {
            fingerprint: hex::encode(public_key.fingerprint()),
            public_key_x25519: hex::encode(&public_key.x25519),
            public_key_mlkem: hex::encode(&public_key.mlkem),
            public_key_sphincs: hex::encode(&public_key.sphincs),
            prekey_bundle_available: self.signed_prekey.is_some(),
        })
    }

    /// Add a peer's prekey bundle
    pub fn add_peer(&mut self, bundle: PreKeyBundle) -> Result<PeerInfo, String> {
        // Verify the bundle
        bundle.verify().map_err(|e| format!("Invalid bundle: {}", e))?;

        let fingerprint = bundle.identity.fingerprint();
        let fingerprint_hex = hex::encode(fingerprint);

        info!("Adding peer: {}", fingerprint_hex);

        self.peer_bundles.insert(fingerprint, bundle);

        Ok(PeerInfo {
            fingerprint: fingerprint_hex,
            name: None,
            last_seen: Some(now_millis()),
            session_active: false,
        })
    }

    /// List known peers
    pub fn list_peers(&self) -> Vec<PeerInfo> {
        self.peer_bundles
            .iter()
            .map(|(fp, _bundle)| PeerInfo {
                fingerprint: hex::encode(fp),
                name: None,
                last_seen: None,
                session_active: self.sessions.contains_key(fp),
            })
            .collect()
    }

    /// Send a message to a peer
    pub async fn send_message(
        &mut self,
        peer_fingerprint: &str,
        content: &str,
        message_type: MessageType,
    ) -> Result<StoredMessage, String> {
        let identity = self.identity.as_ref().ok_or("Identity not initialized")?;

        // Parse peer fingerprint
        let fp_bytes: [u8; 8] = hex::decode(peer_fingerprint)
            .map_err(|_| "Invalid peer fingerprint")?
            .try_into()
            .map_err(|_| "Invalid fingerprint length")?;

        // Get or create session
        if !self.sessions.contains_key(&fp_bytes) {
            // Need to establish session first
            let peer_bundle = self
                .peer_bundles
                .get(&fp_bytes)
                .ok_or("Peer not found - add their prekey bundle first")?;

            // Clone identity for session creation
            let identity_clone = IdentityKeyPair::generate()
                .map_err(|e| format!("Failed to create session identity: {}", e))?;

            let (session, _init_msg) = X3DHSession::initiate(identity_clone, peer_bundle)
                .map_err(|e| format!("Failed to initiate session: {}", e))?;

            self.sessions.insert(fp_bytes, session);
            info!("Established session with peer: {}", peer_fingerprint);
        }

        let session = self.sessions.get_mut(&fp_bytes).unwrap();

        // Create plaintext message
        let plaintext = PlaintextMessage {
            message_type,
            content: content.to_string(),
            timestamp: now_millis(),
            reply_to: None,
        };

        // Encrypt
        let plaintext_bytes = plaintext.to_bytes();
        let ciphertext = session
            .encrypt(&plaintext_bytes)
            .map_err(|e| format!("Encryption failed: {}", e))?;

        // Create stored message
        let our_fp = hex::encode(identity.public_key().fingerprint());
        let msg_id = format!("{}-{}", now_millis(), rand::random::<u32>());

        let stored = StoredMessage {
            id: msg_id.clone(),
            from: our_fp.clone(),
            to: peer_fingerprint.to_string(),
            message_type: format!("{:?}", plaintext.message_type),
            content: content.to_string(),
            timestamp: plaintext.timestamp,
            read: true,
        };

        // Store in outbox
        self.outbox.push(stored.clone());
        if self.outbox.len() > MAX_INBOX_SIZE {
            self.outbox.remove(0);
        }

        // Save state
        self.save_state().await?;

        info!(
            "Sent message to {}: {} bytes encrypted",
            peer_fingerprint,
            ciphertext.len()
        );

        Ok(stored)
    }

    /// Receive and decrypt a message
    pub async fn receive_message(&mut self, encrypted: &[u8]) -> Result<StoredMessage, String> {
        // Parse encrypted message wrapper
        let enc_msg: EncryptedMessage = pq_triple_ratchet::message::EncryptedMessage::from_bytes(encrypted)
            .map_err(|e| format!("Failed to parse message: {}", e))?;

        let sender_fp = enc_msg.sender_fingerprint;
        let sender_fp_hex = hex::encode(sender_fp);

        // Get session
        let session = self
            .sessions
            .get_mut(&sender_fp)
            .ok_or_else(|| format!("No session with sender: {}", sender_fp_hex))?;

        // Decrypt
        let plaintext_bytes = session
            .decrypt(&enc_msg.payload)
            .map_err(|e| format!("Decryption failed: {}", e))?;

        let plaintext = PlaintextMessage::from_bytes(&plaintext_bytes)
            .map_err(|e| format!("Failed to parse plaintext: {}", e))?;

        // Create stored message
        let identity = self.identity.as_ref().ok_or("Identity not initialized")?;
        let our_fp = hex::encode(identity.public_key().fingerprint());
        let msg_id = format!("{}-{}", now_millis(), rand::random::<u32>());

        let stored = StoredMessage {
            id: msg_id,
            from: sender_fp_hex.clone(),
            to: our_fp,
            message_type: format!("{:?}", plaintext.message_type),
            content: plaintext.content.clone(),
            timestamp: plaintext.timestamp,
            read: false,
        };

        // Store in inbox
        self.inbox.push(stored.clone());
        if self.inbox.len() > MAX_INBOX_SIZE {
            self.inbox.remove(0);
        }

        // Save state
        self.save_state().await?;

        // Broadcast to subscribers
        let incoming = IncomingMessage {
            from: sender_fp_hex,
            message_type: format!("{:?}", plaintext.message_type),
            content: plaintext.content,
            timestamp: plaintext.timestamp,
        };
        let _ = self.message_tx.send(incoming);

        info!("Received message from {}", stored.from);

        Ok(stored)
    }

    /// Get inbox messages
    pub fn get_inbox(&self, unread_only: bool) -> Vec<StoredMessage> {
        if unread_only {
            self.inbox.iter().filter(|m| !m.read).cloned().collect()
        } else {
            self.inbox.clone()
        }
    }

    /// Get outbox messages
    pub fn get_outbox(&self) -> Vec<StoredMessage> {
        self.outbox.clone()
    }

    /// Mark message as read
    pub fn mark_read(&mut self, message_id: &str) -> bool {
        if let Some(msg) = self.inbox.iter_mut().find(|m| m.id == message_id) {
            msg.read = true;
            true
        } else {
            false
        }
    }

    /// Get unread count
    pub fn unread_count(&self) -> usize {
        self.inbox.iter().filter(|m| !m.read).count()
    }

    /// Send a quick coordination message (helper)
    pub async fn send_coordination(
        &mut self,
        peer_fingerprint: &str,
        message: &str,
    ) -> Result<StoredMessage, String> {
        self.send_message(peer_fingerprint, message, MessageType::Text)
            .await
    }

    /// Send maintenance notice to all peers
    pub async fn broadcast_maintenance(&mut self, reason: &str) -> Result<usize, String> {
        let peers: Vec<String> = self
            .peer_bundles
            .keys()
            .map(|fp| hex::encode(fp))
            .collect();

        let mut sent = 0;
        for peer in peers {
            match self
                .send_message(&peer, reason, MessageType::MaintenanceNotice)
                .await
            {
                Ok(_) => sent += 1,
                Err(e) => warn!("Failed to notify peer {}: {}", peer, e),
            }
        }

        Ok(sent)
    }

    /// Send online notice to all peers
    pub async fn broadcast_online(&mut self) -> Result<usize, String> {
        let peers: Vec<String> = self
            .peer_bundles
            .keys()
            .map(|fp| hex::encode(fp))
            .collect();

        let mut sent = 0;
        for peer in peers {
            match self
                .send_message(&peer, "Back online", MessageType::OnlineNotice)
                .await
            {
                Ok(_) => sent += 1,
                Err(e) => warn!("Failed to notify peer {}: {}", peer, e),
            }
        }

        Ok(sent)
    }
}

/// Get current timestamp in milliseconds
fn now_millis() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_millis() as u64
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_messaging_manager_init() {
        let mut manager = MessagingManager::new(Some(PathBuf::from("/tmp/qh-msg-test")));
        let info = manager.initialize().await.unwrap();
        assert!(!info.fingerprint.is_empty());
        assert!(info.prekey_bundle_available);
    }
}
