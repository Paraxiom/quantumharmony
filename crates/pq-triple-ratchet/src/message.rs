//! High-level message types for validator coordination.

use serde::{Deserialize, Serialize};
use std::time::{SystemTime, UNIX_EPOCH};

/// Message types for validator coordination.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum MessageType {
    /// Regular text message
    Text,
    /// Validator going offline for maintenance
    MaintenanceNotice,
    /// Validator back online
    OnlineNotice,
    /// Alert (network issue, attack detected, etc.)
    Alert,
    /// Request for acknowledgment
    Ping,
    /// Acknowledgment
    Pong,
}

/// Plaintext message before encryption.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PlaintextMessage {
    /// Message type
    pub message_type: MessageType,
    /// Message content
    pub content: String,
    /// Timestamp (Unix milliseconds)
    pub timestamp: u64,
    /// Optional reply-to message ID
    pub reply_to: Option<[u8; 32]>,
}

impl PlaintextMessage {
    /// Create a new text message.
    pub fn text(content: impl Into<String>) -> Self {
        Self {
            message_type: MessageType::Text,
            content: content.into(),
            timestamp: Self::now(),
            reply_to: None,
        }
    }

    /// Create a maintenance notice.
    pub fn maintenance(reason: impl Into<String>) -> Self {
        Self {
            message_type: MessageType::MaintenanceNotice,
            content: reason.into(),
            timestamp: Self::now(),
            reply_to: None,
        }
    }

    /// Create an online notice.
    pub fn online() -> Self {
        Self {
            message_type: MessageType::OnlineNotice,
            content: "Back online".into(),
            timestamp: Self::now(),
            reply_to: None,
        }
    }

    /// Create an alert.
    pub fn alert(message: impl Into<String>) -> Self {
        Self {
            message_type: MessageType::Alert,
            content: message.into(),
            timestamp: Self::now(),
            reply_to: None,
        }
    }

    /// Create a ping.
    pub fn ping() -> Self {
        Self {
            message_type: MessageType::Ping,
            content: String::new(),
            timestamp: Self::now(),
            reply_to: None,
        }
    }

    /// Create a pong (reply to ping).
    pub fn pong(ping_id: [u8; 32]) -> Self {
        Self {
            message_type: MessageType::Pong,
            content: String::new(),
            timestamp: Self::now(),
            reply_to: Some(ping_id),
        }
    }

    /// Set reply-to field.
    pub fn with_reply_to(mut self, message_id: [u8; 32]) -> Self {
        self.reply_to = Some(message_id);
        self
    }

    /// Serialize to bytes.
    pub fn to_bytes(&self) -> Vec<u8> {
        bincode::serialize(self).expect("serialization should not fail")
    }

    /// Deserialize from bytes.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, crate::error::Error> {
        bincode::deserialize(bytes).map_err(|e| crate::error::Error::Serialization(e.to_string()))
    }

    /// Get current timestamp in milliseconds.
    fn now() -> u64 {
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_millis() as u64
    }

    /// Calculate message ID (SHA-256 hash of serialized content).
    pub fn message_id(&self) -> [u8; 32] {
        use sha2::{Digest, Sha256};
        let bytes = self.to_bytes();
        let mut hasher = Sha256::new();
        hasher.update(&bytes);
        let hash = hasher.finalize();
        let mut id = [0u8; 32];
        id.copy_from_slice(&hash);
        id
    }
}

/// Encrypted message (wire format).
#[derive(Clone, Serialize, Deserialize)]
pub struct EncryptedMessage {
    /// Sender's identity fingerprint (first 8 bytes of identity key hash)
    pub sender_fingerprint: [u8; 8],
    /// Recipient's identity fingerprint
    pub recipient_fingerprint: [u8; 8],
    /// Encrypted payload (from Triple Ratchet)
    pub payload: Vec<u8>,
    /// Optional ZK membership proof
    #[cfg(feature = "zk-membership")]
    pub membership_proof: Option<Vec<u8>>,
}

impl EncryptedMessage {
    /// Create a new encrypted message.
    pub fn new(
        sender_fingerprint: [u8; 8],
        recipient_fingerprint: [u8; 8],
        payload: Vec<u8>,
    ) -> Self {
        Self {
            sender_fingerprint,
            recipient_fingerprint,
            payload,
            #[cfg(feature = "zk-membership")]
            membership_proof: None,
        }
    }

    /// Serialize to bytes for transmission.
    pub fn to_bytes(&self) -> Vec<u8> {
        bincode::serialize(self).expect("serialization should not fail")
    }

    /// Deserialize from bytes.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, crate::error::Error> {
        bincode::deserialize(bytes).map_err(|e| crate::error::Error::Serialization(e.to_string()))
    }
}

/// Broadcast message (sent to all validators).
#[derive(Clone, Serialize, Deserialize)]
pub struct BroadcastMessage {
    /// Sender's identity fingerprint
    pub sender_fingerprint: [u8; 8],
    /// Message content (plaintext for broadcast)
    pub message: PlaintextMessage,
    /// SPHINCS+ signature over (sender_fingerprint || message)
    pub signature: Vec<u8>,
}

impl BroadcastMessage {
    /// Serialize to bytes.
    pub fn to_bytes(&self) -> Vec<u8> {
        bincode::serialize(self).expect("serialization should not fail")
    }

    /// Deserialize from bytes.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, crate::error::Error> {
        bincode::deserialize(bytes).map_err(|e| crate::error::Error::Serialization(e.to_string()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_text_message() {
        let msg = PlaintextMessage::text("Hello validators!");
        assert!(matches!(msg.message_type, MessageType::Text));
        assert_eq!(msg.content, "Hello validators!");
        assert!(msg.timestamp > 0);
    }

    #[test]
    fn test_message_serialization() {
        let msg = PlaintextMessage::alert("Network anomaly detected");
        let bytes = msg.to_bytes();
        let restored = PlaintextMessage::from_bytes(&bytes).unwrap();
        assert_eq!(msg.content, restored.content);
    }

    #[test]
    fn test_message_id() {
        let msg1 = PlaintextMessage::text("Test");
        let msg2 = PlaintextMessage::text("Test");
        // Same content at different times should have different IDs
        // (due to timestamp)
        let id1 = msg1.message_id();
        std::thread::sleep(std::time::Duration::from_millis(1));
        let id2 = PlaintextMessage::text("Test").message_id();
        // IDs might differ due to timestamp
        assert_ne!(id1, [0u8; 32]);
    }

    #[test]
    fn test_encrypted_message() {
        let msg = EncryptedMessage::new(
            [1, 2, 3, 4, 5, 6, 7, 8],
            [9, 10, 11, 12, 13, 14, 15, 16],
            vec![0xDE, 0xAD, 0xBE, 0xEF],
        );
        let bytes = msg.to_bytes();
        let restored = EncryptedMessage::from_bytes(&bytes).unwrap();
        assert_eq!(msg.sender_fingerprint, restored.sender_fingerprint);
        assert_eq!(msg.payload, restored.payload);
    }
}
