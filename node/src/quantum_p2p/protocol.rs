// node/src/quantum_p2p/protocol.rs
//
// Quantum-secured P2P protocol using Falcon-1024 signatures
// for message authentication and ML-KEM + AES-256-GCM for encryption.

use crate::quantum_p2p::identity::{FalconIdentity, FalconIdentityError};
use crate::quantum_p2p::transport::{QkdTransport, QkdTransportError};
use sp_core::H256;
use std::sync::{Arc, Mutex};
use std::time::{SystemTime, UNIX_EPOCH};

/// Protocol version
pub const PROTOCOL_VERSION: u8 = 1;

/// Protocol name for network registration
pub const PROTOCOL_NAME: &str = "/quantumharmony/quantum/1";

/// Message types
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum MessageType {
    /// Regular data message
    Data = 0x01,
    /// Session establishment request (contains KEM ciphertext)
    SessionRequest = 0x02,
    /// Session establishment response
    SessionResponse = 0x03,
    /// Key rotation request
    KeyRotation = 0x04,
    /// Ping/keepalive
    Ping = 0x05,
    /// Pong response
    Pong = 0x06,
}

impl TryFrom<u8> for MessageType {
    type Error = ProtocolError;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0x01 => Ok(MessageType::Data),
            0x02 => Ok(MessageType::SessionRequest),
            0x03 => Ok(MessageType::SessionResponse),
            0x04 => Ok(MessageType::KeyRotation),
            0x05 => Ok(MessageType::Ping),
            0x06 => Ok(MessageType::Pong),
            _ => Err(ProtocolError::InvalidMessageType(value)),
        }
    }
}

/// Header for quantum protocol messages
///
/// Format: [Version(1)][Type(1)][Timestamp(8)][Sender Node ID(32)][Payload Length(4)]
/// Total: 46 bytes
#[derive(Debug, Clone)]
pub struct MessageHeader {
    pub version: u8,
    pub message_type: MessageType,
    pub timestamp: u64,
    pub sender_node_id: H256,
    pub payload_length: u32,
}

impl MessageHeader {
    pub const SIZE: usize = 1 + 1 + 8 + 32 + 4; // 46 bytes

    pub fn new(message_type: MessageType, sender_node_id: H256, payload_length: u32) -> Self {
        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs();

        Self {
            version: PROTOCOL_VERSION,
            message_type,
            timestamp,
            sender_node_id,
            payload_length,
        }
    }

    pub fn encode(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(Self::SIZE);
        bytes.push(self.version);
        bytes.push(self.message_type as u8);
        bytes.extend_from_slice(&self.timestamp.to_be_bytes());
        bytes.extend_from_slice(self.sender_node_id.as_bytes());
        bytes.extend_from_slice(&self.payload_length.to_be_bytes());
        bytes
    }

    pub fn decode(bytes: &[u8]) -> Result<Self, ProtocolError> {
        if bytes.len() < Self::SIZE {
            return Err(ProtocolError::MessageTooShort {
                expected: Self::SIZE,
                actual: bytes.len(),
            });
        }

        let version = bytes[0];
        if version != PROTOCOL_VERSION {
            return Err(ProtocolError::UnsupportedVersion(version));
        }

        let message_type = MessageType::try_from(bytes[1])?;

        let mut timestamp_bytes = [0u8; 8];
        timestamp_bytes.copy_from_slice(&bytes[2..10]);
        let timestamp = u64::from_be_bytes(timestamp_bytes);

        let sender_node_id = H256::from_slice(&bytes[10..42]);

        let mut length_bytes = [0u8; 4];
        length_bytes.copy_from_slice(&bytes[42..46]);
        let payload_length = u32::from_be_bytes(length_bytes);

        Ok(Self {
            version,
            message_type,
            timestamp,
            sender_node_id,
            payload_length,
        })
    }
}

/// Quantum-secured P2P protocol handler
pub struct QuantumProtocol {
    /// Our identity for signing
    identity: Arc<Mutex<FalconIdentity>>,
    /// Transport layer for encryption
    transport: Arc<QkdTransport>,
    /// Our node ID
    node_id: H256,
    /// Known peer signing public keys (node_id -> public_key)
    peer_pubkeys: std::sync::Mutex<std::collections::HashMap<H256, Vec<u8>>>,
}

impl QuantumProtocol {
    /// Create a new quantum protocol instance
    pub fn new(identity: Arc<Mutex<FalconIdentity>>, transport: Arc<QkdTransport>) -> Self {
        let node_id = identity.lock().unwrap().node_id().unwrap_or_default();
        Self {
            identity,
            transport,
            node_id,
            peer_pubkeys: std::sync::Mutex::new(std::collections::HashMap::new()),
        }
    }

    /// Register a peer's signing public key
    pub fn register_peer(&self, peer_id: H256, sign_pubkey: Vec<u8>) {
        let mut peers = self.peer_pubkeys.lock().unwrap();
        peers.insert(peer_id, sign_pubkey);
        log::debug!("Registered peer {:?} with signing key", peer_id);
    }

    /// Get a peer's signing public key
    pub fn get_peer_pubkey(&self, peer_id: &H256) -> Option<Vec<u8>> {
        let peers = self.peer_pubkeys.lock().unwrap();
        peers.get(peer_id).cloned()
    }

    /// Create a session establishment request for a peer
    ///
    /// Returns a message that should be sent to the peer to establish an encrypted session
    pub fn create_session_request(
        &self,
        peer_id: &H256,
        peer_kem_pubkey: &[u8],
    ) -> Result<Vec<u8>, ProtocolError> {
        // Establish session and get the KEM ciphertext
        let kem_ciphertext = self
            .transport
            .establish_session(peer_id, peer_kem_pubkey)
            .map_err(ProtocolError::Transport)?;

        // Include our KEM public key so peer can respond
        let our_kem_pubkey = self
            .identity
            .lock()
            .unwrap()
            .kem_public_key()
            .ok_or(ProtocolError::KeyNotGenerated)?
            .to_vec();

        // Payload: [KEM ciphertext length(4)][KEM ciphertext][Our KEM pubkey]
        let mut payload = Vec::new();
        payload.extend_from_slice(&(kem_ciphertext.len() as u32).to_be_bytes());
        payload.extend_from_slice(&kem_ciphertext);
        payload.extend_from_slice(&our_kem_pubkey);

        // Create and sign the message
        self.create_signed_message(MessageType::SessionRequest, &payload)
    }

    /// Process a session establishment request from a peer
    ///
    /// Returns a session response message to send back
    pub fn process_session_request(
        &self,
        message: &[u8],
    ) -> Result<(H256, Vec<u8>), ProtocolError> {
        // Verify and decode the message
        let (header, payload) = self.verify_and_decode_message(message)?;

        if header.message_type != MessageType::SessionRequest {
            return Err(ProtocolError::UnexpectedMessageType {
                expected: MessageType::SessionRequest,
                actual: header.message_type,
            });
        }

        // Parse payload
        if payload.len() < 4 {
            return Err(ProtocolError::InvalidPayload(
                "Payload too short for KEM ciphertext length".into(),
            ));
        }

        let mut ct_len_bytes = [0u8; 4];
        ct_len_bytes.copy_from_slice(&payload[..4]);
        let ct_len = u32::from_be_bytes(ct_len_bytes) as usize;

        if payload.len() < 4 + ct_len {
            return Err(ProtocolError::InvalidPayload(
                "Payload too short for KEM ciphertext".into(),
            ));
        }

        let kem_ciphertext = &payload[4..4 + ct_len];
        let peer_kem_pubkey = &payload[4 + ct_len..];

        // Accept the session
        self.transport
            .accept_session(&header.sender_node_id, kem_ciphertext)
            .map_err(ProtocolError::Transport)?;

        // Create our own session for sending to them
        let response_ciphertext = self
            .transport
            .establish_session(&header.sender_node_id, peer_kem_pubkey)
            .map_err(ProtocolError::Transport)?;

        // Create response message
        let response = self.create_signed_message(MessageType::SessionResponse, &response_ciphertext)?;

        Ok((header.sender_node_id, response))
    }

    /// Process a session establishment response
    pub fn process_session_response(
        &self,
        message: &[u8],
    ) -> Result<H256, ProtocolError> {
        let (header, payload) = self.verify_and_decode_message(message)?;

        if header.message_type != MessageType::SessionResponse {
            return Err(ProtocolError::UnexpectedMessageType {
                expected: MessageType::SessionResponse,
                actual: header.message_type,
            });
        }

        // Accept the session for receiving from them
        self.transport
            .accept_session(&header.sender_node_id, &payload)
            .map_err(ProtocolError::Transport)?;

        log::info!(
            "Quantum session established with peer {:?}",
            header.sender_node_id
        );

        Ok(header.sender_node_id)
    }

    /// Send an encrypted data message to a peer
    pub fn send_data(&self, peer_id: &H256, data: &[u8]) -> Result<Vec<u8>, ProtocolError> {
        // Encrypt the data
        let encrypted = self
            .transport
            .encrypt(peer_id, data)
            .map_err(ProtocolError::Transport)?;

        // Create and sign the message
        self.create_signed_message(MessageType::Data, &encrypted)
    }

    /// Receive and decrypt a data message from a peer
    pub fn receive_data(&self, message: &[u8]) -> Result<(H256, Vec<u8>), ProtocolError> {
        let (header, payload) = self.verify_and_decode_message(message)?;

        if header.message_type != MessageType::Data {
            return Err(ProtocolError::UnexpectedMessageType {
                expected: MessageType::Data,
                actual: header.message_type,
            });
        }

        // Decrypt the data
        let decrypted = self
            .transport
            .decrypt(&header.sender_node_id, &payload)
            .map_err(ProtocolError::Transport)?;

        Ok((header.sender_node_id, decrypted))
    }

    /// Create a signed message with header
    ///
    /// Format: [Header(46)][Payload][Signature]
    fn create_signed_message(
        &self,
        message_type: MessageType,
        payload: &[u8],
    ) -> Result<Vec<u8>, ProtocolError> {
        let header = MessageHeader::new(message_type, self.node_id, payload.len() as u32);
        let header_bytes = header.encode();

        // Data to sign: header + payload
        let mut data_to_sign = Vec::with_capacity(header_bytes.len() + payload.len());
        data_to_sign.extend_from_slice(&header_bytes);
        data_to_sign.extend_from_slice(payload);

        // Sign the data
        let identity = self.identity.lock().unwrap();
        let signed_message = identity.sign(&data_to_sign).map_err(ProtocolError::Identity)?;

        Ok(signed_message)
    }

    /// Verify signature and decode a message
    ///
    /// Returns the header and payload if valid
    fn verify_and_decode_message(
        &self,
        message: &[u8],
    ) -> Result<(MessageHeader, Vec<u8>), ProtocolError> {
        // The message is a signed message (signature || original data)
        // We need to verify and extract the original data

        // We need at least enough bytes for a minimal signed message
        if message.len() < MessageHeader::SIZE + 100 {
            // Rough minimum for Falcon signature
            return Err(ProtocolError::MessageTooShort {
                expected: MessageHeader::SIZE + 100,
                actual: message.len(),
            });
        }

        // Try to verify with our own key first (self-sent messages)
        {
            let identity = self.identity.lock().unwrap();
            if let Ok(verified_data) = identity.verify(message) {
                return self.decode_verified_data(&verified_data);
            }
        }

        // Try each registered peer's public key
        let peers = self.peer_pubkeys.lock().unwrap();
        for (_peer_id, pubkey) in peers.iter() {
            if let Ok(data) = Self::open_signed_message(message, pubkey) {
                return self.decode_verified_data(&data);
            }
        }

        Err(ProtocolError::SignatureVerificationFailed)
    }

    /// Open a signed message using a public key
    fn open_signed_message(message: &[u8], pubkey: &[u8]) -> Result<Vec<u8>, ProtocolError> {
        use pqcrypto_falcon::falcon1024;
        use pqcrypto_traits::sign::{PublicKey, SignedMessage};

        let public_key = falcon1024::PublicKey::from_bytes(pubkey)
            .map_err(|_| ProtocolError::SignatureVerificationFailed)?;

        let sm = falcon1024::SignedMessage::from_bytes(message)
            .map_err(|_| ProtocolError::SignatureVerificationFailed)?;

        falcon1024::open(&sm, &public_key)
            .map_err(|_| ProtocolError::SignatureVerificationFailed)
    }

    /// Decode the verified data into header and payload
    fn decode_verified_data(&self, verified_data: &[u8]) -> Result<(MessageHeader, Vec<u8>), ProtocolError> {
        let header = MessageHeader::decode(verified_data)?;

        let payload_start = MessageHeader::SIZE;
        let payload_end = payload_start + header.payload_length as usize;

        if verified_data.len() < payload_end {
            return Err(ProtocolError::MessageTooShort {
                expected: payload_end,
                actual: verified_data.len(),
            });
        }

        let payload = verified_data[payload_start..payload_end].to_vec();

        Ok((header, payload))
    }

    /// Check if we have an active session with a peer
    pub fn has_session(&self, peer_id: &H256) -> bool {
        self.transport.has_session(peer_id)
    }

    /// Get our node ID
    pub fn node_id(&self) -> H256 {
        self.node_id
    }

    /// Get the protocol name for network registration
    pub fn protocol_name() -> &'static str {
        PROTOCOL_NAME
    }
}

/// Errors that can occur with the quantum protocol
#[derive(Debug)]
pub enum ProtocolError {
    Identity(FalconIdentityError),
    Transport(QkdTransportError),
    KeyNotGenerated,
    MessageTooShort { expected: usize, actual: usize },
    UnsupportedVersion(u8),
    InvalidMessageType(u8),
    UnexpectedMessageType { expected: MessageType, actual: MessageType },
    InvalidPayload(String),
    SignatureVerificationFailed,
}

impl std::fmt::Display for ProtocolError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Identity(e) => write!(f, "Identity error: {}", e),
            Self::Transport(e) => write!(f, "Transport error: {}", e),
            Self::KeyNotGenerated => write!(f, "Keys not generated"),
            Self::MessageTooShort { expected, actual } => {
                write!(f, "Message too short: expected {}, got {}", expected, actual)
            }
            Self::UnsupportedVersion(v) => write!(f, "Unsupported protocol version: {}", v),
            Self::InvalidMessageType(t) => write!(f, "Invalid message type: {}", t),
            Self::UnexpectedMessageType { expected, actual } => {
                write!(f, "Unexpected message type: expected {:?}, got {:?}", expected, actual)
            }
            Self::InvalidPayload(msg) => write!(f, "Invalid payload: {}", msg),
            Self::SignatureVerificationFailed => write!(f, "Signature verification failed"),
        }
    }
}

impl std::error::Error for ProtocolError {}

#[cfg(test)]
mod tests {
    use super::*;

    fn create_test_protocol() -> (QuantumProtocol, Arc<Mutex<FalconIdentity>>) {
        let mut identity = FalconIdentity::new();
        identity.generate_keypair().unwrap();
        let identity = Arc::new(Mutex::new(identity));
        let transport = Arc::new(QkdTransport::new(identity.clone()));
        let protocol = QuantumProtocol::new(identity.clone(), transport);
        (protocol, identity)
    }

    #[test]
    fn test_message_header_roundtrip() {
        let node_id = H256::from_slice(&[0x42u8; 32]);
        let header = MessageHeader::new(MessageType::Data, node_id, 1024);

        let encoded = header.encode();
        assert_eq!(encoded.len(), MessageHeader::SIZE);

        let decoded = MessageHeader::decode(&encoded).unwrap();
        assert_eq!(decoded.version, PROTOCOL_VERSION);
        assert_eq!(decoded.message_type, MessageType::Data);
        assert_eq!(decoded.sender_node_id, node_id);
        assert_eq!(decoded.payload_length, 1024);
    }

    #[test]
    fn test_message_type_conversion() {
        assert_eq!(MessageType::try_from(0x01).unwrap(), MessageType::Data);
        assert_eq!(MessageType::try_from(0x02).unwrap(), MessageType::SessionRequest);
        assert!(MessageType::try_from(0xFF).is_err());
    }

    #[test]
    fn test_signed_message_roundtrip() {
        let (protocol, _identity) = create_test_protocol();

        let payload = b"Test payload data";
        let signed = protocol
            .create_signed_message(MessageType::Data, payload)
            .unwrap();

        let (header, decoded_payload) = protocol.verify_and_decode_message(&signed).unwrap();

        assert_eq!(header.message_type, MessageType::Data);
        assert_eq!(decoded_payload, payload);
    }

    #[test]
    fn test_session_establishment() {
        let (protocol_a, identity_a) = create_test_protocol();
        let (protocol_b, identity_b) = create_test_protocol();

        let node_id_a = protocol_a.node_id();
        let node_id_b = protocol_b.node_id();

        // Register each other's signing public keys
        let sign_pubkey_a = identity_a.lock().unwrap().sign_public_key().unwrap().to_vec();
        let sign_pubkey_b = identity_b.lock().unwrap().sign_public_key().unwrap().to_vec();
        protocol_a.register_peer(node_id_b, sign_pubkey_b.clone());
        protocol_b.register_peer(node_id_a, sign_pubkey_a.clone());

        // Get B's KEM public key
        let kem_pubkey_b = identity_b
            .lock()
            .unwrap()
            .kem_public_key()
            .unwrap()
            .to_vec();

        // A creates session request for B
        let request = protocol_a
            .create_session_request(&node_id_b, &kem_pubkey_b)
            .unwrap();

        // B processes the request and creates response
        let (sender_id, response) = protocol_b.process_session_request(&request).unwrap();
        assert_eq!(sender_id, protocol_a.node_id());

        // A processes the response
        let peer_id = protocol_a.process_session_response(&response).unwrap();
        assert_eq!(peer_id, protocol_b.node_id());

        // Both should have sessions
        assert!(protocol_a.has_session(&node_id_b));
        assert!(protocol_b.has_session(&protocol_a.node_id()));
    }

    #[test]
    fn test_encrypted_data_exchange() {
        let (protocol_a, identity_a) = create_test_protocol();
        let (protocol_b, identity_b) = create_test_protocol();

        let node_id_a = protocol_a.node_id();
        let node_id_b = protocol_b.node_id();

        // Register each other's signing public keys
        let sign_pubkey_a = identity_a.lock().unwrap().sign_public_key().unwrap().to_vec();
        let sign_pubkey_b = identity_b.lock().unwrap().sign_public_key().unwrap().to_vec();
        protocol_a.register_peer(node_id_b, sign_pubkey_b);
        protocol_b.register_peer(node_id_a, sign_pubkey_a);

        // Establish sessions
        let kem_pubkey_b = identity_b.lock().unwrap().kem_public_key().unwrap().to_vec();
        let request = protocol_a.create_session_request(&node_id_b, &kem_pubkey_b).unwrap();
        let (_, response) = protocol_b.process_session_request(&request).unwrap();
        protocol_a.process_session_response(&response).unwrap();

        // A sends encrypted data to B
        let message = b"Hello from A to B!";
        let encrypted = protocol_a.send_data(&node_id_b, message).unwrap();

        // B receives and decrypts
        let (sender, decrypted) = protocol_b.receive_data(&encrypted).unwrap();
        assert_eq!(sender, node_id_a);
        assert_eq!(decrypted, message);
    }

    #[test]
    fn test_bidirectional_encrypted_exchange() {
        let (protocol_a, identity_a) = create_test_protocol();
        let (protocol_b, identity_b) = create_test_protocol();

        let node_id_a = protocol_a.node_id();
        let node_id_b = protocol_b.node_id();

        // Register each other's signing public keys
        let sign_pubkey_a = identity_a.lock().unwrap().sign_public_key().unwrap().to_vec();
        let sign_pubkey_b = identity_b.lock().unwrap().sign_public_key().unwrap().to_vec();
        protocol_a.register_peer(node_id_b, sign_pubkey_b);
        protocol_b.register_peer(node_id_a, sign_pubkey_a);

        // A initiates session with B
        let kem_pubkey_b = identity_b.lock().unwrap().kem_public_key().unwrap().to_vec();
        let request_ab = protocol_a.create_session_request(&node_id_b, &kem_pubkey_b).unwrap();
        let (_, response_ab) = protocol_b.process_session_request(&request_ab).unwrap();
        protocol_a.process_session_response(&response_ab).unwrap();

        // B initiates session with A
        let kem_pubkey_a = identity_a.lock().unwrap().kem_public_key().unwrap().to_vec();
        let request_ba = protocol_b.create_session_request(&node_id_a, &kem_pubkey_a).unwrap();
        let (_, response_ba) = protocol_a.process_session_request(&request_ba).unwrap();
        protocol_b.process_session_response(&response_ba).unwrap();

        // A -> B
        let msg_a = b"Message from A";
        let encrypted_a = protocol_a.send_data(&node_id_b, msg_a).unwrap();
        let (_, decrypted_a) = protocol_b.receive_data(&encrypted_a).unwrap();
        assert_eq!(decrypted_a, msg_a);

        // B -> A
        let msg_b = b"Message from B";
        let encrypted_b = protocol_b.send_data(&node_id_a, msg_b).unwrap();
        let (_, decrypted_b) = protocol_a.receive_data(&encrypted_b).unwrap();
        assert_eq!(decrypted_b, msg_b);
    }

    #[test]
    fn test_tampered_message_rejected() {
        let (protocol, _identity) = create_test_protocol();

        let payload = b"Original message";
        let mut signed = protocol
            .create_signed_message(MessageType::Data, payload)
            .unwrap();

        // Tamper with the signed message
        if signed.len() > 50 {
            signed[50] ^= 0xFF;
        }

        // Should fail verification
        let result = protocol.verify_and_decode_message(&signed);
        assert!(result.is_err());
    }
}
