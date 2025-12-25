// node/src/quantum_p2p/network.rs
//
// Network integration for quantum-secured P2P protocol.
//
// This module provides the glue between quantum_p2p and Substrate's network layer,
// enabling quantum-secured communication between validators.

use crate::quantum_p2p::{
    FalconIdentity, FalconIdentityError, QuantumProtocol, QkdTransport,
    PROTOCOL_NAME,
};
use scale_codec::{Decode, Encode};
use sc_network::{
    config::{NonDefaultSetConfig, SetConfig, NonReservedPeerMode},
    service::traits::NotificationService,
    NetworkPeers, PeerId, ProtocolName,
};
use sp_core::H256;
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

/// Protocol name for quantum P2P key exchange
pub const QUANTUM_KEY_EXCHANGE_PROTOCOL: &str = "/quantumharmony/quantum-keyex/1";

/// Messages for the quantum key exchange protocol
#[derive(Clone, Encode, Decode, Debug)]
pub enum QuantumKeyExchangeMessage {
    /// Announce our public keys to a peer
    /// Contains: (node_id, sign_public_key, kem_public_key)
    Announce {
        node_id: [u8; 32],
        sign_pubkey: Vec<u8>,
        kem_pubkey: Vec<u8>,
    },
    /// Session establishment request (KEM ciphertext)
    SessionRequest {
        kem_ciphertext: Vec<u8>,
    },
    /// Session establishment response (KEM ciphertext)
    SessionResponse {
        kem_ciphertext: Vec<u8>,
    },
}

/// Quantum P2P network handler
///
/// Manages quantum-secured sessions with network peers.
pub struct QuantumNetworkHandler {
    /// Our quantum identity
    identity: Arc<Mutex<FalconIdentity>>,
    /// Transport layer for encryption
    transport: Arc<QkdTransport>,
    /// Protocol handler
    protocol: Arc<Mutex<QuantumProtocol>>,
    /// Mapping from libp2p PeerId to our quantum node ID
    peer_to_node_id: Mutex<HashMap<PeerId, H256>>,
    /// Mapping from quantum node ID to libp2p PeerId
    node_id_to_peer: Mutex<HashMap<H256, PeerId>>,
}

impl QuantumNetworkHandler {
    /// Create a new quantum network handler (generates ephemeral identity)
    pub fn new() -> Result<Self, Box<dyn std::error::Error>> {
        let mut identity = FalconIdentity::new();
        identity.generate_keypair()?;

        let node_id = identity.node_id()?;
        log::info!("Initialized quantum network handler with node ID: {:?}", node_id);

        let identity = Arc::new(Mutex::new(identity));
        let transport = Arc::new(QkdTransport::new(identity.clone()));
        let protocol = Arc::new(Mutex::new(QuantumProtocol::new(
            identity.clone(),
            transport.clone(),
        )));

        Ok(Self {
            identity,
            transport,
            protocol,
            peer_to_node_id: Mutex::new(HashMap::new()),
            node_id_to_peer: Mutex::new(HashMap::new()),
        })
    }

    /// Create a quantum network handler with persistent identity from a key file
    ///
    /// If the key file exists, loads the identity from it.
    /// If not, generates a new identity and saves it to the file.
    pub fn new_with_key_file(key_file_path: &str) -> Result<Self, Box<dyn std::error::Error>> {
        let identity = match FalconIdentity::load_from_file(key_file_path) {
            Ok(id) => {
                log::info!("[QUANTUM-P2P] Loaded existing Falcon identity from {}", key_file_path);
                id
            }
            Err(e) => {
                log::warn!("[QUANTUM-P2P] Could not load key file ({}), generating new identity", e);
                let mut id = FalconIdentity::new();
                id.generate_keypair()?;

                // Save the newly generated identity
                if let Err(save_err) = id.save_to_file(key_file_path) {
                    log::error!("[QUANTUM-P2P] Failed to save key file: {}", save_err);
                } else {
                    log::info!("[QUANTUM-P2P] Saved new Falcon identity to {}", key_file_path);
                }

                id
            }
        };

        let node_id = identity.node_id.ok_or("Node ID not set after loading")?;
        log::info!("[QUANTUM-P2P] Handler initialized with persistent node ID: {:?}", node_id);

        let identity = Arc::new(Mutex::new(identity));
        let transport = Arc::new(QkdTransport::new(identity.clone()));
        let protocol = Arc::new(Mutex::new(QuantumProtocol::new(
            identity.clone(),
            transport.clone(),
        )));

        Ok(Self {
            identity,
            transport,
            protocol,
            peer_to_node_id: Mutex::new(HashMap::new()),
            node_id_to_peer: Mutex::new(HashMap::new()),
        })
    }

    /// Get our node ID
    pub fn node_id(&self) -> H256 {
        self.identity.lock().unwrap().node_id().unwrap_or_default()
    }

    /// Get our announce message to send to peers
    pub fn get_announce_message(&self) -> Result<QuantumKeyExchangeMessage, Box<dyn std::error::Error>> {
        let identity = self.identity.lock().unwrap();
        let node_id = identity.node_id.ok_or("Node ID not set")?;
        let sign_pubkey = identity.sign_public_key()
            .ok_or("Sign public key not set")?
            .to_vec();
        let kem_pubkey = identity.kem_public_key()
            .ok_or("KEM public key not set")?
            .to_vec();

        Ok(QuantumKeyExchangeMessage::Announce {
            node_id: node_id.into(),
            sign_pubkey,
            kem_pubkey,
        })
    }

    /// Handle a peer connecting
    pub fn on_peer_connected(&self, peer_id: PeerId) {
        log::debug!("Quantum P2P: Peer connected: {:?}", peer_id);
        // We'll send our announce message when we receive notification service
    }

    /// Handle a peer disconnecting
    pub fn on_peer_disconnected(&self, peer_id: PeerId) {
        log::debug!("Quantum P2P: Peer disconnected: {:?}", peer_id);

        // Clean up mappings
        let mut peer_to_node = self.peer_to_node_id.lock().unwrap();
        if let Some(node_id) = peer_to_node.remove(&peer_id) {
            let mut node_to_peer = self.node_id_to_peer.lock().unwrap();
            node_to_peer.remove(&node_id);

            // Remove session
            self.transport.remove_session(&node_id);
            log::info!("Quantum P2P: Cleaned up session with peer {:?}", peer_id);
        }
    }

    /// Handle an incoming key exchange message
    pub fn handle_message(
        &self,
        peer_id: PeerId,
        message: QuantumKeyExchangeMessage,
    ) -> Option<QuantumKeyExchangeMessage> {
        match message {
            QuantumKeyExchangeMessage::Announce { node_id, sign_pubkey, kem_pubkey } => {
                let node_id = H256::from_slice(&node_id);
                log::info!("Quantum P2P: Received announce from peer {:?} with node ID {:?}", peer_id, node_id);

                // Store peer mapping
                {
                    let mut peer_to_node = self.peer_to_node_id.lock().unwrap();
                    let mut node_to_peer = self.node_id_to_peer.lock().unwrap();
                    peer_to_node.insert(peer_id, node_id);
                    node_to_peer.insert(node_id, peer_id);
                }

                // Register peer's signing key
                {
                    let protocol = self.protocol.lock().unwrap();
                    protocol.register_peer(node_id, sign_pubkey);
                }

                // Initiate session if we don't have one
                if !self.transport.has_session(&node_id) {
                    // Create session request
                    match self.transport.establish_session(&node_id, &kem_pubkey) {
                        Ok(ciphertext) => {
                            log::info!("Quantum P2P: Sending session request to {:?}", node_id);
                            return Some(QuantumKeyExchangeMessage::SessionRequest {
                                kem_ciphertext: ciphertext,
                            });
                        }
                        Err(e) => {
                            log::error!("Quantum P2P: Failed to create session request: {}", e);
                        }
                    }
                }

                None
            }

            QuantumKeyExchangeMessage::SessionRequest { kem_ciphertext } => {
                // Get the node ID for this peer
                let node_id = {
                    let peer_to_node = self.peer_to_node_id.lock().unwrap();
                    peer_to_node.get(&peer_id).cloned()
                };

                if let Some(node_id) = node_id {
                    // Accept the session
                    match self.transport.accept_session(&node_id, &kem_ciphertext) {
                        Ok(()) => {
                            log::info!("Quantum P2P: Accepted session from {:?}", node_id);

                            // Create response
                            let identity = self.identity.lock().unwrap();
                            if let Some(kem_pubkey) = identity.kem_public_key() {
                                drop(identity);

                                // We also need to establish our sending session
                                // Get peer's KEM pubkey from our records or request it
                                // For now, we'll just send an empty response to acknowledge
                                return Some(QuantumKeyExchangeMessage::SessionResponse {
                                    kem_ciphertext: vec![], // Peer already has our key from announce
                                });
                            }
                        }
                        Err(e) => {
                            log::error!("Quantum P2P: Failed to accept session: {}", e);
                        }
                    }
                } else {
                    log::warn!("Quantum P2P: Received session request from unknown peer {:?}", peer_id);
                }

                None
            }

            QuantumKeyExchangeMessage::SessionResponse { kem_ciphertext } => {
                let node_id = {
                    let peer_to_node = self.peer_to_node_id.lock().unwrap();
                    peer_to_node.get(&peer_id).cloned()
                };

                if let Some(node_id) = node_id {
                    if !kem_ciphertext.is_empty() {
                        // Accept the return session
                        match self.transport.accept_session(&node_id, &kem_ciphertext) {
                            Ok(()) => {
                                log::info!("Quantum P2P: Session fully established with {:?}", node_id);
                            }
                            Err(e) => {
                                log::error!("Quantum P2P: Failed to accept session response: {}", e);
                            }
                        }
                    } else {
                        log::info!("Quantum P2P: Session acknowledged by {:?}", node_id);
                    }
                }

                None
            }
        }
    }

    /// Encrypt a message for a peer
    pub fn encrypt_for_peer(&self, peer_id: &PeerId, data: &[u8]) -> Result<Vec<u8>, String> {
        let node_id = {
            let peer_to_node = self.peer_to_node_id.lock().unwrap();
            peer_to_node.get(peer_id).cloned()
                .ok_or_else(|| format!("Unknown peer: {:?}", peer_id))?
        };

        self.transport.encrypt(&node_id, data)
            .map_err(|e| e.to_string())
    }

    /// Decrypt a message from a peer
    pub fn decrypt_from_peer(&self, peer_id: &PeerId, data: &[u8]) -> Result<Vec<u8>, String> {
        let node_id = {
            let peer_to_node = self.peer_to_node_id.lock().unwrap();
            peer_to_node.get(peer_id).cloned()
                .ok_or_else(|| format!("Unknown peer: {:?}", peer_id))?
        };

        self.transport.decrypt(&node_id, data)
            .map_err(|e| e.to_string())
    }

    /// Check if we have a quantum session with a peer
    pub fn has_session(&self, peer_id: &PeerId) -> bool {
        let node_id = {
            let peer_to_node = self.peer_to_node_id.lock().unwrap();
            peer_to_node.get(peer_id).cloned()
        };

        node_id.map(|id| self.transport.has_session(&id)).unwrap_or(false)
    }

    /// Get number of active quantum sessions
    pub fn active_session_count(&self) -> usize {
        self.transport.active_session_count()
    }

    /// Get the underlying protocol for advanced usage
    pub fn protocol(&self) -> Arc<Mutex<QuantumProtocol>> {
        self.protocol.clone()
    }

    /// Get the underlying transport for advanced usage
    pub fn transport(&self) -> Arc<QkdTransport> {
        self.transport.clone()
    }
}

/// Create quantum key exchange protocol configuration
///
/// Returns a tuple of:
/// - NonDefaultSetConfig to add to network
/// - NotificationService for receiving messages
pub fn quantum_keyex_peers_set_config() -> (NonDefaultSetConfig, Box<dyn NotificationService>) {
    NonDefaultSetConfig::new(
        ProtocolName::from(QUANTUM_KEY_EXCHANGE_PROTOCOL),
        Vec::new(), // fallback names
        64 * 1024,  // max notification size: 64 KB (key exchange messages are small)
        None,       // handshake
        SetConfig {
            in_peers: 25,
            out_peers: 25,
            reserved_nodes: Vec::new(),
            non_reserved_mode: NonReservedPeerMode::Accept,
        },
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_quantum_network_handler_creation() {
        let handler = QuantumNetworkHandler::new().expect("Failed to create handler");
        assert_ne!(handler.node_id(), H256::zero());
    }

    #[test]
    fn test_announce_message() {
        let handler = QuantumNetworkHandler::new().expect("Failed to create handler");
        let msg = handler.get_announce_message().expect("Failed to get announce");

        match msg {
            QuantumKeyExchangeMessage::Announce { node_id, sign_pubkey, kem_pubkey } => {
                assert!(!sign_pubkey.is_empty());
                assert!(!kem_pubkey.is_empty());
                assert_ne!(H256::from_slice(&node_id), H256::zero());
            }
            _ => panic!("Expected Announce message"),
        }
    }

    #[test]
    fn test_message_encoding() {
        let msg = QuantumKeyExchangeMessage::Announce {
            node_id: [1u8; 32],
            sign_pubkey: vec![2u8; 100],
            kem_pubkey: vec![3u8; 100],
        };

        let encoded = msg.encode();
        let decoded = QuantumKeyExchangeMessage::decode(&mut &encoded[..]).unwrap();

        match decoded {
            QuantumKeyExchangeMessage::Announce { node_id, sign_pubkey, kem_pubkey } => {
                assert_eq!(node_id, [1u8; 32]);
                assert_eq!(sign_pubkey.len(), 100);
                assert_eq!(kem_pubkey.len(), 100);
            }
            _ => panic!("Wrong message type"),
        }
    }
}
