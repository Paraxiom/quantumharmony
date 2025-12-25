// node/src/quantum_p2p/mod.rs
//
// Quantum-secured P2P networking module.
//
// This module provides post-quantum secure peer-to-peer communication using:
// - Falcon-1024: NIST PQC standard for digital signatures
// - ML-KEM-1024 (Kyber): NIST PQC standard for key encapsulation
// - AES-256-GCM: Authenticated encryption for message confidentiality
//
// Architecture:
// - FalconIdentity: Node identity with signing and KEM keypairs
// - QkdTransport: Session key management and encryption layer
// - QuantumProtocol: Message framing, signing, and session establishment
// - VrfPeerSelection: Verifiable random peer selection

pub mod identity;
pub mod identity_source;
pub mod network;
pub mod protocol;
pub mod qkd_interface;
pub mod transport;
pub mod peer_selection;

// Re-export main types
pub use identity::{
    FalconIdentity, FalconIdentityError,
    FALCON_PUBLIC_KEY_SIZE, FALCON_SECRET_KEY_SIZE,
    KEM_PUBLIC_KEY_SIZE, KEM_SECRET_KEY_SIZE, KEM_CIPHERTEXT_SIZE,
};
pub use protocol::{
    MessageHeader, MessageType, ProtocolError, QuantumProtocol,
    PROTOCOL_NAME, PROTOCOL_VERSION,
};
pub use transport::{
    QkdTransport, QkdTransportError,
    AES_KEY_SIZE, NONCE_SIZE, DEFAULT_KEY_ROTATION_INTERVAL,
};
pub use peer_selection::VrfPeerSelection;
pub use network::{
    QuantumNetworkHandler, QuantumKeyExchangeMessage,
    quantum_keyex_peers_set_config, QUANTUM_KEY_EXCHANGE_PROTOCOL,
};
pub use identity_source::{
    IdentitySource, IdentitySourceConfig, IdentitySourceError,
    IdentityTier, PqcNodeId,
};
pub use qkd_interface::{
    QkdHardwareInterface, QkdDeviceManager, StubQkdDevice,
    QkdKey, QkdError, QkdDeviceStatus, QkdConnectionParams,
};

use std::sync::{Arc, Mutex};

/// Initialize the quantum P2P components
///
/// Returns a tuple of (identity, transport, protocol) ready for use
pub fn init_quantum_p2p() -> Result<
    (
        Arc<Mutex<FalconIdentity>>,
        Arc<QkdTransport>,
        QuantumProtocol,
    ),
    Box<dyn std::error::Error>,
> {
    // Create and initialize identity
    let mut identity = FalconIdentity::new();
    identity.generate_keypair()?;

    let node_id = identity.node_id().map_err(|e| e.to_string())?;
    log::info!("Initialized quantum P2P identity with node ID: {:?}", node_id);

    let identity = Arc::new(Mutex::new(identity));

    // Create transport layer
    let transport = Arc::new(QkdTransport::new(identity.clone()));

    // Create protocol handler
    let protocol = QuantumProtocol::new(identity.clone(), transport.clone());

    log::info!("Quantum P2P components initialized successfully");

    Ok((identity, transport, protocol))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_init_quantum_p2p() {
        let result = init_quantum_p2p();
        assert!(result.is_ok());

        let (identity, transport, protocol) = result.unwrap();

        // Verify identity is initialized
        let id = identity.lock().unwrap();
        assert!(id.sign_public_key().is_some());
        assert!(id.kem_public_key().is_some());
        drop(id);

        // Verify protocol has a node ID
        assert_ne!(protocol.node_id(), sp_core::H256::zero());
    }

    #[test]
    fn test_full_p2p_flow() {
        // Initialize two nodes
        let (identity_a, _transport_a, protocol_a) = init_quantum_p2p().unwrap();
        let (identity_b, _transport_b, protocol_b) = init_quantum_p2p().unwrap();

        let node_id_a = protocol_a.node_id();
        let node_id_b = protocol_b.node_id();

        // Register each other's signing public keys
        let sign_pubkey_a = identity_a.lock().unwrap().sign_public_key().unwrap().to_vec();
        let sign_pubkey_b = identity_b.lock().unwrap().sign_public_key().unwrap().to_vec();
        protocol_a.register_peer(node_id_b, sign_pubkey_b);
        protocol_b.register_peer(node_id_a, sign_pubkey_a);

        // Get B's KEM public key
        let kem_pubkey_b = identity_b
            .lock()
            .unwrap()
            .kem_public_key()
            .unwrap()
            .to_vec();

        // A initiates session with B
        let request = protocol_a
            .create_session_request(&node_id_b, &kem_pubkey_b)
            .unwrap();

        // B processes request and responds
        let (sender, response) = protocol_b.process_session_request(&request).unwrap();
        assert_eq!(sender, node_id_a);

        // A processes response
        protocol_a.process_session_response(&response).unwrap();

        // Now A can send encrypted data to B
        let secret_message = b"This is a quantum-secured secret message!";
        let encrypted = protocol_a.send_data(&node_id_b, secret_message).unwrap();

        // B receives and decrypts
        let (from, decrypted) = protocol_b.receive_data(&encrypted).unwrap();
        assert_eq!(from, node_id_a);
        assert_eq!(&decrypted[..], secret_message);
    }
}
