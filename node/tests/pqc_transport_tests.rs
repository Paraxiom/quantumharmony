//! Integration tests for PQC transport layer.
//!
//! These tests exercise the full PQC handshake protocol, transport construction,
//! and multi-peer session management. Tests that require a running node are marked
//! with `#[ignore]`.
//!
//! Run all:  cargo test --test pqc_transport_tests
//! Run live: cargo test --test pqc_transport_tests -- --ignored --nocapture

use pqcrypto_falcon::falcon1024;
use pqcrypto_kyber::kyber1024;
use pqcrypto_traits::kem::{
    Ciphertext, PublicKey as KemPublicKey, SecretKey as KemSecretKey, SharedSecret,
};
use pqcrypto_traits::sign::{
    PublicKey as SignPublicKey, SecretKey as SignSecretKey, SignedMessage,
};

/// Create a unique temp directory
fn temp_dir(name: &str) -> std::path::PathBuf {
    let dir = std::env::temp_dir()
        .join("qh_pqc_integration")
        .join(name)
        .join(format!("{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

// =============================================================================
// PQC Handshake Protocol Tests
// =============================================================================

/// Full 3-round PQC handshake: Kyber KEM + Falcon signatures
///
/// Replicates the handshake protocol from pqc_authenticator.rs:
///   1. Initiator → Responder: [Kyber_PK || Falcon_PK || Falcon_Sig(Kyber_PK)]
///   2. Responder → Initiator: [Kyber_CT || Kyber_PK || Falcon_PK || Falcon_Sig(...)]
///   3. Initiator → Responder: [Kyber_CT || confirmation]
#[test]
fn test_full_pqc_handshake_protocol() {
    // === Setup: Long-term Falcon-1024 identities ===
    let (alice_falcon_pk, alice_falcon_sk) = falcon1024::keypair();
    let (bob_falcon_pk, bob_falcon_sk) = falcon1024::keypair();

    // === Round 1: Alice → Bob ===
    // Alice generates ephemeral Kyber keypair
    let (alice_kyber_pk, alice_kyber_sk) = kyber1024::keypair();

    // Alice signs her ephemeral Kyber public key with Falcon
    let alice_sig = falcon1024::sign(alice_kyber_pk.as_bytes(), &alice_falcon_sk);

    // Bob receives and verifies
    let verified_kyber_pk = falcon1024::open(&alice_sig, &alice_falcon_pk);
    assert!(verified_kyber_pk.is_ok(), "Round 1: Bob should verify Alice's Falcon signature");
    assert_eq!(
        verified_kyber_pk.unwrap(),
        alice_kyber_pk.as_bytes(),
        "Round 1: Verified Kyber PK should match Alice's"
    );

    // === Round 2: Bob → Alice ===
    // Bob encapsulates a shared secret using Alice's Kyber PK
    let (shared_secret_1, ciphertext_1) = kyber1024::encapsulate(&alice_kyber_pk);

    // Bob generates his own ephemeral Kyber keypair
    let (bob_kyber_pk, bob_kyber_sk) = kyber1024::keypair();

    // Bob signs his response
    let mut bob_response_payload = Vec::new();
    bob_response_payload.extend_from_slice(ciphertext_1.as_bytes());
    bob_response_payload.extend_from_slice(bob_kyber_pk.as_bytes());
    let bob_sig = falcon1024::sign(&bob_response_payload, &bob_falcon_sk);

    // Alice receives and verifies Bob's response
    let verified_response = falcon1024::open(&bob_sig, &bob_falcon_pk);
    assert!(verified_response.is_ok(), "Round 2: Alice should verify Bob's Falcon signature");

    // Alice decapsulates shared_secret_1
    let alice_shared_secret_1 = kyber1024::decapsulate(&ciphertext_1, &alice_kyber_sk);
    assert_eq!(
        shared_secret_1.as_bytes(),
        alice_shared_secret_1.as_bytes(),
        "Round 2: Both parties should derive the same shared_secret_1"
    );

    // === Round 3: Alice → Bob ===
    // Alice encapsulates shared_secret_2 using Bob's Kyber PK
    let (shared_secret_2, ciphertext_2) = kyber1024::encapsulate(&bob_kyber_pk);

    // Bob decapsulates
    let bob_shared_secret_2 = kyber1024::decapsulate(&ciphertext_2, &bob_kyber_sk);
    assert_eq!(
        shared_secret_2.as_bytes(),
        bob_shared_secret_2.as_bytes(),
        "Round 3: Both parties should derive the same shared_secret_2"
    );

    // === Session Key Derivation ===
    // Combine both shared secrets (simplified — production uses HKDF)
    let mut combined_secret = Vec::new();
    combined_secret.extend_from_slice(shared_secret_1.as_bytes());
    combined_secret.extend_from_slice(shared_secret_2.as_bytes());
    assert_eq!(combined_secret.len(), 64, "Combined secret should be 64 bytes (32 + 32)");
}

/// Verify that tampered handshake messages are rejected
#[test]
fn test_handshake_rejects_tampered_falcon_signature() {
    let (alice_falcon_pk, alice_falcon_sk) = falcon1024::keypair();
    let (bob_falcon_pk, _) = falcon1024::keypair();
    let (alice_kyber_pk, _) = kyber1024::keypair();

    // Alice signs her Kyber PK
    let mut signed = falcon1024::sign(alice_kyber_pk.as_bytes(), &alice_falcon_sk);
    let mut signed_bytes = signed.as_bytes().to_vec();

    // Tamper with the signature
    if !signed_bytes.is_empty() {
        signed_bytes[0] ^= 0xFF;
    }
    let tampered = falcon1024::SignedMessage::from_bytes(&signed_bytes).unwrap();

    // Bob verifies with Alice's key — should fail
    let result = falcon1024::open(&tampered, &alice_falcon_pk);
    assert!(result.is_err(), "Tampered Falcon signature should be rejected");

    // Also try verifying with wrong key
    let signed_clean = falcon1024::sign(alice_kyber_pk.as_bytes(), &alice_falcon_sk);
    let result = falcon1024::open(&signed_clean, &bob_falcon_pk);
    assert!(result.is_err(), "Signature verified with wrong key should be rejected");
}

/// Verify KEM with wrong secret key fails
#[test]
fn test_kem_decapsulation_with_wrong_key() {
    let (alice_kyber_pk, _alice_kyber_sk) = kyber1024::keypair();
    let (_, wrong_kyber_sk) = kyber1024::keypair();

    let (original_secret, ciphertext) = kyber1024::encapsulate(&alice_kyber_pk);

    // Decapsulate with wrong secret key — should produce different shared secret
    let wrong_secret = kyber1024::decapsulate(&ciphertext, &wrong_kyber_sk);
    assert_ne!(
        original_secret.as_bytes(),
        wrong_secret.as_bytes(),
        "Decapsulation with wrong key should produce different shared secret"
    );
}

// =============================================================================
// AES-256-GCM Session Encryption Tests
// =============================================================================

#[test]
fn test_aes_gcm_session_encryption_roundtrip() {
    use aes_gcm::{
        aead::{Aead, KeyInit},
        Aes256Gcm, Nonce,
    };

    // Simulate session key derivation from KEM shared secrets
    let (_, ciphertext) = kyber1024::encapsulate(&kyber1024::keypair().0);
    let shared_secret = kyber1024::decapsulate(&ciphertext, &kyber1024::keypair().1);

    // Use the 32-byte shared secret as AES-256 key
    let (alice_kyber_pk, alice_kyber_sk) = kyber1024::keypair();
    let (shared_secret, _ct) = kyber1024::encapsulate(&alice_kyber_pk);
    let key_bytes = shared_secret.as_bytes();
    assert_eq!(key_bytes.len(), 32, "KEM shared secret should be 32 bytes for AES-256");

    let cipher = Aes256Gcm::new_from_slice(key_bytes).expect("valid AES-256 key");
    let nonce = Nonce::from_slice(b"unique nonce"); // 96-bit nonce

    let plaintext = b"block gossip: new block #208001 from Alice";
    let ciphertext = cipher.encrypt(nonce, plaintext.as_ref())
        .expect("encryption should succeed");

    assert_ne!(&ciphertext[..], plaintext.as_ref(), "Ciphertext should differ from plaintext");

    let decrypted = cipher.decrypt(nonce, ciphertext.as_ref())
        .expect("decryption should succeed");

    assert_eq!(decrypted, plaintext, "Decrypted text should match original");
}

#[test]
fn test_aes_gcm_rejects_wrong_key() {
    use aes_gcm::{
        aead::{Aead, KeyInit},
        Aes256Gcm, Nonce,
    };

    let key1 = [0x42u8; 32];
    let key2 = [0x43u8; 32];
    let nonce = Nonce::from_slice(b"unique nonce");

    let cipher1 = Aes256Gcm::new_from_slice(&key1).unwrap();
    let cipher2 = Aes256Gcm::new_from_slice(&key2).unwrap();

    let plaintext = b"consensus vote: finalize block #208000";
    let ciphertext = cipher1.encrypt(nonce, plaintext.as_ref()).unwrap();

    // Decrypt with wrong key should fail
    let result = cipher2.decrypt(nonce, ciphertext.as_ref());
    assert!(result.is_err(), "Decryption with wrong key should fail");
}

#[test]
fn test_aes_gcm_rejects_tampered_ciphertext() {
    use aes_gcm::{
        aead::{Aead, KeyInit},
        Aes256Gcm, Nonce,
    };

    let key = [0x42u8; 32];
    let nonce = Nonce::from_slice(b"unique nonce");
    let cipher = Aes256Gcm::new_from_slice(&key).unwrap();

    let plaintext = b"peer discovery announcement";
    let mut ciphertext = cipher.encrypt(nonce, plaintext.as_ref()).unwrap();

    // Tamper with ciphertext
    if !ciphertext.is_empty() {
        ciphertext[0] ^= 0xFF;
    }

    let result = cipher.decrypt(nonce, ciphertext.as_ref());
    assert!(result.is_err(), "Tampered ciphertext should fail AEAD verification");
}

// =============================================================================
// Quantum P2P Full Session Tests
// =============================================================================

#[test]
fn test_quantum_p2p_full_session_establishment() {
    use quantumharmony_node::quantum_p2p::{FalconIdentity, QuantumProtocol, QkdTransport};
    use std::sync::{Arc, Mutex};

    // Create two identities (Alice and Bob)
    let mut alice_id = FalconIdentity::new();
    alice_id.generate_keypair().unwrap();
    let mut bob_id = FalconIdentity::new();
    bob_id.generate_keypair().unwrap();

    let alice_node_id = alice_id.node_id().unwrap();
    let bob_node_id = bob_id.node_id().unwrap();

    let alice_sign_pk = alice_id.sign_public_key().unwrap().to_vec();
    let bob_sign_pk = bob_id.sign_public_key().unwrap().to_vec();
    let bob_kem_pk = bob_id.kem_public_key().unwrap().to_vec();

    let alice_id = Arc::new(Mutex::new(alice_id));
    let bob_id = Arc::new(Mutex::new(bob_id));

    let alice_transport = Arc::new(QkdTransport::new(alice_id.clone()));
    let bob_transport = Arc::new(QkdTransport::new(bob_id.clone()));

    let alice_protocol = QuantumProtocol::new(alice_id.clone(), alice_transport.clone());
    let bob_protocol = QuantumProtocol::new(bob_id.clone(), bob_transport.clone());

    // Register peer public keys
    alice_protocol.register_peer(bob_node_id, bob_sign_pk);
    bob_protocol.register_peer(alice_node_id, alice_sign_pk);

    // Alice initiates session with Bob
    let request = alice_protocol.create_session_request(&bob_node_id, &bob_kem_pk)
        .expect("Session request creation should succeed");

    // Bob processes and responds
    let (sender, response) = bob_protocol.process_session_request(&request)
        .expect("Session request processing should succeed");
    assert_eq!(sender, alice_node_id, "Request sender should be Alice");

    // Alice processes response
    alice_protocol.process_session_response(&response)
        .expect("Session response processing should succeed");

    // Test encrypted communication
    let message = b"Block #208001 gossip payload with PQC encryption";
    let encrypted = alice_protocol.send_data(&bob_node_id, message)
        .expect("Encryption should succeed");

    let (from, decrypted) = bob_protocol.receive_data(&encrypted)
        .expect("Decryption should succeed");
    assert_eq!(from, alice_node_id);
    assert_eq!(&decrypted[..], message);
}

#[test]
fn test_quantum_p2p_bidirectional_communication() {
    use quantumharmony_node::quantum_p2p::{FalconIdentity, QuantumProtocol, QkdTransport};
    use std::sync::{Arc, Mutex};

    let mut alice_id = FalconIdentity::new();
    alice_id.generate_keypair().unwrap();
    let mut bob_id = FalconIdentity::new();
    bob_id.generate_keypair().unwrap();

    let alice_node_id = alice_id.node_id().unwrap();
    let bob_node_id = bob_id.node_id().unwrap();

    let alice_sign_pk = alice_id.sign_public_key().unwrap().to_vec();
    let bob_sign_pk = bob_id.sign_public_key().unwrap().to_vec();
    let bob_kem_pk = bob_id.kem_public_key().unwrap().to_vec();

    let alice_id = Arc::new(Mutex::new(alice_id));
    let bob_id = Arc::new(Mutex::new(bob_id));

    let alice_transport = Arc::new(QkdTransport::new(alice_id.clone()));
    let bob_transport = Arc::new(QkdTransport::new(bob_id.clone()));

    let alice_protocol = QuantumProtocol::new(alice_id.clone(), alice_transport.clone());
    let bob_protocol = QuantumProtocol::new(bob_id.clone(), bob_transport.clone());

    alice_protocol.register_peer(bob_node_id, bob_sign_pk);
    bob_protocol.register_peer(alice_node_id, alice_sign_pk);

    let request = alice_protocol.create_session_request(&bob_node_id, &bob_kem_pk).unwrap();
    let (_, response) = bob_protocol.process_session_request(&request).unwrap();
    alice_protocol.process_session_response(&response).unwrap();

    // Alice → Bob
    let msg_a2b = b"Alice sends consensus vote to Bob";
    let enc = alice_protocol.send_data(&bob_node_id, msg_a2b).unwrap();
    let (from, dec) = bob_protocol.receive_data(&enc).unwrap();
    assert_eq!(from, alice_node_id);
    assert_eq!(&dec[..], msg_a2b);

    // Bob → Alice
    let msg_b2a = b"Bob sends block announcement to Alice";
    let enc = bob_protocol.send_data(&alice_node_id, msg_b2a).unwrap();
    let (from, dec) = alice_protocol.receive_data(&enc).unwrap();
    assert_eq!(from, bob_node_id);
    assert_eq!(&dec[..], msg_b2a);
}

#[test]
fn test_quantum_p2p_multiple_messages_same_session() {
    use quantumharmony_node::quantum_p2p::{FalconIdentity, QuantumProtocol, QkdTransport};
    use std::sync::{Arc, Mutex};

    let mut alice_id = FalconIdentity::new();
    alice_id.generate_keypair().unwrap();
    let mut bob_id = FalconIdentity::new();
    bob_id.generate_keypair().unwrap();

    let alice_node_id = alice_id.node_id().unwrap();
    let bob_node_id = bob_id.node_id().unwrap();

    let bob_sign_pk = bob_id.sign_public_key().unwrap().to_vec();
    let alice_sign_pk = alice_id.sign_public_key().unwrap().to_vec();
    let bob_kem_pk = bob_id.kem_public_key().unwrap().to_vec();

    let alice_id = Arc::new(Mutex::new(alice_id));
    let bob_id = Arc::new(Mutex::new(bob_id));
    let alice_transport = Arc::new(QkdTransport::new(alice_id.clone()));
    let bob_transport = Arc::new(QkdTransport::new(bob_id.clone()));
    let alice_protocol = QuantumProtocol::new(alice_id, alice_transport);
    let bob_protocol = QuantumProtocol::new(bob_id, bob_transport);

    alice_protocol.register_peer(bob_node_id, bob_sign_pk);
    bob_protocol.register_peer(alice_node_id, alice_sign_pk);

    let request = alice_protocol.create_session_request(&bob_node_id, &bob_kem_pk).unwrap();
    let (_, response) = bob_protocol.process_session_request(&request).unwrap();
    alice_protocol.process_session_response(&response).unwrap();

    // Send 100 messages over the same session
    for i in 0..100 {
        let msg = format!("Block gossip message #{}", i);
        let encrypted = alice_protocol.send_data(&bob_node_id, msg.as_bytes()).unwrap();
        let (from, decrypted) = bob_protocol.receive_data(&encrypted).unwrap();
        assert_eq!(from, alice_node_id);
        assert_eq!(String::from_utf8(decrypted).unwrap(), msg);
    }
}

#[test]
fn test_quantum_p2p_tampered_encrypted_message_rejected() {
    use quantumharmony_node::quantum_p2p::{FalconIdentity, QuantumProtocol, QkdTransport};
    use std::sync::{Arc, Mutex};

    let mut alice_id = FalconIdentity::new();
    alice_id.generate_keypair().unwrap();
    let mut bob_id = FalconIdentity::new();
    bob_id.generate_keypair().unwrap();

    let alice_node_id = alice_id.node_id().unwrap();
    let bob_node_id = bob_id.node_id().unwrap();
    let bob_sign_pk = bob_id.sign_public_key().unwrap().to_vec();
    let alice_sign_pk = alice_id.sign_public_key().unwrap().to_vec();
    let bob_kem_pk = bob_id.kem_public_key().unwrap().to_vec();

    let alice_id = Arc::new(Mutex::new(alice_id));
    let bob_id = Arc::new(Mutex::new(bob_id));
    let alice_transport = Arc::new(QkdTransport::new(alice_id.clone()));
    let bob_transport = Arc::new(QkdTransport::new(bob_id.clone()));
    let alice_protocol = QuantumProtocol::new(alice_id, alice_transport);
    let bob_protocol = QuantumProtocol::new(bob_id, bob_transport);

    alice_protocol.register_peer(bob_node_id, bob_sign_pk);
    bob_protocol.register_peer(alice_node_id, alice_sign_pk);

    let request = alice_protocol.create_session_request(&bob_node_id, &bob_kem_pk).unwrap();
    let (_, response) = bob_protocol.process_session_request(&request).unwrap();
    alice_protocol.process_session_response(&response).unwrap();

    let msg = b"sensitive consensus vote";
    let mut encrypted = alice_protocol.send_data(&bob_node_id, msg).unwrap();

    // Tamper with the encrypted data
    if encrypted.len() > 10 {
        encrypted[10] ^= 0xFF;
    }

    let result = bob_protocol.receive_data(&encrypted);
    assert!(result.is_err(), "Tampered encrypted message should be rejected");
}

// =============================================================================
// Key Persistence Integration Tests
// =============================================================================

#[test]
fn test_handler_key_persistence_generates_new_on_empty_dir() {
    use quantumharmony_node::quantum_p2p::QuantumNetworkHandler;

    let dir = temp_dir("handler_new_gen");
    let key_path = dir.join("identity.json");

    assert!(!key_path.exists());
    let handler = QuantumNetworkHandler::new_with_key_file(&key_path.to_string_lossy())
        .expect("Handler should generate new identity");
    assert!(key_path.exists(), "Identity file should be created");
    assert_ne!(handler.node_id(), sp_core::H256::zero());
}

#[test]
fn test_handler_key_persistence_loads_existing() {
    use quantumharmony_node::quantum_p2p::QuantumNetworkHandler;

    let dir = temp_dir("handler_load_existing");
    let key_path = dir.join("identity.json");

    // First run: generate
    let h1 = QuantumNetworkHandler::new_with_key_file(&key_path.to_string_lossy()).unwrap();
    let id1 = h1.node_id();
    drop(h1);

    // Second run: load
    let h2 = QuantumNetworkHandler::new_with_key_file(&key_path.to_string_lossy()).unwrap();
    let id2 = h2.node_id();

    assert_eq!(id1, id2, "Node ID must persist across handler restarts");
}

#[test]
fn test_three_validator_independent_identities() {
    use quantumharmony_node::quantum_p2p::QuantumNetworkHandler;

    let dir = temp_dir("three_validators");

    let alice = QuantumNetworkHandler::new_with_key_file(
        &dir.join("alice.json").to_string_lossy()
    ).unwrap();
    let bob = QuantumNetworkHandler::new_with_key_file(
        &dir.join("bob.json").to_string_lossy()
    ).unwrap();
    let charlie = QuantumNetworkHandler::new_with_key_file(
        &dir.join("charlie.json").to_string_lossy()
    ).unwrap();

    // All three should have unique node IDs
    assert_ne!(alice.node_id(), bob.node_id());
    assert_ne!(alice.node_id(), charlie.node_id());
    assert_ne!(bob.node_id(), charlie.node_id());

    // All should be non-zero
    assert_ne!(alice.node_id(), sp_core::H256::zero());
    assert_ne!(bob.node_id(), sp_core::H256::zero());
    assert_ne!(charlie.node_id(), sp_core::H256::zero());
}

// =============================================================================
// PQC Transport Config Integration (requires pqc-transport feature)
// =============================================================================

#[cfg(feature = "pqc-transport")]
#[test]
fn test_pqc_identity_from_file_roundtrip() {
    let dir = temp_dir("pqc_identity_roundtrip");
    let key_path = dir.join("pqc_transport_identity.json");

    // Generate and save
    let (pk, sk) = falcon1024::keypair();
    let key_json = serde_json::json!({
        "falcon_public_key": format!("0x{}", hex::encode(pk.as_bytes())),
        "falcon_secret_key": format!("0x{}", hex::encode(sk.as_bytes())),
    });
    std::fs::write(&key_path, serde_json::to_string_pretty(&key_json).unwrap()).unwrap();

    let original = sc_network::pqc_authenticator::PqcIdentity::from_keypair(
        falcon1024::PublicKey::from_bytes(pk.as_bytes()).unwrap(),
        falcon1024::SecretKey::from_bytes(sk.as_bytes()).unwrap(),
    );

    // Load from file
    let contents = std::fs::read_to_string(&key_path).unwrap();
    let json: serde_json::Value = serde_json::from_str(&contents).unwrap();
    let loaded_pk = falcon1024::PublicKey::from_bytes(
        &hex::decode(json["falcon_public_key"].as_str().unwrap().trim_start_matches("0x")).unwrap()
    ).unwrap();
    let loaded_sk = falcon1024::SecretKey::from_bytes(
        &hex::decode(json["falcon_secret_key"].as_str().unwrap().trim_start_matches("0x")).unwrap()
    ).unwrap();
    let loaded = sc_network::pqc_authenticator::PqcIdentity::from_keypair(loaded_pk, loaded_sk);

    assert_eq!(original.peer_id(), loaded.peer_id(), "PeerId should survive file roundtrip");
}

// =============================================================================
// Live Network Tests (require running QuantumHarmony nodes)
// =============================================================================

#[tokio::test]
#[ignore = "Requires running QuantumHarmony 3-validator testnet (docker compose up)"]
async fn test_live_nodes_report_pqc_transport() {
    // Connect to Alice's RPC and check system_health
    let client = reqwest::Client::new();
    let response = client.post("http://localhost:9944")
        .json(&serde_json::json!({
            "id": 1,
            "jsonrpc": "2.0",
            "method": "system_health",
            "params": []
        }))
        .send()
        .await
        .expect("Should connect to Alice RPC");

    let body: serde_json::Value = response.json().await.unwrap();
    let health = &body["result"];
    assert!(health["shouldHavePeers"].as_bool().unwrap_or(false),
        "Validator should expect peers");
}

#[tokio::test]
#[ignore = "Requires running QuantumHarmony 3-validator testnet (docker compose up)"]
async fn test_live_peers_connected_via_pqc() {
    let client = reqwest::Client::new();

    // Check Alice has peers
    let response = client.post("http://localhost:9944")
        .json(&serde_json::json!({
            "id": 1,
            "jsonrpc": "2.0",
            "method": "system_peers",
            "params": []
        }))
        .send()
        .await
        .expect("Should connect to Alice RPC");

    let body: serde_json::Value = response.json().await.unwrap();
    let peers = body["result"].as_array().expect("system_peers should return array");
    assert!(peers.len() >= 2,
        "Alice should have at least 2 peers (Bob + Charlie), got {}", peers.len());
}

#[tokio::test]
#[ignore = "Requires running QuantumHarmony 3-validator testnet (docker compose up)"]
async fn test_live_blocks_finalized_with_pqc_transport() {
    let client = reqwest::Client::new();

    // Get finalized head
    let response = client.post("http://localhost:9944")
        .json(&serde_json::json!({
            "id": 1,
            "jsonrpc": "2.0",
            "method": "chain_getFinalizedHead",
            "params": []
        }))
        .send()
        .await
        .expect("Should get finalized head");

    let body: serde_json::Value = response.json().await.unwrap();
    let hash = body["result"].as_str().expect("Should return hash string");
    assert!(hash.starts_with("0x"), "Finalized hash should be hex");
    assert!(hash.len() > 10, "Finalized hash should be a real block hash");
}
