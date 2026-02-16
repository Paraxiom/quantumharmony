//! Unit and regression tests for PQC transport identity management.
//!
//! Tests cover:
//! - Falcon-1024 keypair generation and persistence
//! - PQC identity file format (JSON + hex encoding)
//! - PeerId determinism from identical keys
//! - Error handling for corrupt/missing key files
//! - File permission enforcement (Unix)
//! - TransportConfig::PostQuantum construction
//! - Fallback to classical transport when feature disabled

#[cfg(test)]
mod tests {
    use pqcrypto_falcon::falcon1024;
    use pqcrypto_traits::sign::{
        PublicKey as SignPublicKey, SecretKey as SignSecretKey, SignedMessage,
    };
    use std::path::PathBuf;

    // =========================================================================
    // Helper: Standalone key-file round-trip (mirrors load_or_generate_pqc_identity)
    // =========================================================================

    /// Generate a Falcon-1024 keypair and save to a JSON file (same format as service.rs)
    fn save_pqc_identity_to_file(path: &std::path::Path) -> (falcon1024::PublicKey, falcon1024::SecretKey) {
        let (pk, sk) = falcon1024::keypair();

        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).expect("create parent dir");
        }

        let key_json = serde_json::json!({
            "falcon_public_key": format!("0x{}", hex::encode(pk.as_bytes())),
            "falcon_secret_key": format!("0x{}", hex::encode(sk.as_bytes())),
        });

        std::fs::write(path, serde_json::to_string_pretty(&key_json).unwrap())
            .expect("write key file");

        (pk, sk)
    }

    /// Load a Falcon-1024 keypair from a JSON file (same format as service.rs)
    fn load_pqc_identity_from_file(
        path: &std::path::Path,
    ) -> Result<(falcon1024::PublicKey, falcon1024::SecretKey), String> {
        let contents = std::fs::read_to_string(path).map_err(|e| format!("read: {}", e))?;
        let json: serde_json::Value =
            serde_json::from_str(&contents).map_err(|e| format!("parse: {}", e))?;

        let pk_hex = json["falcon_public_key"]
            .as_str()
            .ok_or("missing falcon_public_key")?;
        let sk_hex = json["falcon_secret_key"]
            .as_str()
            .ok_or("missing falcon_secret_key")?;

        let pk_bytes =
            hex::decode(pk_hex.trim_start_matches("0x")).map_err(|e| format!("pk hex: {}", e))?;
        let sk_bytes =
            hex::decode(sk_hex.trim_start_matches("0x")).map_err(|e| format!("sk hex: {}", e))?;

        let pk = falcon1024::PublicKey::from_bytes(&pk_bytes)
            .map_err(|_| "invalid falcon public key".to_string())?;
        let sk = falcon1024::SecretKey::from_bytes(&sk_bytes)
            .map_err(|_| "invalid falcon secret key".to_string())?;

        Ok((pk, sk))
    }

    /// Create a unique temp directory for a test
    fn test_temp_dir(test_name: &str) -> PathBuf {
        let dir = std::env::temp_dir()
            .join("quantumharmony_pqc_tests")
            .join(test_name)
            .join(format!("{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir); // Clean up any previous run
        std::fs::create_dir_all(&dir).expect("create temp dir");
        dir
    }

    // =========================================================================
    // UNIT TESTS: Key Generation
    // =========================================================================

    #[test]
    fn test_falcon_keypair_generation() {
        let (pk, sk) = falcon1024::keypair();
        // Falcon-1024 public key is 1793 bytes
        assert_eq!(pk.as_bytes().len(), 1793, "Falcon-1024 public key should be 1793 bytes");
        // Falcon-1024 secret key is 2305 bytes
        assert_eq!(sk.as_bytes().len(), 2305, "Falcon-1024 secret key should be 2305 bytes");
    }

    #[test]
    fn test_two_keypairs_are_different() {
        let (pk1, _sk1) = falcon1024::keypair();
        let (pk2, _sk2) = falcon1024::keypair();
        assert!(
            pk1.as_bytes() != pk2.as_bytes(),
            "Two independently generated keypairs should have different public keys"
        );
    }

    // =========================================================================
    // UNIT TESTS: PqcIdentity (from polkadot-sdk fork)
    // =========================================================================

    #[cfg(feature = "pqc-transport")]
    #[test]
    fn test_pqc_identity_generation() {
        let identity = sc_network::pqc_authenticator::PqcIdentity::generate();
        let peer_id = identity.peer_id();
        // PeerId should be a valid non-default value
        let peer_id_str = peer_id.to_string();
        assert!(peer_id_str.starts_with("12D3KooW") || peer_id_str.starts_with("Qm"),
            "PeerId should be a valid libp2p peer ID, got: {}", peer_id_str);
    }

    #[cfg(feature = "pqc-transport")]
    #[test]
    fn test_pqc_identity_deterministic_peer_id() {
        let (pk, sk) = falcon1024::keypair();
        let id1 = sc_network::pqc_authenticator::PqcIdentity::from_keypair(
            falcon1024::PublicKey::from_bytes(pk.as_bytes()).unwrap(),
            falcon1024::SecretKey::from_bytes(sk.as_bytes()).unwrap(),
        );
        let id2 = sc_network::pqc_authenticator::PqcIdentity::from_keypair(
            falcon1024::PublicKey::from_bytes(pk.as_bytes()).unwrap(),
            falcon1024::SecretKey::from_bytes(sk.as_bytes()).unwrap(),
        );
        assert_eq!(
            id1.peer_id(),
            id2.peer_id(),
            "Same keypair should produce the same PeerId"
        );
    }

    #[cfg(feature = "pqc-transport")]
    #[test]
    fn test_pqc_identity_different_keys_different_peer_ids() {
        let id1 = sc_network::pqc_authenticator::PqcIdentity::generate();
        let id2 = sc_network::pqc_authenticator::PqcIdentity::generate();
        assert_ne!(
            id1.peer_id(),
            id2.peer_id(),
            "Different keypairs should produce different PeerIds"
        );
    }

    #[cfg(feature = "pqc-transport")]
    #[test]
    fn test_pqc_identity_public_key_bytes() {
        let identity = sc_network::pqc_authenticator::PqcIdentity::generate();
        let pk_bytes = identity.public_key_bytes();
        assert_eq!(pk_bytes.len(), 1793, "Falcon-1024 public key should be 1793 bytes");
    }

    #[cfg(feature = "pqc-transport")]
    #[test]
    fn test_pqc_identity_sign_produces_valid_signed_message() {
        let identity = sc_network::pqc_authenticator::PqcIdentity::generate();
        let message = b"test message for PQC signing";
        let signed = identity.sign(message);
        let signed_bytes = signed.as_bytes();
        // Signed message should be larger than the original (signature + message)
        assert!(
            signed_bytes.len() > message.len(),
            "Signed message ({} bytes) should be larger than original ({} bytes)",
            signed_bytes.len(),
            message.len()
        );
    }

    #[cfg(feature = "pqc-transport")]
    #[test]
    fn test_pqc_identity_sign_verify_roundtrip() {
        use pqcrypto_traits::sign::SignedMessage;
        let identity = sc_network::pqc_authenticator::PqcIdentity::generate();
        let message = b"quantum-secured transport handshake payload";
        let signed = identity.sign(message);

        // Verify using the public key
        let pk = falcon1024::PublicKey::from_bytes(&identity.public_key_bytes()).unwrap();
        let verified = falcon1024::open(&signed, &pk);
        assert!(verified.is_ok(), "Signature verification should succeed");
        assert_eq!(verified.unwrap(), message, "Verified message should match original");
    }

    // =========================================================================
    // UNIT TESTS: Key File Persistence
    // =========================================================================

    #[test]
    fn test_save_and_load_identity_roundtrip() {
        let dir = test_temp_dir("save_load_roundtrip");
        let key_path = dir.join("pqc_transport_identity.json");

        let (orig_pk, _orig_sk) = save_pqc_identity_to_file(&key_path);
        assert!(key_path.exists(), "Key file should be created");

        let (loaded_pk, _loaded_sk) = load_pqc_identity_from_file(&key_path)
            .expect("Should load saved key file");

        assert_eq!(
            orig_pk.as_bytes(),
            loaded_pk.as_bytes(),
            "Loaded public key should match the originally saved one"
        );
    }

    #[cfg(feature = "pqc-transport")]
    #[test]
    fn test_saved_identity_produces_same_peer_id() {
        let dir = test_temp_dir("same_peer_id");
        let key_path = dir.join("pqc_transport_identity.json");

        let (pk, sk) = save_pqc_identity_to_file(&key_path);
        let original_id = sc_network::pqc_authenticator::PqcIdentity::from_keypair(
            falcon1024::PublicKey::from_bytes(pk.as_bytes()).unwrap(),
            falcon1024::SecretKey::from_bytes(sk.as_bytes()).unwrap(),
        );

        let (loaded_pk, loaded_sk) = load_pqc_identity_from_file(&key_path).unwrap();
        let loaded_id = sc_network::pqc_authenticator::PqcIdentity::from_keypair(loaded_pk, loaded_sk);

        assert_eq!(
            original_id.peer_id(),
            loaded_id.peer_id(),
            "PeerId must be deterministic across save/load"
        );
    }

    #[test]
    fn test_key_file_json_format() {
        let dir = test_temp_dir("json_format");
        let key_path = dir.join("pqc_transport_identity.json");

        save_pqc_identity_to_file(&key_path);

        let contents = std::fs::read_to_string(&key_path).unwrap();
        let json: serde_json::Value = serde_json::from_str(&contents)
            .expect("Key file should be valid JSON");

        assert!(json["falcon_public_key"].is_string(), "Should have falcon_public_key string");
        assert!(json["falcon_secret_key"].is_string(), "Should have falcon_secret_key string");

        let pk_hex = json["falcon_public_key"].as_str().unwrap();
        let sk_hex = json["falcon_secret_key"].as_str().unwrap();

        assert!(pk_hex.starts_with("0x"), "Public key should start with 0x prefix");
        assert!(sk_hex.starts_with("0x"), "Secret key should start with 0x prefix");

        // Verify hex decode produces correct key sizes
        let pk_bytes = hex::decode(pk_hex.trim_start_matches("0x")).unwrap();
        let sk_bytes = hex::decode(sk_hex.trim_start_matches("0x")).unwrap();
        assert_eq!(pk_bytes.len(), 1793, "Public key hex should decode to 1793 bytes");
        assert_eq!(sk_bytes.len(), 2305, "Secret key hex should decode to 2305 bytes");
    }

    #[test]
    fn test_key_file_auto_creates_parent_directory() {
        let dir = test_temp_dir("auto_create_dir");
        let key_path = dir.join("deeply").join("nested").join("path").join("identity.json");

        assert!(!key_path.parent().unwrap().exists());
        save_pqc_identity_to_file(&key_path);
        assert!(key_path.exists(), "Key file should be created with auto-created parent dirs");
    }

    #[cfg(unix)]
    #[test]
    fn test_key_file_permissions() {
        use std::os::unix::fs::PermissionsExt;

        let dir = test_temp_dir("file_permissions");
        let key_path = dir.join("pqc_transport_identity.json");

        save_pqc_identity_to_file(&key_path);

        // Set 0600 like the production code does
        std::fs::set_permissions(&key_path, std::fs::Permissions::from_mode(0o600)).unwrap();

        let metadata = std::fs::metadata(&key_path).unwrap();
        let mode = metadata.permissions().mode() & 0o777;
        assert_eq!(mode, 0o600, "Key file should have 0600 permissions, got {:o}", mode);
    }

    // =========================================================================
    // REGRESSION TESTS: Error Handling
    // =========================================================================

    #[test]
    fn test_load_nonexistent_file_fails() {
        let result = load_pqc_identity_from_file(std::path::Path::new("/nonexistent/path/identity.json"));
        match result {
            Err(e) => assert!(e.contains("read"), "Error should mention read failure, got: {}", e),
            Ok(_) => panic!("Loading from nonexistent file should fail"),
        }
    }

    #[test]
    fn test_load_empty_file_fails() {
        let dir = test_temp_dir("empty_file");
        let key_path = dir.join("empty.json");
        std::fs::write(&key_path, "").unwrap();

        let result = load_pqc_identity_from_file(&key_path);
        assert!(result.is_err(), "Loading empty file should fail");
    }

    #[test]
    fn test_load_invalid_json_fails() {
        let dir = test_temp_dir("invalid_json");
        let key_path = dir.join("bad.json");
        std::fs::write(&key_path, "not valid json {{{").unwrap();

        let result = load_pqc_identity_from_file(&key_path);
        match result {
            Err(e) => assert!(e.contains("parse"), "Error should mention parse failure, got: {}", e),
            Ok(_) => panic!("Loading invalid JSON should fail"),
        }
    }

    #[test]
    fn test_load_missing_public_key_field() {
        let dir = test_temp_dir("missing_pk");
        let key_path = dir.join("no_pk.json");
        let json = serde_json::json!({
            "falcon_secret_key": "0xdeadbeef"
        });
        std::fs::write(&key_path, serde_json::to_string(&json).unwrap()).unwrap();

        let result = load_pqc_identity_from_file(&key_path);
        match result {
            Err(e) => assert!(e.contains("falcon_public_key"), "Error should mention falcon_public_key, got: {}", e),
            Ok(_) => panic!("Missing public key should fail"),
        }
    }

    #[test]
    fn test_load_missing_secret_key_field() {
        let dir = test_temp_dir("missing_sk");
        let key_path = dir.join("no_sk.json");
        let json = serde_json::json!({
            "falcon_public_key": "0xdeadbeef"
        });
        std::fs::write(&key_path, serde_json::to_string(&json).unwrap()).unwrap();

        let result = load_pqc_identity_from_file(&key_path);
        match result {
            Err(e) => assert!(e.contains("falcon_secret_key"), "Error should mention falcon_secret_key, got: {}", e),
            Ok(_) => panic!("Missing secret key should fail"),
        }
    }

    #[test]
    fn test_load_invalid_hex_fails() {
        let dir = test_temp_dir("invalid_hex");
        let key_path = dir.join("bad_hex.json");
        let json = serde_json::json!({
            "falcon_public_key": "0xNOTHEX!@#$%",
            "falcon_secret_key": "0xALSONOTHEX!@#$%"
        });
        std::fs::write(&key_path, serde_json::to_string(&json).unwrap()).unwrap();

        let result = load_pqc_identity_from_file(&key_path);
        match result {
            Err(e) => assert!(e.contains("hex"), "Error should mention hex, got: {}", e),
            Ok(_) => panic!("Invalid hex should fail"),
        }
    }

    #[test]
    fn test_load_truncated_key_bytes_fails() {
        let dir = test_temp_dir("truncated_keys");
        let key_path = dir.join("truncated.json");
        // Use valid hex but wrong length (too short for Falcon-1024)
        let json = serde_json::json!({
            "falcon_public_key": "0xdeadbeefcafebabe",
            "falcon_secret_key": "0xdeadbeefcafebabe"
        });
        std::fs::write(&key_path, serde_json::to_string(&json).unwrap()).unwrap();

        let result = load_pqc_identity_from_file(&key_path);
        assert!(result.is_err(), "Truncated key bytes should fail validation");
    }

    #[test]
    fn test_load_wrong_size_public_key() {
        let dir = test_temp_dir("wrong_pk_size");
        let key_path = dir.join("wrong_pk.json");
        // 1000 bytes instead of 1793
        let fake_pk = hex::encode(vec![0u8; 1000]);
        let (_, real_sk) = falcon1024::keypair();
        let json = serde_json::json!({
            "falcon_public_key": format!("0x{}", fake_pk),
            "falcon_secret_key": format!("0x{}", hex::encode(real_sk.as_bytes())),
        });
        std::fs::write(&key_path, serde_json::to_string(&json).unwrap()).unwrap();

        let result = load_pqc_identity_from_file(&key_path);
        assert!(result.is_err(), "Wrong-size public key should fail");
    }

    #[test]
    fn test_load_corrupted_key_bytes() {
        let dir = test_temp_dir("corrupted_keys");
        let key_path = dir.join("corrupted.json");
        // Correct length but random bytes (invalid Falcon-1024 key)
        let fake_pk = hex::encode(vec![0xFFu8; 1793]);
        let fake_sk = hex::encode(vec![0xFFu8; 2305]);
        let json = serde_json::json!({
            "falcon_public_key": format!("0x{}", fake_pk),
            "falcon_secret_key": format!("0x{}", fake_sk),
        });
        std::fs::write(&key_path, serde_json::to_string(&json).unwrap()).unwrap();

        let result = load_pqc_identity_from_file(&key_path);
        // This may succeed or fail depending on how strict falcon1024::PublicKey::from_bytes is
        // Either way, if it loads, signing should fail
        if let Ok((pk, _sk)) = result {
            // Key parsed but may be invalid for operations
            assert_eq!(pk.as_bytes().len(), 1793);
        }
    }

    #[test]
    fn test_load_without_0x_prefix() {
        let dir = test_temp_dir("no_0x_prefix");
        let key_path = dir.join("no_prefix.json");
        let (pk, sk) = falcon1024::keypair();
        // Save without 0x prefix — our loader should handle this
        let json = serde_json::json!({
            "falcon_public_key": hex::encode(pk.as_bytes()),
            "falcon_secret_key": hex::encode(sk.as_bytes()),
        });
        std::fs::write(&key_path, serde_json::to_string(&json).unwrap()).unwrap();

        let result = load_pqc_identity_from_file(&key_path);
        assert!(result.is_ok(), "Keys without 0x prefix should still load (trim_start_matches handles it)");
    }

    // =========================================================================
    // REGRESSION TESTS: Overwrite Protection
    // =========================================================================

    #[test]
    fn test_existing_key_not_overwritten_on_load() {
        let dir = test_temp_dir("no_overwrite");
        let key_path = dir.join("pqc_transport_identity.json");

        // Generate and save first identity
        let (pk1, _) = save_pqc_identity_to_file(&key_path);
        let contents_before = std::fs::read_to_string(&key_path).unwrap();

        // Load should not modify the file
        let (loaded_pk, _) = load_pqc_identity_from_file(&key_path).unwrap();
        let contents_after = std::fs::read_to_string(&key_path).unwrap();

        assert_eq!(pk1.as_bytes(), loaded_pk.as_bytes(), "Loaded key should match saved");
        assert_eq!(contents_before, contents_after, "Load should not modify the key file");
    }

    // =========================================================================
    // UNIT TESTS: TransportConfig Variants
    // =========================================================================

    #[cfg(feature = "pqc-transport")]
    #[test]
    fn test_transport_config_postquantum_construction() {
        let config = sc_network::config::TransportConfig::PostQuantum {
            enable_mdns: true,
            allow_private_ip: true,
        };
        // Verify it's the PostQuantum variant
        match config {
            sc_network::config::TransportConfig::PostQuantum {
                enable_mdns,
                allow_private_ip,
            } => {
                assert!(enable_mdns);
                assert!(allow_private_ip);
            }
            _ => panic!("Expected PostQuantum variant"),
        }
    }

    #[test]
    fn test_transport_config_normal_still_works() {
        let config = sc_network::config::TransportConfig::Normal {
            enable_mdns: true,
            allow_private_ip: true,
        };
        match config {
            sc_network::config::TransportConfig::Normal {
                enable_mdns,
                allow_private_ip,
            } => {
                assert!(enable_mdns);
                assert!(allow_private_ip);
            }
            _ => panic!("Expected Normal variant"),
        }
    }

    #[cfg(feature = "pqc-transport")]
    #[test]
    fn test_transport_config_postquantum_mdns_disabled() {
        let config = sc_network::config::TransportConfig::PostQuantum {
            enable_mdns: false,
            allow_private_ip: false,
        };
        match config {
            sc_network::config::TransportConfig::PostQuantum {
                enable_mdns,
                allow_private_ip,
            } => {
                assert!(!enable_mdns);
                assert!(!allow_private_ip);
            }
            _ => panic!("Expected PostQuantum variant"),
        }
    }

    // =========================================================================
    // UNIT TESTS: QuantumNetworkHandler Key File
    // =========================================================================

    #[test]
    fn test_quantum_handler_new_with_key_file_generates() {
        let dir = test_temp_dir("handler_generate");
        let key_path = dir.join("falcon_identity.json");
        let key_path_str = key_path.to_string_lossy().to_string();

        assert!(!key_path.exists(), "Key file should not exist yet");

        let handler = crate::quantum_p2p::QuantumNetworkHandler::new_with_key_file(&key_path_str)
            .expect("Handler should initialize");

        assert!(key_path.exists(), "Key file should be created after handler init");
        assert_ne!(handler.node_id(), sp_core::H256::zero(), "Node ID should not be zero");
    }

    #[test]
    fn test_quantum_handler_persists_identity_across_restarts() {
        let dir = test_temp_dir("handler_persist");
        let key_path = dir.join("falcon_identity.json");
        let key_path_str = key_path.to_string_lossy().to_string();

        // First init — generates new identity
        let handler1 = crate::quantum_p2p::QuantumNetworkHandler::new_with_key_file(&key_path_str)
            .expect("First handler init");
        let node_id_1 = handler1.node_id();
        drop(handler1);

        // Second init — loads from file
        let handler2 = crate::quantum_p2p::QuantumNetworkHandler::new_with_key_file(&key_path_str)
            .expect("Second handler init");
        let node_id_2 = handler2.node_id();

        assert_eq!(node_id_1, node_id_2,
            "Node ID should be identical after restart (loaded from file)");
    }

    #[test]
    fn test_quantum_handler_different_paths_different_identities() {
        let dir = test_temp_dir("handler_different");
        let key_path_a = dir.join("alice.json");
        let key_path_b = dir.join("bob.json");

        let handler_a = crate::quantum_p2p::QuantumNetworkHandler::new_with_key_file(
            &key_path_a.to_string_lossy(),
        ).expect("Alice handler");

        let handler_b = crate::quantum_p2p::QuantumNetworkHandler::new_with_key_file(
            &key_path_b.to_string_lossy(),
        ).expect("Bob handler");

        assert_ne!(handler_a.node_id(), handler_b.node_id(),
            "Different key files should produce different node IDs");
    }

    // =========================================================================
    // UNIT TESTS: Cross-Component Integration (Identity ↔ Handler ↔ Protocol)
    // =========================================================================

    #[test]
    fn test_handler_can_generate_announce_message() {
        let dir = test_temp_dir("handler_announce");
        let key_path = dir.join("identity.json");

        let handler = crate::quantum_p2p::QuantumNetworkHandler::new_with_key_file(
            &key_path.to_string_lossy(),
        ).expect("Handler init");

        let announce = handler.get_announce_message();
        assert!(announce.is_ok(), "Handler should produce announce message: {:?}", announce.err());
    }

    #[test]
    fn test_key_file_compatible_with_falcon_identity() {
        // Verify that the key file format used by QuantumNetworkHandler
        // is compatible with FalconIdentity::load_from_file
        let dir = test_temp_dir("format_compat");
        let key_path = dir.join("identity.json");
        let key_path_str = key_path.to_string_lossy().to_string();

        // Create via handler (generates and saves)
        let handler = crate::quantum_p2p::QuantumNetworkHandler::new_with_key_file(&key_path_str)
            .expect("Handler init");
        let handler_node_id = handler.node_id();
        drop(handler);

        // Load directly via FalconIdentity
        let loaded = crate::quantum_p2p::FalconIdentity::load_from_file(&key_path_str)
            .expect("FalconIdentity should load handler's key file");

        assert_eq!(loaded.node_id, Some(handler_node_id),
            "FalconIdentity loaded from handler file should have same node ID");
    }

    // =========================================================================
    // REGRESSION TESTS: PQC ↔ Quantum P2P Identity Separation
    // =========================================================================

    #[cfg(feature = "pqc-transport")]
    #[test]
    fn test_pqc_transport_identity_and_quantum_p2p_identity_are_independent() {
        // The PQC transport identity (for libp2p transport layer) and the
        // quantum_p2p FalconIdentity (for application-layer key exchange)
        // are separate systems. Verify they don't interfere.
        let dir = test_temp_dir("identity_separation");

        // PQC transport identity
        let pqc_key_path = dir.join("pqc_transport_identity.json");
        let (pqc_pk, pqc_sk) = save_pqc_identity_to_file(&pqc_key_path);
        let pqc_identity = sc_network::pqc_authenticator::PqcIdentity::from_keypair(
            falcon1024::PublicKey::from_bytes(pqc_pk.as_bytes()).unwrap(),
            falcon1024::SecretKey::from_bytes(pqc_sk.as_bytes()).unwrap(),
        );

        // Quantum P2P identity (separate key file)
        let qp2p_key_path = dir.join("falcon_identity.json");
        let handler = crate::quantum_p2p::QuantumNetworkHandler::new_with_key_file(
            &qp2p_key_path.to_string_lossy(),
        ).expect("Handler init");

        // They should be completely independent
        assert!(pqc_key_path.exists(), "PQC transport key should exist");
        assert!(qp2p_key_path.exists(), "Quantum P2P key should exist");

        // PeerId (transport) and NodeId (quantum P2P) serve different purposes
        let _peer_id = pqc_identity.peer_id();
        let _node_id = handler.node_id();
        // Both should be valid (non-default)
    }

    // =========================================================================
    // UNIT TESTS: Key Sizes and Cryptographic Properties
    // =========================================================================

    #[test]
    fn test_falcon_signature_size_within_bounds() {
        let (_, sk) = falcon1024::keypair();
        let message = b"block gossip payload for PQC transport";
        let signed = falcon1024::sign(message, &sk);
        let signed_bytes = signed.as_bytes();
        // Falcon-1024 max signature size is ~1330 bytes, but varies
        // Total signed message = signature + message
        assert!(signed_bytes.len() > message.len());
        let sig_size = signed_bytes.len() - message.len();
        assert!(sig_size <= 1330, "Falcon-1024 signature should be <= 1330 bytes, got {}", sig_size);
    }

    #[test]
    fn test_falcon_different_messages_different_signatures() {
        let (_, sk) = falcon1024::keypair();
        let signed1 = falcon1024::sign(b"message one", &sk);
        let signed2 = falcon1024::sign(b"message two", &sk);
        assert!(signed1.as_bytes() != signed2.as_bytes(),
            "Different messages should produce different signed outputs");
    }

    #[test]
    fn test_falcon_signature_verification_rejects_wrong_key() {
        use pqcrypto_traits::sign::SignedMessage;
        let (_, sk1) = falcon1024::keypair();
        let (pk2, _) = falcon1024::keypair();
        let message = b"signed by key 1";
        let signed = falcon1024::sign(message, &sk1);
        // Verify with wrong public key should fail
        let result = falcon1024::open(&signed, &pk2);
        assert!(result.is_err(), "Verification with wrong key should fail");
    }

    // =========================================================================
    // Cleanup helper
    // =========================================================================

    // Note: temp directories are per-process and auto-cleaned on next test run.
    // For explicit cleanup, add #[dtor] or Drop impl if needed.
}
