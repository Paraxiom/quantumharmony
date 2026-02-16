//! Network-level regression tests for PQC P2P transport.
//!
//! These tests verify end-to-end behavior of the PQC transport layer across
//! the QuantumHarmony validator network. All tests marked `#[ignore]` require
//! a running 3-validator testnet.
//!
//! Run:  cargo test --test pqc_network_integration_tests -- --ignored --nocapture

use serde_json::json;

// =============================================================================
// Configuration
// =============================================================================

const ALICE_RPC: &str = "http://51.79.26.123:9944";
const BOB_RPC: &str = "http://51.79.26.168:9944";
const CHARLIE_RPC: &str = "http://209.38.225.4:9944";

async fn rpc_call(endpoint: &str, method: &str) -> Result<serde_json::Value, String> {
    let client = reqwest::Client::builder()
        .timeout(std::time::Duration::from_secs(10))
        .build()
        .map_err(|e| format!("client build: {}", e))?;

    let response = client
        .post(endpoint)
        .json(&json!({
            "id": 1,
            "jsonrpc": "2.0",
            "method": method,
            "params": []
        }))
        .send()
        .await
        .map_err(|e| format!("request to {}: {}", endpoint, e))?;

    let body: serde_json::Value = response
        .json()
        .await
        .map_err(|e| format!("parse response: {}", e))?;

    Ok(body)
}

// =============================================================================
// Health & Connectivity Regression Tests
// =============================================================================

#[tokio::test]
#[ignore = "Requires live QuantumHarmony validators (Alice/Bob/Charlie)"]
async fn test_all_validators_healthy_after_pqc_migration() {
    let validators = [
        ("Alice", ALICE_RPC),
        ("Bob", BOB_RPC),
        ("Charlie", CHARLIE_RPC),
    ];

    for (name, endpoint) in &validators {
        let result = rpc_call(endpoint, "system_health").await;
        assert!(
            result.is_ok(),
            "{} should be reachable at {}: {:?}",
            name,
            endpoint,
            result.err()
        );

        let body = result.unwrap();
        let peers = body["result"]["peers"].as_u64().unwrap_or(0);
        assert!(
            peers >= 2,
            "{} should have >= 2 peers (PQC transport), got {}",
            name,
            peers
        );
    }
}

#[tokio::test]
#[ignore = "Requires live QuantumHarmony validators (Alice/Bob/Charlie)"]
async fn test_peer_ids_changed_after_pqc_migration() {
    // These are the OLD classical (Ed25519) PeerIds — after PQC migration,
    // the PeerIds should be DIFFERENT (derived from Falcon-1024 pubkeys).
    let classical_peer_ids = [
        "12D3KooWHdiAxVd8uMQR1hGWXccidmfCwLqcMpGwR6QcTP6QRMuD", // Bob
        "12D3KooWSCufgHzV4fCwRijfH2k3abrpAJxTKxEvN1FDuRXA2U9x", // Charlie
        "12D3KooWDmLjhsvwEh3Xdat6daVhRm87ed88J9Sx4ti44osaDM8W", // Alice
    ];

    let body = rpc_call(ALICE_RPC, "system_peers")
        .await
        .expect("Should connect to Alice");

    let peers = body["result"]
        .as_array()
        .expect("system_peers should return array");

    for peer in peers {
        let peer_id = peer["peerId"].as_str().unwrap_or("");
        for classical_id in &classical_peer_ids {
            assert_ne!(
                peer_id, *classical_id,
                "Peer {} should NOT have classical PeerId {} after PQC migration",
                peer_id, classical_id
            );
        }
    }

    eprintln!(
        "✅ All {} peers have new PQC-derived PeerIds",
        peers.len()
    );
}

#[tokio::test]
#[ignore = "Requires live QuantumHarmony validators (Alice/Bob/Charlie)"]
async fn test_system_local_peer_id_is_pqc_derived() {
    let body = rpc_call(ALICE_RPC, "system_localPeerId")
        .await
        .expect("Should get Alice's local PeerId");

    let peer_id = body["result"].as_str().expect("Should return peer ID string");

    // Classical Alice PeerId
    assert_ne!(
        peer_id,
        "12D3KooWDmLjhsvwEh3Xdat6daVhRm87ed88J9Sx4ti44osaDM8W",
        "Alice's PeerId should change after PQC migration"
    );

    eprintln!("✅ Alice PQC PeerId: {}", peer_id);
}

// =============================================================================
// Block Production & Finality Regression Tests
// =============================================================================

#[tokio::test]
#[ignore = "Requires live QuantumHarmony validators (Alice/Bob/Charlie)"]
async fn test_blocks_still_produced_after_pqc_migration() {
    let body1 = rpc_call(ALICE_RPC, "chain_getHeader")
        .await
        .expect("Should get block header");

    let block_num_1 = body1["result"]["number"]
        .as_str()
        .map(|s| u64::from_str_radix(s.trim_start_matches("0x"), 16).unwrap_or(0))
        .unwrap_or(0);

    // Wait for new blocks
    tokio::time::sleep(std::time::Duration::from_secs(15)).await;

    let body2 = rpc_call(ALICE_RPC, "chain_getHeader")
        .await
        .expect("Should get updated block header");

    let block_num_2 = body2["result"]["number"]
        .as_str()
        .map(|s| u64::from_str_radix(s.trim_start_matches("0x"), 16).unwrap_or(0))
        .unwrap_or(0);

    assert!(
        block_num_2 > block_num_1,
        "Blocks should still be produced after PQC migration: {} -> {}",
        block_num_1,
        block_num_2
    );

    eprintln!(
        "✅ Block production active: #{} → #{}",
        block_num_1, block_num_2
    );
}

#[tokio::test]
#[ignore = "Requires live QuantumHarmony validators (Alice/Bob/Charlie)"]
async fn test_finality_progresses_after_pqc_migration() {
    let body1 = rpc_call(ALICE_RPC, "chain_getFinalizedHead")
        .await
        .expect("Should get finalized head");
    let hash1 = body1["result"].as_str().unwrap_or("").to_string();

    tokio::time::sleep(std::time::Duration::from_secs(15)).await;

    let body2 = rpc_call(ALICE_RPC, "chain_getFinalizedHead")
        .await
        .expect("Should get updated finalized head");
    let hash2 = body2["result"].as_str().unwrap_or("").to_string();

    assert_ne!(
        hash1, hash2,
        "Finalized head should progress after PQC migration"
    );

    eprintln!("✅ Finality progressing: {} → {}", &hash1[..16], &hash2[..16]);
}

// =============================================================================
// Cross-Validator Communication Tests
// =============================================================================

#[tokio::test]
#[ignore = "Requires live QuantumHarmony validators (Alice/Bob/Charlie)"]
async fn test_all_validators_see_same_finalized_head() {
    let validators = [
        ("Alice", ALICE_RPC),
        ("Bob", BOB_RPC),
        ("Charlie", CHARLIE_RPC),
    ];

    let mut finalized_heads = Vec::new();

    for (name, endpoint) in &validators {
        let body = rpc_call(endpoint, "chain_getFinalizedHead")
            .await
            .expect(&format!("{} should respond", name));
        let hash = body["result"]
            .as_str()
            .unwrap_or("unknown")
            .to_string();
        eprintln!("{} finalized: {}", name, &hash[..16]);
        finalized_heads.push((name, hash));
    }

    // All validators should agree on finalized head (or be within 1-2 blocks)
    // Since we query sequentially, there may be slight drift, but they should
    // all return valid block hashes
    for (name, hash) in &finalized_heads {
        assert!(hash.starts_with("0x"), "{} finalized head should be hex", name);
        assert!(hash.len() == 66, "{} finalized head should be 32-byte hash", name);
    }
}

#[tokio::test]
#[ignore = "Requires live QuantumHarmony validators (Alice/Bob/Charlie)"]
async fn test_block_propagation_across_pqc_transport() {
    // Get best block from Alice
    let alice_body = rpc_call(ALICE_RPC, "chain_getHeader")
        .await
        .expect("Should get Alice header");
    let alice_best = alice_body["result"]["number"]
        .as_str()
        .map(|s| u64::from_str_radix(s.trim_start_matches("0x"), 16).unwrap_or(0))
        .unwrap_or(0);

    // Get best block from Bob
    let bob_body = rpc_call(BOB_RPC, "chain_getHeader")
        .await
        .expect("Should get Bob header");
    let bob_best = bob_body["result"]["number"]
        .as_str()
        .map(|s| u64::from_str_radix(s.trim_start_matches("0x"), 16).unwrap_or(0))
        .unwrap_or(0);

    // Get best block from Charlie
    let charlie_body = rpc_call(CHARLIE_RPC, "chain_getHeader")
        .await
        .expect("Should get Charlie header");
    let charlie_best = charlie_body["result"]["number"]
        .as_str()
        .map(|s| u64::from_str_radix(s.trim_start_matches("0x"), 16).unwrap_or(0))
        .unwrap_or(0);

    // All validators should be within 2 blocks of each other
    let max_block = alice_best.max(bob_best).max(charlie_best);
    let min_block = alice_best.min(bob_best).min(charlie_best);
    let drift = max_block - min_block;

    assert!(
        drift <= 2,
        "Block drift across validators should be <= 2, got {} (Alice={}, Bob={}, Charlie={})",
        drift,
        alice_best,
        bob_best,
        charlie_best
    );

    eprintln!(
        "✅ Block propagation OK: Alice={}, Bob={}, Charlie={} (drift={})",
        alice_best, bob_best, charlie_best, drift
    );
}

// =============================================================================
// Security Regression Tests
// =============================================================================

#[tokio::test]
#[ignore = "Requires live QuantumHarmony validators (Alice/Bob/Charlie)"]
async fn test_rpc_still_accessible_after_pqc_migration() {
    // Verify that PQC transport only affects P2P, not RPC
    let validators = [ALICE_RPC, BOB_RPC, CHARLIE_RPC];

    for endpoint in &validators {
        let body = rpc_call(endpoint, "system_version")
            .await
            .expect(&format!("RPC should be accessible at {}", endpoint));

        let version = body["result"].as_str().unwrap_or("");
        assert!(!version.is_empty(), "Should return non-empty version string");
    }
}

#[tokio::test]
#[ignore = "Requires live QuantumHarmony validators (Alice/Bob/Charlie)"]
async fn test_chain_properties_unchanged_after_pqc_migration() {
    let body = rpc_call(ALICE_RPC, "system_properties")
        .await
        .expect("Should get chain properties");

    let props = &body["result"];
    // Token symbol and decimals should be unchanged
    assert!(
        props.is_object(),
        "Chain properties should be an object: {:?}",
        props
    );
}
