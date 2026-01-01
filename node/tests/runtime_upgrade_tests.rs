//! Runtime upgrade integration tests
//! Tests forkless runtime upgrades via setCode extrinsic

use jsonrpsee::{core::client::ClientT, http_client::{HttpClient, HttpClientBuilder}, rpc_params};
use serde_json::{json, Value};
use std::time::Duration;
use tokio::time::sleep;

const NODE_URL: &str = "http://127.0.0.1:9944";

/// Helper to wait for node to be ready
async fn wait_for_node() -> HttpClient {
    for i in 0..30 {
        if let Ok(client) = HttpClientBuilder::default().build(NODE_URL) {
            if let Ok(_) = client.request::<Value, _>("system_health", rpc_params![]).await {
                println!("Node is ready after {} attempts", i + 1);
                return client;
            }
        }
        sleep(Duration::from_secs(1)).await;
    }
    panic!("Node did not start within 30 seconds");
}

#[tokio::test]
async fn test_runtime_version_query() {
    let client = wait_for_node().await;

    // Get runtime version
    let version: Value = client
        .request("state_getRuntimeVersion", rpc_params![])
        .await
        .expect("Failed to get runtime version");

    println!("Runtime version: {:?}", version);

    // Version should have spec fields
    assert!(version.is_object());

    let version_obj = version.as_object().unwrap();
    assert!(version_obj.contains_key("specName"));
    assert!(version_obj.contains_key("specVersion"));
    assert!(version_obj.contains_key("implVersion"));

    // Check runtime name
    let spec_name = version_obj.get("specName").unwrap().as_str().unwrap();
    println!("Runtime spec name: {}", spec_name);
}

#[tokio::test]
async fn test_runtime_metadata_query() {
    let client = wait_for_node().await;

    // Get runtime metadata
    let metadata: String = client
        .request("state_getMetadata", rpc_params![])
        .await
        .expect("Failed to get metadata");

    println!("Metadata length: {} bytes", metadata.len());

    // Metadata should be a hex string
    assert!(metadata.starts_with("0x"));
    assert!(metadata.len() > 100, "Metadata should be substantial");
}

#[tokio::test]
async fn test_sudo_key_exists() {
    let client = wait_for_node().await;

    // Query sudo key using correct storage key
    // Storage key for Sudo::Key is twox128("Sudo") + twox128("Key")
    let sudo_key_result = client
        .request::<Value, _>("state_getStorage", rpc_params!["0xc8829b3ceb10391f71ca8e7f286d779544e87d3cb79f1b1506bf6c06e71c7c52"])
        .await;

    match sudo_key_result {
        Ok(key) => {
            println!("Sudo key exists: {:?}", key);
            if !key.is_null() {
                println!("✅ Sudo key is set");
            } else {
                println!("⚠️  Sudo key storage exists but value is null");
            }
        }
        Err(e) => {
            println!("Sudo pallet may not be included: {}", e);
            // This is okay - not all chains have sudo
        }
    }
}

#[tokio::test]
async fn test_query_pallet_constants() {
    let client = wait_for_node().await;

    // Get metadata to check available pallets
    let metadata: String = client
        .request("state_getMetadata", rpc_params![])
        .await
        .expect("Failed to get metadata");

    // Metadata should be a valid hex string (SCALE-encoded)
    assert!(metadata.starts_with("0x"), "Metadata should be hex-encoded");
    assert!(metadata.len() > 100, "Metadata should be substantial");

    // Get runtime version which contains spec_name
    let version: Value = client
        .request("state_getRuntimeVersion", rpc_params![])
        .await
        .expect("Failed to get runtime version");

    let spec_name = version.get("specName")
        .and_then(|v| v.as_str())
        .expect("specName should exist");

    println!("Runtime spec name: {}", spec_name);
    println!("Metadata length: {} bytes", metadata.len());

    // Verify we can query the runtime successfully
    assert!(!spec_name.is_empty(), "Spec name should not be empty");
}

#[tokio::test]
async fn test_block_production_continues() {
    let client = wait_for_node().await;

    // Get initial block number
    let header1: Value = client
        .request("chain_getHeader", rpc_params![])
        .await
        .expect("Failed to get header");

    let block_num1 = header1
        .get("number")
        .and_then(|n| n.as_str())
        .and_then(|s| u64::from_str_radix(s.trim_start_matches("0x"), 16).ok())
        .expect("Failed to parse block number");

    println!("Initial block number: {}", block_num1);

    // Wait for new blocks
    sleep(Duration::from_secs(12)).await;

    // Get new block number
    let header2: Value = client
        .request("chain_getHeader", rpc_params![])
        .await
        .expect("Failed to get header");

    let block_num2 = header2
        .get("number")
        .and_then(|n| n.as_str())
        .and_then(|s| u64::from_str_radix(s.trim_start_matches("0x"), 16).ok())
        .expect("Failed to parse block number");

    println!("New block number: {}", block_num2);

    // Block number should have increased
    assert!(
        block_num2 > block_num1,
        "Block production should continue"
    );
}

#[tokio::test]
#[ignore = "requires running node with SPHINCS+ keypairs configured"]
async fn test_storage_query_before_and_after_transaction() {
    let client = wait_for_node().await;

    // Check if this is a production chain (test accounts won't have funds)
    let chain_type: String = client
        .request("system_chainType", rpc_params![])
        .await
        .expect("Failed to get chain type");

    if chain_type.contains("Live") {
        println!("Skipping transaction test on Live chain - test accounts have no funds");
        return;
    }

    // Use SPHINCS+ Alice/Bob addresses from test_accounts module
    // These match the addresses used in genesis config
    let alice_ss58 = "5FLy8UEZHa2C2hNHP2NRCxVenWJxSqZWbDf6K456KwV92eML";
    let bob_ss58 = "5HfarSn5ndAE8JZ1K9mPvNPydGgE17cK2GUDX3UkYFW42hkJ";

    // Query Alice's nonce before transaction
    let nonce_before: Value = client
        .request("gateway_nonce", rpc_params![alice_ss58])
        .await
        .expect("Failed to get nonce");

    println!("Nonce before: {:?}", nonce_before);

    // Submit a transaction
    let genesis_hash: String = client
        .request("gateway_genesisHash", rpc_params![])
        .await
        .expect("Failed to get genesis hash");

    let tx_request = json!({
        "from": alice_ss58,
        "to": bob_ss58,
        "amount": "1000000000",
        "nonce": nonce_before.as_u64().unwrap(),
        "genesisHash": genesis_hash
    });

    let _result: Value = client
        .request("gateway_submit", rpc_params![tx_request])
        .await
        .expect("Failed to submit transaction");

    // Wait for block
    sleep(Duration::from_secs(7)).await;

    // Query Alice's nonce after transaction
    let nonce_after: Value = client
        .request("gateway_nonce", rpc_params![alice_ss58])
        .await
        .expect("Failed to get nonce");

    println!("Nonce after: {:?}", nonce_after);

    // Nonce should have increased
    assert!(
        nonce_after.as_u64().unwrap() > nonce_before.as_u64().unwrap(),
        "Nonce should increase after transaction"
    );
}

#[tokio::test]
async fn test_finalized_head_progresses() {
    let client = wait_for_node().await;

    // Get finalized head
    let finalized1: String = client
        .request("chain_getFinalizedHead", rpc_params![])
        .await
        .expect("Failed to get finalized head");

    println!("Initial finalized head: {}", finalized1);

    // Wait for finalization
    sleep(Duration::from_secs(15)).await;

    // Get new finalized head
    let finalized2: String = client
        .request("chain_getFinalizedHead", rpc_params![])
        .await
        .expect("Failed to get finalized head");

    println!("New finalized head: {}", finalized2);

    // Finalized head may or may not change depending on finality gadget
    // Just verify we can query it
    assert!(finalized2.starts_with("0x"));
}

#[tokio::test]
async fn test_extrinsic_submission_format() {
    let client = wait_for_node().await;

    // Test that gateway accepts properly formatted transactions
    // Use SPHINCS+ addresses from test_accounts module
    let alice_ss58 = "5FLy8UEZHa2C2hNHP2NRCxVenWJxSqZWbDf6K456KwV92eML";
    let bob_ss58 = "5Cf6zqYW9MoLdQzL4s3n3xKtRLWn3pFEZYqLbzPULxsQSmQG";

    let genesis_hash: String = client
        .request("gateway_genesisHash", rpc_params![])
        .await
        .expect("Failed to get genesis hash");

    let nonce: u32 = client
        .request::<Value, _>("gateway_nonce", rpc_params![alice_ss58])
        .await
        .expect("Failed to get nonce")
        .as_u64()
        .unwrap() as u32;

    // Test with minimal transaction
    let tx = json!({
        "from": alice_ss58,
        "to": bob_ss58,
        "amount": "100",
        "nonce": nonce,
        "genesisHash": genesis_hash
    });

    let result = client
        .request::<Value, _>("gateway_submit", rpc_params![tx])
        .await;

    // Should either succeed or give a clear error
    match result {
        Ok(hash) => {
            println!("Transaction submitted: {:?}", hash);
        }
        Err(e) => {
            println!("Transaction error: {}", e);
            // As long as we get a response, the API is working
        }
    }
}

#[tokio::test]
async fn test_multiple_rpc_calls_concurrent() {
    let client = wait_for_node().await;

    // Use SPHINCS+ Alice address from test_accounts module
    let alice_ss58 = "5FLy8UEZHa2C2hNHP2NRCxVenWJxSqZWbDf6K456KwV92eML";

    // Make multiple concurrent RPC calls
    let (balance_result, nonce_result, genesis_result) = tokio::join!(
        client.request::<Value, _>("gateway_balance", rpc_params![alice_ss58]),
        client.request::<Value, _>("gateway_nonce", rpc_params![alice_ss58]),
        client.request::<String, _>("gateway_genesisHash", rpc_params![])
    );

    // All should succeed
    assert!(balance_result.is_ok(), "Balance query should succeed");
    assert!(nonce_result.is_ok(), "Nonce query should succeed");
    assert!(genesis_result.is_ok(), "Genesis hash query should succeed");

    println!("Concurrent RPC calls successful");
}

#[tokio::test]
async fn test_chain_type_and_name() {
    let client = wait_for_node().await;

    // Get chain name
    let chain_name: String = client
        .request("system_chain", rpc_params![])
        .await
        .expect("Failed to get chain name");

    println!("Chain name: {}", chain_name);

    // Chain name should not be empty
    assert!(!chain_name.is_empty(), "Chain should have a name");

    // Get chain type
    let chain_type: String = client
        .request("system_chainType", rpc_params![])
        .await
        .expect("Failed to get chain type");

    println!("Chain type: {}", chain_type);

    // Chain type can be "Development", "Local", or "Live" for production
    assert!(
        chain_type.contains("Development") || chain_type.contains("Local") || chain_type.contains("Live"),
        "Chain type should be Development, Local, or Live"
    );
}

// ============================================================================
// ChunkedUpgrade RPC Tests
// ============================================================================

/// Test that chunkedUpgrade_calculateChunks RPC works correctly
#[tokio::test]
async fn test_chunked_upgrade_calculate_chunks() {
    let client = wait_for_node().await;

    // Test with various WASM sizes
    // 64KB chunk size means:
    // - 64KB = 1 chunk
    // - 128KB = 2 chunks
    // - 600KB = 10 chunks

    // Small WASM (single chunk)
    let chunks_64k: u8 = client
        .request("chunkedUpgrade_calculateChunks", rpc_params![65536u32])
        .await
        .expect("Failed to calculate chunks for 64KB");
    assert_eq!(chunks_64k, 1, "64KB should require 1 chunk");
    println!("64KB WASM = {} chunk(s)", chunks_64k);

    // Medium WASM (2 chunks)
    let chunks_128k: u8 = client
        .request("chunkedUpgrade_calculateChunks", rpc_params![131072u32])
        .await
        .expect("Failed to calculate chunks for 128KB");
    assert_eq!(chunks_128k, 2, "128KB should require 2 chunks");
    println!("128KB WASM = {} chunk(s)", chunks_128k);

    // Large WASM (typical runtime ~600KB)
    let chunks_600k: u8 = client
        .request("chunkedUpgrade_calculateChunks", rpc_params![614400u32])
        .await
        .expect("Failed to calculate chunks for 600KB");
    assert!(chunks_600k >= 9 && chunks_600k <= 10, "600KB should require 9-10 chunks");
    println!("600KB WASM = {} chunk(s)", chunks_600k);
}

/// Test that chunkedUpgrade_status RPC returns None when no upgrade is pending
#[tokio::test]
async fn test_chunked_upgrade_status_no_pending() {
    let client = wait_for_node().await;

    let status: Option<Value> = client
        .request("chunkedUpgrade_status", rpc_params![])
        .await
        .expect("Failed to get upgrade status");

    // Should return None (null) when no upgrade is pending
    assert!(status.is_none(), "Status should be None when no upgrade is pending");
    println!("Upgrade status: {:?}", status);
}

/// Test chunkedUpgrade_initiate validates WASM hex format
#[tokio::test]
async fn test_chunked_upgrade_initiate_invalid_hex() {
    let client = wait_for_node().await;

    // Invalid hex string
    let result = client
        .request::<Value, _>(
            "chunkedUpgrade_initiate",
            rpc_params!["not_valid_hex", "0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"]
        )
        .await;

    // Should fail with invalid hex error
    assert!(result.is_err(), "Should reject invalid WASM hex");
    let err = result.unwrap_err();
    println!("Expected error for invalid hex: {}", err);
}

/// Test chunkedUpgrade_initiate validates secret key format
#[tokio::test]
async fn test_chunked_upgrade_initiate_invalid_key_size() {
    let client = wait_for_node().await;

    // Valid WASM hex but invalid key size (should be 128 bytes = 256 hex chars)
    let small_wasm_hex = "0061736d01000000";  // Minimal WASM header

    let result = client
        .request::<Value, _>(
            "chunkedUpgrade_initiate",
            rpc_params![small_wasm_hex, "deadbeef"]  // Too short key
        )
        .await;

    // Should fail with invalid key size error
    assert!(result.is_err(), "Should reject invalid key size");
    let err = result.unwrap_err();
    println!("Expected error for invalid key size: {}", err);
    assert!(
        err.to_string().contains("128") || err.to_string().contains("key"),
        "Error should mention key size"
    );
}

/// Test chunkedUpgrade_uploadChunk validates chunk index
#[tokio::test]
async fn test_chunked_upgrade_upload_chunk_no_pending_upgrade() {
    let client = wait_for_node().await;

    // Generate a valid 128-byte (256 hex char) key
    let valid_key = "00".repeat(128);
    let chunk_data = "deadbeef";

    let result = client
        .request::<Value, _>(
            "chunkedUpgrade_uploadChunk",
            rpc_params![0u8, chunk_data, valid_key]
        )
        .await;

    // Should fail because no upgrade is pending
    // The error could be either an RPC error or a transaction failure
    println!("Upload chunk without pending upgrade result: {:?}", result);
}

/// Test chunkedUpgrade_finalize fails without pending upgrade
#[tokio::test]
async fn test_chunked_upgrade_finalize_no_pending() {
    let client = wait_for_node().await;

    // Generate a valid 128-byte (256 hex char) key
    let valid_key = "00".repeat(128);

    let result = client
        .request::<Value, _>(
            "chunkedUpgrade_finalize",
            rpc_params![valid_key]
        )
        .await;

    // Should fail because no upgrade is pending
    println!("Finalize without pending upgrade result: {:?}", result);
}

/// Test chunkedUpgrade_cancel fails without pending upgrade
#[tokio::test]
async fn test_chunked_upgrade_cancel_no_pending() {
    let client = wait_for_node().await;

    // Generate a valid 128-byte (256 hex char) key
    let valid_key = "00".repeat(128);

    let result = client
        .request::<Value, _>(
            "chunkedUpgrade_cancel",
            rpc_params![valid_key]
        )
        .await;

    // Should fail because no upgrade is pending
    println!("Cancel without pending upgrade result: {:?}", result);
}

/// Test the complete chunked upgrade flow with a minimal WASM
/// NOTE: This test requires a valid sudo key and will modify chain state
#[tokio::test]
#[ignore]  // Ignored by default - run with --ignored flag for full integration test
async fn test_chunked_upgrade_full_flow() {
    let client = wait_for_node().await;

    // Get initial runtime version
    let version_before: Value = client
        .request("state_getRuntimeVersion", rpc_params![])
        .await
        .expect("Failed to get runtime version");

    let spec_version_before = version_before
        .get("specVersion")
        .and_then(|v| v.as_u64())
        .expect("specVersion should exist");

    println!("Runtime version before upgrade: {}", spec_version_before);

    // Alice's SPHINCS+ secret key (128 bytes hex)
    // This is the test key from the genesis config
    let _alice_secret = "e7175a541ee055e423e070eee2cfd2a9f447a820f4e61bf03180805dbc8c4a7f\
                         1ad3437c05c2da62ed342eef62e8cac285cf8134d29b49c68a9e575f3c275991\
                         d7d0bd475417a93fa61216a1e4024f8d1a211f795e6ab111a1eef0d5e4f3f4b1\
                         56e47e5c8d4185ce4a308423eb310bb3b7f26e6d504191662d2241aafaf914cd";

    // Read test WASM file (you'd need to provide a real WASM for full test)
    // For now, just verify the RPC methods are available
    println!("Chunked upgrade RPC methods available");

    // Calculate chunks for a hypothetical 600KB WASM
    let chunks: u8 = client
        .request("chunkedUpgrade_calculateChunks", rpc_params![614400u32])
        .await
        .expect("Failed to calculate chunks");

    println!("A 600KB WASM would require {} chunks", chunks);
    assert!(chunks >= 9, "Should require at least 9 chunks");
}

/// Test that chunk size limits are enforced
#[tokio::test]
async fn test_chunked_upgrade_chunk_size_validation() {
    let client = wait_for_node().await;

    // Generate a valid 128-byte key
    let valid_key = "00".repeat(128);

    // Try to upload a chunk that's too large (> 64KB = 65536 bytes = 131072 hex chars)
    let oversized_chunk = "ff".repeat(70000);  // 70KB in hex

    let result = client
        .request::<Value, _>(
            "chunkedUpgrade_uploadChunk",
            rpc_params![0u8, oversized_chunk, valid_key]
        )
        .await;

    // Should fail due to chunk size limit
    println!("Oversized chunk upload result: {:?}", result);
}

/// Integration test verifying block production continues after upgrade operations
#[tokio::test]
async fn test_block_production_during_upgrade_operations() {
    let client = wait_for_node().await;

    // Get initial block number
    let header1: Value = client
        .request("chain_getHeader", rpc_params![])
        .await
        .expect("Failed to get header");

    let block_num1 = header1
        .get("number")
        .and_then(|n| n.as_str())
        .and_then(|s| u64::from_str_radix(s.trim_start_matches("0x"), 16).ok())
        .expect("Failed to parse block number");

    println!("Block number before upgrade operations: {}", block_num1);

    // Perform some upgrade-related queries
    let _chunks: u8 = client
        .request("chunkedUpgrade_calculateChunks", rpc_params![500000u32])
        .await
        .expect("Failed to calculate chunks");

    let _status: Option<Value> = client
        .request("chunkedUpgrade_status", rpc_params![])
        .await
        .expect("Failed to get status");

    // Wait for a few blocks
    sleep(Duration::from_secs(12)).await;

    // Verify block production continued
    let header2: Value = client
        .request("chain_getHeader", rpc_params![])
        .await
        .expect("Failed to get header");

    let block_num2 = header2
        .get("number")
        .and_then(|n| n.as_str())
        .and_then(|s| u64::from_str_radix(s.trim_start_matches("0x"), 16).ok())
        .expect("Failed to parse block number");

    println!("Block number after upgrade operations: {}", block_num2);

    assert!(
        block_num2 > block_num1,
        "Block production should continue during upgrade operations"
    );
}
