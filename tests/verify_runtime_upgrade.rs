//! Runtime Upgrade Verification Tests
//!
//! This module provides TDD-style tests to verify and debug runtime upgrades.
//!
//! KEY INSIGHT: After calling set_code, the new runtime version is NOT immediately
//! visible. It only becomes active on the NEXT block. This is because:
//!
//! 1. set_code stores new WASM in :code storage
//! 2. On next block initialization, the new WASM is loaded
//! 3. Executive::runtime_upgraded() detects the version change
//! 4. on_runtime_upgrade hooks are executed
//! 5. LastRuntimeUpgrade storage is updated
//!
//! Test Strategy:
//! - test_01_*: Pre-upgrade state verification
//! - test_02_*: Upgrade execution
//! - test_03_*: Post-upgrade verification (run after a new block is produced)

use jsonrpsee::{core::client::ClientT, http_client::{HttpClient, HttpClientBuilder}, rpc_params};
use serde_json::Value;
use std::time::Duration;
use tokio::time::sleep;

const NODE_URL: &str = "http://127.0.0.1:9944";

/// Wait for node to be ready and return client
async fn wait_for_node() -> Option<HttpClient> {
    for i in 0..30 {
        if let Ok(client) = HttpClientBuilder::default()
            .request_timeout(Duration::from_secs(30))
            .build(NODE_URL)
        {
            if client.request::<Value, _>("system_health", rpc_params![]).await.is_ok() {
                println!("Node ready after {} attempts", i + 1);
                return Some(client);
            }
        }
        sleep(Duration::from_secs(1)).await;
    }
    None
}

/// Get current block number
async fn get_block_number(client: &HttpClient) -> u64 {
    let header: Value = client
        .request("chain_getHeader", rpc_params![])
        .await
        .expect("Failed to get header");

    header
        .get("number")
        .and_then(|n| n.as_str())
        .and_then(|s| u64::from_str_radix(s.trim_start_matches("0x"), 16).ok())
        .unwrap_or(0)
}

/// Get spec_version from runtime
async fn get_spec_version(client: &HttpClient) -> u64 {
    let version: Value = client
        .request("state_getRuntimeVersion", rpc_params![])
        .await
        .expect("Failed to get runtime version");

    version
        .get("specVersion")
        .and_then(|v| v.as_u64())
        .unwrap_or(0)
}

/// Get code storage hash
async fn get_code_hash(client: &HttpClient) -> String {
    client
        .request("state_getStorageHash", rpc_params!["0x3a636f6465"])
        .await
        .unwrap_or_else(|_| "unknown".to_string())
}

// =============================================================================
// Phase 1: Pre-Upgrade Verification
// =============================================================================

/// Test 01a: Record initial state before upgrade
#[tokio::test]
async fn test_01a_record_initial_state() {
    println!("\n========================================");
    println!("TEST 01a: Record Initial State");
    println!("========================================\n");

    let client = wait_for_node().await.expect("Node not available");

    let block_number = get_block_number(&client).await;
    let spec_version = get_spec_version(&client).await;
    let code_hash = get_code_hash(&client).await;

    println!("Initial State:");
    println!("  Block number: {}", block_number);
    println!("  spec_version: {}", spec_version);
    println!("  Code hash: {}", code_hash);

    // These values should be recorded and compared after upgrade
    println!("\n✓ Record these values to compare after upgrade");
}

/// Test 01b: Verify runtime source has correct version
#[tokio::test]
async fn test_01b_verify_source_version() {
    println!("\n========================================");
    println!("TEST 01b: Verify Source Version");
    println!("========================================\n");

    // Read the runtime lib.rs and check spec_version
    let runtime_source = std::fs::read_to_string("runtime/src/lib.rs")
        .expect("Failed to read runtime/src/lib.rs");

    // Look for spec_version declaration
    if let Some(pos) = runtime_source.find("spec_version:") {
        let line_start = runtime_source[..pos].rfind('\n').map(|p| p + 1).unwrap_or(0);
        let line_end = runtime_source[pos..].find('\n').map(|p| pos + p).unwrap_or(runtime_source.len());
        let line = &runtime_source[line_start..line_end];
        println!("Found in source: {}", line.trim());

        // Extract version number
        if let Some(num_start) = line.find("spec_version:") {
            let after_colon = &line[num_start + 13..];
            let version_str: String = after_colon
                .chars()
                .skip_while(|c| !c.is_ascii_digit())
                .take_while(|c| c.is_ascii_digit())
                .collect();

            if let Ok(version) = version_str.parse::<u64>() {
                println!("spec_version in source: {}", version);

                // Expected version after upgrade
                let expected = 9u64;
                if version == expected {
                    println!("✓ Source has correct spec_version ({})", expected);
                } else {
                    println!("⚠ Source has spec_version {} but expected {}", version, expected);
                }
            }
        }
    } else {
        println!("⚠ Could not find spec_version in runtime source");
    }
}

// =============================================================================
// Phase 2: During Upgrade
// =============================================================================

/// Test 02a: Monitor block production during upgrade
#[tokio::test]
async fn test_02a_monitor_blocks() {
    println!("\n========================================");
    println!("TEST 02a: Monitor Block Production");
    println!("========================================\n");

    let client = wait_for_node().await.expect("Node not available");

    let initial_block = get_block_number(&client).await;
    println!("Initial block: {}", initial_block);

    // Wait for several blocks
    println!("Waiting for blocks...");
    for i in 1..=5 {
        sleep(Duration::from_secs(6)).await;
        let current_block = get_block_number(&client).await;
        let spec_version = get_spec_version(&client).await;
        println!("  Block {}: block_num={}, spec_version={}", i, current_block, spec_version);
    }

    let final_block = get_block_number(&client).await;
    assert!(final_block > initial_block, "Blocks should be produced");
    println!("\n✓ Block production is working");
}

// =============================================================================
// Phase 3: Post-Upgrade Verification
// =============================================================================

/// Test 03a: Verify spec_version after upgrade
#[tokio::test]
async fn test_03a_verify_spec_version_after_upgrade() {
    println!("\n========================================");
    println!("TEST 03a: Verify spec_version After Upgrade");
    println!("========================================\n");

    let client = wait_for_node().await.expect("Node not available");

    let spec_version = get_spec_version(&client).await;
    let expected_version = 9u64;

    println!("Current spec_version: {}", spec_version);
    println!("Expected spec_version: {}", expected_version);

    if spec_version == expected_version {
        println!("\n✓ SUCCESS: spec_version is {} as expected", expected_version);
    } else if spec_version < expected_version {
        println!("\n⚠ ISSUE: spec_version is still {} (expected {})", spec_version, expected_version);
        println!();
        println!("This usually means:");
        println!("1. The set_code extrinsic was not submitted");
        println!("2. The extrinsic failed (check events)");
        println!("3. Not enough blocks have been produced since set_code");
        println!();
        println!("Actions to take:");
        println!("1. Check the transaction was successful");
        println!("2. Wait for at least one more block to be produced");
        println!("3. If using native execution, restart the node");
    } else {
        println!("\n? UNEXPECTED: spec_version {} > expected {}", spec_version, expected_version);
    }

    assert_eq!(spec_version, expected_version, "spec_version should match expected");
}

/// Test 03b: Verify code hash changed
#[tokio::test]
async fn test_03b_verify_code_hash_changed() {
    println!("\n========================================");
    println!("TEST 03b: Verify Code Hash Changed");
    println!("========================================\n");

    let client = wait_for_node().await.expect("Node not available");

    let code_hash = get_code_hash(&client).await;
    println!("Current code hash: {}", code_hash);

    // You would compare this with the hash recorded before upgrade
    // For now, just verify it's a valid hash
    assert!(code_hash.starts_with("0x"), "Code hash should be hex");
    assert!(code_hash.len() > 10, "Code hash should be substantial");

    println!("\n✓ Code hash retrieved successfully");
    println!("   Compare with pre-upgrade hash to verify change");
}

/// Test 03c: Verify LastRuntimeUpgrade storage
#[tokio::test]
async fn test_03c_verify_last_runtime_upgrade() {
    println!("\n========================================");
    println!("TEST 03c: Verify LastRuntimeUpgrade Storage");
    println!("========================================\n");

    let client = wait_for_node().await.expect("Node not available");

    // LastRuntimeUpgrade storage key
    let key = "0x26aa394eea5630e07c48ae0c9558cef7f9cce9c888469bb1a0dceaa129672ef8";

    let storage: Result<String, _> = client
        .request("state_getStorage", rpc_params![key])
        .await;

    match storage {
        Ok(value) => {
            println!("LastRuntimeUpgrade storage: {}", value);

            // The value is SCALE-encoded LastRuntimeUpgradeInfo:
            // - Compact<u32> spec_version
            // - String spec_name

            if !value.is_empty() && value != "null" {
                println!("\n✓ LastRuntimeUpgrade storage is set");

                // Try to decode the compact spec_version
                if value.len() > 4 {
                    let hex_data = &value[2..]; // Skip 0x
                    println!("   Raw hex: {}", hex_data);

                    // Compact encoding: if first byte & 0b11 == 0, then value = byte >> 2
                    if let Ok(first_byte) = u8::from_str_radix(&hex_data[0..2], 16) {
                        let encoding_mode = first_byte & 0b11;
                        if encoding_mode == 0 {
                            let stored_version = first_byte >> 2;
                            println!("   Decoded spec_version: {}", stored_version);
                        }
                    }
                }
            } else {
                println!("\n⚠ LastRuntimeUpgrade storage is empty");
                println!("   This suggests the runtime upgrade hasn't been detected yet");
            }
        }
        Err(e) => {
            println!("Failed to query LastRuntimeUpgrade: {}", e);
        }
    }
}

// =============================================================================
// Combined Verification
// =============================================================================

/// Full upgrade verification sequence
#[tokio::test]
async fn test_full_upgrade_verification() {
    println!("\n");
    println!("╔════════════════════════════════════════════════════════════════╗");
    println!("║           RUNTIME UPGRADE VERIFICATION SEQUENCE               ║");
    println!("╚════════════════════════════════════════════════════════════════╝");
    println!();

    let client = match wait_for_node().await {
        Some(c) => c,
        None => {
            println!("❌ Cannot connect to node at {}", NODE_URL);
            println!();
            println!("To start a dev node:");
            println!("  ./target/release/quantumharmony-node --dev --tmp");
            return;
        }
    };

    // Step 1: Get current state
    println!("Step 1: Current State");
    println!("---------------------");
    let block_number = get_block_number(&client).await;
    let spec_version = get_spec_version(&client).await;
    let code_hash = get_code_hash(&client).await;

    println!("  Block number: {}", block_number);
    println!("  spec_version: {}", spec_version);
    println!("  Code hash: {}", code_hash);
    println!();

    // Step 2: Expected values
    println!("Step 2: Expected Values");
    println!("-----------------------");
    let expected_version = 9u64;
    println!("  Expected spec_version: {}", expected_version);
    println!();

    // Step 3: Comparison
    println!("Step 3: Verification");
    println!("--------------------");

    if spec_version == expected_version {
        println!("  ✓ spec_version is correct ({})", expected_version);
        println!();
        println!("═══════════════════════════════════════════════════════════════════");
        println!("  RUNTIME UPGRADE VERIFIED SUCCESSFULLY!");
        println!("═══════════════════════════════════════════════════════════════════");
    } else {
        println!("  ✗ spec_version mismatch");
        println!("    Current:  {}", spec_version);
        println!("    Expected: {}", expected_version);
        println!();

        // Determine likely cause
        if spec_version < expected_version {
            println!("DIAGNOSIS: Upgrade Not Applied");
            println!("==============================");
            println!();
            println!("The runtime is still running version {}.", spec_version);
            println!();
            println!("Most likely causes:");
            println!();
            println!("1. WASM NOT UPLOADED");
            println!("   - The set_code extrinsic may not have been submitted");
            println!("   - Check for CodeUpdated event in recent blocks");
            println!();
            println!("2. NEED TO WAIT FOR NEXT BLOCK");
            println!("   - After set_code, the new version activates on the NEXT block");
            println!("   - Wait for at least one new block to be produced");
            println!();
            println!("3. NATIVE EXECUTION");
            println!("   - If the node binary was built with the same version,");
            println!("     it may prefer native execution over WASM");
            println!("   - Rebuild the node binary with the new runtime version");
            println!("   - Or use --execution=wasm flag when starting the node");
            println!();
            println!("4. SET_CODE FAILED");
            println!("   - The extrinsic may have failed silently");
            println!("   - Check for errors in node logs");
            println!("   - Verify sudo key is correctly configured");
            println!();

            println!("RECOMMENDED ACTIONS:");
            println!("-------------------");
            println!("1. cargo build --release -p quantumharmony-runtime");
            println!("2. Use tools/runtime-upgrade to submit set_code");
            println!("3. Wait for 2 blocks (~12 seconds)");
            println!("4. Re-run this test");
        }
    }
}

/// Wait for version change test
#[tokio::test]
#[ignore]  // Run manually: cargo test test_wait_for_version_change -- --ignored --nocapture
async fn test_wait_for_version_change() {
    println!("\n========================================");
    println!("Monitoring for version change...");
    println!("========================================\n");

    let client = wait_for_node().await.expect("Node not available");

    let initial_version = get_spec_version(&client).await;
    let expected_version = 9u64;

    println!("Current version: {}", initial_version);
    println!("Expected version: {}", expected_version);

    if initial_version == expected_version {
        println!("\n✓ Already at expected version");
        return;
    }

    println!("\nWaiting for version to change...");
    println!("(Submit set_code extrinsic now if not already done)");
    println!();

    for i in 1..=60 {
        sleep(Duration::from_secs(6)).await;
        let current_block = get_block_number(&client).await;
        let current_version = get_spec_version(&client).await;

        print!("Block {}: version={}", current_block, current_version);

        if current_version == expected_version {
            println!(" ✓ VERSION CHANGED!");
            println!("\n═══════════════════════════════════════════");
            println!("  RUNTIME UPGRADE DETECTED AFTER {} BLOCKS", i);
            println!("═══════════════════════════════════════════");
            return;
        }
        println!();
    }

    println!("\n⚠ Version did not change after 60 blocks");
    println!("   The upgrade may have failed or was not submitted");
}
