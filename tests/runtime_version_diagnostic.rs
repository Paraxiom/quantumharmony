//! Runtime Version Diagnostic Tests
//!
//! This module contains tests to diagnose why runtime upgrade version numbers
//! are not updating after a successful upgrade.
//!
//! The issue: After performing a runtime upgrade via set_code, the version
//! number reported by state_getRuntimeVersion might not reflect the new version.
//!
//! Possible causes to test:
//! 1. WASM code was not actually stored (set_code failed silently)
//! 2. Nodes are executing native code instead of WASM
//! 3. LastRuntimeUpgrade storage is stale
//! 4. The runtime upgrade didn't trigger on_runtime_upgrade hooks

use jsonrpsee::{core::client::ClientT, http_client::{HttpClient, HttpClientBuilder}, rpc_params};
use serde_json::{json, Value};
use std::time::Duration;
use tokio::time::sleep;

// Test against different node configurations
const LOCAL_NODE: &str = "http://127.0.0.1:9944";
const ALICE_NODE: &str = "http://localhost:9944";
const BOB_NODE: &str = "http://localhost:9944";
const CHARLIE_NODE: &str = "http://localhost:9944";

/// Storage keys for runtime upgrade diagnostics
mod storage_keys {
    // System::LastRuntimeUpgrade storage key
    // twox128("System") + twox128("LastRuntimeUpgrade")
    pub const LAST_RUNTIME_UPGRADE: &str = "0x26aa394eea5630e07c48ae0c9558cef7f9cce9c888469bb1a0dceaa129672ef8";

    // :code storage key (well-known key for WASM code)
    pub const CODE: &str = "0x3a636f6465";  // hex(":code")
}

/// Helper to connect to a node
async fn connect_to_node(url: &str) -> Option<HttpClient> {
    for _ in 0..5 {
        if let Ok(client) = HttpClientBuilder::default()
            .request_timeout(Duration::from_secs(30))
            .build(url)
        {
            if client.request::<Value, _>("system_health", rpc_params![]).await.is_ok() {
                return Some(client);
            }
        }
        sleep(Duration::from_millis(500)).await;
    }
    None
}

/// Get runtime version from a node
async fn get_runtime_version(client: &HttpClient) -> Option<Value> {
    client.request("state_getRuntimeVersion", rpc_params![]).await.ok()
}

/// Get storage value at a specific key
async fn get_storage(client: &HttpClient, key: &str) -> Option<String> {
    client.request("state_getStorage", rpc_params![key]).await.ok()
}

/// Get system properties including native runtime version
async fn get_system_properties(client: &HttpClient) -> (Option<Value>, Option<String>) {
    let version = client.request::<Value, _>("state_getRuntimeVersion", rpc_params![]).await.ok();
    let chain = client.request::<String, _>("system_chain", rpc_params![]).await.ok();
    (version, chain)
}

/// Test 1: Query runtime version from all production nodes
#[tokio::test]
async fn test_query_all_nodes_runtime_version() {
    println!("\n========================================");
    println!("DIAGNOSTIC: Runtime Version on All Nodes");
    println!("========================================\n");

    let nodes = vec![
        ("Local", LOCAL_NODE),
        ("Alice", ALICE_NODE),
        ("Bob", BOB_NODE),
        ("Charlie", CHARLIE_NODE),
    ];

    let mut results = Vec::new();

    for (name, url) in &nodes {
        print!("Connecting to {} ({})... ", name, url);

        match connect_to_node(url).await {
            Some(client) => {
                println!("✓ Connected");

                let version = get_runtime_version(&client).await;
                if let Some(v) = &version {
                    let spec_version = v.get("specVersion").and_then(|v| v.as_u64()).unwrap_or(0);
                    let impl_version = v.get("implVersion").and_then(|v| v.as_u64()).unwrap_or(0);
                    let spec_name = v.get("specName").and_then(|v| v.as_str()).unwrap_or("unknown");

                    println!("  spec_name: {}", spec_name);
                    println!("  spec_version: {}", spec_version);
                    println!("  impl_version: {}", impl_version);

                    results.push((name.to_string(), spec_version));
                }
            }
            None => {
                println!("✗ Failed to connect");
                results.push((name.to_string(), 0));
            }
        }
        println!();
    }

    // Check if all connected nodes have the same version
    let connected: Vec<_> = results.iter().filter(|(_, v)| *v > 0).collect();
    if connected.len() > 1 {
        let first_version = connected[0].1;
        let all_same = connected.iter().all(|(_, v)| *v == first_version);

        if all_same {
            println!("✓ All connected nodes report the same spec_version: {}", first_version);
        } else {
            println!("⚠ WARNING: Nodes report different spec_versions!");
            for (name, version) in &connected {
                println!("  {}: {}", name, version);
            }
        }
    }

    // Check expected version (should be 9 after upgrade)
    let expected_version = 9u64;
    for (name, version) in &results {
        if *version > 0 && *version != expected_version {
            println!("⚠ {} reports version {} but expected {}", name, version, expected_version);
        }
    }
}

/// Test 2: Check LastRuntimeUpgrade storage value
#[tokio::test]
async fn test_last_runtime_upgrade_storage() {
    println!("\n========================================");
    println!("DIAGNOSTIC: LastRuntimeUpgrade Storage");
    println!("========================================\n");

    let client = match connect_to_node(LOCAL_NODE).await {
        Some(c) => c,
        None => {
            println!("Cannot connect to local node, skipping...");
            return;
        }
    };

    // Query LastRuntimeUpgrade storage
    match get_storage(&client, storage_keys::LAST_RUNTIME_UPGRADE).await {
        Some(value) => {
            println!("LastRuntimeUpgrade storage value: {}", value);
            println!();
            println!("This storage contains the spec_version and spec_name");
            println!("from the last time a runtime upgrade was detected.");
            println!();

            // Decode the value (it's SCALE encoded)
            if value.len() > 2 {
                // Skip 0x prefix
                let hex_data = &value[2..];
                println!("Raw hex data: {}", hex_data);

                // LastRuntimeUpgradeInfo is:
                // - Compact<u32> spec_version
                // - String spec_name
                // The compact encoding for small numbers is just the number * 4
            } else {
                println!("⚠ Storage value is empty or too short");
            }
        }
        None => {
            println!("⚠ LastRuntimeUpgrade storage not found!");
            println!("   This could mean:");
            println!("   1. Genesis config didn't initialize it");
            println!("   2. Runtime upgrade never executed on_runtime_upgrade");
        }
    }
}

/// Test 3: Check if WASM code storage changed
#[tokio::test]
async fn test_wasm_code_storage_hash() {
    println!("\n========================================");
    println!("DIAGNOSTIC: WASM Code Storage Hash");
    println!("========================================\n");

    let client = match connect_to_node(LOCAL_NODE).await {
        Some(c) => c,
        None => {
            println!("Cannot connect to local node, skipping...");
            return;
        }
    };

    // Get the hash of the code storage
    // We can't easily get the full code as it's huge, but we can get metadata
    let result: Result<String, _> = client
        .request("state_getStorageHash", rpc_params![storage_keys::CODE])
        .await;

    match result {
        Ok(hash) => {
            println!("WASM code storage hash: {}", hash);
            println!();
            println!("Compare this hash before and after runtime upgrade");
            println!("If the hash changed, the WASM was successfully stored");
        }
        Err(e) => {
            println!("Failed to get code storage hash: {}", e);
        }
    }

    // Also get the size
    let result: Result<String, _> = client
        .request("state_getStorageSize", rpc_params![storage_keys::CODE])
        .await;

    match result {
        Ok(size) => {
            println!("WASM code storage size: {} bytes", size);
        }
        Err(e) => {
            println!("Failed to get code storage size: {}", e);
        }
    }
}

/// Test 4: Check system events for CodeUpdated
#[tokio::test]
async fn test_check_recent_events() {
    println!("\n========================================");
    println!("DIAGNOSTIC: Recent System Events");
    println!("========================================\n");

    let client = match connect_to_node(LOCAL_NODE).await {
        Some(c) => c,
        None => {
            println!("Cannot connect to local node, skipping...");
            return;
        }
    };

    // Get the latest finalized block
    let finalized_hash: Result<String, _> = client
        .request("chain_getFinalizedHead", rpc_params![])
        .await;

    match finalized_hash {
        Ok(hash) => {
            println!("Finalized block hash: {}", hash);

            // Get events from that block
            // Events are stored at System.Events
            let events_key = "0x26aa394eea5630e07c48ae0c9558cef780d41e5e16056765bc8461851072c9d7";

            let result: Result<String, _> = client
                .request("state_getStorage", rpc_params![events_key, hash])
                .await;

            match result {
                Ok(events) => {
                    println!("Events data length: {} bytes", events.len());
                    // We'd need to decode SCALE-encoded events to find CodeUpdated
                    // For now, just report that events exist
                    if events.len() > 10 {
                        println!("✓ Events data found in finalized block");
                    }
                }
                Err(e) => {
                    println!("Failed to get events: {}", e);
                }
            }
        }
        Err(e) => {
            println!("Failed to get finalized head: {}", e);
        }
    }
}

/// Test 5: Compare native vs WASM runtime version
#[tokio::test]
async fn test_native_vs_wasm_version() {
    println!("\n========================================");
    println!("DIAGNOSTIC: Native vs WASM Runtime");
    println!("========================================\n");

    let client = match connect_to_node(LOCAL_NODE).await {
        Some(c) => c,
        None => {
            println!("Cannot connect to local node, skipping...");
            return;
        }
    };

    // Get runtime version (this uses WASM by default for state queries)
    let version: Result<Value, _> = client
        .request("state_getRuntimeVersion", rpc_params![])
        .await;

    match version {
        Ok(v) => {
            println!("Reported runtime version:");
            println!("{}", serde_json::to_string_pretty(&v).unwrap_or_default());
            println!();

            let spec_version = v.get("specVersion").and_then(|v| v.as_u64()).unwrap_or(0);

            println!("Analysis:");
            println!("=========");

            if spec_version == 9 {
                println!("✓ Runtime reports spec_version 9 (expected after upgrade)");
            } else if spec_version == 8 {
                println!("⚠ Runtime still reports spec_version 8 (pre-upgrade version)");
                println!();
                println!("Possible causes:");
                println!("1. Runtime upgrade WASM was never submitted to chain");
                println!("2. The set_code extrinsic failed");
                println!("3. Nodes are running native code, not WASM");
                println!("4. You need to rebuild and redeploy the runtime");
            } else {
                println!("? Runtime reports spec_version {} (unexpected)", spec_version);
            }
        }
        Err(e) => {
            println!("Failed to get runtime version: {}", e);
        }
    }
}

/// Test 6: Check execution strategy
#[tokio::test]
async fn test_check_system_properties() {
    println!("\n========================================");
    println!("DIAGNOSTIC: System Properties");
    println!("========================================\n");

    let client = match connect_to_node(LOCAL_NODE).await {
        Some(c) => c,
        None => {
            println!("Cannot connect to local node, skipping...");
            return;
        }
    };

    // Get system name and version
    let name: Result<String, _> = client.request("system_name", rpc_params![]).await;
    let version_str: Result<String, _> = client.request("system_version", rpc_params![]).await;
    let chain: Result<String, _> = client.request("system_chain", rpc_params![]).await;
    let health: Result<Value, _> = client.request("system_health", rpc_params![]).await;

    println!("Node Information:");
    if let Ok(n) = name {
        println!("  system_name: {}", n);
    }
    if let Ok(v) = version_str {
        println!("  system_version: {} (node binary version)", v);
    }
    if let Ok(c) = chain {
        println!("  system_chain: {}", c);
    }
    if let Ok(h) = health {
        println!("  system_health: {}", serde_json::to_string(&h).unwrap_or_default());
    }

    println!();
    println!("Note: system_version is the NODE binary version, not the runtime version.");
    println!("The runtime version (spec_version) comes from the WASM/native runtime.");
}

/// Test 7: Full diagnostic summary
#[tokio::test]
async fn test_full_diagnostic_summary() {
    println!("\n");
    println!("╔════════════════════════════════════════════════════════════╗");
    println!("║        RUNTIME UPGRADE VERSION DIAGNOSTIC SUMMARY         ║");
    println!("╚════════════════════════════════════════════════════════════╝");
    println!();

    let client = match connect_to_node(LOCAL_NODE).await {
        Some(c) => c,
        None => {
            println!("❌ Cannot connect to local node");
            println!();
            println!("Please ensure a node is running at {}", LOCAL_NODE);
            println!();
            println!("To start a dev node:");
            println!("  ./target/release/quantumharmony-node --dev");
            return;
        }
    };

    println!("✓ Connected to node at {}", LOCAL_NODE);
    println!();

    // 1. Get current runtime version
    let version: Value = client
        .request("state_getRuntimeVersion", rpc_params![])
        .await
        .expect("Failed to get runtime version");

    let spec_version = version.get("specVersion").and_then(|v| v.as_u64()).unwrap_or(0);
    let spec_name = version.get("specName").and_then(|v| v.as_str()).unwrap_or("unknown");

    println!("Current Runtime:");
    println!("  spec_name: {}", spec_name);
    println!("  spec_version: {}", spec_version);
    println!();

    // 2. Check expected version
    let expected_version = 9u64;

    if spec_version == expected_version {
        println!("✓ Runtime version matches expected version {}", expected_version);
        println!();
        println!("The runtime upgrade appears to have been successful!");
    } else {
        println!("⚠ VERSION MISMATCH");
        println!("  Expected: {}", expected_version);
        println!("  Actual: {}", spec_version);
        println!();

        println!("DIAGNOSTIC STEPS:");
        println!("-----------------");
        println!();
        println!("1. Check if WASM was built with the new version:");
        println!("   - Open runtime/src/lib.rs");
        println!("   - Verify spec_version in VERSION constant is {}", expected_version);
        println!();
        println!("2. Rebuild the runtime WASM:");
        println!("   cd runtime && cargo build --release");
        println!();
        println!("3. Verify the WASM file exists:");
        println!("   ls -la target/release/wbuild/quantumharmony-runtime/");
        println!();
        println!("4. Submit the runtime upgrade again:");
        println!("   - Use the runtime-upgrade tool");
        println!("   - Or submit via Polkadot.js Apps");
        println!();
        println!("5. Wait for the next block to be produced");
        println!("   - The version updates on the NEXT block after set_code");
        println!();
        println!("6. If using native execution, restart the node:");
        println!("   - Native code takes precedence if version matches");
        println!("   - Restart node after set_code to use WASM");
    }

    // 3. Get code hash for comparison
    let code_hash: Result<String, _> = client
        .request("state_getStorageHash", rpc_params![storage_keys::CODE])
        .await;

    if let Ok(hash) = code_hash {
        println!();
        println!("WASM Code Hash: {}", hash);
        println!("(Compare this with previous hash to verify code was updated)");
    }
}
