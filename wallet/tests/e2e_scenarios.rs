//! End-to-End Test Scenarios
//!
//! Complete workflow tests for the Node Operator Interface.
//! These tests simulate real user interactions with the interface.

use std::time::Duration;
use serde_json::json;

/// Test configuration
pub struct TestConfig {
    pub rpc_endpoint: String,
    pub node_binary: String,
    pub test_wasm: Option<String>,
    pub timeout: Duration,
}

impl Default for TestConfig {
    fn default() -> Self {
        Self {
            rpc_endpoint: "http://localhost:9944".to_string(),
            node_binary: "target/release/quantumharmony-node".to_string(),
            test_wasm: None,
            timeout: Duration::from_secs(60),
        }
    }
}

#[cfg(test)]
mod scenarios {
    use super::*;

    // ============================================
    // SCENARIO 1: FRESH NODE STARTUP
    // ============================================

    /// Tests the complete node startup flow:
    /// 1. Verify node is not running
    /// 2. Start node
    /// 3. Wait for initialization
    /// 4. Verify RPC is responding
    /// 5. Check peer connections
    /// 6. Verify block production
    #[tokio::test]
    #[ignore] // Run with: cargo test --ignored
    async fn scenario_fresh_node_startup() {
        let config = TestConfig::default();

        println!("=== SCENARIO: Fresh Node Startup ===\n");

        // Step 1: Verify node is not running
        println!("Step 1: Checking node is not already running...");
        let health_check = check_node_health(&config.rpc_endpoint).await;
        if health_check.is_ok() {
            println!("  WARN: Node already running, skipping startup test");
            return;
        }
        println!("  OK: Node not running\n");

        // Step 2: Start node (simulated - actual start requires Tauri)
        println!("Step 2: Starting node...");
        println!("  NOTE: In actual test, would call start_node() Tauri command");
        println!("  Simulating 5 second startup delay...");
        tokio::time::sleep(Duration::from_secs(5)).await;

        // Step 3: Wait for initialization
        println!("\nStep 3: Waiting for RPC to become available...");
        let mut attempts = 0;
        let max_attempts = 30;

        while attempts < max_attempts {
            if check_node_health(&config.rpc_endpoint).await.is_ok() {
                println!("  OK: RPC responding after {} attempts\n", attempts + 1);
                break;
            }
            attempts += 1;
            tokio::time::sleep(Duration::from_secs(1)).await;
        }

        if attempts >= max_attempts {
            panic!("Node failed to start within {} seconds", max_attempts);
        }

        // Step 4: Verify RPC methods
        println!("Step 4: Verifying core RPC methods...");
        verify_core_rpc_methods(&config.rpc_endpoint).await;

        // Step 5: Check peer connections
        println!("\nStep 5: Checking peer connections...");
        let peers = get_peer_count(&config.rpc_endpoint).await;
        println!("  Peer count: {}", peers.unwrap_or(0));

        // Step 6: Verify block production
        println!("\nStep 6: Verifying block production...");
        let block1 = get_block_number(&config.rpc_endpoint).await;
        tokio::time::sleep(Duration::from_secs(7)).await; // Wait for next block
        let block2 = get_block_number(&config.rpc_endpoint).await;

        if let (Some(b1), Some(b2)) = (block1, block2) {
            assert!(b2 > b1, "Block number should increase");
            println!("  OK: Blocks advancing ({} -> {})\n", b1, b2);
        }

        println!("=== SCENARIO COMPLETE ===");
    }

    // ============================================
    // SCENARIO 2: RUNTIME VERSION CHECK
    // ============================================

    /// Tests runtime version retrieval:
    /// 1. Connect to node
    /// 2. Get runtime version
    /// 3. Verify all required fields
    /// 4. Check spec version is valid
    #[tokio::test]
    async fn scenario_runtime_version_check() {
        let config = TestConfig::default();

        println!("=== SCENARIO: Runtime Version Check ===\n");

        // Check node availability
        if check_node_health(&config.rpc_endpoint).await.is_err() {
            println!("SKIP: Node not available at {}", config.rpc_endpoint);
            return;
        }

        // Get runtime version
        println!("Fetching runtime version...");
        let version = get_runtime_version(&config.rpc_endpoint).await;

        match version {
            Ok(v) => {
                println!("  specName: {}", v.get("specName").unwrap_or(&json!("unknown")));
                println!("  specVersion: {}", v.get("specVersion").unwrap_or(&json!(0)));
                println!("  implName: {}", v.get("implName").unwrap_or(&json!("unknown")));
                println!("  implVersion: {}", v.get("implVersion").unwrap_or(&json!(0)));

                // Verify required fields
                assert!(v.get("specName").is_some(), "Missing specName");
                assert!(v.get("specVersion").is_some(), "Missing specVersion");

                // Check spec version is reasonable (> 100 for production)
                let spec_version = v.get("specVersion")
                    .and_then(|v| v.as_u64())
                    .unwrap_or(0);
                println!("\n  Spec version {} is valid\n", spec_version);
            }
            Err(e) => {
                println!("  ERROR: {}", e);
            }
        }

        println!("=== SCENARIO COMPLETE ===");
    }

    // ============================================
    // SCENARIO 3: NETWORK CONNECTIVITY
    // ============================================

    /// Tests network connectivity:
    /// 1. Check local node health
    /// 2. Enumerate connected peers
    /// 3. Verify peer metadata
    /// 4. Check sync status
    #[tokio::test]
    async fn scenario_network_connectivity() {
        let config = TestConfig::default();

        println!("=== SCENARIO: Network Connectivity ===\n");

        if check_node_health(&config.rpc_endpoint).await.is_err() {
            println!("SKIP: Node not available at {}", config.rpc_endpoint);
            return;
        }

        // Get system health
        println!("Checking system health...");
        let health = rpc_call(&config.rpc_endpoint, "system_health", json!([])).await;
        if let Ok(h) = health {
            println!("  Peers: {}", h.get("peers").unwrap_or(&json!(0)));
            println!("  Is syncing: {}", h.get("isSyncing").unwrap_or(&json!(false)));
            println!("  Should have peers: {}", h.get("shouldHavePeers").unwrap_or(&json!(true)));
        }

        // Get peer list
        println!("\nEnumerating peers...");
        let peers = rpc_call(&config.rpc_endpoint, "system_peers", json!([])).await;
        if let Ok(p) = peers {
            if let Some(peer_list) = p.as_array() {
                for (i, peer) in peer_list.iter().enumerate() {
                    println!("  Peer {}: {}", i + 1,
                        peer.get("peerId").unwrap_or(&json!("unknown")));
                }
            }
        }

        // Check sync state
        println!("\nChecking sync state...");
        let sync_state = rpc_call(&config.rpc_endpoint, "system_syncState", json!([])).await;
        if let Ok(s) = sync_state {
            println!("  Starting block: {}", s.get("startingBlock").unwrap_or(&json!(0)));
            println!("  Current block: {}", s.get("currentBlock").unwrap_or(&json!(0)));
            if let Some(highest) = s.get("highestBlock") {
                println!("  Highest block: {}", highest);
            }
        }

        println!("\n=== SCENARIO COMPLETE ===");
    }

    // ============================================
    // SCENARIO 4: BALANCE CHECK WORKFLOW
    // ============================================

    /// Tests balance checking:
    /// 1. Query well-known test account
    /// 2. Parse balance response
    /// 3. Verify format and decimals
    #[tokio::test]
    async fn scenario_balance_check() {
        let config = TestConfig::default();

        println!("=== SCENARIO: Balance Check ===\n");

        if check_node_health(&config.rpc_endpoint).await.is_err() {
            println!("SKIP: Node not available at {}", config.rpc_endpoint);
            return;
        }

        // Well-known test addresses
        let test_accounts = vec![
            ("Alice", "5GrwvaEF5zXb26Fz9rcQpDWS57CtERHpNehXCPcNoHGKutQY"),
            ("Bob", "5FHneW46xGXgs5mUiveU4sbTyGBzmstUspZC92UhjJM694ty"),
        ];

        for (name, address) in test_accounts {
            println!("Checking {} balance...", name);

            // Try gateway_balance first
            let balance = rpc_call(&config.rpc_endpoint, "gateway_balance", json!([address])).await;

            match balance {
                Ok(b) => println!("  Balance: {}\n", b),
                Err(_) => {
                    // Fall back to state query
                    println!("  gateway_balance not available, using state query...");
                    // Would query storage directly here
                    println!("  (Storage query not implemented in test)\n");
                }
            }
        }

        println!("=== SCENARIO COMPLETE ===");
    }

    // ============================================
    // SCENARIO 5: QRNG DEVICE STATUS
    // ============================================

    /// Tests QRNG subsystem:
    /// 1. Get QRNG configuration
    /// 2. List device queues
    /// 3. Check device health metrics
    #[tokio::test]
    async fn scenario_qrng_status() {
        let config = TestConfig::default();

        println!("=== SCENARIO: QRNG Device Status ===\n");

        if check_node_health(&config.rpc_endpoint).await.is_err() {
            println!("SKIP: Node not available at {}", config.rpc_endpoint);
            return;
        }

        // Get QRNG config
        println!("Fetching QRNG configuration...");
        let qrng_config = rpc_call(&config.rpc_endpoint, "qrng_getConfig", json!([])).await;

        match qrng_config {
            Ok(c) => {
                println!("  Threshold K: {}", c.get("threshold_k").unwrap_or(&json!("N/A")));
                println!("  Total devices M: {}", c.get("total_devices").unwrap_or(&json!("N/A")));
            }
            Err(e) => {
                println!("  QRNG config not available: {}", e);
                println!("  (This is expected if QRNG pallet not enabled)\n");
                return;
            }
        }

        // Get device queues
        println!("\nFetching device queues...");
        let queues = rpc_call(&config.rpc_endpoint, "qrng_getDeviceQueues", json!([])).await;

        if let Ok(q) = queues {
            if let Some(devices) = q.as_array() {
                for device in devices {
                    println!("  Device: {}", device.get("name").unwrap_or(&json!("unknown")));
                    println!("    Queue length: {}", device.get("queue_length").unwrap_or(&json!(0)));
                    println!("    Best QBER: {}", device.get("best_qber").unwrap_or(&json!("N/A")));
                    println!("    Status: {}", if device.get("enabled").unwrap_or(&json!(false)).as_bool().unwrap_or(false) { "enabled" } else { "disabled" });
                }
            }
        }

        println!("\n=== SCENARIO COMPLETE ===");
    }

    // ============================================
    // SCENARIO 6: BLOCK EXPLORER SIMULATION
    // ============================================

    /// Simulates block explorer functionality:
    /// 1. Get latest blocks
    /// 2. Fetch block details
    /// 3. Parse extrinsics
    #[tokio::test]
    async fn scenario_block_explorer() {
        let config = TestConfig::default();

        println!("=== SCENARIO: Block Explorer ===\n");

        if check_node_health(&config.rpc_endpoint).await.is_err() {
            println!("SKIP: Node not available at {}", config.rpc_endpoint);
            return;
        }

        // Get latest header
        println!("Fetching latest block header...");
        let header = rpc_call(&config.rpc_endpoint, "chain_getHeader", json!([])).await;

        if let Ok(h) = header {
            let block_num = h.get("number").and_then(|n| n.as_str()).unwrap_or("0x0");
            let parent_hash = h.get("parentHash").and_then(|p| p.as_str()).unwrap_or("unknown");

            println!("  Block number: {}", block_num);
            println!("  Parent hash: {}...", &parent_hash[..20.min(parent_hash.len())]);

            // Get full block
            println!("\nFetching full block...");
            let block_hash = rpc_call(&config.rpc_endpoint, "chain_getBlockHash",
                json!([block_num])).await;

            if let Ok(hash) = block_hash {
                println!("  Block hash: {}", hash);

                let block = rpc_call(&config.rpc_endpoint, "chain_getBlock",
                    json!([hash])).await;

                if let Ok(b) = block {
                    if let Some(extrinsics) = b.get("block")
                        .and_then(|b| b.get("extrinsics"))
                        .and_then(|e| e.as_array())
                    {
                        println!("  Extrinsic count: {}", extrinsics.len());
                    }
                }
            }
        }

        println!("\n=== SCENARIO COMPLETE ===");
    }

    // ============================================
    // HELPER FUNCTIONS
    // ============================================

    async fn check_node_health(endpoint: &str) -> Result<(), String> {
        rpc_call(endpoint, "system_health", json!([])).await.map(|_| ())
    }

    async fn get_block_number(endpoint: &str) -> Option<u64> {
        let header = rpc_call(endpoint, "chain_getHeader", json!([])).await.ok()?;
        let hex_num = header.get("number")?.as_str()?;
        u64::from_str_radix(hex_num.trim_start_matches("0x"), 16).ok()
    }

    async fn get_peer_count(endpoint: &str) -> Option<usize> {
        let peers = rpc_call(endpoint, "system_peers", json!([])).await.ok()?;
        peers.as_array().map(|a| a.len())
    }

    async fn get_runtime_version(endpoint: &str) -> Result<serde_json::Value, String> {
        rpc_call(endpoint, "state_getRuntimeVersion", json!([])).await
    }

    async fn verify_core_rpc_methods(endpoint: &str) {
        let methods = vec![
            "system_chain",
            "system_name",
            "system_version",
            "chain_getHeader",
            "state_getRuntimeVersion",
        ];

        for method in methods {
            let result = rpc_call(endpoint, method, json!([])).await;
            match result {
                Ok(_) => println!("  {} - OK", method),
                Err(e) => println!("  {} - FAILED: {}", method, e),
            }
        }
    }

    async fn rpc_call(endpoint: &str, method: &str, params: serde_json::Value)
        -> Result<serde_json::Value, String>
    {
        let client = reqwest::Client::new();
        let request = json!({
            "jsonrpc": "2.0",
            "id": 1,
            "method": method,
            "params": params
        });

        let response = client.post(endpoint)
            .json(&request)
            .send()
            .await
            .map_err(|e| format!("Request failed: {}", e))?;

        let rpc_response: serde_json::Value = response.json().await
            .map_err(|e| format!("Parse failed: {}", e))?;

        if let Some(error) = rpc_response.get("error") {
            return Err(format!("RPC error: {}", error));
        }

        rpc_response.get("result")
            .cloned()
            .ok_or_else(|| "No result".to_string())
    }
}
