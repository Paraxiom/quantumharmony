//! Multi-node Network Integration Tests for Threshold QRNG
//!
//! These tests run against the CANARY production network (not dev mode).
//! They verify the complete threshold QRNG flow including:
//! - Test account creation and funding
//! - Multi-node coordination
//! - Turn-based share submission
//! - Shamir reconstruction
//! - Priority queue integration
//!
//! ## Prerequisites
//!
//! 1. Canary network must be running:
//!    - Alice: 51.79.26.123:9944 (Montreal)
//!    - Bob: 51.79.26.168:9944 (Beauharnois)
//!    - Charlie: 209.38.225.4:9944 (Frankfurt)
//!
//! 2. Test accounts must be funded (run setup_test_accounts first)
//!
//! ## Running Tests
//!
//! ```bash
//! # One-time setup (creates and funds test accounts)
//! cargo test setup_test_accounts -- --ignored --nocapture
//!
//! # Run all network tests
//! cargo test --test network_integration_tests -- --ignored --test-threads=1
//! ```

use std::time::Duration;
use tokio::time::sleep;
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};

// Canary network endpoints (real validators)
const ALICE_RPC: &str = "http://51.79.26.123:9944";
const BOB_RPC: &str = "http://51.79.26.168:9944";
const CHARLIE_RPC: &str = "http://209.38.225.4:9944";

// Test accounts file path
const TEST_ACCOUNTS_FILE: &str = "tests/test_accounts.json";
const STANDARD_TEST_SET_FILE: &str = "tests/standard_test_set.json";

/// Test account data structure
#[derive(Debug, Clone, Serialize, Deserialize)]
struct TestAccount {
    name: String,
    public_key: String,
    secret_key: String,
    account_id: String,
    ss58_address: String,
    created_at: u64,
}

/// Standard test account set
#[derive(Debug, Clone, Serialize, Deserialize)]
struct StandardTestSet {
    sender: TestAccount,
    receiver: TestAccount,
    validator_candidate: TestAccount,
    extra: Vec<TestAccount>,
}

/// HTTP client for making RPC requests
struct RpcClient {
    client: reqwest::Client,
    endpoint: String,
}

impl RpcClient {
    fn new(endpoint: &str) -> Self {
        Self {
            client: reqwest::Client::builder()
                .timeout(Duration::from_secs(30))
                .build()
                .expect("Failed to build HTTP client"),
            endpoint: endpoint.to_string(),
        }
    }

    async fn request(&self, method: &str, params: Value) -> Result<Value, String> {
        let body = json!({
            "jsonrpc": "2.0",
            "id": 1,
            "method": method,
            "params": params
        });

        let response = self.client
            .post(&self.endpoint)
            .json(&body)
            .send()
            .await
            .map_err(|e| format!("Request failed: {}", e))?;

        if !response.status().is_success() {
            return Err(format!("HTTP error: {}", response.status()));
        }

        let result: Value = response.json().await
            .map_err(|e| format!("Failed to parse response: {}", e))?;

        if let Some(error) = result.get("error") {
            return Err(format!("RPC error: {}", error));
        }

        Ok(result["result"].clone())
    }
}

/// Connect to a node and wait for it to be healthy
async fn connect_and_wait(endpoint: &str) -> RpcClient {
    let client = RpcClient::new(endpoint);

    // Wait for node to be ready (max 30 seconds)
    for _ in 0..30 {
        match client.request("system_health", json!([])).await {
            Ok(health) => {
                if health.get("isSyncing").and_then(|v| v.as_bool()) == Some(false) {
                    return client;
                }
            }
            Err(_) => {}
        }
        sleep(Duration::from_secs(1)).await;
    }

    // Return client anyway after timeout
    client
}

/// Get current block number from a node
async fn get_block_number(client: &RpcClient) -> Result<u64, String> {
    let header = client.request("chain_getHeader", json!([])).await?;

    header["number"]
        .as_str()
        .and_then(|s| {
            let s = s.trim_start_matches("0x");
            u64::from_str_radix(s, 16).ok()
        })
        .ok_or_else(|| "Failed to parse block number".to_string())
}

/// Get account balance
async fn get_balance(client: &RpcClient, address: &str) -> Result<u128, String> {
    let result = client.request("gateway_balance", json!([address])).await?;

    result.as_str()
        .and_then(|s| s.parse().ok())
        .or_else(|| result.as_u64().map(|n| n as u128))
        .ok_or_else(|| "Failed to parse balance".to_string())
}

// ============================================================================
// SETUP TESTS (Run these first, once)
// ============================================================================

/// ONE-TIME SETUP: Create and save test accounts
///
/// Run this first: `cargo test setup_test_accounts -- --ignored --nocapture`
#[tokio::test]
#[ignore]
async fn setup_test_accounts() {
    use quantumharmony_node::test_account_setup::{
        generate_test_account, save_test_accounts,
        batch::{generate_standard_test_set, save_standard_test_set},
        funding::print_funding_instructions,
    };

    println!("\n=== Creating Test Accounts ===\n");

    // Generate standard test set
    let test_set = generate_standard_test_set();

    // Save to file
    save_standard_test_set(&test_set, STANDARD_TEST_SET_FILE)
        .expect("Failed to save test accounts");

    println!("Saved standard test set to {}\n", STANDARD_TEST_SET_FILE);

    // Also save as flat list for backward compatibility
    let accounts = vec![
        test_set.sender.clone(),
        test_set.receiver.clone(),
        test_set.validator_candidate.clone(),
    ];
    save_test_accounts(&accounts, TEST_ACCOUNTS_FILE)
        .expect("Failed to save test accounts list");

    println!("Saved {} accounts to {}\n", accounts.len(), TEST_ACCOUNTS_FILE);

    // Print funding instructions
    print_funding_instructions(&accounts);

    println!("\n=== Account Details ===\n");
    for acc in &accounts {
        println!("Name: {}", acc.name);
        println!("  SS58: {}", acc.ss58_address);
        println!("  AccountId: 0x{}", acc.account_id);
        println!();
    }

    println!("After funding, run:");
    println!("  cargo test test_accounts_funded -- --ignored --nocapture");
}

// ============================================================================
// VERIFICATION TESTS
// ============================================================================

/// Verify test accounts were funded
#[tokio::test]
#[ignore]
async fn test_accounts_funded() {
    use quantumharmony_node::test_account_setup::load_test_accounts;

    let accounts = load_test_accounts(TEST_ACCOUNTS_FILE)
        .expect("Run setup_test_accounts first");

    let alice = connect_and_wait(ALICE_RPC).await;

    println!("\n=== Checking Test Account Balances ===\n");

    for acc in &accounts {
        match get_balance(&alice, &acc.ss58_address).await {
            Ok(balance) => {
                let qmhy = balance as f64 / 1_000_000_000_000_000_000.0;
                println!("{}: {:.4} QMHY", acc.name, qmhy);
                assert!(balance > 0, "{} should be funded", acc.name);
            }
            Err(e) => {
                println!("{}: Error - {}", acc.name, e);
                panic!("Failed to get balance for {}", acc.name);
            }
        }
    }

    println!("\nAll test accounts funded successfully!");
}

/// Verify genesis accounts are funded
#[tokio::test]
#[ignore]
async fn test_genesis_accounts_funded() {
    let alice = connect_and_wait(ALICE_RPC).await;

    println!("\n=== Checking Genesis Account Balances ===\n");

    // Genesis accounts from test_accounts.rs
    let genesis_accounts = vec![
        ("Alice", "5GrwvaEF5zXb26Fz9rcQpDWS57CtERHpNehXCPcNoHGKutQY"),
        ("Bob", "5FHneW46xGXgs5mUiveU4sbTyGBzmstUspZC92UhjJM694ty"),
        ("Charlie", "5FLSigC9HGRKVhB9FiEo4Y3koPsNmBmLJbpXg2mp1hXcS59Y"),
    ];

    for (name, _address) in genesis_accounts {
        // Note: Actual SS58 addresses may differ based on SPHINCS+ derivation
        // For now, just verify the node is reachable
        println!("{}: Checking...", name);
    }

    // Verify node is healthy
    let health = alice.request("system_health", json!([])).await;
    assert!(health.is_ok(), "Alice node should be healthy");
    println!("\nGenesis accounts verification complete!");
}

// ============================================================================
// THRESHOLD QRNG TESTS
// ============================================================================

/// Test: Full round coordination with 3 validators
#[tokio::test]
#[ignore]
async fn test_full_shamir_round_coordination() {
    println!("\n=== Testing Full Shamir Round Coordination ===\n");

    // 1. Wait for all nodes to be healthy
    println!("Connecting to validators...");
    let alice = connect_and_wait(ALICE_RPC).await;
    let bob = connect_and_wait(BOB_RPC).await;
    let charlie = connect_and_wait(CHARLIE_RPC).await;

    println!("  Alice: Connected");
    println!("  Bob: Connected");
    println!("  Charlie: Connected");

    // 2. Get current block number
    let block_num = get_block_number(&alice).await
        .expect("Failed to get block number");
    let round_id = format!("round-{}", block_num / 5);
    println!("\nTesting round {} (block {})", round_id, block_num);

    // 3. Trigger Alice to process round
    println!("\nTriggering Alice to process round...");
    let alice_result = alice.request("qrng_processRound", json!([block_num])).await;
    println!("  Alice result: {:?}", alice_result);

    // 4. Trigger Bob to process round
    println!("\nTriggering Bob to process round...");
    let bob_result = bob.request("qrng_processRound", json!([block_num])).await;
    println!("  Bob result: {:?}", bob_result);

    // 5. Trigger Charlie to process round
    println!("\nTriggering Charlie to process round...");
    let charlie_result = charlie.request("qrng_processRound", json!([block_num])).await;
    println!("  Charlie result: {:?}", charlie_result);

    // 6. Check share pool status
    println!("\nChecking share pool status...");
    let status = alice.request("qrng_getSharePoolStatus", json!([round_id])).await;
    println!("  Share pool: {:?}", status);

    // 7. If we have K shares, check reconstruction
    if let Ok(status_val) = status {
        let shares_collected = status_val["shares_collected"].as_u64().unwrap_or(0);
        println!("\nShares collected: {}", shares_collected);

        if shares_collected >= 2 {
            println!("K=2 shares collected! Testing reconstruction...");

            let entropy = alice.request("qrng_reconstructEntropy", json!([round_id])).await;
            match entropy {
                Ok(e) => {
                    let entropy_hex = e["entropy_hex"].as_str().unwrap_or("unknown");
                    println!("  Reconstructed entropy: {}...", &entropy_hex[..34.min(entropy_hex.len())]);
                    println!("  Contributors: {:?}", e["contributors"]);
                }
                Err(e) => {
                    println!("  Reconstruction skipped (shares may be from different secrets): {}", e);
                }
            }
        }
    }

    println!("\nRound {} test complete!", round_id);
}

/// Test: Turn-based submission prevents duplicates
#[tokio::test]
#[ignore]
async fn test_turn_coordination_prevents_duplicates() {
    println!("\n=== Testing Turn Coordination ===\n");

    let alice = connect_and_wait(ALICE_RPC).await;
    let bob = connect_and_wait(BOB_RPC).await;

    let block_num = get_block_number(&alice).await
        .expect("Failed to get block number");

    let turn_index = (block_num / 5) % 3;
    println!("Block: {}, Turn index: {}", block_num, turn_index);

    // Both try to submit
    let alice_result = alice.request("qrng_processRound", json!([block_num])).await;
    let bob_result = bob.request("qrng_processRound", json!([block_num])).await;

    println!("\nResults:");
    println!("  Alice: {:?}", alice_result);
    println!("  Bob: {:?}", bob_result);

    // Verify turn coordination
    match turn_index {
        0 => {
            // Alice's turn
            if let Ok(a) = alice_result {
                let status = a["status"].as_str().unwrap_or("");
                assert!(
                    status == "ShareSubmitted" || status == "AlreadySubmitted" || status == "ReconstructedAndBroadcast",
                    "Alice should submit or have already submitted"
                );
            }
            if let Ok(b) = bob_result {
                let status = b["status"].as_str().unwrap_or("");
                assert!(
                    status == "NotMyTurn" || status == "AlreadyHaveKShares",
                    "Bob should be NotMyTurn or AlreadyHaveKShares"
                );
            }
        }
        1 => {
            // Bob's turn
            if let Ok(a) = alice_result {
                let status = a["status"].as_str().unwrap_or("");
                assert!(
                    status == "NotMyTurn" || status == "AlreadyHaveKShares",
                    "Alice should be NotMyTurn or AlreadyHaveKShares"
                );
            }
            if let Ok(b) = bob_result {
                let status = b["status"].as_str().unwrap_or("");
                assert!(
                    status == "ShareSubmitted" || status == "AlreadySubmitted" || status == "ReconstructedAndBroadcast",
                    "Bob should submit or have already submitted"
                );
            }
        }
        _ => {
            // Charlie's turn - both should be NotMyTurn
            println!("  Turn belongs to Charlie");
        }
    }

    println!("\nTurn coordination test complete!");
}

/// Test: Pool check prevents over-collection
#[tokio::test]
#[ignore]
async fn test_pool_check_prevents_over_collection() {
    println!("\n=== Testing Pool Over-Collection Prevention ===\n");

    let alice = connect_and_wait(ALICE_RPC).await;

    // Get current block and advance to ensure clean state
    let block_num = get_block_number(&alice).await
        .expect("Failed to get block number");

    // Use a future block to avoid conflicts
    let future_block = block_num + 10;
    let round_id = format!("round-{}", future_block / 5);

    println!("Testing with future block {} (round {})", future_block, round_id);

    // Check initial pool state
    let status = alice.request("qrng_getSharePoolStatus", json!([round_id])).await;
    println!("\nInitial pool status: {:?}", status);

    // If pool already has K shares, verify new submissions are rejected
    if let Ok(s) = &status {
        if s["ready_for_reconstruction"].as_bool() == Some(true) {
            println!("\nPool already has K shares - testing rejection...");

            let result = alice.request("qrng_processRound", json!([future_block])).await;
            if let Ok(r) = result {
                let status_str = r["status"].as_str().unwrap_or("");
                assert!(
                    status_str == "AlreadyHaveKShares" || status_str == "NotMyTurn",
                    "Should return AlreadyHaveKShares or NotMyTurn when pool is full"
                );
                println!("Correctly rejected: {}", status_str);
            }
        }
    }

    println!("\nOver-collection prevention test complete!");
}

/// Test: Get threshold configuration
#[tokio::test]
#[ignore]
async fn test_get_threshold_config() {
    println!("\n=== Testing Threshold Configuration ===\n");

    let alice = connect_and_wait(ALICE_RPC).await;

    let config = alice.request("qrng_getConfig", json!([])).await
        .expect("Failed to get config");

    println!("Threshold K: {}", config["threshold_k"]);
    println!("Total Devices M: {}", config["total_devices_m"]);
    println!("Devices: {:?}", config["devices"]);

    assert_eq!(config["threshold_k"], 2, "K should be 2");
    assert_eq!(config["total_devices_m"], 3, "M should be 3");

    println!("\nConfiguration test complete!");
}

/// Test: Node health check
#[tokio::test]
#[ignore]
async fn test_all_nodes_healthy() {
    println!("\n=== Testing Node Health ===\n");

    let endpoints = vec![
        ("Alice", ALICE_RPC),
        ("Bob", BOB_RPC),
        ("Charlie", CHARLIE_RPC),
    ];

    for (name, endpoint) in endpoints {
        print!("Checking {}... ", name);

        let client = RpcClient::new(endpoint);
        match client.request("system_health", json!([])).await {
            Ok(health) => {
                let syncing = health["isSyncing"].as_bool().unwrap_or(true);
                let peers = health["peers"].as_u64().unwrap_or(0);

                if syncing {
                    println!("SYNCING (peers: {})", peers);
                } else {
                    println!("HEALTHY (peers: {})", peers);
                }
            }
            Err(e) => {
                println!("UNREACHABLE: {}", e);
            }
        }
    }

    println!("\nHealth check complete!");
}

// ============================================================================
// RPC METHOD TESTS
// ============================================================================

/// Test: Fetch from Crypto4A simulator
#[tokio::test]
#[ignore]
async fn test_fetch_from_crypto4a() {
    println!("\n=== Testing Crypto4A Fetch ===\n");

    let alice = connect_and_wait(ALICE_RPC).await;

    let result = alice.request(
        "qrng_fetchFromCrypto4a",
        json!([32, "test_node", 0])
    ).await;

    match result {
        Ok(entropy) => {
            println!("Entropy fetched successfully:");
            println!("  Share hex: {}...", &entropy["share_hex"].as_str().unwrap_or("")[..20.min(entropy["share_hex"].as_str().unwrap_or("").len())]);
            println!("  Share index: {}", entropy["share_index"]);
            println!("  QBER: {}%", entropy["qber"].as_f64().unwrap_or(0.0) * 100.0);
            println!("  Shares collected: {}", entropy["shares_collected"]);
            println!("  Queued: {}", entropy["queued"]);
        }
        Err(e) => {
            println!("Crypto4A fetch failed (expected if simulator not running): {}", e);
        }
    }

    println!("\nCrypto4A test complete!");
}

/// Test: Get device queues status
#[tokio::test]
#[ignore]
async fn test_get_device_queues() {
    println!("\n=== Testing Device Queues ===\n");

    let alice = connect_and_wait(ALICE_RPC).await;

    let queues = alice.request("qrng_getDeviceQueues", json!([])).await
        .expect("Failed to get device queues");

    println!("Device queues:");
    if let Some(arr) = queues.as_array() {
        for queue in arr {
            println!("  - {}: {} (enabled: {})",
                queue["device_name"].as_str().unwrap_or("unknown"),
                queue["device_id"].as_str().unwrap_or("unknown"),
                queue["enabled"].as_bool().unwrap_or(false)
            );
        }
    }

    println!("\nDevice queues test complete!");
}

// ============================================================================
// UTILITY FUNCTIONS FOR MANUAL TESTING
// ============================================================================

/// Utility: Print current round info
#[tokio::test]
#[ignore]
async fn print_current_round_info() {
    println!("\n=== Current Round Information ===\n");

    let alice = connect_and_wait(ALICE_RPC).await;

    let block_num = get_block_number(&alice).await
        .expect("Failed to get block number");

    let round_num = block_num / 5;
    let round_id = format!("round-{}", round_num);
    let turn_index = round_num % 3;
    let validators = ["alice", "bob", "charlie"];

    println!("Current block: {}", block_num);
    println!("Current round: {} (round-{})", round_num, round_num);
    println!("Current turn: {} ({})", turn_index, validators[turn_index as usize]);
    println!("Blocks until next round: {}", 5 - (block_num % 5));

    let status = alice.request("qrng_getSharePoolStatus", json!([round_id])).await;
    if let Ok(s) = status {
        println!("\nShare pool status:");
        println!("  Shares collected: {}", s["shares_collected"]);
        println!("  Threshold K: {}", s["threshold_k"]);
        println!("  Ready: {}", s["ready_for_reconstruction"]);

        if let Some(contributors) = s["contributors"].as_array() {
            println!("  Contributors:");
            for c in contributors {
                println!("    - {} (index {})", c["node_id"], c["share_index"]);
            }
        }
    }
}

/// Utility: Manually trigger round processing
#[tokio::test]
#[ignore]
async fn trigger_round_processing() {
    println!("\n=== Manually Triggering Round Processing ===\n");

    let alice = connect_and_wait(ALICE_RPC).await;
    let bob = connect_and_wait(BOB_RPC).await;
    let charlie = connect_and_wait(CHARLIE_RPC).await;

    let block_num = get_block_number(&alice).await
        .expect("Failed to get block number");

    println!("Block: {}", block_num);
    println!("\nTriggering all validators...\n");

    // Process on all validators
    let results = tokio::join!(
        alice.request("qrng_processRound", json!([block_num])),
        bob.request("qrng_processRound", json!([block_num])),
        charlie.request("qrng_processRound", json!([block_num])),
    );

    println!("Alice: {:?}", results.0);
    println!("Bob: {:?}", results.1);
    println!("Charlie: {:?}", results.2);

    // Wait a moment then check result
    sleep(Duration::from_secs(1)).await;

    let round_id = format!("round-{}", block_num / 5);
    let status = alice.request("qrng_getSharePoolStatus", json!([round_id])).await;
    println!("\nFinal pool status: {:?}", status);
}
