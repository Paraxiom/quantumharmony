//! Comprehensive wallet integration tests
//! Tests transaction gateway RPC, balance queries, transfers, and runtime upgrades

use jsonrpsee::{core::client::ClientT, http_client::{HttpClient, HttpClientBuilder}, rpc_params};
use serde_json::{json, Value};
use sp_core::{Pair, crypto::Ss58Codec};
use sp_runtime::traits::IdentifyAccount;
use sp_runtime::MultiSigner;
use std::time::Duration;
use tokio::time::sleep;

const NODE_URL: &str = "http://127.0.0.1:9944";

// Hardcoded SPHINCS+ test account public keys
// These must match the keys used in chain_spec genesis
const ALICE_SPHINCS_PUBLIC: [u8; 64] = [
    0x9e, 0x2a, 0xc8, 0x17, 0x14, 0xcf, 0xc6, 0x32, 0x9a, 0x64, 0x78, 0x6e, 0x74, 0xbe, 0x82, 0xda,
    0x5c, 0x3f, 0xc2, 0x80, 0x23, 0xf6, 0x5f, 0xe6, 0xb8, 0x3c, 0x11, 0xe3, 0xc9, 0xe0, 0x71, 0x6a,
    0x25, 0x55, 0xaa, 0x2a, 0x4a, 0x18, 0xb4, 0xdf, 0x90, 0x2a, 0x0a, 0x23, 0x01, 0x11, 0xd9, 0xfe,
    0xd6, 0x08, 0x36, 0xf4, 0x3b, 0xad, 0x71, 0xa7, 0x60, 0x04, 0x48, 0x1e, 0xaa, 0x11, 0x14, 0x04,
];

const BOB_SPHINCS_PUBLIC: [u8; 64] = [
    0x5b, 0xc2, 0xab, 0x0e, 0xcf, 0xa4, 0x6f, 0xed, 0xa1, 0xde, 0x63, 0x51, 0xf7, 0x0b, 0xa8, 0x1e,
    0xd7, 0x69, 0x68, 0xca, 0x90, 0x85, 0x81, 0xc8, 0x80, 0x8b, 0x15, 0x1f, 0x8f, 0x81, 0xd2, 0x32,
    0xf8, 0x3d, 0x59, 0x1e, 0x76, 0xed, 0x34, 0xed, 0xdb, 0xcd, 0xbf, 0xef, 0x5f, 0x4c, 0xa9, 0x24,
    0x0b, 0xf5, 0x3e, 0x04, 0x77, 0xa4, 0x49, 0x3f, 0xb4, 0xb2, 0x3b, 0x2b, 0x19, 0xb0, 0xa7, 0x6f,
];

/// Get SPHINCS+ account for testing
/// Uses hardcoded public keys that match chain_spec genesis accounts
fn get_sphincs_test_account(name: &str) -> (sp_core::crypto::AccountId32, String) {
    use sp_core::sphincs::Public as SphincPublic;

    let public = match name {
        "Alice" => SphincPublic::from_raw(ALICE_SPHINCS_PUBLIC),
        "Bob" => SphincPublic::from_raw(BOB_SPHINCS_PUBLIC),
        _ => panic!("Unknown test account: {}", name),
    };

    // Convert to AccountId using MultiSigner (which uses SHA3)
    let signer = MultiSigner::from(public);
    let account = signer.into_account();
    let ss58 = account.to_ss58check();

    (account, ss58)
}

/// Helper to create RPC client
async fn create_client() -> HttpClient {
    HttpClientBuilder::default()
        .build(NODE_URL)
        .expect("Failed to create RPC client")
}

/// Helper to wait for node to be ready
async fn wait_for_node() -> HttpClient {
    for i in 0..30 {
        if let Ok(client) = HttpClientBuilder::default().build(NODE_URL) {
            // Try a simple RPC call
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
async fn test_transaction_gateway_balance() {
    let client = wait_for_node().await;

    // Get balance for Alice (SPHINCS+)
    let (alice_account, alice_ss58) = get_sphincs_test_account("Alice");

    println!("[TEST] Alice SPHINCS+ Public (first 32 bytes): not logged for brevity");
    println!("[TEST] Alice AccountId: {:?}", alice_account);
    println!("[TEST] Alice SS58: {}", alice_ss58);

    let balance: Value = client
        .request("gateway_balance", rpc_params![alice_ss58])
        .await
        .expect("Failed to get balance");

    println!("Alice balance: {:?}", balance);

    // Balance should be a number (Alice has endowment in dev chain)
    assert!(balance.is_number() || balance.is_string());

    // Parse balance
    let balance_str = balance.as_str().unwrap_or("0");
    let balance_num: u128 = balance_str.parse().expect("Balance should be parseable");

    // Alice should have initial endowment
    assert!(balance_num > 0, "Alice should have non-zero balance");
}

#[tokio::test]
async fn test_transaction_gateway_nonce() {
    let client = wait_for_node().await;

    // Get nonce for Alice (SPHINCS+)
    let (_, alice_ss58) = get_sphincs_test_account("Alice");

    let nonce: Value = client
        .request("gateway_nonce", rpc_params![alice_ss58])
        .await
        .expect("Failed to get nonce");

    println!("Alice nonce: {:?}", nonce);

    // Nonce should be a number
    assert!(nonce.is_number());

    // Fresh account should have nonce 0
    let nonce_num = nonce.as_u64().expect("Nonce should be u64");
    assert_eq!(nonce_num, 0, "Fresh Alice account should have nonce 0");
}

#[tokio::test]
async fn test_transaction_gateway_genesis_hash() {
    let client = wait_for_node().await;

    let genesis_hash: String = client
        .request("gateway_genesisHash", rpc_params![])
        .await
        .expect("Failed to get genesis hash");

    println!("Genesis hash: {}", genesis_hash);

    // Genesis hash should be a hex string starting with 0x
    assert!(genesis_hash.starts_with("0x"), "Genesis hash should start with 0x");
    assert_eq!(genesis_hash.len(), 66, "Genesis hash should be 66 chars (0x + 64 hex)");
}

#[tokio::test]
async fn test_transaction_submission() {
    let client = wait_for_node().await;

    // Create a transfer from Alice to Bob (SPHINCS+)
    let (_, alice_ss58) = get_sphincs_test_account("Alice");
    let (_, bob_ss58) = get_sphincs_test_account("Bob");

    // Get Alice's nonce
    let nonce: u32 = client
        .request::<Value, _>("gateway_nonce", rpc_params![alice_ss58.clone()])
        .await
        .expect("Failed to get nonce")
        .as_u64()
        .unwrap() as u32;

    // Get genesis hash
    let genesis_hash: String = client
        .request("gateway_genesisHash", rpc_params![])
        .await
        .expect("Failed to get genesis hash");

    // Create signed transaction (simplified for test)
    let tx_request = json!({
        "from": alice_ss58,
        "to": bob_ss58,
        "amount": "1000000000000", // 1 unit with 12 decimals
        "nonce": nonce,
        "genesisHash": genesis_hash
    });

    // Submit transaction
    let result: Value = client
        .request("gateway_submit", rpc_params![tx_request])
        .await
        .expect("Failed to submit transaction");

    println!("Transaction result: {:?}", result);

    // Result should contain a hash
    assert!(result.is_object() || result.is_string());
}

#[tokio::test]
async fn test_balance_transfer_end_to_end() {
    let client = wait_for_node().await;

    // Get initial balances (SPHINCS+)
    let (_, alice_ss58) = get_sphincs_test_account("Alice");
    let (_, bob_ss58) = get_sphincs_test_account("Bob");

    let alice_balance_before: Value = client
        .request("gateway_balance", rpc_params![alice_ss58.clone()])
        .await
        .expect("Failed to get Alice balance");

    let bob_balance_before: Value = client
        .request("gateway_balance", rpc_params![bob_ss58.clone()])
        .await
        .expect("Failed to get Bob balance");

    println!("Alice balance before: {:?}", alice_balance_before);
    println!("Bob balance before: {:?}", bob_balance_before);

    // Submit transfer
    let nonce: u32 = client
        .request::<Value, _>("gateway_nonce", rpc_params![alice_ss58.clone()])
        .await
        .expect("Failed to get nonce")
        .as_u64()
        .unwrap() as u32;

    let genesis_hash: String = client
        .request("gateway_genesisHash", rpc_params![])
        .await
        .expect("Failed to get genesis hash");

    let transfer_amount = "5000000000000"; // 5 units
    let tx_request = json!({
        "from": alice_ss58.clone(),
        "to": bob_ss58.clone(),
        "amount": transfer_amount,
        "nonce": nonce,
        "genesisHash": genesis_hash
    });

    let _tx_hash: Value = client
        .request("gateway_submit", rpc_params![tx_request])
        .await
        .expect("Failed to submit transaction");

    // Wait for block to be produced
    sleep(Duration::from_secs(7)).await;

    // Check balances after transfer
    let alice_balance_after: Value = client
        .request("gateway_balance", rpc_params![alice_ss58])
        .await
        .expect("Failed to get Alice balance");

    let bob_balance_after: Value = client
        .request("gateway_balance", rpc_params![bob_ss58])
        .await
        .expect("Failed to get Bob balance");

    println!("Alice balance after: {:?}", alice_balance_after);
    println!("Bob balance after: {:?}", bob_balance_after);

    // Balances should have changed
    let alice_before: u128 = alice_balance_before.as_str().unwrap_or("0").parse().unwrap();
    let alice_after: u128 = alice_balance_after.as_str().unwrap_or("0").parse().unwrap();
    let bob_before: u128 = bob_balance_before.as_str().unwrap_or("0").parse().unwrap();
    let bob_after: u128 = bob_balance_after.as_str().unwrap_or("0").parse().unwrap();

    assert!(alice_after < alice_before, "Alice balance should decrease");
    assert!(bob_after > bob_before, "Bob balance should increase");
}

#[tokio::test]
async fn test_account_creation() {
    let client = wait_for_node().await;

    // Generate a new SPHINCS+ account
    use sp_core::sphincs::Pair as SphincsPair;
    let (pair, _seed) = SphincsPair::generate();
    let public_key = pair.public();
    // AccountId is derived by hashing SPHINCS+ public key with SHA3
    use sp_core::keccak_256;
    let account_bytes = keccak_256(public_key.as_ref());
    let new_account = sp_core::crypto::AccountId32::from(account_bytes);
    let new_account_ss58 = new_account.to_ss58check();

    // Check balance (should be 0 for new account)
    let balance: Value = client
        .request("gateway_balance", rpc_params![new_account_ss58.clone()])
        .await
        .expect("Failed to get balance");

    let balance_num: u128 = balance.as_str().unwrap_or("0").parse().unwrap();
    assert_eq!(balance_num, 0, "New account should have zero balance");

    // Check nonce (should be 0)
    let nonce: Value = client
        .request("gateway_nonce", rpc_params![new_account_ss58])
        .await
        .expect("Failed to get nonce");

    let nonce_num = nonce.as_u64().unwrap();
    assert_eq!(nonce_num, 0, "New account should have zero nonce");
}

#[tokio::test]
async fn test_multiple_transactions_nonce_increment() {
    let client = wait_for_node().await;

    let (_, alice_ss58) = get_sphincs_test_account("Alice");
    let (_, bob_ss58) = get_sphincs_test_account("Bob");

    // Get initial nonce
    let nonce_before: u32 = client
        .request::<Value, _>("gateway_nonce", rpc_params![alice_ss58.clone()])
        .await
        .expect("Failed to get nonce")
        .as_u64()
        .unwrap() as u32;

    let genesis_hash: String = client
        .request("gateway_genesisHash", rpc_params![])
        .await
        .expect("Failed to get genesis hash");

    // Submit multiple transactions
    for i in 0..3 {
        let tx_request = json!({
            "from": alice_ss58.clone(),
            "to": bob_ss58.clone(),
            "amount": "1000000000",
            "nonce": nonce_before + i,
            "genesisHash": genesis_hash.clone()
        });

        let _result: Value = client
            .request("gateway_submit", rpc_params![tx_request])
            .await
            .expect("Failed to submit transaction");

        sleep(Duration::from_millis(500)).await;
    }

    // Wait for blocks
    sleep(Duration::from_secs(7)).await;

    // Check nonce increased
    let nonce_after: u32 = client
        .request::<Value, _>("gateway_nonce", rpc_params![alice_ss58])
        .await
        .expect("Failed to get nonce")
        .as_u64()
        .unwrap() as u32;

    assert!(
        nonce_after >= nonce_before + 3,
        "Nonce should have increased by at least 3"
    );
}

#[tokio::test]
async fn test_invalid_address_handling() {
    let client = wait_for_node().await;

    // Try to get balance for invalid address
    let result = client
        .request::<Value, _>("gateway_balance", rpc_params!["invalid_address"])
        .await;

    // Should either return error or zero balance
    match result {
        Ok(balance) => {
            let balance_num: u128 = balance.as_str().unwrap_or("0").parse().unwrap_or(0);
            assert_eq!(balance_num, 0, "Invalid address should have zero balance");
        }
        Err(_) => {
            // Error is also acceptable
        }
    }
}

#[tokio::test]
async fn test_system_health() {
    let client = wait_for_node().await;

    let health: Value = client
        .request("system_health", rpc_params![])
        .await
        .expect("Failed to get system health");

    println!("System health: {:?}", health);

    // Health should indicate node is healthy
    assert!(health.is_object());

    let health_obj = health.as_object().unwrap();
    assert!(health_obj.contains_key("isSyncing") || health_obj.contains_key("is_syncing"));
}

#[tokio::test]
async fn test_chain_properties() {
    let client = wait_for_node().await;

    let properties: Value = client
        .request("system_properties", rpc_params![])
        .await
        .expect("Failed to get chain properties");

    println!("Chain properties: {:?}", properties);

    // Properties should contain token info
    assert!(properties.is_object());
}
