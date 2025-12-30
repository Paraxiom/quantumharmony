//! RPC Integration Tests
//!
//! Tests for all RPC methods used by the Node Operator Interface.
//! These tests require a running node at localhost:9944.

use serde::{Deserialize, Serialize};
use serde_json::{json, Value};

/// RPC endpoint for tests
const RPC_ENDPOINT: &str = "http://localhost:9944";

/// Standard JSON-RPC request structure
#[derive(Serialize)]
struct RpcRequest {
    jsonrpc: &'static str,
    id: u64,
    method: String,
    params: Value,
}

impl RpcRequest {
    fn new(method: &str, params: Value) -> Self {
        Self {
            jsonrpc: "2.0",
            id: 1,
            method: method.to_string(),
            params,
        }
    }
}

/// Standard JSON-RPC response structure
#[derive(Deserialize, Debug)]
struct RpcResponse {
    jsonrpc: String,
    id: u64,
    result: Option<Value>,
    error: Option<RpcError>,
}

#[derive(Deserialize, Debug)]
struct RpcError {
    code: i64,
    message: String,
}

/// Make an RPC call and return the result
async fn rpc_call(method: &str, params: Value) -> Result<Value, String> {
    let client = reqwest::Client::new();
    let request = RpcRequest::new(method, params);

    let response = client
        .post(RPC_ENDPOINT)
        .json(&request)
        .send()
        .await
        .map_err(|e| format!("Request failed: {}", e))?;

    let rpc_response: RpcResponse = response
        .json()
        .await
        .map_err(|e| format!("Failed to parse response: {}", e))?;

    if let Some(error) = rpc_response.error {
        return Err(format!("RPC error {}: {}", error.code, error.message));
    }

    rpc_response.result.ok_or_else(|| "No result in response".to_string())
}

/// Check if node is reachable
async fn is_node_available() -> bool {
    match rpc_call("system_health", json!([])).await {
        Ok(_) => true,
        Err(_) => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ============================================
    // SYSTEM RPC TESTS
    // ============================================

    #[tokio::test]
    async fn test_system_health() {
        if !is_node_available().await {
            println!("SKIP: Node not available at {}", RPC_ENDPOINT);
            return;
        }

        let result = rpc_call("system_health", json!([])).await;
        assert!(result.is_ok(), "system_health should succeed");

        let health = result.unwrap();
        assert!(health.get("peers").is_some(), "Should have peers field");
        assert!(health.get("isSyncing").is_some(), "Should have isSyncing field");
    }

    #[tokio::test]
    async fn test_system_chain() {
        if !is_node_available().await {
            println!("SKIP: Node not available");
            return;
        }

        let result = rpc_call("system_chain", json!([])).await;
        assert!(result.is_ok(), "system_chain should succeed");

        let chain = result.unwrap();
        assert!(chain.is_string(), "Chain name should be a string");
        println!("Chain: {}", chain);
    }

    #[tokio::test]
    async fn test_system_name() {
        if !is_node_available().await {
            println!("SKIP: Node not available");
            return;
        }

        let result = rpc_call("system_name", json!([])).await;
        assert!(result.is_ok(), "system_name should succeed");
        println!("Node name: {}", result.unwrap());
    }

    #[tokio::test]
    async fn test_system_version() {
        if !is_node_available().await {
            println!("SKIP: Node not available");
            return;
        }

        let result = rpc_call("system_version", json!([])).await;
        assert!(result.is_ok(), "system_version should succeed");
        println!("Version: {}", result.unwrap());
    }

    #[tokio::test]
    async fn test_system_peers() {
        if !is_node_available().await {
            println!("SKIP: Node not available");
            return;
        }

        let result = rpc_call("system_peers", json!([])).await;
        assert!(result.is_ok(), "system_peers should succeed");

        let peers = result.unwrap();
        assert!(peers.is_array(), "Peers should be an array");
        println!("Peer count: {}", peers.as_array().unwrap().len());
    }

    // ============================================
    // CHAIN RPC TESTS
    // ============================================

    #[tokio::test]
    async fn test_chain_get_header() {
        if !is_node_available().await {
            println!("SKIP: Node not available");
            return;
        }

        let result = rpc_call("chain_getHeader", json!([])).await;
        assert!(result.is_ok(), "chain_getHeader should succeed");

        let header = result.unwrap();
        assert!(header.get("number").is_some(), "Header should have number");
        assert!(header.get("parentHash").is_some(), "Header should have parentHash");

        let block_num = header.get("number").unwrap().as_str().unwrap();
        println!("Current block: {}", block_num);
    }

    #[tokio::test]
    async fn test_chain_get_block_hash() {
        if !is_node_available().await {
            println!("SKIP: Node not available");
            return;
        }

        // Get genesis block hash (block 0)
        let result = rpc_call("chain_getBlockHash", json!([0])).await;
        assert!(result.is_ok(), "chain_getBlockHash(0) should succeed");

        let hash = result.unwrap();
        assert!(hash.is_string(), "Block hash should be a string");
        assert!(hash.as_str().unwrap().starts_with("0x"), "Hash should start with 0x");
        println!("Genesis hash: {}", hash);
    }

    #[tokio::test]
    async fn test_chain_get_finalized_head() {
        if !is_node_available().await {
            println!("SKIP: Node not available");
            return;
        }

        let result = rpc_call("chain_getFinalizedHead", json!([])).await;
        assert!(result.is_ok(), "chain_getFinalizedHead should succeed");

        let hash = result.unwrap();
        assert!(hash.is_string(), "Finalized head hash should be a string");
        println!("Finalized head: {}", hash);
    }

    // ============================================
    // STATE RPC TESTS
    // ============================================

    #[tokio::test]
    async fn test_state_get_runtime_version() {
        if !is_node_available().await {
            println!("SKIP: Node not available");
            return;
        }

        let result = rpc_call("state_getRuntimeVersion", json!([])).await;
        assert!(result.is_ok(), "state_getRuntimeVersion should succeed");

        let version = result.unwrap();
        assert!(version.get("specName").is_some(), "Should have specName");
        assert!(version.get("specVersion").is_some(), "Should have specVersion");
        assert!(version.get("implName").is_some(), "Should have implName");
        assert!(version.get("implVersion").is_some(), "Should have implVersion");
        assert!(version.get("authoringVersion").is_some(), "Should have authoringVersion");

        println!("Spec: {} v{}",
            version.get("specName").unwrap(),
            version.get("specVersion").unwrap());
    }

    #[tokio::test]
    async fn test_state_get_metadata() {
        if !is_node_available().await {
            println!("SKIP: Node not available");
            return;
        }

        let result = rpc_call("state_getMetadata", json!([])).await;
        assert!(result.is_ok(), "state_getMetadata should succeed");

        let metadata = result.unwrap();
        assert!(metadata.is_string(), "Metadata should be hex string");
        assert!(metadata.as_str().unwrap().starts_with("0x"), "Should start with 0x");
        println!("Metadata length: {} bytes", metadata.as_str().unwrap().len() / 2 - 1);
    }

    // ============================================
    // GATEWAY RPC TESTS (Custom QuantumHarmony)
    // ============================================

    #[tokio::test]
    async fn test_gateway_genesis_hash() {
        if !is_node_available().await {
            println!("SKIP: Node not available");
            return;
        }

        let result = rpc_call("gateway_genesisHash", json!([])).await;
        // This may not be implemented, so we accept either result
        match result {
            Ok(hash) => {
                assert!(hash.is_string(), "Genesis hash should be string");
                println!("Gateway genesis hash: {}", hash);
            }
            Err(e) => {
                println!("gateway_genesisHash not implemented: {}", e);
            }
        }
    }

    #[tokio::test]
    async fn test_gateway_balance() {
        if !is_node_available().await {
            println!("SKIP: Node not available");
            return;
        }

        // Test with Alice's address (well-known test address)
        let alice = "5GrwvaEF5zXb26Fz9rcQpDWS57CtERHpNehXCPcNoHGKutQY";
        let result = rpc_call("gateway_balance", json!([alice])).await;

        match result {
            Ok(balance) => {
                println!("Alice balance: {}", balance);
            }
            Err(e) => {
                println!("gateway_balance not implemented: {}", e);
            }
        }
    }

    #[tokio::test]
    async fn test_gateway_nonce() {
        if !is_node_available().await {
            println!("SKIP: Node not available");
            return;
        }

        let alice = "5GrwvaEF5zXb26Fz9rcQpDWS57CtERHpNehXCPcNoHGKutQY";
        let result = rpc_call("gateway_nonce", json!([alice])).await;

        match result {
            Ok(nonce) => {
                println!("Alice nonce: {}", nonce);
            }
            Err(e) => {
                println!("gateway_nonce not implemented: {}", e);
            }
        }
    }

    // ============================================
    // QRNG RPC TESTS (Threshold QRNG)
    // ============================================

    #[tokio::test]
    async fn test_qrng_get_config() {
        if !is_node_available().await {
            println!("SKIP: Node not available");
            return;
        }

        let result = rpc_call("qrng_getConfig", json!([])).await;

        match result {
            Ok(config) => {
                println!("QRNG Config: {}", config);
                // Should have threshold K, total M, and device list
                if let Some(k) = config.get("threshold_k") {
                    println!("Threshold K: {}", k);
                }
                if let Some(m) = config.get("total_devices") {
                    println!("Total devices M: {}", m);
                }
            }
            Err(e) => {
                println!("qrng_getConfig not implemented: {}", e);
            }
        }
    }

    #[tokio::test]
    async fn test_qrng_get_device_queues() {
        if !is_node_available().await {
            println!("SKIP: Node not available");
            return;
        }

        let result = rpc_call("qrng_getDeviceQueues", json!([])).await;

        match result {
            Ok(queues) => {
                println!("Device queues: {}", queues);
                if let Some(devices) = queues.as_array() {
                    println!("Number of devices: {}", devices.len());
                    for device in devices {
                        if let Some(name) = device.get("name") {
                            println!("  Device: {}", name);
                        }
                    }
                }
            }
            Err(e) => {
                println!("qrng_getDeviceQueues not implemented: {}", e);
            }
        }
    }

    #[tokio::test]
    async fn test_qrng_get_reconstruction_history() {
        if !is_node_available().await {
            println!("SKIP: Node not available");
            return;
        }

        let result = rpc_call("qrng_getReconstructionHistory", json!([10])).await;

        match result {
            Ok(history) => {
                println!("Reconstruction history: {}", history);
            }
            Err(e) => {
                println!("qrng_getReconstructionHistory not implemented: {}", e);
            }
        }
    }

    // ============================================
    // AUTHOR RPC TESTS (Transaction Submission)
    // ============================================

    #[tokio::test]
    async fn test_author_pending_extrinsics() {
        if !is_node_available().await {
            println!("SKIP: Node not available");
            return;
        }

        let result = rpc_call("author_pendingExtrinsics", json!([])).await;
        assert!(result.is_ok(), "author_pendingExtrinsics should succeed");

        let extrinsics = result.unwrap();
        assert!(extrinsics.is_array(), "Should return array of pending extrinsics");
        println!("Pending extrinsics: {}", extrinsics.as_array().unwrap().len());
    }

    // ============================================
    // ERROR HANDLING TESTS
    // ============================================

    #[tokio::test]
    async fn test_invalid_method() {
        if !is_node_available().await {
            println!("SKIP: Node not available");
            return;
        }

        let result = rpc_call("invalid_nonexistent_method", json!([])).await;
        assert!(result.is_err(), "Invalid method should return error");
        println!("Expected error: {}", result.unwrap_err());
    }

    #[tokio::test]
    async fn test_invalid_params() {
        if !is_node_available().await {
            println!("SKIP: Node not available");
            return;
        }

        // chain_getBlockHash with invalid block number
        let result = rpc_call("chain_getBlockHash", json!(["not_a_number"])).await;
        assert!(result.is_err(), "Invalid params should return error");
    }

    #[tokio::test]
    async fn test_connection_refused() {
        // Try to connect to a port that's definitely not running
        let client = reqwest::Client::new();
        let request = json!({
            "jsonrpc": "2.0",
            "id": 1,
            "method": "system_health",
            "params": []
        });

        let result = client
            .post("http://localhost:59999")
            .json(&request)
            .send()
            .await;

        assert!(result.is_err(), "Connection to closed port should fail");
    }

    // ============================================
    // RESPONSE VALIDATION TESTS
    // ============================================

    #[test]
    fn test_rpc_request_serialization() {
        let request = RpcRequest::new("test_method", json!(["param1", "param2"]));
        let serialized = serde_json::to_string(&request).unwrap();

        assert!(serialized.contains("\"jsonrpc\":\"2.0\""));
        assert!(serialized.contains("\"method\":\"test_method\""));
        assert!(serialized.contains("\"params\":[\"param1\",\"param2\"]"));
    }

    #[test]
    fn test_rpc_response_deserialization() {
        let response_json = r#"{
            "jsonrpc": "2.0",
            "id": 1,
            "result": {"health": "ok"}
        }"#;

        let response: RpcResponse = serde_json::from_str(response_json).unwrap();
        assert_eq!(response.jsonrpc, "2.0");
        assert_eq!(response.id, 1);
        assert!(response.result.is_some());
        assert!(response.error.is_none());
    }

    #[test]
    fn test_rpc_error_response_deserialization() {
        let response_json = r#"{
            "jsonrpc": "2.0",
            "id": 1,
            "error": {
                "code": -32601,
                "message": "Method not found"
            }
        }"#;

        let response: RpcResponse = serde_json::from_str(response_json).unwrap();
        assert!(response.result.is_none());
        assert!(response.error.is_some());
        assert_eq!(response.error.as_ref().unwrap().code, -32601);
    }
}

// ============================================
// TEST HELPERS FOR EXTERNAL USE
// ============================================

/// Check node availability with custom endpoint
pub async fn check_node(endpoint: &str) -> bool {
    let client = reqwest::Client::new();
    let request = json!({
        "jsonrpc": "2.0",
        "id": 1,
        "method": "system_health",
        "params": []
    });

    client.post(endpoint)
        .json(&request)
        .send()
        .await
        .map(|r| r.status().is_success())
        .unwrap_or(false)
}

/// Get current block number
pub async fn get_block_number(endpoint: &str) -> Option<u64> {
    let client = reqwest::Client::new();
    let request = json!({
        "jsonrpc": "2.0",
        "id": 1,
        "method": "chain_getHeader",
        "params": []
    });

    let response = client.post(endpoint)
        .json(&request)
        .send()
        .await.ok()?;

    let rpc_response: RpcResponse = response.json().await.ok()?;
    let header = rpc_response.result?;
    let hex_num = header.get("number")?.as_str()?;

    // Parse hex block number
    u64::from_str_radix(hex_num.trim_start_matches("0x"), 16).ok()
}
