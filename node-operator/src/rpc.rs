//! RPC client for communicating with the QuantumHarmony node
//!
//! Provides a secure proxy for node RPC calls and status queries.

use serde::{Deserialize, Serialize};
use tracing::{debug, error};

/// Node status from RPC queries
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NodeStatus {
    pub block_height: u64,
    pub peers: u32,
    pub syncing: bool,
    pub chain_name: Option<String>,
    pub node_name: Option<String>,
    pub version: Option<String>,
}

/// RPC request structure
#[derive(Debug, Serialize)]
struct RpcRequest {
    jsonrpc: &'static str,
    id: u32,
    method: String,
    params: serde_json::Value,
}

/// RPC response structure
#[derive(Debug, Deserialize)]
struct RpcResponse {
    jsonrpc: String,
    id: u32,
    result: Option<serde_json::Value>,
    error: Option<RpcError>,
}

#[derive(Debug, Deserialize)]
struct RpcError {
    code: i32,
    message: String,
}

/// Get comprehensive node status
pub async fn get_node_status(rpc_port: u16) -> Result<NodeStatus, String> {
    let rpc_url = format!("http://localhost:{}", rpc_port);
    let client = reqwest::Client::builder()
        .timeout(std::time::Duration::from_secs(5))
        .build()
        .map_err(|e| format!("Failed to create HTTP client: {}", e))?;

    // Get health
    let health = call_rpc(&client, &rpc_url, "system_health", serde_json::json!([])).await?;
    let peers = health
        .get("peers")
        .and_then(|v| v.as_u64())
        .unwrap_or(0) as u32;
    let syncing = health
        .get("isSyncing")
        .and_then(|v| v.as_bool())
        .unwrap_or(false);

    // Get block header
    let header = call_rpc(&client, &rpc_url, "chain_getHeader", serde_json::json!([])).await?;
    let block_height = header
        .get("number")
        .and_then(|v| v.as_str())
        .and_then(|s| u64::from_str_radix(s.trim_start_matches("0x"), 16).ok())
        .unwrap_or(0);

    // Get chain name
    let chain_name = call_rpc(&client, &rpc_url, "system_chain", serde_json::json!([]))
        .await
        .ok()
        .and_then(|v| v.as_str().map(|s| s.to_string()));

    // Get node name
    let node_name = call_rpc(&client, &rpc_url, "system_name", serde_json::json!([]))
        .await
        .ok()
        .and_then(|v| v.as_str().map(|s| s.to_string()));

    // Get version
    let version = call_rpc(&client, &rpc_url, "system_version", serde_json::json!([]))
        .await
        .ok()
        .and_then(|v| v.as_str().map(|s| s.to_string()));

    Ok(NodeStatus {
        block_height,
        peers,
        syncing,
        chain_name,
        node_name,
        version,
    })
}

/// Forward an RPC request to the node
pub async fn forward_rpc(rpc_port: u16, body: serde_json::Value) -> Result<serde_json::Value, String> {
    let rpc_url = format!("http://localhost:{}", rpc_port);
    let client = reqwest::Client::builder()
        .timeout(std::time::Duration::from_secs(30))
        .build()
        .map_err(|e| format!("Failed to create HTTP client: {}", e))?;

    let response = client
        .post(&rpc_url)
        .json(&body)
        .send()
        .await
        .map_err(|e| format!("RPC request failed: {}", e))?;

    let result: serde_json::Value = response
        .json()
        .await
        .map_err(|e| format!("Failed to parse RPC response: {}", e))?;

    Ok(result)
}

/// Call a specific RPC method
async fn call_rpc(
    client: &reqwest::Client,
    url: &str,
    method: &str,
    params: serde_json::Value,
) -> Result<serde_json::Value, String> {
    let request = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 1,
        "method": method,
        "params": params
    });

    debug!("RPC call: {} -> {}", url, method);

    let response = client
        .post(url)
        .json(&request)
        .send()
        .await
        .map_err(|e| format!("RPC request failed: {}", e))?;

    let result: RpcResponse = response
        .json()
        .await
        .map_err(|e| format!("Failed to parse RPC response: {}", e))?;

    if let Some(error) = result.error {
        error!("RPC error: {} (code: {})", error.message, error.code);
        return Err(format!("RPC error: {}", error.message));
    }

    result.result.ok_or_else(|| "Empty RPC result".to_string())
}

/// Get runtime version
pub async fn get_runtime_version(rpc_port: u16) -> Result<RuntimeVersion, String> {
    let rpc_url = format!("http://localhost:{}", rpc_port);
    let client = reqwest::Client::builder()
        .timeout(std::time::Duration::from_secs(5))
        .build()
        .map_err(|e| format!("Failed to create HTTP client: {}", e))?;

    let result = call_rpc(&client, &rpc_url, "state_getRuntimeVersion", serde_json::json!([])).await?;

    Ok(RuntimeVersion {
        spec_name: result
            .get("specName")
            .and_then(|v| v.as_str())
            .unwrap_or("unknown")
            .to_string(),
        spec_version: result
            .get("specVersion")
            .and_then(|v| v.as_u64())
            .unwrap_or(0) as u32,
        impl_version: result
            .get("implVersion")
            .and_then(|v| v.as_u64())
            .unwrap_or(0) as u32,
    })
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RuntimeVersion {
    pub spec_name: String,
    pub spec_version: u32,
    pub impl_version: u32,
}

/// Submit a runtime upgrade via sudo
pub async fn submit_runtime_upgrade(
    rpc_port: u16,
    wasm_code: &[u8],
    sudo_seed: &str,
) -> Result<String, String> {
    // This would need proper substrate-api-client or subxt integration
    // For now, we'll use the custom RPC that the node provides

    let rpc_url = format!("http://localhost:{}", rpc_port);
    let client = reqwest::Client::builder()
        .timeout(std::time::Duration::from_secs(120))
        .build()
        .map_err(|e| format!("Failed to create HTTP client: {}", e))?;

    let wasm_hex = format!("0x{}", hex::encode(wasm_code));

    // Try the custom sphincs_runtimeUpgrade RPC
    let request = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 1,
        "method": "sphincs_runtimeUpgrade",
        "params": {
            "suri": sudo_seed,
            "code": wasm_hex
        }
    });

    let response = client
        .post(&rpc_url)
        .json(&request)
        .send()
        .await
        .map_err(|e| format!("Runtime upgrade request failed: {}", e))?;

    let result: serde_json::Value = response
        .json()
        .await
        .map_err(|e| format!("Failed to parse response: {}", e))?;

    if let Some(error) = result.get("error") {
        return Err(format!("Runtime upgrade failed: {}", error));
    }

    result
        .get("result")
        .and_then(|r| r.as_str())
        .map(|s| s.to_string())
        .ok_or_else(|| "No transaction hash returned".to_string())
}

/// Get finalized block
pub async fn get_finalized_block(rpc_port: u16) -> Result<u64, String> {
    let rpc_url = format!("http://localhost:{}", rpc_port);
    let client = reqwest::Client::builder()
        .timeout(std::time::Duration::from_secs(5))
        .build()
        .map_err(|e| format!("Failed to create HTTP client: {}", e))?;

    // Get finalized hash
    let hash = call_rpc(&client, &rpc_url, "chain_getFinalizedHead", serde_json::json!([])).await?;
    let hash_str = hash.as_str().ok_or("Invalid hash format")?;

    // Get header for finalized block
    let header = call_rpc(
        &client,
        &rpc_url,
        "chain_getHeader",
        serde_json::json!([hash_str]),
    )
    .await?;

    let block_height = header
        .get("number")
        .and_then(|v| v.as_str())
        .and_then(|s| u64::from_str_radix(s.trim_start_matches("0x"), 16).ok())
        .unwrap_or(0);

    Ok(block_height)
}
