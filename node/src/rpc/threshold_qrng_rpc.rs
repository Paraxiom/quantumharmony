//! Threshold QRNG RPC
//!
//! Real-time interface for threshold quantum random number generation:
//! 1. qrng_getDeviceQueues - Get current device queue status
//! 2. qrng_submitDeviceShare - Submit a share from a QRNG device
//! 3. qrng_collectShares - Trigger leader share collection (dev mode)
//! 4. qrng_getConfig - Get threshold configuration (K, M, devices)
//! 5. qrng_getReconstructionHistory - Get recent entropy reconstructions
//! 6. qrng_fetchFromKirqHub - Fetch entropy from Kirq Hub API
//! 7. qrng_pushToQueue - Push signal to priority queue

use jsonrpsee::{
    core::{async_trait, RpcResult},
    proc_macros::rpc,
    types::error::{ErrorCode, ErrorObject},
};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::sync::Arc;
use sp_runtime::traits::Block as BlockT;

use crate::threshold_qrng::{DeviceId, DeviceShare, ThresholdConfig};

/// Signal types for the priority queue
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SignalType {
    /// QRNG entropy signal from kirq-hub
    QrngEntropy,
    /// Oracle price feed
    OraclePrice,
    /// Custom signal type
    Custom(String),
}

/// Entropy fetched from Kirq Hub
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct KirqHubEntropy {
    pub entropy_hex: String,
    pub sources_used: Vec<String>,
    pub timestamp: u64,
    pub proof: Option<Value>,
}

/// Signal to push to priority queue
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SignalEvent {
    pub signal_type: SignalType,
    pub data: String,
    pub source: String,
    pub timestamp: u64,
}

/// Device queue status for wallet display
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeviceQueueStatus {
    pub device_id: String,
    pub device_name: String,
    pub queue_length: usize,
    pub best_qber: Option<f64>,  // Best QBER in queue (%)
    pub enabled: bool,
}

/// Reconstruction event for history display
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReconstructionEvent {
    pub timestamp: u64,
    pub entropy_hash: String,
    pub devices_used: Vec<String>,
    pub qber_average: f64,
    pub threshold_k: u32,
}

/// Request to submit a device share
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SubmitShareRequest {
    pub device_id: String,
    pub share_hex: String,
    pub qber: f64,  // QBER as percentage (e.g., 0.8 for 0.8%)
    pub stark_proof_hex: String,
}

/// Threshold QRNG RPC API
#[rpc(client, server)]
pub trait ThresholdQrngApi {
    /// Get current status of all device queues
    #[method(name = "qrng_getDeviceQueues")]
    async fn get_device_queues(&self) -> RpcResult<Vec<DeviceQueueStatus>>;

    /// Submit a share from a QRNG device
    #[method(name = "qrng_submitDeviceShare")]
    async fn submit_device_share(&self, request: SubmitShareRequest) -> RpcResult<String>;

    /// Trigger leader share collection (dev/test mode only)
    #[method(name = "qrng_collectShares")]
    async fn collect_shares(&self, leader_id: String) -> RpcResult<String>;

    /// Get threshold configuration
    #[method(name = "qrng_getConfig")]
    async fn get_config(&self) -> RpcResult<Value>;

    /// Get recent reconstruction history
    #[method(name = "qrng_getReconstructionHistory")]
    async fn get_reconstruction_history(&self, limit: u32) -> RpcResult<Vec<ReconstructionEvent>>;

    /// Fetch entropy from Kirq Hub API
    /// Returns mixed entropy from configured sources (crypto4a, quantum_vault, etc.)
    #[method(name = "qrng_fetchFromKirqHub")]
    async fn fetch_from_kirq_hub(&self, num_bytes: u32) -> RpcResult<KirqHubEntropy>;

    /// Push a signal to the local priority queue
    /// Signal will be propagated to other validators via gossip
    #[method(name = "qrng_pushToQueue")]
    async fn push_to_queue(&self, signal: SignalEvent, priority: i32) -> RpcResult<String>;

    /// Get signals from priority queue by type
    #[method(name = "qrng_getSignalsByType")]
    async fn get_signals_by_type(&self, signal_type: String, limit: u32) -> RpcResult<Vec<SignalEvent>>;
}

/// Threshold QRNG RPC implementation
pub struct ThresholdQrngRpc<Block> {
    _phantom: std::marker::PhantomData<Block>,
}

impl<Block> ThresholdQrngRpc<Block>
where
    Block: BlockT,
{
    pub fn new() -> Self {
        Self {
            _phantom: Default::default(),
        }
    }
}

#[async_trait]
impl<Block> ThresholdQrngApiServer for ThresholdQrngRpc<Block>
where
    Block: BlockT,
{
    async fn get_device_queues(&self) -> RpcResult<Vec<DeviceQueueStatus>> {
        // TODO: Connect to actual coherence gadget device queues
        // For now, return mock data for testing
        Ok(vec![
            DeviceQueueStatus {
                device_id: "toshiba-qrng".to_string(),
                device_name: "Toshiba QRNG".to_string(),
                queue_length: 0,
                best_qber: None,
                enabled: true,
            },
            DeviceQueueStatus {
                device_id: "crypto4a-qrng".to_string(),
                device_name: "Crypto4A QRNG".to_string(),
                queue_length: 0,
                best_qber: None,
                enabled: true,
            },
            DeviceQueueStatus {
                device_id: "kirq".to_string(),
                device_name: "KIRQ".to_string(),
                queue_length: 0,
                best_qber: None,
                enabled: true,
            },
        ])
    }

    async fn submit_device_share(&self, request: SubmitShareRequest) -> RpcResult<String> {
        // TODO: Parse request and queue share
        // For now, return success message
        Ok(format!(
            "Share queued for device '{}' with QBER {}%",
            request.device_id, request.qber
        ))
    }

    async fn collect_shares(&self, leader_id: String) -> RpcResult<String> {
        // TODO: Trigger actual share collection
        Ok(format!(
            "Share collection triggered by leader: {}",
            leader_id
        ))
    }

    async fn get_config(&self) -> RpcResult<Value> {
        Ok(serde_json::json!({
            "threshold_k": 2,
            "total_devices_m": 3,
            "devices": [
                {
                    "device_id": "toshiba-qrng",
                    "endpoint": "http://localhost:8001/qrng",
                    "qber_threshold": 11.0,
                    "enabled": true
                },
                {
                    "device_id": "crypto4a-qrng",
                    "endpoint": "http://localhost:8002/qrng",
                    "qber_threshold": 11.0,
                    "enabled": true
                },
                {
                    "device_id": "kirq",
                    "endpoint": "http://localhost:8003/qrng",
                    "qber_threshold": 11.0,
                    "enabled": true
                }
            ]
        }))
    }

    async fn get_reconstruction_history(&self, limit: u32) -> RpcResult<Vec<ReconstructionEvent>> {
        // TODO: Return actual history from gadget
        Ok(vec![])
    }

    async fn fetch_from_kirq_hub(&self, num_bytes: u32) -> RpcResult<KirqHubEntropy> {
        // Kirq Hub endpoint - configurable via env var
        let kirq_url = std::env::var("KIRQ_HUB_URL")
            .unwrap_or_else(|_| "http://localhost:8001".to_string());

        let url = format!("{}/api/entropy/mixed", kirq_url);

        // Build request body
        let request_body = serde_json::json!({
            "num_bytes": num_bytes,
            "sources": ["crypto4a", "quantum_vault"],
            "proof_required": true
        });

        // Make HTTP request to Kirq Hub
        let client = reqwest::Client::new();
        let response = client
            .post(&url)
            .json(&request_body)
            .timeout(std::time::Duration::from_secs(5))
            .send()
            .await
            .map_err(|e| ErrorObject::owned(
                ErrorCode::InternalError.code(),
                format!("Failed to reach Kirq Hub: {}", e),
                None::<String>,
            ))?;

        if !response.status().is_success() {
            return Err(ErrorObject::owned(
                ErrorCode::InternalError.code(),
                format!("Kirq Hub returned error: {}", response.status()),
                None::<String>,
            ));
        }

        let data: serde_json::Value = response.json().await.map_err(|e| {
            ErrorObject::owned(
                ErrorCode::InternalError.code(),
                format!("Failed to parse Kirq Hub response: {}", e),
                None::<String>,
            )
        })?;

        Ok(KirqHubEntropy {
            entropy_hex: data["entropy"].as_str().unwrap_or("").to_string(),
            sources_used: data["sources_used"]
                .as_array()
                .map(|arr| arr.iter().filter_map(|v| v.as_str().map(String::from)).collect())
                .unwrap_or_default(),
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_millis() as u64,
            proof: data.get("proof").cloned(),
        })
    }

    async fn push_to_queue(&self, signal: SignalEvent, priority: i32) -> RpcResult<String> {
        // Priority queue endpoint - configurable via env var
        let pq_port = std::env::var("PRIORITY_QUEUE_PORT")
            .unwrap_or_else(|_| "5555".to_string());

        let url = format!("http://127.0.0.1:{}", pq_port);

        // Build JSON-RPC request
        let request_body = serde_json::json!({
            "jsonrpc": "2.0",
            "id": 1,
            "method": "submit_event",
            "params": [{
                "id": signal.timestamp,
                "data": serde_json::to_string(&signal).unwrap_or_default(),
                "timestamp": signal.timestamp,
                "block_height": 0  // Will be filled by the queue
            }, priority]
        });

        let client = reqwest::Client::new();
        let response = client
            .post(&url)
            .json(&request_body)
            .timeout(std::time::Duration::from_secs(2))
            .send()
            .await
            .map_err(|e| ErrorObject::owned(
                ErrorCode::InternalError.code(),
                format!("Failed to reach priority queue: {}", e),
                None::<String>,
            ))?;

        if !response.status().is_success() {
            return Err(ErrorObject::owned(
                ErrorCode::InternalError.code(),
                format!("Priority queue returned error: {}", response.status()),
                None::<String>,
            ));
        }

        Ok(format!(
            "Signal pushed to queue with priority {} (type: {:?})",
            priority, signal.signal_type
        ))
    }

    async fn get_signals_by_type(&self, signal_type: String, limit: u32) -> RpcResult<Vec<SignalEvent>> {
        // Priority queue endpoint
        let pq_port = std::env::var("PRIORITY_QUEUE_PORT")
            .unwrap_or_else(|_| "5555".to_string());

        let url = format!("http://127.0.0.1:{}", pq_port);

        // Build JSON-RPC request to list events
        let request_body = serde_json::json!({
            "jsonrpc": "2.0",
            "id": 1,
            "method": "list_all_events",
            "params": []
        });

        let client = reqwest::Client::new();
        let response = client
            .post(&url)
            .json(&request_body)
            .timeout(std::time::Duration::from_secs(2))
            .send()
            .await
            .map_err(|e| ErrorObject::owned(
                ErrorCode::InternalError.code(),
                format!("Failed to reach priority queue: {}", e),
                None::<String>,
            ))?;

        let data: serde_json::Value = response.json().await.map_err(|e| {
            ErrorObject::owned(
                ErrorCode::InternalError.code(),
                format!("Failed to parse priority queue response: {}", e),
                None::<String>,
            )
        })?;

        // Parse events and filter by type
        let events = data["result"]
            .as_array()
            .map(|arr| {
                arr.iter()
                    .filter_map(|event| {
                        let data_str = event[0]["data"].as_str()?;
                        let signal: SignalEvent = serde_json::from_str(data_str).ok()?;

                        // Filter by type
                        let type_matches = match &signal.signal_type {
                            SignalType::QrngEntropy => signal_type == "qrng" || signal_type == "QrngEntropy",
                            SignalType::OraclePrice => signal_type == "oracle" || signal_type == "OraclePrice",
                            SignalType::Custom(t) => signal_type == *t || signal_type == "custom",
                        };

                        if type_matches { Some(signal) } else { None }
                    })
                    .take(limit as usize)
                    .collect()
            })
            .unwrap_or_default();

        Ok(events)
    }
}
