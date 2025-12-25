//! Threshold QRNG RPC
//!
//! Real-time interface for threshold quantum random number generation:
//! 1. qrng_getDeviceQueues - Get current device queue status
//! 2. qrng_submitDeviceShare - Submit a share from a QRNG device
//! 3. qrng_collectShares - Trigger leader share collection (dev mode)
//! 4. qrng_getConfig - Get threshold configuration (K, M, devices)
//! 5. qrng_getReconstructionHistory - Get recent entropy reconstructions

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
}
