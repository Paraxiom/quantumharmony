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
//! 8. qrng_fetchFromCrypto4a - Fetch from local simulator, create Shamir share, push to queue
//! 9. qrng_reconstructEntropy - Reconstruct from K collected shares
//! 10. qrng_processRound - Process a complete round with turn coordination

use jsonrpsee::{
    core::{async_trait, RpcResult},
    proc_macros::rpc,
    types::error::{ErrorCode, ErrorObject},
};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::sync::{Arc, RwLock};
use std::collections::HashMap;
use sp_runtime::traits::Block as BlockT;
use sp_core::{Blake2Hasher, Hasher};
use sharks::{Share, Sharks};
use hex;

use crate::threshold_qrng::{DeviceId, DeviceShare, ThresholdConfig};
use crate::round_coordinator::{RoundCoordinator, RoundResult};

/// Global share pool for collecting shares from multiple nodes
/// In production this would be managed by the coherence gadget
lazy_static::lazy_static! {
    static ref SHARE_POOL: RwLock<HashMap<String, Vec<CollectedShare>>> = RwLock::new(HashMap::new());
}

/// A collected share waiting for reconstruction
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CollectedShare {
    pub node_id: String,
    pub share_bytes: Vec<u8>,
    pub share_index: u8,
    pub qber: f64,
    pub timestamp: u64,
    /// Device STARK proof (Level 1 proof hierarchy)
    pub device_proof: DeviceProof,
}

/// Device proof of quantum origin (Level 1 of 3-level proof hierarchy)
/// In production: Full STARK proof from QRNG hardware
/// In simulator: Simplified commitment + signature
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeviceProof {
    /// Commitment: Hash(share_hash || qber || device_id || timestamp)
    pub commitment: String,
    /// Signature over commitment (Falcon1024 in production, HMAC in simulator)
    pub signature: String,
    /// Public inputs for verification
    pub public_inputs: DeviceProofInputs,
}

/// Public inputs for device proof verification
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeviceProofInputs {
    /// Hash of the share
    pub share_hash: String,
    /// QBER measurement (scaled)
    pub qber_scaled: u32,
    /// Device identifier
    pub device_id: String,
    /// Measurement timestamp
    pub timestamp: u64,
}

/// Generate a device proof for a share (simulator version)
fn create_device_proof(
    share_bytes: &[u8],
    qber: f64,
    device_id: &str,
    timestamp: u64,
) -> DeviceProof {
    use sp_core::{Blake2Hasher, Hasher};

    // Compute share hash
    let share_hash = Blake2Hasher::hash(share_bytes);
    let share_hash_hex = hex::encode(share_hash.as_ref());

    // Scale QBER (0.005 -> 50)
    let qber_scaled = (qber * 10000.0) as u32;

    // Create commitment: Hash(share_hash || qber || device_id || timestamp)
    let mut commitment_data = Vec::new();
    commitment_data.extend_from_slice(share_hash.as_ref());
    commitment_data.extend_from_slice(&qber_scaled.to_le_bytes());
    commitment_data.extend_from_slice(device_id.as_bytes());
    commitment_data.extend_from_slice(&timestamp.to_le_bytes());

    let commitment = Blake2Hasher::hash(&commitment_data);
    let commitment_hex = hex::encode(commitment.as_ref());

    // In simulator: use HMAC-like signature (Hash(commitment || secret))
    // In production: this would be Falcon1024 signature
    let mut sig_data = Vec::new();
    sig_data.extend_from_slice(commitment.as_ref());
    sig_data.extend_from_slice(b"simulator_secret_key"); // Placeholder
    let signature = Blake2Hasher::hash(&sig_data);
    let signature_hex = hex::encode(signature.as_ref());

    DeviceProof {
        commitment: commitment_hex,
        signature: signature_hex,
        public_inputs: DeviceProofInputs {
            share_hash: share_hash_hex,
            qber_scaled,
            device_id: device_id.to_string(),
            timestamp,
        },
    }
}

/// Verify a device proof
fn verify_device_proof(proof: &DeviceProof, share_bytes: &[u8]) -> Result<(), String> {
    use sp_core::{Blake2Hasher, Hasher};

    // Recompute share hash
    let share_hash = Blake2Hasher::hash(share_bytes);
    let share_hash_hex = hex::encode(share_hash.as_ref());

    if share_hash_hex != proof.public_inputs.share_hash {
        return Err("Share hash mismatch".to_string());
    }

    // Recompute commitment
    let mut commitment_data = Vec::new();
    commitment_data.extend_from_slice(share_hash.as_ref());
    commitment_data.extend_from_slice(&proof.public_inputs.qber_scaled.to_le_bytes());
    commitment_data.extend_from_slice(proof.public_inputs.device_id.as_bytes());
    commitment_data.extend_from_slice(&proof.public_inputs.timestamp.to_le_bytes());

    let expected_commitment = Blake2Hasher::hash(&commitment_data);
    let expected_commitment_hex = hex::encode(expected_commitment.as_ref());

    if expected_commitment_hex != proof.commitment {
        return Err("Commitment mismatch".to_string());
    }

    // Verify signature (simulator version)
    let mut sig_data = Vec::new();
    sig_data.extend_from_slice(expected_commitment.as_ref());
    sig_data.extend_from_slice(b"simulator_secret_key");
    let expected_sig = Blake2Hasher::hash(&sig_data);
    let expected_sig_hex = hex::encode(expected_sig.as_ref());

    if expected_sig_hex != proof.signature {
        return Err("Signature verification failed".to_string());
    }

    // Check QBER threshold (11% max)
    if proof.public_inputs.qber_scaled > 1100 {
        return Err(format!(
            "QBER {}% exceeds threshold 11%",
            proof.public_inputs.qber_scaled as f64 / 100.0
        ));
    }

    Ok(())
}

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

/// Response from Crypto4A simulator with Shamir share
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Crypto4aEntropy {
    /// Raw entropy from QRNG (kept locally, not shared)
    pub entropy_hex: String,
    /// This node's Shamir share (distributed to peers)
    pub share_hex: String,
    /// Share index for Shamir reconstruction
    pub share_index: u8,
    /// Quantum bit error rate
    pub qber: f64,
    pub timestamp: u64,
    pub source: String,
    /// Whether share was pushed to queue
    pub queued: bool,
    pub queue_id: Option<String>,
    /// Current shares collected (toward K threshold)
    pub shares_collected: usize,
    /// Threshold K required for reconstruction
    pub threshold_k: u8,
}

/// Result of Shamir reconstruction
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReconstructedEntropy {
    /// Combined entropy from K shares
    pub entropy_hex: String,
    /// Number of shares used
    pub shares_used: usize,
    /// Node IDs that contributed
    pub contributors: Vec<String>,
    /// Average QBER of contributing shares
    pub average_qber: f64,
    /// Timestamp of reconstruction
    pub timestamp: u64,
    /// Round identifier
    pub round_id: String,
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

    /// Fetch entropy directly from local Crypto4A simulator and push to priority queue
    /// This is the primary method for nodes to get entropy from their local QRNG source
    /// Creates a Shamir share and adds it to the share pool for reconstruction
    #[method(name = "qrng_fetchFromCrypto4a")]
    async fn fetch_from_crypto4a(&self, num_bytes: u32, node_id: String, share_index: u8) -> RpcResult<Crypto4aEntropy>;

    /// Submit a share received from another node (via gossip)
    #[method(name = "qrng_submitShareFromPeer")]
    async fn submit_share_from_peer(&self, share: CollectedShare, round_id: String) -> RpcResult<String>;

    /// Reconstruct entropy from collected shares (called by leader when K shares ready)
    #[method(name = "qrng_reconstructEntropy")]
    async fn reconstruct_entropy(&self, round_id: String) -> RpcResult<ReconstructedEntropy>;

    /// Get current share pool status for a round
    #[method(name = "qrng_getSharePoolStatus")]
    async fn get_share_pool_status(&self, round_id: String) -> RpcResult<Value>;

    /// Push a signal to the local priority queue
    /// Signal will be propagated to other validators via gossip
    #[method(name = "qrng_pushToQueue")]
    async fn push_to_queue(&self, signal: SignalEvent, priority: i32) -> RpcResult<String>;

    /// Get signals from priority queue by type
    #[method(name = "qrng_getSignalsByType")]
    async fn get_signals_by_type(&self, signal_type: String, limit: u32) -> RpcResult<Vec<SignalEvent>>;

    /// Process a complete round with turn-based coordination
    ///
    /// This is the main entry point for the automatic share submission flow:
    /// 1. Check if it's this node's turn based on block number
    /// 2. Check if pool already has K shares (avoid over-collection)
    /// 3. If it's our turn and pool needs shares, fetch from Crypto4A and submit
    /// 4. If K shares collected, trigger reconstruction and gossip
    ///
    /// # Arguments
    /// * `block_number` - Current block number for turn calculation
    ///
    /// # Returns
    /// RoundResult indicating what action was taken
    #[method(name = "qrng_processRound")]
    async fn process_round(&self, block_number: u64) -> RpcResult<Value>;
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
        // NOTE: Returns mock device queue status; coherence gadget integration requires Arc<Mutex<CoherenceGadget>> injection
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
        // NOTE: Returns acknowledgement; actual share queueing requires coherence gadget device queue integration
        Ok(format!(
            "Share queued for device '{}' with QBER {}%",
            request.device_id, request.qber
        ))
    }

    async fn collect_shares(&self, leader_id: String) -> RpcResult<String> {
        // NOTE: Returns acknowledgement; actual collection requires leader election and device polling
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
        // NOTE: Returns empty history; actual history requires coherence gadget reconstruction event storage
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

    async fn fetch_from_crypto4a(&self, num_bytes: u32, node_id: String, share_index: u8) -> RpcResult<Crypto4aEntropy> {
        // Threshold configuration
        let threshold_k: u8 = std::env::var("QRNG_THRESHOLD_K")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(2);
        let total_m: u8 = std::env::var("QRNG_TOTAL_M")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(3);

        // Crypto4A simulator endpoint - configurable via env var
        let crypto4a_url = std::env::var("CRYPTO4A_URL")
            .unwrap_or_else(|_| "http://localhost:8106".to_string());

        let url = format!("{}/entropy/crypto4a?size={}", crypto4a_url, num_bytes);

        // Fetch entropy from Crypto4A simulator
        let client = reqwest::Client::new();
        let response = client
            .get(&url)
            .timeout(std::time::Duration::from_secs(5))
            .send()
            .await
            .map_err(|e| ErrorObject::owned(
                ErrorCode::InternalError.code(),
                format!("Failed to reach Crypto4A simulator: {}", e),
                None::<String>,
            ))?;

        if !response.status().is_success() {
            return Err(ErrorObject::owned(
                ErrorCode::InternalError.code(),
                format!("Crypto4A simulator returned error: {}", response.status()),
                None::<String>,
            ));
        }

        let data: serde_json::Value = response.json().await.map_err(|e| {
            ErrorObject::owned(
                ErrorCode::InternalError.code(),
                format!("Failed to parse Crypto4A response: {}", e),
                None::<String>,
            )
        })?;

        let entropy_hex = data["entropy"].as_str().unwrap_or("").to_string();
        let qber = data["qber"].as_f64().unwrap_or(0.005);
        let timestamp = data["timestamp"].as_u64().unwrap_or_else(|| {
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_millis() as u64
        });
        let source = data["source"].as_str().unwrap_or("crypto4a-simulator").to_string();

        // Convert hex entropy to bytes
        let entropy_bytes = hex::decode(entropy_hex.trim_start_matches("0x"))
            .map_err(|e| ErrorObject::owned(
                ErrorCode::InternalError.code(),
                format!("Invalid entropy hex: {}", e),
                None::<String>,
            ))?;

        // Create Shamir shares from this node's entropy
        // K-of-M threshold: need K shares to reconstruct
        let sharks = Sharks(threshold_k);
        let dealer = sharks.dealer(&entropy_bytes);

        // Generate M shares, take the one for this node's index
        let shares: Vec<Share> = dealer.take(total_m as usize).collect();

        if share_index as usize >= shares.len() {
            return Err(ErrorObject::owned(
                ErrorCode::InvalidParams.code(),
                format!("Share index {} out of range (max {})", share_index, shares.len() - 1),
                None::<String>,
            ));
        }

        let my_share = &shares[share_index as usize];
        let share_bytes: Vec<u8> = my_share.into();
        let share_hex = hex::encode(&share_bytes);

        // Create round ID based on timestamp (nodes in same round should use same ID)
        let round_id = format!("round-{}", timestamp / 10000); // 10 second rounds

        // Create device proof (Level 1 of 3-level proof hierarchy)
        let device_proof = create_device_proof(
            &share_bytes,
            qber,
            &source,
            timestamp,
        );

        // Add this node's share to the share pool
        let collected_share = CollectedShare {
            node_id: node_id.clone(),
            share_bytes: share_bytes.clone(),
            share_index,
            qber,
            timestamp,
            device_proof: device_proof.clone(),
        };

        let shares_collected = {
            let mut pool = SHARE_POOL.write().unwrap();
            let round_shares = pool.entry(round_id.clone()).or_insert_with(Vec::new);

            // Don't add duplicate shares from same node
            if !round_shares.iter().any(|s| s.node_id == node_id) {
                round_shares.push(collected_share.clone());
            }
            round_shares.len()
        };

        // Push share to priority queue for gossip propagation
        let pq_port = std::env::var("PRIORITY_QUEUE_PORT")
            .unwrap_or_else(|_| "5555".to_string());

        let pq_url = format!("http://127.0.0.1:{}", pq_port);

        // Create signal event with SHARE (not raw entropy)
        let signal = SignalEvent {
            signal_type: SignalType::QrngEntropy,
            data: serde_json::json!({
                "share_hex": share_hex,
                "share_index": share_index,
                "node_id": node_id,
                "qber": qber,
                "round_id": round_id,
            }).to_string(),
            source: source.clone(),
            timestamp,
        };

        // Calculate priority based on QBER (lower QBER = higher priority)
        let priority = (1000.0 - (qber * 10000.0)).max(0.0) as i32;

        // Build JSON-RPC request for priority queue
        let queue_id = format!("share-{}-{}", node_id, timestamp);
        let request_body = serde_json::json!({
            "jsonrpc": "2.0",
            "id": 1,
            "method": "submit_event",
            "params": [{
                "id": queue_id,
                "data": serde_json::to_string(&signal).unwrap_or_default(),
                "timestamp": timestamp,
                "block_height": 0
            }, priority]
        });

        let queue_result = client
            .post(&pq_url)
            .json(&request_body)
            .timeout(std::time::Duration::from_secs(2))
            .send()
            .await;

        let queued = queue_result.is_ok() &&
            queue_result.as_ref().map(|r| r.status().is_success()).unwrap_or(false);

        Ok(Crypto4aEntropy {
            entropy_hex: format!("0x{}", hex::encode(&entropy_bytes)), // Raw entropy (kept locally)
            share_hex: format!("0x{}", share_hex), // Share (distributed)
            share_index,
            qber,
            timestamp,
            source,
            queued,
            queue_id: if queued { Some(queue_id) } else { None },
            shares_collected,
            threshold_k,
        })
    }

    async fn submit_share_from_peer(&self, share: CollectedShare, round_id: String) -> RpcResult<String> {
        // Verify device proof before accepting share (Level 1 verification)
        verify_device_proof(&share.device_proof, &share.share_bytes)
            .map_err(|e| ErrorObject::owned(
                ErrorCode::InvalidParams.code(),
                format!("Device proof verification failed: {}", e),
                None::<String>,
            ))?;

        let shares_collected = {
            let mut pool = SHARE_POOL.write().unwrap();
            let round_shares = pool.entry(round_id.clone()).or_insert_with(Vec::new);

            // Don't add duplicate shares from same node
            if !round_shares.iter().any(|s| s.node_id == share.node_id) {
                round_shares.push(share.clone());
            }
            round_shares.len()
        };

        let threshold_k: u8 = std::env::var("QRNG_THRESHOLD_K")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(2);

        Ok(format!(
            "Share from {} added to round {} (proof verified). Collected {}/{} shares.",
            share.node_id, round_id, shares_collected, threshold_k
        ))
    }

    async fn reconstruct_entropy(&self, round_id: String) -> RpcResult<ReconstructedEntropy> {
        let threshold_k: u8 = std::env::var("QRNG_THRESHOLD_K")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(2);

        // Get shares for this round
        let shares = {
            let pool = SHARE_POOL.read().unwrap();
            pool.get(&round_id).cloned().unwrap_or_default()
        };

        if shares.len() < threshold_k as usize {
            return Err(ErrorObject::owned(
                ErrorCode::InvalidParams.code(),
                format!(
                    "Insufficient shares for reconstruction: {} < {} (threshold)",
                    shares.len(), threshold_k
                ),
                None::<String>,
            ));
        }

        // Verify all device proofs before reconstruction (Level 1 verification)
        for share in &shares {
            verify_device_proof(&share.device_proof, &share.share_bytes)
                .map_err(|e| ErrorObject::owned(
                    ErrorCode::InvalidParams.code(),
                    format!("Device proof failed for {}: {}", share.node_id, e),
                    None::<String>,
                ))?;
        }

        // Sort by QBER (best quality first) and take K shares
        let mut sorted_shares = shares.clone();
        sorted_shares.sort_by(|a, b| a.qber.partial_cmp(&b.qber).unwrap());
        let best_shares = &sorted_shares[0..threshold_k as usize];

        // Convert to Sharks shares
        let sharks_shares: Vec<Share> = best_shares
            .iter()
            .map(|s| Share::try_from(s.share_bytes.as_slice()))
            .collect::<Result<Vec<_>, _>>()
            .map_err(|e| ErrorObject::owned(
                ErrorCode::InternalError.code(),
                format!("Invalid share format: {:?}", e),
                None::<String>,
            ))?;

        // Reconstruct via Shamir/Lagrange interpolation
        let sharks = Sharks(threshold_k);
        let reconstructed = sharks.recover(&sharks_shares)
            .map_err(|_| ErrorObject::owned(
                ErrorCode::InternalError.code(),
                "Shamir reconstruction failed - shares may be from different secrets".to_string(),
                None::<String>,
            ))?;

        // Calculate average QBER
        let average_qber = best_shares.iter().map(|s| s.qber).sum::<f64>() / best_shares.len() as f64;

        // Get contributors
        let contributors: Vec<String> = best_shares.iter().map(|s| s.node_id.clone()).collect();

        let timestamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_millis() as u64;

        // Clear this round from pool (one-time use)
        {
            let mut pool = SHARE_POOL.write().unwrap();
            pool.remove(&round_id);
        }

        Ok(ReconstructedEntropy {
            entropy_hex: format!("0x{}", hex::encode(&reconstructed)),
            shares_used: best_shares.len(),
            contributors,
            average_qber,
            timestamp,
            round_id,
        })
    }

    async fn get_share_pool_status(&self, round_id: String) -> RpcResult<Value> {
        let threshold_k: u8 = std::env::var("QRNG_THRESHOLD_K")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(2);

        let pool = SHARE_POOL.read().unwrap();
        let shares = pool.get(&round_id);

        match shares {
            Some(s) => Ok(serde_json::json!({
                "round_id": round_id,
                "shares_collected": s.len(),
                "threshold_k": threshold_k,
                "ready_for_reconstruction": s.len() >= threshold_k as usize,
                "contributors": s.iter().map(|share| serde_json::json!({
                    "node_id": share.node_id,
                    "share_index": share.share_index,
                    "qber": share.qber,
                    "timestamp": share.timestamp,
                })).collect::<Vec<_>>(),
            })),
            None => Ok(serde_json::json!({
                "round_id": round_id,
                "shares_collected": 0,
                "threshold_k": threshold_k,
                "ready_for_reconstruction": false,
                "contributors": [],
            })),
        }
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

    async fn process_round(&self, block_number: u64) -> RpcResult<Value> {
        // Initialize round coordinator
        let coordinator = RoundCoordinator::new(block_number);
        let round_id = RoundCoordinator::get_round_id(block_number);
        let my_node_id = std::env::var("NODE_ID")
            .or_else(|_| std::env::var("VALIDATOR_NAME"))
            .unwrap_or_else(|_| "unknown".to_string());

        log::info!(
            "Processing round {} (block {}) - my_index: {}, turn_index: {}",
            round_id,
            block_number,
            coordinator.my_index,
            coordinator.get_turn_index(block_number)
        );

        // 1. Check if pool already has K shares
        if coordinator.can_reconstruct(&round_id) {
            let share_count = coordinator.get_share_count(&round_id);
            log::info!(
                "Round {} already has {} shares (K={}), skipping submission",
                round_id,
                share_count,
                coordinator.threshold_k
            );
            return Ok(serde_json::json!({
                "status": "AlreadyHaveKShares",
                "round_id": round_id,
                "shares_collected": share_count,
                "threshold_k": coordinator.threshold_k,
            }));
        }

        // 2. Check if it's this node's turn
        if !coordinator.is_my_turn(block_number) {
            let turn_index = coordinator.get_turn_index(block_number);
            let current_validator = coordinator.get_current_turn_validator(block_number)
                .cloned()
                .unwrap_or_else(|| "unknown".to_string());

            log::debug!(
                "Not my turn (turn={}, my_index={}). Current turn: {}",
                turn_index,
                coordinator.my_index,
                current_validator
            );

            return Ok(serde_json::json!({
                "status": "NotMyTurn",
                "round_id": round_id,
                "turn_index": turn_index,
                "my_index": coordinator.my_index,
                "current_validator": current_validator,
            }));
        }

        // 3. Check if we've already submitted for this round
        if coordinator.has_submitted(&round_id, &my_node_id) {
            log::info!("Already submitted share for round {}", round_id);
            return Ok(serde_json::json!({
                "status": "AlreadySubmitted",
                "round_id": round_id,
                "node_id": my_node_id,
            }));
        }

        // 4. Fetch entropy from Crypto4A and create Shamir share
        log::info!("It's my turn! Fetching entropy from Crypto4A for round {}", round_id);

        let share_index = coordinator.get_my_share_index();
        let crypto4a_result = self.fetch_from_crypto4a(32, my_node_id.clone(), share_index).await?;

        log::info!(
            "Fetched entropy: share_index={}, qber={:.4}%, shares_collected={}",
            crypto4a_result.share_index,
            crypto4a_result.qber * 100.0,
            crypto4a_result.shares_collected
        );

        // 5. Check again if K shares collected after our submission
        let shares_after = coordinator.get_share_count(&round_id);
        if shares_after >= coordinator.threshold_k as usize {
            log::info!(
                "K={} shares collected for round {}! Triggering reconstruction.",
                coordinator.threshold_k,
                round_id
            );

            // 6. Reconstruct entropy
            let reconstructed = self.reconstruct_entropy(round_id.clone()).await?;

            // 7. Gossip to all peers
            let gossip_result = self.gossip_reconstructed_entropy(&reconstructed).await;
            if let Err(e) = &gossip_result {
                log::warn!("Failed to gossip entropy: {}", e);
            }

            return Ok(serde_json::json!({
                "status": "ReconstructedAndBroadcast",
                "round_id": round_id,
                "entropy_hash": format!("{}...", &reconstructed.entropy_hex[..34.min(reconstructed.entropy_hex.len())]),
                "shares_used": reconstructed.shares_used,
                "contributors": reconstructed.contributors,
                "average_qber": reconstructed.average_qber,
                "gossip_status": if gossip_result.is_ok() { "success" } else { "failed" },
            }));
        }

        // Return success - share submitted but waiting for more
        Ok(serde_json::json!({
            "status": "ShareSubmitted",
            "round_id": round_id,
            "node_id": my_node_id,
            "share_index": crypto4a_result.share_index,
            "shares_collected": shares_after,
            "threshold_k": coordinator.threshold_k,
            "queued": crypto4a_result.queued,
        }))
    }
}

impl<Block> ThresholdQrngRpc<Block>
where
    Block: BlockT,
{
    /// Gossip reconstructed entropy to all peer validators
    async fn gossip_reconstructed_entropy(&self, entropy: &ReconstructedEntropy) -> Result<(), String> {
        use crate::round_coordinator::canary_network;

        let queue_endpoints = canary_network::get_all_queue_endpoints();
        let client = reqwest::Client::new();

        let timestamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_millis() as u64)
            .unwrap_or(0);

        // Create signal event with reconstructed entropy
        let signal = SignalEvent {
            signal_type: SignalType::QrngEntropy,
            data: serde_json::json!({
                "entropy_hex": entropy.entropy_hex,
                "round_id": entropy.round_id,
                "shares_used": entropy.shares_used,
                "contributors": entropy.contributors,
                "average_qber": entropy.average_qber,
                "source": "reconstructed",
            }).to_string(),
            source: "threshold_qrng_reconstruction".to_string(),
            timestamp,
        };

        // High priority for reconstructed entropy
        let priority = 100;

        let mut success_count = 0;
        let mut errors = Vec::new();

        for (node_name, queue_url) in queue_endpoints {
            let queue_id = format!("entropy-{}-{}", entropy.round_id, timestamp);
            let request_body = serde_json::json!({
                "jsonrpc": "2.0",
                "id": 1,
                "method": "submit_event",
                "params": [{
                    "id": queue_id,
                    "data": serde_json::to_string(&signal).unwrap_or_default(),
                    "timestamp": timestamp,
                    "block_height": 0
                }, priority]
            });

            match client
                .post(queue_url)
                .json(&request_body)
                .timeout(std::time::Duration::from_secs(2))
                .send()
                .await
            {
                Ok(response) if response.status().is_success() => {
                    log::info!("Gossiped entropy to {} ({})", node_name, queue_url);
                    success_count += 1;
                }
                Ok(response) => {
                    let err = format!("{}: HTTP {}", node_name, response.status());
                    log::warn!("Failed to gossip to {}: {}", node_name, err);
                    errors.push(err);
                }
                Err(e) => {
                    let err = format!("{}: {}", node_name, e);
                    log::warn!("Failed to gossip to {}: {}", node_name, e);
                    errors.push(err);
                }
            }
        }

        let total_endpoints = canary_network::get_all_queue_endpoints().len();

        if success_count > 0 {
            log::info!("Gossiped entropy to {}/{} peers", success_count, total_endpoints);
            Ok(())
        } else {
            Err(format!("Failed to gossip to any peer: {:?}", errors))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_device_proof_creation_and_verification() {
        let share_bytes = vec![1, 2, 3, 4, 5, 6, 7, 8];
        let qber = 0.005; // 0.5%
        let device_id = "crypto4a-simulator";
        let timestamp = 1700000000u64;

        // Create proof
        let proof = create_device_proof(&share_bytes, qber, device_id, timestamp);

        // Verify proof succeeds
        let result = verify_device_proof(&proof, &share_bytes);
        assert!(result.is_ok(), "Proof verification should succeed: {:?}", result);

        // Verify QBER is correctly scaled
        assert_eq!(proof.public_inputs.qber_scaled, 50); // 0.005 * 10000 = 50
        assert_eq!(proof.public_inputs.device_id, device_id);
        assert_eq!(proof.public_inputs.timestamp, timestamp);
    }

    #[test]
    fn test_device_proof_fails_with_wrong_share() {
        let share_bytes = vec![1, 2, 3, 4, 5, 6, 7, 8];
        let qber = 0.005;
        let device_id = "crypto4a-simulator";
        let timestamp = 1700000000u64;

        let proof = create_device_proof(&share_bytes, qber, device_id, timestamp);

        // Verify with different share bytes should fail
        let wrong_share = vec![9, 9, 9, 9, 9, 9, 9, 9];
        let result = verify_device_proof(&proof, &wrong_share);
        assert!(result.is_err(), "Proof verification should fail with wrong share");
        assert!(result.unwrap_err().contains("Share hash mismatch"));
    }

    #[test]
    fn test_device_proof_fails_high_qber() {
        let share_bytes = vec![1, 2, 3, 4, 5, 6, 7, 8];
        let qber = 0.15; // 15% - above threshold
        let device_id = "crypto4a-simulator";
        let timestamp = 1700000000u64;

        let proof = create_device_proof(&share_bytes, qber, device_id, timestamp);

        let result = verify_device_proof(&proof, &share_bytes);
        assert!(result.is_err(), "Proof verification should fail with high QBER");
        assert!(result.unwrap_err().contains("exceeds threshold"));
    }

    #[test]
    fn test_shamir_share_creation() {
        let secret = b"quantum_entropy_test_secret_32by";
        let threshold_k = 2u8;
        let total_m = 3usize;

        let sharks = Sharks(threshold_k);
        let dealer = sharks.dealer(secret);
        let shares: Vec<Share> = dealer.take(total_m).collect();

        assert_eq!(shares.len(), 3, "Should generate M shares");

        // Convert to bytes and back
        for share in &shares {
            let share_bytes: Vec<u8> = share.into();
            let recovered = Share::try_from(share_bytes.as_slice());
            assert!(recovered.is_ok(), "Share should round-trip through bytes");
        }
    }

    #[test]
    fn test_shamir_reconstruction() {
        let secret = b"quantum_entropy_test_secret_32by";
        let threshold_k = 2u8;
        let total_m = 3usize;

        let sharks = Sharks(threshold_k);
        let dealer = sharks.dealer(secret);
        let shares: Vec<Share> = dealer.take(total_m).collect();

        // Reconstruct with K=2 shares
        let subset: Vec<Share> = shares.into_iter().take(2).collect();
        let reconstructed = sharks.recover(&subset);

        assert!(reconstructed.is_ok(), "Reconstruction should succeed with K shares");
        assert_eq!(reconstructed.unwrap(), secret.to_vec(), "Reconstructed secret should match original");
    }

    #[test]
    fn test_shamir_reconstruction_fails_with_insufficient_shares() {
        let secret = b"quantum_entropy_test_secret_32by";
        let threshold_k = 2u8;
        let total_m = 3usize;

        let sharks = Sharks(threshold_k);
        let dealer = sharks.dealer(secret);
        let shares: Vec<Share> = dealer.take(total_m).collect();

        // Try to reconstruct with only 1 share (less than K=2)
        let subset: Vec<Share> = shares.into_iter().take(1).collect();
        let reconstructed = sharks.recover(&subset);

        assert!(reconstructed.is_err(), "Reconstruction should fail with < K shares");
    }

    #[test]
    fn test_collected_share_with_proof() {
        let share_bytes = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        let qber = 0.008; // 0.8%
        let timestamp = 1700000000u64;
        let device_id = "toshiba-qrng";

        let device_proof = create_device_proof(&share_bytes, qber, device_id, timestamp);

        let collected_share = CollectedShare {
            node_id: "alice".to_string(),
            share_bytes: share_bytes.clone(),
            share_index: 0,
            qber,
            timestamp,
            device_proof,
        };

        // Verify proof within the share
        let result = verify_device_proof(&collected_share.device_proof, &collected_share.share_bytes);
        assert!(result.is_ok(), "Collected share proof should verify");
    }

    #[test]
    fn test_share_pool_operations() {
        // Clear pool first
        {
            let mut pool = SHARE_POOL.write().unwrap();
            pool.clear();
        }

        let round_id = "test-round-1".to_string();
        let timestamp = 1700000000u64;

        // Create shares from different nodes
        let share1_bytes = vec![1, 2, 3, 4];
        let proof1 = create_device_proof(&share1_bytes, 0.005, "device1", timestamp);
        let share1 = CollectedShare {
            node_id: "alice".to_string(),
            share_bytes: share1_bytes,
            share_index: 0,
            qber: 0.005,
            timestamp,
            device_proof: proof1,
        };

        let share2_bytes = vec![5, 6, 7, 8];
        let proof2 = create_device_proof(&share2_bytes, 0.008, "device2", timestamp);
        let share2 = CollectedShare {
            node_id: "bob".to_string(),
            share_bytes: share2_bytes,
            share_index: 1,
            qber: 0.008,
            timestamp,
            device_proof: proof2,
        };

        // Add shares to pool
        {
            let mut pool = SHARE_POOL.write().unwrap();
            let round_shares = pool.entry(round_id.clone()).or_insert_with(Vec::new);
            round_shares.push(share1);
            round_shares.push(share2);
        }

        // Check pool state
        {
            let pool = SHARE_POOL.read().unwrap();
            let shares = pool.get(&round_id).unwrap();
            assert_eq!(shares.len(), 2, "Pool should have 2 shares");
            assert_eq!(shares[0].node_id, "alice");
            assert_eq!(shares[1].node_id, "bob");
        }

        // Clean up
        {
            let mut pool = SHARE_POOL.write().unwrap();
            pool.remove(&round_id);
        }
    }

    #[test]
    fn test_full_shamir_flow_with_proofs() {
        // Clear pool first
        {
            let mut pool = SHARE_POOL.write().unwrap();
            pool.clear();
        }

        let secret = b"full_flow_test_quantum_entropy!!"; // 32 bytes
        let threshold_k = 2u8;
        let round_id = "test-full-flow".to_string();
        let timestamp = 1700000000u64;

        // Generate Shamir shares
        let sharks = Sharks(threshold_k);
        let dealer = sharks.dealer(secret);
        let shares: Vec<Share> = dealer.take(3).collect();

        // Convert to CollectedShares with proofs
        let node_ids = ["alice", "bob", "charlie"];
        let qbers = [0.005, 0.008, 0.012]; // Different QBER values

        for (i, share) in shares.iter().enumerate() {
            let share_bytes: Vec<u8> = share.into();
            let device_proof = create_device_proof(
                &share_bytes,
                qbers[i],
                &format!("device-{}", i),
                timestamp,
            );

            let collected = CollectedShare {
                node_id: node_ids[i].to_string(),
                share_bytes,
                share_index: i as u8,
                qber: qbers[i],
                timestamp,
                device_proof,
            };

            // Verify proof before adding
            let verify_result = verify_device_proof(&collected.device_proof, &collected.share_bytes);
            assert!(verify_result.is_ok(), "Proof {} should verify", i);

            // Add to pool
            let mut pool = SHARE_POOL.write().unwrap();
            let round_shares = pool.entry(round_id.clone()).or_insert_with(Vec::new);
            round_shares.push(collected);
        }

        // Get shares and reconstruct
        let collected_shares = {
            let pool = SHARE_POOL.read().unwrap();
            pool.get(&round_id).cloned().unwrap()
        };

        assert_eq!(collected_shares.len(), 3, "Should have 3 shares");

        // Sort by QBER and take best K
        let mut sorted = collected_shares.clone();
        sorted.sort_by(|a, b| a.qber.partial_cmp(&b.qber).unwrap());
        let best_k: Vec<_> = sorted.into_iter().take(threshold_k as usize).collect();

        assert_eq!(best_k[0].node_id, "alice", "Alice should have best QBER");
        assert_eq!(best_k[1].node_id, "bob", "Bob should have second best QBER");

        // Convert back to Sharks shares and reconstruct
        let sharks_shares: Vec<Share> = best_k
            .iter()
            .map(|s| Share::try_from(s.share_bytes.as_slice()).unwrap())
            .collect();

        let reconstructed = sharks.recover(&sharks_shares).unwrap();
        assert_eq!(reconstructed, secret.to_vec(), "Reconstructed secret should match");

        // Clean up
        {
            let mut pool = SHARE_POOL.write().unwrap();
            pool.remove(&round_id);
        }
    }

    #[test]
    fn test_proof_tamper_detection() {
        let share_bytes = vec![1, 2, 3, 4, 5, 6, 7, 8];
        let qber = 0.005;
        let device_id = "crypto4a-simulator";
        let timestamp = 1700000000u64;

        let mut proof = create_device_proof(&share_bytes, qber, device_id, timestamp);

        // Tamper with commitment
        proof.commitment = "0000000000000000000000000000000000000000000000000000000000000000".to_string();

        let result = verify_device_proof(&proof, &share_bytes);
        assert!(result.is_err(), "Tampered commitment should fail verification");
        assert!(result.unwrap_err().contains("Commitment mismatch"));
    }

    #[test]
    fn test_signature_tamper_detection() {
        let share_bytes = vec![1, 2, 3, 4, 5, 6, 7, 8];
        let qber = 0.005;
        let device_id = "crypto4a-simulator";
        let timestamp = 1700000000u64;

        let mut proof = create_device_proof(&share_bytes, qber, device_id, timestamp);

        // Tamper with signature (keep valid commitment)
        proof.signature = "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff".to_string();

        let result = verify_device_proof(&proof, &share_bytes);
        assert!(result.is_err(), "Tampered signature should fail verification");
        assert!(result.unwrap_err().contains("Signature verification failed"));
    }
}
