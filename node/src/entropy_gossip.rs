// SPDX-License-Identifier: Apache-2.0
// Phase 2: Entropy Distribution Protocol for Nokia
//
// ## ISO 23631:2024 Compliance
//
// This module implements ISO 23631 interoperability standards:
// - ISO-compliant Signal format with version and schema fields
// - Falcon-1024 post-quantum signatures for authenticity
// - Structured signal types (QRNG, Oracle, Attestation)
//
// Distributes reconstructed entropy to all validators using:
// - Falcon1024 public key encryption (post-quantum secure)
// - AES-256-GCM for actual data encryption
// - Falcon1024 signature for authenticity
//
// Message Flow:
// 1. Leader reconstructs combined entropy from K-of-M device shares
// 2. Leader creates EntropyPackage with all device shares + combined entropy
// 3. For each validator:
//    - Generate random AES-256-GCM key
//    - Encrypt entropy package with AES key
//    - Encrypt AES key with validator's Falcon1024 public key
//    - Sign encrypted package with leader's Falcon1024 private key
// 4. Distribute EntropyMessage to all validators

use scale_codec::{Decode, Encode};
use serde::{Deserialize, Serialize};
use log::{debug, info};
use sp_core::blake2_256;

use crate::threshold_qrng::DeviceShare;

// Post-quantum cryptography
use pqcrypto_falcon::falcon1024;
use pqcrypto_traits::sign::{PublicKey as SignPublicKey, SecretKey as SignSecretKey, SignedMessage};
use pqcrypto_kyber::kyber1024;
use pqcrypto_traits::kem::{PublicKey as KemPublicKey, SecretKey as KemSecretKey, Ciphertext, SharedSecret};

// For AES-GCM encryption
use aes_gcm::{
    aead::{Aead, KeyInit, OsRng as AeadOsRng},
    Aes256Gcm, Nonce,
};
use rand::RngCore;

/// Maximum entropy package size (10 KB)
const MAX_ENTROPY_SIZE: usize = 10 * 1024;

/// Current ISO signal format version
pub const SIGNAL_VERSION: &str = "1.0";

/// ISO signal schema identifier
pub const SIGNAL_SCHEMA: &str = "iso:tc307:signal:v1";

// ==================== ISO 23631 SIGNAL FORMAT ====================

/// Signal type classification per ISO 23631
#[derive(Clone, Debug, Encode, Decode, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum SignalType {
    /// Quantum random number entropy
    QrngEntropy,
    /// Oracle price feed data
    OraclePrice,
    /// Generic oracle data
    OracleData,
    /// Document attestation
    Attestation,
    /// Custom signal type
    Custom(Vec<u8>),
}

/// Signal source information per ISO 23631
#[derive(Clone, Debug, Encode, Decode, Serialize, Deserialize)]
pub struct SignalSource {
    /// 256-bit node identifier (libp2p PeerId hash)
    pub node_id: [u8; 32],

    /// SS58-encoded reporter account (optional)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reporter_id: Option<String>,

    /// Unix timestamp in milliseconds
    pub timestamp: u64,

    /// Falcon-1024 signature over (schema + payload + timestamp)
    /// Format: "falcon1024:0x{hex_signature}"
    pub signature: String,
}

/// Signal payload per ISO 23631
#[derive(Clone, Debug, Encode, Decode, Serialize, Deserialize)]
pub struct SignalPayload {
    /// Signal type classification
    #[serde(rename = "type")]
    pub signal_type: SignalType,

    /// Oracle feed identifier (for oracle types)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub feed_id: Option<String>,

    /// Hex-encoded payload data (0x prefix)
    pub data: String,

    /// Type-specific metadata
    #[serde(skip_serializing_if = "Option::is_none")]
    #[codec(skip)]
    pub metadata: Option<serde_json::Value>,
}

/// Signal routing hints per ISO 23631
#[derive(Clone, Debug, Encode, Decode, Serialize, Deserialize, Default)]
pub struct SignalRouting {
    /// Time-to-live hop count (0-255)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub ttl: Option<u8>,

    /// Processing priority
    #[serde(skip_serializing_if = "Option::is_none")]
    pub priority: Option<SignalPriority>,

    /// Specific target node IDs (empty = broadcast)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub target_nodes: Option<Vec<String>>,
}

/// Signal priority levels
#[derive(Clone, Debug, Encode, Decode, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
pub enum SignalPriority {
    Low,
    Normal,
    High,
    Critical,
}

/// ISO 23631 compliant Signal structure
///
/// This is the standard format for cross-node data exchange in QuantumHarmony.
/// All signals must conform to this schema for interoperability.
///
/// # Example JSON
/// ```json
/// {
///   "version": "1.0",
///   "schema": "iso:tc307:signal:v1",
///   "source": {
///     "node_id": "0x1234...abcd",
///     "timestamp": 1705680000000,
///     "signature": "falcon1024:0x..."
///   },
///   "payload": {
///     "type": "qrng_entropy",
///     "data": "0x7f3c...",
///     "metadata": { "qber": 0.005 }
///   }
/// }
/// ```
#[derive(Clone, Debug, Encode, Decode, Serialize, Deserialize)]
pub struct Signal {
    /// Signal format version (always "1.0")
    pub version: String,

    /// Schema identifier (always "iso:tc307:signal:v1")
    pub schema: String,

    /// Source information including node ID and signature
    pub source: SignalSource,

    /// Signal payload with type and data
    pub payload: SignalPayload,

    /// Optional routing hints for network propagation
    #[serde(skip_serializing_if = "Option::is_none")]
    pub routing: Option<SignalRouting>,
}

impl Signal {
    /// Create a new QRNG entropy signal
    pub fn new_qrng_entropy(
        node_id: [u8; 32],
        entropy_hex: String,
        qber: f64,
        source_type: &str,
    ) -> Self {
        let timestamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_millis() as u64)
            .unwrap_or(0);

        Signal {
            version: SIGNAL_VERSION.to_string(),
            schema: SIGNAL_SCHEMA.to_string(),
            source: SignalSource {
                node_id,
                reporter_id: None,
                timestamp,
                signature: String::new(), // To be filled after signing
            },
            payload: SignalPayload {
                signal_type: SignalType::QrngEntropy,
                feed_id: None,
                data: entropy_hex,
                metadata: Some(serde_json::json!({
                    "source_type": source_type,
                    "qber": qber,
                    "bits": 256
                })),
            },
            routing: Some(SignalRouting {
                ttl: Some(10),
                priority: Some(SignalPriority::High),
                target_nodes: None,
            }),
        }
    }

    /// Create a new oracle price signal
    pub fn new_oracle_price(
        node_id: [u8; 32],
        reporter_id: String,
        feed_id: String,
        price_data: String,
        price_usd: &str,
        sources: Vec<String>,
    ) -> Self {
        let timestamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_millis() as u64)
            .unwrap_or(0);

        Signal {
            version: SIGNAL_VERSION.to_string(),
            schema: SIGNAL_SCHEMA.to_string(),
            source: SignalSource {
                node_id,
                reporter_id: Some(reporter_id),
                timestamp,
                signature: String::new(),
            },
            payload: SignalPayload {
                signal_type: SignalType::OraclePrice,
                feed_id: Some(feed_id),
                data: price_data,
                metadata: Some(serde_json::json!({
                    "price_usd": price_usd,
                    "decimal_places": 8,
                    "sources": sources,
                    "aggregation": "median"
                })),
            },
            routing: Some(SignalRouting {
                ttl: Some(5),
                priority: Some(SignalPriority::Normal),
                target_nodes: None,
            }),
        }
    }

    /// Validate signal format
    pub fn validate(&self) -> Result<(), String> {
        if self.version != SIGNAL_VERSION {
            return Err(format!("Invalid version: expected {}, got {}", SIGNAL_VERSION, self.version));
        }
        if self.schema != SIGNAL_SCHEMA {
            return Err(format!("Invalid schema: expected {}, got {}", SIGNAL_SCHEMA, self.schema));
        }
        if self.source.timestamp == 0 {
            return Err("Invalid timestamp".to_string());
        }
        if self.payload.data.is_empty() {
            return Err("Empty payload data".to_string());
        }
        Ok(())
    }

    /// Convert to JSON string
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(self)
    }

    /// Parse from JSON string
    pub fn from_json(json: &str) -> Result<Self, serde_json::Error> {
        serde_json::from_str(json)
    }
}

// ==================== END ISO 23631 SIGNAL FORMAT ====================

/// Canary network validator queue endpoints
pub mod canary_endpoints {
    /// Alice (Montreal) priority queue
    pub const ALICE_QUEUE: &str = "http://51.79.26.123:5555";
    /// Bob (Beauharnois) priority queue
    pub const BOB_QUEUE: &str = "http://51.79.26.168:5556";
    /// Charlie (Frankfurt) priority queue
    pub const CHARLIE_QUEUE: &str = "http://209.38.225.4:5557";

    /// Get all peer queue endpoints with names
    pub fn get_all_queue_endpoints() -> Vec<(&'static str, &'static str)> {
        vec![
            ("alice", ALICE_QUEUE),
            ("bob", BOB_QUEUE),
            ("charlie", CHARLIE_QUEUE),
        ]
    }
}

/// Reconstructed entropy data from threshold QRNG
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ReconstructedEntropy {
    /// Combined entropy from K shares (hex encoded)
    pub entropy_hex: String,
    /// Number of shares used in reconstruction
    pub shares_used: usize,
    /// Node IDs that contributed shares
    pub contributors: Vec<String>,
    /// Average QBER of contributing shares
    pub average_qber: f64,
    /// Timestamp of reconstruction
    pub timestamp: u64,
    /// Round identifier
    pub round_id: String,
}

/// Gossip reconstructed entropy to all peer validators
///
/// This function broadcasts the reconstructed entropy to all known validators'
/// priority queues. Each validator receives the entropy so they can use it
/// for consensus or other purposes.
///
/// # Arguments
/// * `entropy` - The reconstructed entropy to broadcast
///
/// # Returns
/// Result with number of successful broadcasts or error
pub async fn gossip_entropy_to_peers(entropy: &ReconstructedEntropy) -> Result<usize, String> {
    let endpoints = canary_endpoints::get_all_queue_endpoints();
    let client = reqwest::Client::new();

    let timestamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_millis() as u64)
        .unwrap_or(0);

    // Create ISO 23631 compliant signal
    let node_id = std::env::var("NODE_ID")
        .or_else(|_| std::env::var("VALIDATOR_NAME"))
        .unwrap_or_else(|_| "unknown".to_string());

    // Hash the node ID to get a 32-byte identifier
    let node_id_bytes: [u8; 32] = sp_core::blake2_256(node_id.as_bytes());

    let signal = Signal::new_qrng_entropy(
        node_id_bytes,
        entropy.entropy_hex.clone(),
        entropy.average_qber,
        "threshold_reconstruction",
    );

    // Convert to JSON for transmission
    let signal_json = signal.to_json()
        .map_err(|e| format!("Failed to serialize signal: {}", e))?;

    // High priority for reconstructed entropy (100)
    let priority = 100;

    let mut success_count = 0;
    let mut errors = Vec::new();

    for (node_name, queue_url) in endpoints {
        let result = push_entropy_to_priority_queue_url(
            queue_url,
            &signal_json,
            &entropy.round_id,
            priority,
        ).await;

        match result {
            Ok(()) => {
                info!("Gossiped entropy to {} ({})", node_name, queue_url);
                success_count += 1;
            }
            Err(e) => {
                info!("Failed to gossip to {}: {}", node_name, e);
                errors.push(format!("{}: {}", node_name, e));
            }
        }
    }

    let total_endpoints = canary_endpoints::get_all_queue_endpoints().len();

    if success_count > 0 {
        info!(
            "Successfully gossiped entropy for round {} to {}/{} peers",
            entropy.round_id,
            success_count,
            total_endpoints
        );
        Ok(success_count)
    } else {
        Err(format!(
            "Failed to gossip entropy to any peer: {:?}",
            errors
        ))
    }
}

/// Push entropy signal to a specific priority queue URL
///
/// # Arguments
/// * `queue_url` - Full URL of the priority queue endpoint
/// * `signal_json` - JSON-serialized signal to push
/// * `round_id` - Round identifier for the entropy
/// * `priority` - Priority level (higher = more urgent)
async fn push_entropy_to_priority_queue_url(
    queue_url: &str,
    signal_json: &str,
    round_id: &str,
    priority: i32,
) -> Result<(), String> {
    let client = reqwest::Client::new();

    let timestamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_millis() as u64)
        .unwrap_or(0);

    let queue_id = format!("entropy-{}-{}", round_id, timestamp);

    let request_body = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 1,
        "method": "submit_event",
        "params": [{
            "id": queue_id,
            "data": signal_json,
            "timestamp": timestamp,
            "block_height": 0
        }, priority]
    });

    let response = client
        .post(queue_url)
        .json(&request_body)
        .timeout(std::time::Duration::from_secs(2))
        .send()
        .await
        .map_err(|e| format!("Connection failed: {}", e))?;

    if !response.status().is_success() {
        return Err(format!("HTTP error: {}", response.status()));
    }

    Ok(())
}

/// Push received entropy to the local priority queue
///
/// This function is called when entropy is received via gossip from other validators.
/// It stores the entropy in the local priority queue for later use.
pub async fn push_entropy_to_priority_queue(
    entropy_hex: &str,
    source: &str,
    priority: i32,
) -> Result<(), String> {
    let pq_port = std::env::var("PRIORITY_QUEUE_PORT")
        .unwrap_or_else(|_| "5555".to_string());

    let url = format!("http://127.0.0.1:{}", pq_port);
    let timestamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_millis() as u64)
        .unwrap_or(0);

    // Create signal event
    let signal = serde_json::json!({
        "signal_type": "QrngEntropy",
        "data": entropy_hex,
        "source": source,
        "timestamp": timestamp
    });

    // Build JSON-RPC request
    let request_body = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 1,
        "method": "submit_event",
        "params": [{
            "id": timestamp,
            "data": serde_json::to_string(&signal).unwrap_or_default(),
            "timestamp": timestamp,
            "block_height": 0
        }, priority]
    });

    let client = reqwest::Client::new();
    let response = client
        .post(&url)
        .json(&request_body)
        .timeout(std::time::Duration::from_secs(2))
        .send()
        .await
        .map_err(|e| format!("Failed to reach priority queue: {}", e))?;

    if !response.status().is_success() {
        return Err(format!("Priority queue returned error: {}", response.status()));
    }

    info!("📥 Pushed entropy from {} to priority queue with priority {}", source, priority);
    Ok(())
}

/// Handle received entropy message from gossip and store in priority queue
pub async fn handle_received_entropy(
    package: &EntropyPackage,
) -> Result<(), String> {
    let entropy_hex = hex::encode(&package.combined_entropy);
    let source = format!(
        "gossip/block-{}",
        package.block_number
    );

    // High priority (75) for gossip-received entropy
    push_entropy_to_priority_queue(&entropy_hex, &source, 75).await
}

/// Entropy package containing all data needed for consensus
#[derive(Clone, Encode, Decode, Debug)]
pub struct EntropyPackage {
    /// Block number this entropy is for
    pub block_number: u32,

    /// Timestamp when leader reconstructed this entropy
    pub timestamp: u64,

    /// Combined entropy reconstructed from device shares
    pub combined_entropy: Vec<u8>,

    /// All device shares collected (K-of-M)
    pub device_shares: Vec<DeviceShare>,

    /// Threshold parameters
    pub threshold_k: u8,
    pub total_devices_m: u8,

    /// Leader's node ID (for audit trail)
    pub leader_node_id: Vec<u8>,
}

/// Encrypted entropy message sent via gossip
#[derive(Clone, Encode, Decode, Debug)]
pub struct EntropyMessage {
    /// Block number this entropy is for
    pub block_number: u32,

    /// Encrypted entropy package (AES-256-GCM)
    pub encrypted_package: Vec<u8>,

    /// AES key encrypted with recipient's Falcon1024 public key
    pub encrypted_aes_key: Vec<u8>,

    /// AES-GCM nonce (96 bits)
    pub nonce: [u8; 12],

    /// Falcon1024 signature of encrypted_package by leader
    pub leader_signature: Vec<u8>,

    /// Leader's Falcon1024 public key (for signature verification)
    pub leader_pubkey: Vec<u8>,

    /// Recipient's Falcon1024 public key hash (to identify intended recipient)
    pub recipient_pubkey_hash: [u8; 32],
}

impl EntropyMessage {
    /// Check if message size is within limits
    pub fn is_valid_size(&self) -> bool {
        let size = self.encoded_size();
        size <= MAX_ENTROPY_SIZE
    }

    /// Get encoded size
    pub fn encoded_size(&self) -> usize {
        self.encode().len()
    }
}

/// Nokia Mode: Pure PQC encryption using Falcon1024 + AES-256-GCM
pub mod nokia_mode {
    use super::*;
    use aes_gcm::{
        aead::{Aead, KeyInit, OsRng},
        Aes256Gcm, Nonce,
    };
    use rand::RngCore;

    /// Encrypt entropy package for a specific validator (Nokia mode)
    ///
    /// Steps:
    /// 1. Generate random 32-byte AES key
    /// 2. Encrypt entropy package with AES-256-GCM
    /// 3. Encrypt AES key with recipient's Falcon1024 public key
    /// 4. Sign encrypted package with leader's Falcon1024 private key
    pub fn encrypt_entropy_for_validator(
        package: &EntropyPackage,
        recipient_falcon_pubkey: &[u8],
        leader_falcon_privkey: &[u8],
        leader_falcon_pubkey: &[u8],
    ) -> Result<EntropyMessage, String> {
        // 1. Generate random AES-256 key
        // QPP Integration: This could use qpp_integration::wrap_aes256_key() for compile-time
        // size checking with ConstrainedKey<32>, preventing buffer overflows at compile time.
        let mut aes_key = [0u8; 32];
        OsRng.fill_bytes(&mut aes_key);

        // 2. Generate random nonce for AES-GCM
        let mut nonce_bytes = [0u8; 12];
        OsRng.fill_bytes(&mut nonce_bytes);
        let nonce = Nonce::from_slice(&nonce_bytes);

        // 3. Encrypt entropy package with AES-256-GCM
        let cipher = Aes256Gcm::new_from_slice(&aes_key)
            .map_err(|e| format!("Failed to create AES cipher: {:?}", e))?;

        let package_bytes = package.encode();
        let encrypted_package = cipher.encrypt(nonce, package_bytes.as_ref())
            .map_err(|e| format!("Failed to encrypt package: {:?}", e))?;

        // 4. Encrypt AES key with recipient's Falcon1024 public key
        // TODO: Use actual Falcon1024 encryption when available
        // For now, use placeholder
        let encrypted_aes_key = encrypt_with_falcon1024(&aes_key, recipient_falcon_pubkey)?;

        // 5. Sign encrypted package with leader's Falcon1024 private key
        let leader_signature = sign_with_falcon1024(&encrypted_package, leader_falcon_privkey)?;

        // 6. Create entropy message
        let recipient_pubkey_hash = blake2_256(recipient_falcon_pubkey);

        let msg = EntropyMessage {
            block_number: package.block_number,
            encrypted_package,
            encrypted_aes_key,
            nonce: nonce_bytes,
            leader_signature,
            leader_pubkey: leader_falcon_pubkey.to_vec(),
            recipient_pubkey_hash,
        };

        info!("🔐 Encrypted entropy package for validator (size: {} bytes)", msg.encoded_size());

        Ok(msg)
    }

    /// Decrypt entropy package (Nokia mode)
    pub fn decrypt_entropy_package(
        msg: &EntropyMessage,
        recipient_falcon_privkey: &[u8],
        recipient_falcon_pubkey: &[u8],
    ) -> Result<EntropyPackage, String> {
        // 1. Verify we are the intended recipient
        let our_pubkey_hash = blake2_256(recipient_falcon_pubkey);
        if our_pubkey_hash != msg.recipient_pubkey_hash {
            return Err("Not intended recipient".into());
        }

        debug!("✅ Verified we are intended recipient");

        // 2. Verify leader's signature
        verify_falcon1024_signature(
            &msg.encrypted_package,
            &msg.leader_signature,
            &msg.leader_pubkey,
        )?;

        debug!("✅ Verified leader signature");

        // 3. Decrypt AES key with our Falcon1024 private key
        let aes_key = decrypt_with_falcon1024(&msg.encrypted_aes_key, recipient_falcon_privkey)?;

        // 4. Decrypt entropy package with AES key
        let cipher = Aes256Gcm::new_from_slice(&aes_key)
            .map_err(|e| format!("Failed to create AES cipher: {:?}", e))?;

        let nonce = Nonce::from_slice(&msg.nonce);
        let package_bytes = cipher.decrypt(nonce, msg.encrypted_package.as_ref())
            .map_err(|e| format!("Failed to decrypt package: {:?}", e))?;

        // 5. Decode entropy package
        let package = EntropyPackage::decode(&mut &package_bytes[..])
            .map_err(|e| format!("Failed to decode package: {:?}", e))?;

        info!("🔓 Decrypted entropy package for block #{}", package.block_number);

        Ok(package)
    }

    // Real Falcon1024 + ML-KEM authenticated encryption functions

    /// Encrypt data using ML-KEM-1024 (for encryption) + AES-256-GCM
    /// Note: Falcon is signature-only, so we use ML-KEM-1024 (Kyber) for key encapsulation
    fn encrypt_with_falcon1024(data: &[u8], kem_pubkey: &[u8]) -> Result<Vec<u8>, String> {
        debug!("🔒 ML-KEM-1024 + AES-256-GCM encryption - {} bytes", data.len());

        // Parse ML-KEM public key
        let public_key = kyber1024::PublicKey::from_bytes(kem_pubkey)
            .map_err(|_| "Invalid ML-KEM public key".to_string())?;

        // Encapsulate: generate shared secret + ciphertext
        let (shared_secret, ciphertext) = kyber1024::encapsulate(&public_key);

        // Use shared secret as AES-256-GCM key (first 32 bytes)
        let shared_bytes = shared_secret.as_bytes();
        let aes_key = &shared_bytes[..32];

        // Generate random nonce
        let mut nonce_bytes = [0u8; 12];
        rand::thread_rng().fill_bytes(&mut nonce_bytes);
        let nonce = Nonce::from_slice(&nonce_bytes);

        // Encrypt data with AES-256-GCM
        let cipher = Aes256Gcm::new_from_slice(aes_key)
            .map_err(|e| format!("AES key error: {}", e))?;
        let ciphertext_data = cipher
            .encrypt(nonce, data)
            .map_err(|e| format!("Encryption failed: {}", e))?;

        // Format: [KEM ciphertext length (4 bytes)][KEM ciphertext][nonce (12 bytes)][AES ciphertext]
        let kem_ct_bytes = ciphertext.as_bytes();
        let mut result = Vec::with_capacity(4 + kem_ct_bytes.len() + 12 + ciphertext_data.len());
        result.extend_from_slice(&(kem_ct_bytes.len() as u32).to_le_bytes());
        result.extend_from_slice(kem_ct_bytes);
        result.extend_from_slice(&nonce_bytes);
        result.extend_from_slice(&ciphertext_data);

        debug!("✅ Encrypted {} bytes → {} bytes", data.len(), result.len());
        Ok(result)
    }

    /// Decrypt data using ML-KEM-1024 secret key
    fn decrypt_with_falcon1024(encrypted: &[u8], kem_privkey: &[u8]) -> Result<Vec<u8>, String> {
        debug!("🔓 ML-KEM-1024 + AES-256-GCM decryption - {} bytes", encrypted.len());

        if encrypted.len() < 4 + 12 {
            return Err("Encrypted data too short".into());
        }

        // Parse format: [KEM ct length][KEM ciphertext][nonce][AES ciphertext]
        let kem_ct_len = u32::from_le_bytes([encrypted[0], encrypted[1], encrypted[2], encrypted[3]]) as usize;
        if encrypted.len() < 4 + kem_ct_len + 12 {
            return Err("Invalid encrypted data format".into());
        }

        let kem_ct_bytes = &encrypted[4..4 + kem_ct_len];
        let nonce_bytes = &encrypted[4 + kem_ct_len..4 + kem_ct_len + 12];
        let ciphertext_data = &encrypted[4 + kem_ct_len + 12..];

        // Parse ML-KEM secret key and ciphertext
        let secret_key = kyber1024::SecretKey::from_bytes(kem_privkey)
            .map_err(|_| "Invalid ML-KEM secret key".to_string())?;
        let ciphertext = kyber1024::Ciphertext::from_bytes(kem_ct_bytes)
            .map_err(|_| "Invalid ML-KEM ciphertext".to_string())?;

        // Decapsulate to get shared secret
        let shared_secret = kyber1024::decapsulate(&ciphertext, &secret_key);
        let shared_bytes = shared_secret.as_bytes();
        let aes_key = &shared_bytes[..32];

        // Decrypt with AES-256-GCM
        let cipher = Aes256Gcm::new_from_slice(aes_key)
            .map_err(|e| format!("AES key error: {}", e))?;
        let nonce = Nonce::from_slice(nonce_bytes);
        let plaintext = cipher
            .decrypt(nonce, ciphertext_data)
            .map_err(|e| format!("Decryption failed: {}", e))?;

        debug!("✅ Decrypted {} bytes → {} bytes", encrypted.len(), plaintext.len());
        Ok(plaintext)
    }

    /// Sign data with Falcon1024
    fn sign_with_falcon1024(data: &[u8], privkey: &[u8]) -> Result<Vec<u8>, String> {
        debug!("✍️  Falcon1024 signature - {} bytes", data.len());

        let secret_key = falcon1024::SecretKey::from_bytes(privkey)
            .map_err(|_| "Invalid Falcon1024 secret key".to_string())?;

        let signed_msg = falcon1024::sign(data, &secret_key);
        let signature = signed_msg.as_bytes().to_vec();

        debug!("✅ Falcon1024 signature generated - {} bytes", signature.len());
        Ok(signature)
    }

    /// Verify Falcon1024 signature
    fn verify_falcon1024_signature(
        data: &[u8],
        signature: &[u8],
        pubkey: &[u8],
    ) -> Result<(), String> {
        debug!("🔍 Falcon1024 signature verification");

        let public_key = falcon1024::PublicKey::from_bytes(pubkey)
            .map_err(|_| "Invalid Falcon1024 public key".to_string())?;

        let signed_msg = falcon1024::SignedMessage::from_bytes(signature)
            .map_err(|_| "Invalid Falcon1024 signature format".to_string())?;

        let verified_msg = falcon1024::open(&signed_msg, &public_key)
            .map_err(|_| "Falcon1024 signature verification failed".to_string())?;

        // Verify the message content matches
        if verified_msg != data {
            return Err("Message content mismatch".into());
        }

        debug!("✅ Falcon1024 signature valid");
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::threshold_qrng::DeviceId;

    #[test]
    fn test_entropy_package_encoding() {
        let package = EntropyPackage {
            block_number: 100,
            timestamp: 1234567890,
            combined_entropy: vec![0x01, 0x02, 0x03],
            device_shares: vec![
                DeviceShare {
                    device_id: DeviceId::from_str("test-device"),
                    share: vec![0xAA, 0xBB],
                    qber: 50,
                    stark_proof: vec![0xCC; 32],
                    timestamp: 1234567890,
                }
            ],
            threshold_k: 2,
            total_devices_m: 3,
            leader_node_id: vec![0x01, 0x02],
        };

        let encoded = package.encode();
        let decoded = EntropyPackage::decode(&mut &encoded[..]).unwrap();

        assert_eq!(decoded.block_number, 100);
        assert_eq!(decoded.combined_entropy, vec![0x01, 0x02, 0x03]);
        assert_eq!(decoded.device_shares.len(), 1);
    }

    #[test]
    fn test_nokia_mode_encryption() {
        let package = EntropyPackage {
            block_number: 100,
            timestamp: 1234567890,
            combined_entropy: vec![0x01, 0x02, 0x03],
            device_shares: vec![],
            threshold_k: 2,
            total_devices_m: 3,
            leader_node_id: vec![0x01],
        };

        // Generate real ML-KEM-1024 keypair for encryption
        let (recipient_kem_pubkey, recipient_kem_privkey) = kyber1024::keypair();

        // Generate real Falcon1024 keypair for signing
        let (leader_falcon_pubkey, leader_falcon_privkey) = falcon1024::keypair();

        let msg = nokia_mode::encrypt_entropy_for_validator(
            &package,
            recipient_kem_pubkey.as_bytes(),
            leader_falcon_privkey.as_bytes(),
            leader_falcon_pubkey.as_bytes(),
        ).unwrap();

        assert_eq!(msg.block_number, 100);
        assert!(!msg.encrypted_package.is_empty());
        assert!(!msg.encrypted_aes_key.is_empty());
        assert!(msg.is_valid_size());

        // Test decryption
        let decrypted = nokia_mode::decrypt_entropy_package(
            &msg,
            recipient_kem_privkey.as_bytes(),
            recipient_kem_pubkey.as_bytes(),
        ).unwrap();

        assert_eq!(decrypted.block_number, 100);
        assert_eq!(decrypted.combined_entropy, vec![0x01, 0x02, 0x03]);
    }
}
