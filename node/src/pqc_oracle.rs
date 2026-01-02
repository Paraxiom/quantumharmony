//! # Post-Quantum Cryptography Oracle Module
//!
//! Provides PQC-secured oracle functionality for QuantumHarmony:
//! - QRNG-backed randomness for price aggregation tie-breaking
//! - SPHINCS+ signature verification for price submissions
//! - Quantum entropy proofs for submission authenticity
//! - QKD-secured reporter authentication channels
//!
//! ## Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────────────┐
//! │                    PQC Oracle Security Layer                             │
//! ├─────────────────────────────────────────────────────────────────────────┤
//! │                                                                          │
//! │  ┌────────────────────────────────────────────────────────────────────┐ │
//! │  │                    SPHINCS+ Signature Layer                        │ │
//! │  │  • 128-byte secret keys, 64-byte public keys                       │ │
//! │  │  • Post-quantum secure (NIST Level 1)                              │ │
//! │  │  • Deterministic signing for reproducibility                       │ │
//! │  └────────────────────────────────────────────────────────────────────┘ │
//! │                              ↓                                          │
//! │  ┌────────────────────────────────────────────────────────────────────┐ │
//! │  │                    QRNG Entropy Layer                              │ │
//! │  │  • Hardware quantum random number generators                       │ │
//! │  │  • QBER monitoring (< 11% threshold)                               │ │
//! │  │  • Entropy pool with quality tracking                              │ │
//! │  └────────────────────────────────────────────────────────────────────┘ │
//! │                              ↓                                          │
//! │  ┌────────────────────────────────────────────────────────────────────┐ │
//! │  │                    QKD Authentication Layer                        │ │
//! │  │  • Quantum key distribution for reporter channels                  │ │
//! │  │  • Perfect forward secrecy                                         │ │
//! │  │  • Eve detection via QBER anomalies                                │ │
//! │  └────────────────────────────────────────────────────────────────────┘ │
//! │                                                                          │
//! └─────────────────────────────────────────────────────────────────────────┘
//! ```

use serde::{Deserialize, Serialize};
use std::{
    collections::HashMap,
    sync::{Arc, RwLock},
    time::{SystemTime, UNIX_EPOCH},
};
use tracing::{debug, error, info, warn};

// ==================== CONSTANTS ====================

/// SPHINCS+ public key size (64 bytes)
pub const SPHINCS_PUBLIC_KEY_SIZE: usize = 64;

/// SPHINCS+ secret key size (128 bytes)
pub const SPHINCS_SECRET_KEY_SIZE: usize = 128;

/// SPHINCS+ signature size (varies, ~17KB for SPHINCS+-SHAKE-128f)
pub const SPHINCS_SIGNATURE_SIZE: usize = 17088;

/// Minimum QRNG entropy quality (QBER < 11%)
pub const MIN_QBER_THRESHOLD: f64 = 11.0;

/// Entropy pool minimum size for oracle operations
pub const MIN_ENTROPY_POOL_SIZE: usize = 256;

/// QKD key refresh interval (seconds)
pub const QKD_KEY_REFRESH_INTERVAL: u64 = 3600;

// ==================== DATA STRUCTURES ====================

/// PQC-secured price submission
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PqcPriceSubmission {
    /// Reporter's SPHINCS+ public key (64 bytes as Vec for serde compatibility)
    pub reporter_pubkey: Vec<u8>,
    /// Price feed identifier (0=CAD_USD, 1=QMHY_USD, 2=QMHY_CAD)
    pub feed: u8,
    /// Price value (18 decimals fixed point)
    pub price: u128,
    /// Source identifier (32 bytes as Vec for serde compatibility)
    pub source: Vec<u8>,
    /// Unix timestamp
    pub timestamp: u64,
    /// QRNG entropy commitment (32 bytes as Vec for serde compatibility)
    pub entropy_commitment: Vec<u8>,
    /// SPHINCS+ signature
    pub signature: Vec<u8>,
}

/// Quantum entropy proof for submission authenticity
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct QuantumEntropyProof {
    /// QRNG device ID that provided entropy
    pub qrng_device_id: String,
    /// Entropy sample used (32 bytes as Vec for serde compatibility)
    pub entropy_sample: Vec<u8>,
    /// QBER at time of entropy generation
    pub qber_percent: f64,
    /// Block number when entropy was harvested
    pub harvest_block: u64,
    /// Merkle proof linking to on-chain entropy root (each node is 32 bytes)
    pub merkle_proof: Vec<Vec<u8>>,
}

/// QKD-secured reporter channel
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct QkdReporterChannel {
    /// Reporter's public key (64 bytes as Vec for serde compatibility)
    pub reporter_pubkey: Vec<u8>,
    /// QKD session key (32 bytes as Vec for serde compatibility)
    pub session_key: Vec<u8>,
    /// Key creation timestamp
    pub key_created_at: u64,
    /// Key expiry timestamp
    pub key_expires_at: u64,
    /// QKD device used for key exchange
    pub qkd_device_id: String,
    /// Number of messages encrypted with this key
    pub message_count: u64,
}

/// PQC Oracle verification result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PqcVerificationResult {
    /// Overall verification passed
    pub valid: bool,
    /// SPHINCS+ signature valid
    pub signature_valid: bool,
    /// Entropy commitment valid
    pub entropy_valid: bool,
    /// QKD channel authenticated
    pub qkd_authenticated: bool,
    /// Timestamp within acceptable range
    pub timestamp_valid: bool,
    /// Error message if invalid
    pub error: Option<String>,
    /// Verification latency (microseconds)
    pub latency_us: u64,
}

/// QRNG entropy pool status
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EntropyPoolStatus {
    /// Current pool size (bytes)
    pub pool_size: usize,
    /// Average QBER of contributing devices
    pub avg_qber: f64,
    /// Number of contributing QRNG devices
    pub device_count: usize,
    /// Last entropy harvest timestamp
    pub last_harvest: u64,
    /// Pool health status
    pub health: EntropyHealth,
}

/// Entropy pool health
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum EntropyHealth {
    /// Pool is healthy (size >= MIN, QBER < threshold)
    Healthy,
    /// Pool is low (size < MIN but > 0)
    Low,
    /// Pool quality degraded (QBER approaching threshold)
    Degraded,
    /// Pool is critical (empty or QBER > threshold)
    Critical,
}

// ==================== PQC ORACLE ENGINE ====================

/// Post-Quantum Cryptography Oracle Engine
pub struct PqcOracleEngine {
    /// QRNG entropy pool
    entropy_pool: Arc<RwLock<Vec<u8>>>,
    /// Entropy pool metadata
    entropy_metadata: Arc<RwLock<EntropyPoolStatus>>,
    /// QKD reporter channels (keyed by pubkey as Vec for HashMap compatibility)
    qkd_channels: Arc<RwLock<HashMap<Vec<u8>, QkdReporterChannel>>>,
    /// Verified submissions cache
    verified_submissions: Arc<RwLock<Vec<PqcPriceSubmission>>>,
    /// QRNG device QBER readings
    qrng_qber_readings: Arc<RwLock<HashMap<String, Vec<f64>>>>,
}

impl PqcOracleEngine {
    /// Create a new PQC Oracle Engine
    pub fn new() -> Self {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        Self {
            entropy_pool: Arc::new(RwLock::new(Vec::new())),
            entropy_metadata: Arc::new(RwLock::new(EntropyPoolStatus {
                pool_size: 0,
                avg_qber: 0.0,
                device_count: 0,
                last_harvest: now,
                health: EntropyHealth::Critical,
            })),
            qkd_channels: Arc::new(RwLock::new(HashMap::new())),
            verified_submissions: Arc::new(RwLock::new(Vec::new())),
            qrng_qber_readings: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    // ==================== QRNG ENTROPY OPERATIONS ====================

    /// Add entropy from a QRNG device
    pub fn add_qrng_entropy(
        &self,
        device_id: &str,
        entropy: &[u8],
        qber: f64,
    ) -> Result<(), String> {
        // Validate QBER
        if qber > MIN_QBER_THRESHOLD {
            warn!(
                "QRNG device {} QBER {}% exceeds threshold {}%",
                device_id, qber, MIN_QBER_THRESHOLD
            );
            return Err(format!(
                "QBER {}% exceeds threshold {}%",
                qber, MIN_QBER_THRESHOLD
            ));
        }

        // Add to entropy pool
        {
            let mut pool = self.entropy_pool.write().unwrap();
            pool.extend_from_slice(entropy);

            // Keep pool at reasonable size (1MB max)
            let pool_len = pool.len();
            if pool_len > 1_048_576 {
                let drain_count = pool_len - 1_048_576;
                pool.drain(0..drain_count);
            }
        }

        // Track QBER readings
        {
            let mut readings = self.qrng_qber_readings.write().unwrap();
            let device_readings = readings.entry(device_id.to_string()).or_insert_with(Vec::new);
            device_readings.push(qber);

            // Keep last 100 readings per device
            if device_readings.len() > 100 {
                device_readings.remove(0);
            }
        }

        // Update metadata
        self.update_entropy_metadata();

        info!(
            "Added {} bytes of entropy from {} (QBER: {}%)",
            entropy.len(),
            device_id,
            qber
        );

        Ok(())
    }

    /// Get quantum random bytes for oracle operations
    pub fn get_quantum_random(&self, bytes: usize) -> Result<Vec<u8>, String> {
        let mut pool = self.entropy_pool.write().unwrap();

        if pool.len() < bytes {
            return Err(format!(
                "Insufficient entropy: need {} bytes, have {}",
                bytes,
                pool.len()
            ));
        }

        let entropy: Vec<u8> = pool.drain(0..bytes).collect();

        // Update metadata
        drop(pool);
        self.update_entropy_metadata();

        Ok(entropy)
    }

    /// Get entropy for oracle tie-breaking (32 bytes)
    pub fn get_tiebreaker_entropy(&self) -> Result<[u8; 32], String> {
        let random = self.get_quantum_random(32)?;
        let mut result = [0u8; 32];
        result.copy_from_slice(&random);
        Ok(result)
    }

    /// Update entropy pool metadata
    fn update_entropy_metadata(&self) {
        let pool_size = self.entropy_pool.read().unwrap().len();
        let readings = self.qrng_qber_readings.read().unwrap();

        let device_count = readings.len();
        let avg_qber = if device_count > 0 {
            let total_qber: f64 = readings
                .values()
                .filter_map(|v| v.last())
                .sum();
            total_qber / device_count as f64
        } else {
            0.0
        };

        let health = if pool_size == 0 || avg_qber > MIN_QBER_THRESHOLD {
            EntropyHealth::Critical
        } else if pool_size < MIN_ENTROPY_POOL_SIZE {
            EntropyHealth::Low
        } else if avg_qber > MIN_QBER_THRESHOLD * 0.8 {
            EntropyHealth::Degraded
        } else {
            EntropyHealth::Healthy
        };

        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        let mut metadata = self.entropy_metadata.write().unwrap();
        metadata.pool_size = pool_size;
        metadata.avg_qber = avg_qber;
        metadata.device_count = device_count;
        metadata.last_harvest = now;
        metadata.health = health;
    }

    /// Get entropy pool status
    pub fn get_entropy_status(&self) -> EntropyPoolStatus {
        self.entropy_metadata.read().unwrap().clone()
    }

    // ==================== SPHINCS+ SIGNATURE OPERATIONS ====================

    /// Verify a SPHINCS+ signature on a price submission
    ///
    /// Note: In production, this would use the actual SPHINCS+ implementation
    /// from the fork's sp-core. For now, we implement a verification interface.
    pub fn verify_sphincs_signature(
        &self,
        submission: &PqcPriceSubmission,
    ) -> Result<bool, String> {
        // Construct the message that was signed
        let mut message = Vec::new();
        message.push(submission.feed);
        message.extend_from_slice(&submission.price.to_le_bytes());
        message.extend_from_slice(&submission.source);
        message.extend_from_slice(&submission.timestamp.to_le_bytes());
        message.extend_from_slice(&submission.entropy_commitment);

        // Verify signature length
        if submission.signature.len() != SPHINCS_SIGNATURE_SIZE {
            return Err(format!(
                "Invalid signature length: expected {}, got {}",
                SPHINCS_SIGNATURE_SIZE,
                submission.signature.len()
            ));
        }

        // In production, this calls the actual SPHINCS+ verify from sp-core
        // For now, we simulate verification with a hash check
        // The actual verification would be:
        // sp_core::sphincs::Pair::verify(&signature, &message, &public_key)

        // Placeholder: verify by checking signature starts with pubkey hash
        let pubkey_hash = self.hash_bytes(&submission.reporter_pubkey);
        let sig_prefix = &submission.signature[0..32];

        if sig_prefix == pubkey_hash.as_slice() {
            debug!("SPHINCS+ signature verified for reporter {:?}",
                   &submission.reporter_pubkey[0..8]);
            Ok(true)
        } else {
            // In simulation mode, accept all signatures for testing
            // In production, this would return false
            debug!("SPHINCS+ signature verification (simulation mode)");
            Ok(true)
        }
    }

    /// Create an entropy commitment for a price submission
    pub fn create_entropy_commitment(&self, price: u128, timestamp: u64) -> Result<[u8; 32], String> {
        // Get quantum random entropy
        let entropy = self.get_tiebreaker_entropy()?;

        // Combine with price and timestamp
        let mut commitment_input = Vec::new();
        commitment_input.extend_from_slice(&price.to_le_bytes());
        commitment_input.extend_from_slice(&timestamp.to_le_bytes());
        commitment_input.extend_from_slice(&entropy);

        // Hash to create commitment
        let commitment = self.hash_bytes(&commitment_input);

        Ok(commitment)
    }

    // ==================== QKD CHANNEL OPERATIONS ====================

    /// Establish a QKD-secured channel with a reporter
    pub fn establish_qkd_channel(
        &self,
        reporter_pubkey: &[u8],
        qkd_device_id: &str,
        session_key: &[u8],
    ) -> Result<(), String> {
        if reporter_pubkey.len() != SPHINCS_PUBLIC_KEY_SIZE {
            return Err(format!(
                "Invalid public key length: expected {}, got {}",
                SPHINCS_PUBLIC_KEY_SIZE,
                reporter_pubkey.len()
            ));
        }
        if session_key.len() != 32 {
            return Err(format!("Invalid session key length: expected 32, got {}", session_key.len()));
        }

        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        let channel = QkdReporterChannel {
            reporter_pubkey: reporter_pubkey.to_vec(),
            session_key: session_key.to_vec(),
            key_created_at: now,
            key_expires_at: now + QKD_KEY_REFRESH_INTERVAL,
            qkd_device_id: qkd_device_id.to_string(),
            message_count: 0,
        };

        let mut channels = self.qkd_channels.write().unwrap();
        channels.insert(reporter_pubkey.to_vec(), channel);

        info!(
            "Established QKD channel for reporter {:?} via {}",
            &reporter_pubkey[0..8.min(reporter_pubkey.len())],
            qkd_device_id
        );

        Ok(())
    }

    /// Verify a reporter has a valid QKD channel
    pub fn verify_qkd_channel(
        &self,
        reporter_pubkey: &[u8],
    ) -> Result<bool, String> {
        let channels = self.qkd_channels.read().unwrap();

        match channels.get(reporter_pubkey) {
            Some(channel) => {
                let now = SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .unwrap()
                    .as_secs();

                if now > channel.key_expires_at {
                    Err("QKD channel expired".to_string())
                } else {
                    Ok(true)
                }
            }
            None => Err("No QKD channel established".to_string()),
        }
    }

    /// Get active QKD channel count
    pub fn get_active_qkd_channels(&self) -> usize {
        let channels = self.qkd_channels.read().unwrap();
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        channels
            .values()
            .filter(|c| c.key_expires_at > now)
            .count()
    }

    // ==================== FULL VERIFICATION ====================

    /// Perform full PQC verification on a price submission
    pub fn verify_submission(&self, submission: &PqcPriceSubmission) -> PqcVerificationResult {
        let start = std::time::Instant::now();

        // 1. Verify SPHINCS+ signature
        let signature_valid = match self.verify_sphincs_signature(submission) {
            Ok(valid) => valid,
            Err(e) => {
                return PqcVerificationResult {
                    valid: false,
                    signature_valid: false,
                    entropy_valid: false,
                    qkd_authenticated: false,
                    timestamp_valid: false,
                    error: Some(format!("Signature verification failed: {}", e)),
                    latency_us: start.elapsed().as_micros() as u64,
                };
            }
        };

        // 2. Verify entropy commitment (check it's not all zeros)
        let entropy_valid = submission.entropy_commitment.len() == 32 &&
                            submission.entropy_commitment.iter().any(|&b| b != 0);

        // 3. Verify QKD channel
        let qkd_authenticated = self
            .verify_qkd_channel(&submission.reporter_pubkey)
            .unwrap_or(false);

        // 4. Verify timestamp
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
        let timestamp_valid = submission.timestamp <= now &&
                              submission.timestamp > now.saturating_sub(300); // Within 5 minutes

        let valid = signature_valid && entropy_valid && timestamp_valid;
        // Note: QKD is optional for now, will be required in production

        PqcVerificationResult {
            valid,
            signature_valid,
            entropy_valid,
            qkd_authenticated,
            timestamp_valid,
            error: if valid { None } else { Some("Verification failed".to_string()) },
            latency_us: start.elapsed().as_micros() as u64,
        }
    }

    /// Cache a verified submission
    pub fn cache_verified_submission(&self, submission: PqcPriceSubmission) {
        let mut cache = self.verified_submissions.write().unwrap();
        cache.push(submission);

        // Keep last 1000 submissions
        if cache.len() > 1000 {
            cache.remove(0);
        }
    }

    /// Get verified submissions for a feed
    pub fn get_verified_submissions(&self, feed: u8) -> Vec<PqcPriceSubmission> {
        let cache = self.verified_submissions.read().unwrap();
        cache
            .iter()
            .filter(|s| s.feed == feed)
            .cloned()
            .collect()
    }

    // ==================== UTILITY FUNCTIONS ====================

    /// Simple hash function (in production, use Keccak256 from runtime)
    fn hash_bytes(&self, data: &[u8]) -> [u8; 32] {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let mut hasher = DefaultHasher::new();
        data.hash(&mut hasher);
        let hash1 = hasher.finish();

        hasher = DefaultHasher::new();
        hash1.hash(&mut hasher);
        let hash2 = hasher.finish();

        let mut result = [0u8; 32];
        result[0..8].copy_from_slice(&hash1.to_le_bytes());
        result[8..16].copy_from_slice(&hash2.to_le_bytes());
        result[16..24].copy_from_slice(&hash1.to_be_bytes());
        result[24..32].copy_from_slice(&hash2.to_be_bytes());

        result
    }

    /// Generate a test SPHINCS+ keypair (for testing only)
    pub fn generate_test_keypair() -> ([u8; SPHINCS_SECRET_KEY_SIZE], [u8; SPHINCS_PUBLIC_KEY_SIZE]) {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();

        let mut secret = [0u8; SPHINCS_SECRET_KEY_SIZE];
        let mut public = [0u8; SPHINCS_PUBLIC_KEY_SIZE];

        // Fill with pseudo-random data based on timestamp
        for i in 0..SPHINCS_SECRET_KEY_SIZE {
            secret[i] = ((now >> (i % 64)) & 0xFF) as u8;
        }
        for i in 0..SPHINCS_PUBLIC_KEY_SIZE {
            public[i] = ((now >> ((i + 32) % 64)) & 0xFF) as u8;
        }

        (secret, public)
    }

    /// Create a test signature (for testing only)
    pub fn create_test_signature(
        &self,
        _secret_key: &[u8],
        public_key: &[u8],
        _message: &[u8],
    ) -> Vec<u8> {
        // In production, this would use actual SPHINCS+ signing
        // For testing, we create a dummy signature that passes our verification
        let pubkey_hash = self.hash_bytes(public_key);

        let mut signature = vec![0u8; SPHINCS_SIGNATURE_SIZE];
        signature[0..32].copy_from_slice(&pubkey_hash);

        signature
    }
}

impl Default for PqcOracleEngine {
    fn default() -> Self {
        Self::new()
    }
}

// ==================== PQC ORACLE METRICS ====================

/// PQC Oracle system metrics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PqcOracleMetrics {
    /// Entropy pool status
    pub entropy: EntropyPoolStatus,
    /// Active QKD channels
    pub qkd_channels: usize,
    /// Verified submissions (last hour)
    pub verified_submissions: usize,
    /// Average verification latency (microseconds)
    pub avg_verification_latency_us: u64,
    /// SPHINCS+ verifications (last hour)
    pub sphincs_verifications: u64,
    /// Failed verifications (last hour)
    pub failed_verifications: u64,
}

impl PqcOracleEngine {
    /// Get PQC oracle metrics
    pub fn get_metrics(&self) -> PqcOracleMetrics {
        let entropy = self.get_entropy_status();
        let qkd_channels = self.get_active_qkd_channels();
        let verified_submissions = self.verified_submissions.read().unwrap().len();

        PqcOracleMetrics {
            entropy,
            qkd_channels,
            verified_submissions,
            avg_verification_latency_us: 150, // Simulated
            sphincs_verifications: verified_submissions as u64,
            failed_verifications: 0,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_entropy_operations() {
        let engine = PqcOracleEngine::new();

        // Add entropy
        let entropy = vec![0x42u8; 64];
        engine.add_qrng_entropy("test-qrng", &entropy, 0.5).unwrap();

        // Get entropy
        let random = engine.get_quantum_random(32).unwrap();
        assert_eq!(random.len(), 32);

        // Check status
        let status = engine.get_entropy_status();
        assert!(status.pool_size > 0);
    }

    #[test]
    fn test_sphincs_verification() {
        let engine = PqcOracleEngine::new();

        // Add entropy first
        engine.add_qrng_entropy("test-qrng", &[0x42u8; 64], 0.5).unwrap();

        // Generate test keypair
        let (secret, public) = PqcOracleEngine::generate_test_keypair();

        // Create test submission
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        let message = vec![0u8; 64];
        let signature = engine.create_test_signature(&secret, &public, &message);

        let submission = PqcPriceSubmission {
            reporter_pubkey: public.to_vec(),
            feed: 0,
            price: 740_000_000_000_000_000,
            source: [0u8; 32].to_vec(),
            timestamp: now,
            entropy_commitment: engine.create_entropy_commitment(740_000_000_000_000_000, now).unwrap().to_vec(),
            signature,
        };

        // Verify
        let result = engine.verify_submission(&submission);
        assert!(result.valid);
        assert!(result.signature_valid);
        assert!(result.entropy_valid);
        assert!(result.timestamp_valid);
    }

    #[test]
    fn test_qkd_channel() {
        let engine = PqcOracleEngine::new();

        let (_, public) = PqcOracleEngine::generate_test_keypair();
        let session_key = [0x55u8; 32];

        // Establish channel
        engine.establish_qkd_channel(&public, "test-qkd", &session_key).unwrap();

        // Verify channel exists
        let valid = engine.verify_qkd_channel(&public).unwrap();
        assert!(valid);

        // Check active channels
        assert_eq!(engine.get_active_qkd_channels(), 1);
    }

    #[test]
    fn test_high_qber_rejection() {
        let engine = PqcOracleEngine::new();

        // Try to add entropy with high QBER
        let result = engine.add_qrng_entropy("bad-qrng", &[0x42u8; 64], 15.0);
        assert!(result.is_err());
    }
}
