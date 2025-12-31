//! # PQC Oracle RPC API
//!
//! Provides RPC endpoints for the Post-Quantum Cryptography oracle system:
//! - QRNG entropy management
//! - SPHINCS+ signature verification
//! - QKD channel management
//! - PQC metrics and status

use crate::pqc_oracle::{
    EntropyHealth, EntropyPoolStatus, PqcOracleEngine, PqcOracleMetrics,
    PqcPriceSubmission, PqcVerificationResult, QkdReporterChannel,
    SPHINCS_PUBLIC_KEY_SIZE, SPHINCS_SECRET_KEY_SIZE,
};
use jsonrpsee::core::RpcResult;
use jsonrpsee::proc_macros::rpc;
use jsonrpsee::types::ErrorObjectOwned;
use serde::{Deserialize, Serialize};
use sp_api::ProvideRuntimeApi;
use sp_blockchain::HeaderBackend;
use sp_runtime::traits::Block as BlockT;
use std::marker::PhantomData;
use std::sync::{Arc, RwLock};
use std::time::{SystemTime, UNIX_EPOCH};

// ==================== RPC DATA TYPES ====================

/// PQC system status returned by RPC
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PqcStatus {
    /// Entropy pool health
    pub entropy_health: String,
    /// Entropy pool size (bytes)
    pub entropy_pool_size: usize,
    /// Average QBER across QRNG devices
    pub avg_qber: f64,
    /// Active QRNG devices
    pub qrng_device_count: usize,
    /// Active QKD channels
    pub qkd_channels: usize,
    /// Verified submissions (cached)
    pub verified_submissions: usize,
    /// System ready for PQC operations
    pub ready: bool,
}

/// SPHINCS+ keypair for testing
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SphincsKeypair {
    /// Secret key (hex encoded, 128 bytes)
    pub secret_key: String,
    /// Public key (hex encoded, 64 bytes)
    pub public_key: String,
}

/// PQC price submission request
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PqcSubmissionRequest {
    /// Reporter's public key (hex)
    pub reporter_pubkey: String,
    /// Feed (0=CAD_USD, 1=QMHY_USD, 2=QMHY_CAD)
    pub feed: u8,
    /// Price (string for precision)
    pub price: String,
    /// Source identifier
    pub source: String,
    /// SPHINCS+ signature (hex)
    pub signature: String,
}

/// PQC verification response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PqcVerificationResponse {
    /// Overall valid
    pub valid: bool,
    /// Signature valid
    pub signature_valid: bool,
    /// Entropy commitment valid
    pub entropy_valid: bool,
    /// QKD authenticated
    pub qkd_authenticated: bool,
    /// Timestamp valid
    pub timestamp_valid: bool,
    /// Error if any
    pub error: Option<String>,
    /// Verification latency (microseconds)
    pub latency_us: u64,
}

/// QKD channel establishment request
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct QkdChannelRequest {
    /// Reporter's public key (hex)
    pub reporter_pubkey: String,
    /// QKD device ID
    pub qkd_device_id: String,
    /// Session key (hex, 32 bytes) - in production, derived from QKD
    pub session_key: String,
}

// ==================== RPC TRAIT ====================

/// PQC Oracle RPC trait
#[rpc(server, client)]
pub trait PqcOracleApi {
    /// Get PQC system status
    #[method(name = "pqc_getStatus")]
    async fn get_status(&self) -> RpcResult<PqcStatus>;

    /// Get detailed PQC metrics
    #[method(name = "pqc_getMetrics")]
    async fn get_metrics(&self) -> RpcResult<PqcOracleMetrics>;

    /// Get entropy pool status
    #[method(name = "pqc_getEntropyStatus")]
    async fn get_entropy_status(&self) -> RpcResult<EntropyPoolStatus>;

    /// Add QRNG entropy to the pool
    #[method(name = "pqc_addEntropy")]
    async fn add_entropy(
        &self,
        device_id: String,
        entropy_hex: String,
        qber: f64,
    ) -> RpcResult<bool>;

    /// Get quantum random bytes (hex encoded)
    #[method(name = "pqc_getQuantumRandom")]
    async fn get_quantum_random(&self, bytes: usize) -> RpcResult<String>;

    /// Generate a test SPHINCS+ keypair
    #[method(name = "pqc_generateTestKeypair")]
    async fn generate_test_keypair(&self) -> RpcResult<SphincsKeypair>;

    /// Submit a PQC-secured price
    #[method(name = "pqc_submitPrice")]
    async fn submit_price(&self, request: PqcSubmissionRequest) -> RpcResult<PqcVerificationResponse>;

    /// Verify a price submission without caching
    #[method(name = "pqc_verifySubmission")]
    async fn verify_submission(&self, request: PqcSubmissionRequest) -> RpcResult<PqcVerificationResponse>;

    /// Establish a QKD channel with a reporter
    #[method(name = "pqc_establishQkdChannel")]
    async fn establish_qkd_channel(&self, request: QkdChannelRequest) -> RpcResult<bool>;

    /// Check if a reporter has a valid QKD channel
    #[method(name = "pqc_checkQkdChannel")]
    async fn check_qkd_channel(&self, reporter_pubkey: String) -> RpcResult<bool>;

    /// Get verified submissions for a feed
    #[method(name = "pqc_getVerifiedSubmissions")]
    async fn get_verified_submissions(&self, feed: u8) -> RpcResult<Vec<PqcPriceSubmission>>;

    /// Create a test signature for a price submission
    #[method(name = "pqc_createTestSignature")]
    async fn create_test_signature(
        &self,
        secret_key: String,
        public_key: String,
        feed: u8,
        price: String,
    ) -> RpcResult<String>;
}

// ==================== RPC IMPLEMENTATION ====================

/// PQC Oracle RPC implementation
pub struct PqcOracleRpc<C, Block> {
    client: Arc<C>,
    engine: Arc<RwLock<PqcOracleEngine>>,
    _phantom: PhantomData<Block>,
}

impl<C, Block> PqcOracleRpc<C, Block>
where
    Block: BlockT,
    C: ProvideRuntimeApi<Block> + HeaderBackend<Block> + 'static,
{
    pub fn new(client: Arc<C>) -> Self {
        Self {
            client,
            engine: Arc::new(RwLock::new(PqcOracleEngine::new())),
            _phantom: PhantomData,
        }
    }

    fn hex_to_bytes(hex: &str) -> Result<Vec<u8>, String> {
        let hex = hex.strip_prefix("0x").unwrap_or(hex);
        hex::decode(hex).map_err(|e| format!("Invalid hex: {}", e))
    }

    fn bytes_to_hex(bytes: &[u8]) -> String {
        format!("0x{}", hex::encode(bytes))
    }

    fn parse_pubkey(hex: &str) -> Result<Vec<u8>, String> {
        let bytes = Self::hex_to_bytes(hex)?;
        if bytes.len() != SPHINCS_PUBLIC_KEY_SIZE {
            return Err(format!(
                "Invalid public key length: expected {}, got {}",
                SPHINCS_PUBLIC_KEY_SIZE,
                bytes.len()
            ));
        }
        Ok(bytes)
    }
}

#[jsonrpsee::core::async_trait]
impl<C, Block> PqcOracleApiServer for PqcOracleRpc<C, Block>
where
    Block: BlockT,
    C: ProvideRuntimeApi<Block> + HeaderBackend<Block> + Send + Sync + 'static,
{
    async fn get_status(&self) -> RpcResult<PqcStatus> {
        let engine = self.engine.read().unwrap();
        let entropy = engine.get_entropy_status();
        let metrics = engine.get_metrics();

        let health_str = match entropy.health {
            EntropyHealth::Healthy => "healthy",
            EntropyHealth::Low => "low",
            EntropyHealth::Degraded => "degraded",
            EntropyHealth::Critical => "critical",
        };

        let ready = entropy.health == EntropyHealth::Healthy ||
                    entropy.health == EntropyHealth::Low;

        Ok(PqcStatus {
            entropy_health: health_str.to_string(),
            entropy_pool_size: entropy.pool_size,
            avg_qber: entropy.avg_qber,
            qrng_device_count: entropy.device_count,
            qkd_channels: metrics.qkd_channels,
            verified_submissions: metrics.verified_submissions,
            ready,
        })
    }

    async fn get_metrics(&self) -> RpcResult<PqcOracleMetrics> {
        let engine = self.engine.read().unwrap();
        Ok(engine.get_metrics())
    }

    async fn get_entropy_status(&self) -> RpcResult<EntropyPoolStatus> {
        let engine = self.engine.read().unwrap();
        Ok(engine.get_entropy_status())
    }

    async fn add_entropy(
        &self,
        device_id: String,
        entropy_hex: String,
        qber: f64,
    ) -> RpcResult<bool> {
        let entropy = Self::hex_to_bytes(&entropy_hex).map_err(|e| {
            ErrorObjectOwned::owned(-32001, e, None::<String>)
        })?;

        let engine = self.engine.read().unwrap();
        engine.add_qrng_entropy(&device_id, &entropy, qber).map_err(|e| {
            ErrorObjectOwned::owned(-32002, e, None::<String>)
        })?;

        Ok(true)
    }

    async fn get_quantum_random(&self, bytes: usize) -> RpcResult<String> {
        if bytes > 1024 {
            return Err(ErrorObjectOwned::owned(
                -32003,
                "Maximum 1024 bytes allowed",
                None::<String>,
            ));
        }

        let engine = self.engine.read().unwrap();
        let random = engine.get_quantum_random(bytes).map_err(|e| {
            ErrorObjectOwned::owned(-32004, e, None::<String>)
        })?;

        Ok(Self::bytes_to_hex(&random))
    }

    async fn generate_test_keypair(&self) -> RpcResult<SphincsKeypair> {
        let (secret, public) = PqcOracleEngine::generate_test_keypair();

        Ok(SphincsKeypair {
            secret_key: Self::bytes_to_hex(&secret),
            public_key: Self::bytes_to_hex(&public),
        })
    }

    async fn submit_price(&self, request: PqcSubmissionRequest) -> RpcResult<PqcVerificationResponse> {
        let reporter_pubkey = Self::parse_pubkey(&request.reporter_pubkey).map_err(|e| {
            ErrorObjectOwned::owned(-32010, e, None::<String>)
        })?;

        let price: u128 = request.price.parse().map_err(|_| {
            ErrorObjectOwned::owned(-32011, "Invalid price", None::<String>)
        })?;

        let signature = Self::hex_to_bytes(&request.signature).map_err(|e| {
            ErrorObjectOwned::owned(-32012, format!("Invalid signature: {}", e), None::<String>)
        })?;

        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        // Build source as Vec<u8> (padded to 32 bytes)
        let source_bytes = request.source.as_bytes();
        let mut source = vec![0u8; 32];
        let copy_len = source_bytes.len().min(32);
        source[..copy_len].copy_from_slice(&source_bytes[..copy_len]);

        let engine = self.engine.read().unwrap();

        // Create entropy commitment (returns [u8; 32], convert to Vec)
        let entropy_commitment_arr = engine.create_entropy_commitment(price, now).map_err(|e| {
            ErrorObjectOwned::owned(-32013, format!("Entropy error: {}", e), None::<String>)
        })?;
        let entropy_commitment = entropy_commitment_arr.to_vec();

        let submission = PqcPriceSubmission {
            reporter_pubkey,
            feed: request.feed,
            price,
            source,
            timestamp: now,
            entropy_commitment,
            signature,
        };

        // Verify
        let result = engine.verify_submission(&submission);

        if result.valid {
            // Cache the verified submission
            drop(engine);
            let engine = self.engine.read().unwrap();
            engine.cache_verified_submission(submission);
        }

        Ok(PqcVerificationResponse {
            valid: result.valid,
            signature_valid: result.signature_valid,
            entropy_valid: result.entropy_valid,
            qkd_authenticated: result.qkd_authenticated,
            timestamp_valid: result.timestamp_valid,
            error: result.error,
            latency_us: result.latency_us,
        })
    }

    async fn verify_submission(&self, request: PqcSubmissionRequest) -> RpcResult<PqcVerificationResponse> {
        let reporter_pubkey = Self::parse_pubkey(&request.reporter_pubkey).map_err(|e| {
            ErrorObjectOwned::owned(-32010, e, None::<String>)
        })?;

        let price: u128 = request.price.parse().map_err(|_| {
            ErrorObjectOwned::owned(-32011, "Invalid price", None::<String>)
        })?;

        let signature = Self::hex_to_bytes(&request.signature).map_err(|e| {
            ErrorObjectOwned::owned(-32012, format!("Invalid signature: {}", e), None::<String>)
        })?;

        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        // Build source as Vec<u8> (padded to 32 bytes)
        let source_bytes = request.source.as_bytes();
        let mut source = vec![0u8; 32];
        let copy_len = source_bytes.len().min(32);
        source[..copy_len].copy_from_slice(&source_bytes[..copy_len]);

        let engine = self.engine.read().unwrap();

        let entropy_commitment = engine.create_entropy_commitment(price, now)
            .unwrap_or([0u8; 32])
            .to_vec();

        let submission = PqcPriceSubmission {
            reporter_pubkey,
            feed: request.feed,
            price,
            source,
            timestamp: now,
            entropy_commitment,
            signature,
        };

        let result = engine.verify_submission(&submission);

        Ok(PqcVerificationResponse {
            valid: result.valid,
            signature_valid: result.signature_valid,
            entropy_valid: result.entropy_valid,
            qkd_authenticated: result.qkd_authenticated,
            timestamp_valid: result.timestamp_valid,
            error: result.error,
            latency_us: result.latency_us,
        })
    }

    async fn establish_qkd_channel(&self, request: QkdChannelRequest) -> RpcResult<bool> {
        let reporter_pubkey = Self::parse_pubkey(&request.reporter_pubkey).map_err(|e| {
            ErrorObjectOwned::owned(-32020, e, None::<String>)
        })?;

        let session_key_bytes = Self::hex_to_bytes(&request.session_key).map_err(|e| {
            ErrorObjectOwned::owned(-32021, format!("Invalid session key: {}", e), None::<String>)
        })?;

        if session_key_bytes.len() != 32 {
            return Err(ErrorObjectOwned::owned(
                -32022,
                "Session key must be 32 bytes",
                None::<String>,
            ));
        }

        let engine = self.engine.read().unwrap();
        engine.establish_qkd_channel(&reporter_pubkey, &request.qkd_device_id, &session_key_bytes)
            .map_err(|e| ErrorObjectOwned::owned(-32023, e, None::<String>))?;

        Ok(true)
    }

    async fn check_qkd_channel(&self, reporter_pubkey: String) -> RpcResult<bool> {
        let pubkey = Self::parse_pubkey(&reporter_pubkey).map_err(|e| {
            ErrorObjectOwned::owned(-32020, e, None::<String>)
        })?;

        let engine = self.engine.read().unwrap();
        match engine.verify_qkd_channel(&pubkey) {
            Ok(valid) => Ok(valid),
            Err(_) => Ok(false),
        }
    }

    async fn get_verified_submissions(&self, feed: u8) -> RpcResult<Vec<PqcPriceSubmission>> {
        let engine = self.engine.read().unwrap();
        Ok(engine.get_verified_submissions(feed))
    }

    async fn create_test_signature(
        &self,
        secret_key: String,
        public_key: String,
        feed: u8,
        price: String,
    ) -> RpcResult<String> {
        let secret_bytes = Self::hex_to_bytes(&secret_key).map_err(|e| {
            ErrorObjectOwned::owned(-32030, format!("Invalid secret key: {}", e), None::<String>)
        })?;

        if secret_bytes.len() != SPHINCS_SECRET_KEY_SIZE {
            return Err(ErrorObjectOwned::owned(
                -32031,
                format!("Secret key must be {} bytes", SPHINCS_SECRET_KEY_SIZE),
                None::<String>,
            ));
        }

        let public = Self::parse_pubkey(&public_key).map_err(|e| {
            ErrorObjectOwned::owned(-32032, e, None::<String>)
        })?;

        let price_u128: u128 = price.parse().map_err(|_| {
            ErrorObjectOwned::owned(-32033, "Invalid price", None::<String>)
        })?;

        // Create message
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        let mut message = Vec::new();
        message.push(feed);
        message.extend_from_slice(&price_u128.to_le_bytes());
        message.extend_from_slice(&now.to_le_bytes());

        let engine = self.engine.read().unwrap();
        let signature = engine.create_test_signature(&secret_bytes, &public, &message);

        Ok(Self::bytes_to_hex(&signature))
    }
}
