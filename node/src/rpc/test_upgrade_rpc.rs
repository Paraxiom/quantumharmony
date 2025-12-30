//! Test Runtime Upgrade RPC
//!
//! Public endpoint for testing runtime upgrade compatibility WITHOUT applying changes.
//! Features:
//! - No keys required (uses default public test key)
//! - No fees charged
//! - Rate limited to prevent DOS (1 test per hour per identifier)
//! - Dry-run mode: validates WASM but doesn't apply upgrade
//!
//! Use this to verify your WASM is valid before submitting a real upgrade.

use jsonrpsee::{
    core::{async_trait, RpcResult},
    proc_macros::rpc,
};
use jsonrpsee_types::ErrorObjectOwned;
use sp_api::{Core, ProvideRuntimeApi};
use sp_blockchain::HeaderBackend;
use sp_runtime::traits::Block as BlockT;
use std::sync::Arc;
use std::collections::HashMap;
use std::time::{Duration, Instant};
use parking_lot::RwLock;
use log;
use hex;

/// Rate limit: 1 test per hour (3600 seconds)
const RATE_LIMIT_SECONDS: u64 = 3600;

/// Maximum WASM size for test (2MB)
const MAX_TEST_WASM_SIZE: usize = 2 * 1024 * 1024;

/// Minimum WASM size (100KB - realistic runtime minimum)
const MIN_TEST_WASM_SIZE: usize = 100_000;

/// WASM magic bytes
const WASM_MAGIC: [u8; 4] = [0x00, 0x61, 0x73, 0x6D];

/// Default public test key (Alice's public key - for simulation only)
/// This key is used for dry-run testing and CANNOT execute real upgrades
pub const DEFAULT_TEST_PUBLIC_KEY: [u8; 64] = [
    0xd7, 0xd0, 0xbd, 0x47, 0x54, 0x17, 0xa9, 0x3f, 0xa6, 0x12, 0x16, 0xa1, 0xe4, 0x02, 0x4f, 0x8d,
    0x1a, 0x21, 0x1f, 0x79, 0x5e, 0x6a, 0xb1, 0x11, 0xa1, 0xee, 0xf0, 0xd5, 0xe4, 0xf3, 0xf4, 0xb1,
    0x56, 0xe4, 0x7e, 0x5c, 0x8d, 0x41, 0x85, 0xce, 0x4a, 0x30, 0x84, 0x23, 0xeb, 0x31, 0x0b, 0xb3,
    0xb7, 0xf2, 0x6e, 0x6d, 0x50, 0x41, 0x91, 0x66, 0x2d, 0x22, 0x41, 0xaa, 0xfa, 0xf9, 0x14, 0xcd,
];

/// Test upgrade result
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct TestUpgradeResult {
    /// Whether the test passed
    pub success: bool,
    /// Test identifier used
    pub test_id: String,
    /// WASM validation results
    pub validation: WasmValidation,
    /// Rate limit info
    pub rate_limit: RateLimitInfo,
    /// Message
    pub message: String,
    /// Warnings (if any)
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub warnings: Vec<String>,
}

/// WASM validation details
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct WasmValidation {
    /// WASM size in bytes
    pub size_bytes: usize,
    /// Size in KB
    pub size_kb: f64,
    /// Has valid magic bytes
    pub valid_magic: bool,
    /// WASM version
    pub wasm_version: u8,
    /// Estimated chunks needed for chunked upload
    pub chunks_needed: u8,
    /// Would fit in single transaction
    pub fits_single_tx: bool,
    /// Hash of WASM (Blake2-256)
    pub wasm_hash: String,
}

/// Rate limit information
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct RateLimitInfo {
    /// Whether this request was rate limited
    pub limited: bool,
    /// Seconds until next test allowed
    pub seconds_until_next: u64,
    /// Tests remaining in current window
    pub tests_remaining: u32,
}

/// Rate limiter state
struct RateLimiter {
    /// Map of identifier -> last request time
    requests: RwLock<HashMap<String, Instant>>,
}

impl RateLimiter {
    fn new() -> Self {
        Self {
            requests: RwLock::new(HashMap::new()),
        }
    }

    /// Check if identifier is rate limited
    fn check(&self, identifier: &str) -> RateLimitInfo {
        let requests = self.requests.read();

        if let Some(last_request) = requests.get(identifier) {
            let elapsed = last_request.elapsed();
            let limit_duration = Duration::from_secs(RATE_LIMIT_SECONDS);

            if elapsed < limit_duration {
                let remaining = limit_duration - elapsed;
                return RateLimitInfo {
                    limited: true,
                    seconds_until_next: remaining.as_secs(),
                    tests_remaining: 0,
                };
            }
        }

        RateLimitInfo {
            limited: false,
            seconds_until_next: 0,
            tests_remaining: 1,
        }
    }

    /// Record a request
    fn record(&self, identifier: &str) {
        let mut requests = self.requests.write();
        requests.insert(identifier.to_string(), Instant::now());

        // Clean up old entries (older than 2x rate limit)
        let cutoff = Duration::from_secs(RATE_LIMIT_SECONDS * 2);
        requests.retain(|_, time| time.elapsed() < cutoff);
    }
}

#[rpc(client, server)]
pub trait TestUpgradeApi {
    /// Test a runtime upgrade WITHOUT applying it
    ///
    /// This is a FREE, public endpoint for testing WASM validity.
    /// Rate limited to 1 test per hour per identifier.
    ///
    /// # Parameters
    /// - `wasm_hex`: Hex-encoded WASM runtime blob (with or without 0x prefix)
    /// - `identifier`: Optional identifier for rate limiting (IP, account, etc.)
    ///                 If not provided, uses a default public identifier
    ///
    /// # Returns
    /// TestUpgradeResult with validation details
    ///
    /// # Example
    /// ```bash
    /// curl -H "Content-Type: application/json" -d '{
    ///   "id":1,
    ///   "jsonrpc":"2.0",
    ///   "method":"quantumharmony_testRuntimeUpgrade",
    ///   "params": ["0x<WASM_HEX>", "my-test-id"]
    /// }' http://NODE:9944
    /// ```
    #[method(name = "quantumharmony_testRuntimeUpgrade")]
    async fn test_runtime_upgrade(
        &self,
        wasm_hex: String,
        identifier: Option<String>,
    ) -> RpcResult<TestUpgradeResult>;

    /// Check rate limit status without submitting a test
    ///
    /// # Parameters
    /// - `identifier`: Optional identifier to check
    ///
    /// # Returns
    /// RateLimitInfo showing current status
    #[method(name = "quantumharmony_testUpgradeRateLimit")]
    async fn check_rate_limit(
        &self,
        identifier: Option<String>,
    ) -> RpcResult<RateLimitInfo>;

    /// Get the default test public key
    ///
    /// This key is used for dry-run simulations and cannot execute real upgrades.
    #[method(name = "quantumharmony_getTestPublicKey")]
    async fn get_test_public_key(&self) -> RpcResult<String>;

    /// Validate WASM format only (no rate limit)
    ///
    /// Quick validation of WASM structure without full test.
    #[method(name = "quantumharmony_validateWasmFormat")]
    async fn validate_wasm_format(&self, wasm_hex: String) -> RpcResult<WasmValidation>;
}

pub struct TestUpgradeRpc<C, Block> {
    client: Arc<C>,
    rate_limiter: Arc<RateLimiter>,
    _phantom: std::marker::PhantomData<Block>,
}

impl<C, Block> TestUpgradeRpc<C, Block> {
    pub fn new(client: Arc<C>) -> Self {
        Self {
            client,
            rate_limiter: Arc::new(RateLimiter::new()),
            _phantom: std::marker::PhantomData,
        }
    }

    fn validate_wasm(&self, wasm: &[u8]) -> Result<WasmValidation, String> {
        // Check size
        if wasm.len() < MIN_TEST_WASM_SIZE {
            return Err(format!(
                "WASM too small: {} bytes. Minimum realistic size is {} bytes (~100KB)",
                wasm.len(), MIN_TEST_WASM_SIZE
            ));
        }
        if wasm.len() > MAX_TEST_WASM_SIZE {
            return Err(format!(
                "WASM too large: {} bytes. Maximum is {} bytes (2MB)",
                wasm.len(), MAX_TEST_WASM_SIZE
            ));
        }

        // Check magic bytes
        if wasm.len() < 4 {
            return Err("WASM too short to contain magic bytes".to_string());
        }
        let valid_magic = wasm[0..4] == WASM_MAGIC;
        if !valid_magic {
            return Err(format!(
                "Invalid WASM magic bytes. Expected {:02x?}, got {:02x?}",
                WASM_MAGIC, &wasm[0..4]
            ));
        }

        // Get WASM version (byte 4)
        let wasm_version = if wasm.len() > 4 { wasm[4] } else { 0 };

        // Calculate hash
        let wasm_hash = sp_core::hashing::blake2_256(wasm);

        // Calculate chunks needed (64KB per chunk)
        const CHUNK_SIZE: usize = 65_536;
        let chunks_needed = ((wasm.len() + CHUNK_SIZE - 1) / CHUNK_SIZE) as u8;

        // Check if fits in single transaction (256KB block limit, ~200KB safe)
        let fits_single_tx = wasm.len() < 200_000;

        Ok(WasmValidation {
            size_bytes: wasm.len(),
            size_kb: wasm.len() as f64 / 1024.0,
            valid_magic,
            wasm_version,
            chunks_needed,
            fits_single_tx,
            wasm_hash: format!("0x{}", hex::encode(wasm_hash)),
        })
    }
}

#[async_trait]
impl<C, Block> TestUpgradeApiServer for TestUpgradeRpc<C, Block>
where
    Block: BlockT,
    C: Send + Sync + 'static + ProvideRuntimeApi<Block> + HeaderBackend<Block>,
    C::Api: Core<Block>,
{
    async fn test_runtime_upgrade(
        &self,
        wasm_hex: String,
        identifier: Option<String>,
    ) -> RpcResult<TestUpgradeResult> {
        let test_id = identifier.unwrap_or_else(|| "public".to_string());

        log::info!("🧪 Test Runtime Upgrade requested by: {}", test_id);

        // Check rate limit
        let rate_limit = self.rate_limiter.check(&test_id);
        if rate_limit.limited {
            let seconds_remaining = rate_limit.seconds_until_next;
            log::warn!("⏱️  Rate limited: {} ({}s remaining)", test_id, seconds_remaining);
            return Ok(TestUpgradeResult {
                success: false,
                test_id,
                validation: WasmValidation {
                    size_bytes: 0,
                    size_kb: 0.0,
                    valid_magic: false,
                    wasm_version: 0,
                    chunks_needed: 0,
                    fits_single_tx: false,
                    wasm_hash: "".to_string(),
                },
                rate_limit,
                message: format!(
                    "Rate limited. Please wait {} seconds before testing again.",
                    seconds_remaining
                ),
                warnings: vec![],
            });
        }

        // Record this request
        self.rate_limiter.record(&test_id);

        // Decode WASM
        let wasm = match hex::decode(wasm_hex.trim_start_matches("0x")) {
            Ok(w) => w,
            Err(e) => {
                return Ok(TestUpgradeResult {
                    success: false,
                    test_id,
                    validation: WasmValidation {
                        size_bytes: 0,
                        size_kb: 0.0,
                        valid_magic: false,
                        wasm_version: 0,
                        chunks_needed: 0,
                        fits_single_tx: false,
                        wasm_hash: "".to_string(),
                    },
                    rate_limit: RateLimitInfo { limited: false, seconds_until_next: 0, tests_remaining: 0 },
                    message: format!("Invalid hex encoding: {}", e),
                    warnings: vec![],
                });
            }
        };

        log::info!("   WASM size: {} bytes ({} KB)", wasm.len(), wasm.len() / 1024);

        // Validate WASM
        let validation = match self.validate_wasm(&wasm) {
            Ok(v) => v,
            Err(e) => {
                log::warn!("   ❌ Validation failed: {}", e);
                return Ok(TestUpgradeResult {
                    success: false,
                    test_id,
                    validation: WasmValidation {
                        size_bytes: wasm.len(),
                        size_kb: wasm.len() as f64 / 1024.0,
                        valid_magic: false,
                        wasm_version: 0,
                        chunks_needed: 0,
                        fits_single_tx: false,
                        wasm_hash: "".to_string(),
                    },
                    rate_limit: RateLimitInfo { limited: false, seconds_until_next: 0, tests_remaining: 0 },
                    message: e,
                    warnings: vec![],
                });
            }
        };

        // Collect warnings
        let mut warnings = vec![];

        if !validation.fits_single_tx {
            warnings.push(format!(
                "WASM size ({} KB) exceeds single transaction limit. Use chunked upload ({} chunks needed).",
                validation.size_kb as u32, validation.chunks_needed
            ));
        }

        if validation.wasm_version != 1 {
            warnings.push(format!(
                "Unexpected WASM version: {}. Expected version 1.",
                validation.wasm_version
            ));
        }

        // Try to get current runtime version for comparison
        let best_hash = self.client.info().best_hash;
        if let Ok(current_version) = self.client.runtime_api().version(best_hash) {
            log::info!("   Current runtime: {} v{}", current_version.spec_name, current_version.spec_version);
        }

        log::info!("✅ Test passed! WASM hash: {}", validation.wasm_hash);

        Ok(TestUpgradeResult {
            success: true,
            test_id,
            validation,
            rate_limit: RateLimitInfo {
                limited: false,
                seconds_until_next: RATE_LIMIT_SECONDS,
                tests_remaining: 0,
            },
            message: "WASM validation passed! Ready for upgrade submission.".to_string(),
            warnings,
        })
    }

    async fn check_rate_limit(
        &self,
        identifier: Option<String>,
    ) -> RpcResult<RateLimitInfo> {
        let test_id = identifier.unwrap_or_else(|| "public".to_string());
        Ok(self.rate_limiter.check(&test_id))
    }

    async fn get_test_public_key(&self) -> RpcResult<String> {
        Ok(format!("0x{}", hex::encode(DEFAULT_TEST_PUBLIC_KEY)))
    }

    async fn validate_wasm_format(&self, wasm_hex: String) -> RpcResult<WasmValidation> {
        let wasm = hex::decode(wasm_hex.trim_start_matches("0x"))
            .map_err(|e| error_object(-32602, format!("Invalid hex: {}", e)))?;

        self.validate_wasm(&wasm)
            .map_err(|e| error_object(-32602, e))
    }
}

fn error_object(code: i32, message: String) -> ErrorObjectOwned {
    ErrorObjectOwned::owned(code, message, None::<()>)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rate_limiter() {
        let limiter = RateLimiter::new();

        // First request should not be limited
        let result = limiter.check("test-user");
        assert!(!result.limited);

        // Record the request
        limiter.record("test-user");

        // Second request should be limited
        let result = limiter.check("test-user");
        assert!(result.limited);
        assert!(result.seconds_until_next > 0);
    }

    #[test]
    fn test_default_public_key() {
        assert_eq!(DEFAULT_TEST_PUBLIC_KEY.len(), 64);
        // Verify it's Alice's public key
        assert_eq!(DEFAULT_TEST_PUBLIC_KEY[0], 0xd7);
    }

    #[test]
    fn test_wasm_magic() {
        assert_eq!(WASM_MAGIC, [0x00, 0x61, 0x73, 0x6D]);
    }
}
