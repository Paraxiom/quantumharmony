//! High-Performance SPHINCS+ Signature Pre-Verification System
//!
//! Achieves high effective TPS while maintaining full quantum resistance
//! by moving signature verification off the critical block production path.
//!
//! ## Architecture
//!
//! ### Pre-Verification Pool
//! - SPHINCS+ signatures verified when transactions enter mempool
//! - Results cached with configurable expiry
//! - Block proposer only includes pre-verified transactions
//! - Achieves high effective TPS by moving verification off critical path
//!
//! ### Signature Caching
//! - Verified signatures cached to avoid re-verification
//! - LRU-style cache with time-based expiry
//! - Reduces redundant verification work
//!
//! ### Parallel Verification Workers
//! - Multiple worker threads verify signatures concurrently
//! - Work distributed across CPU cores
//! - With N cores and ~4 TPS per core, achieves N*4 TPS
//!
//! ## Performance
//! - SPHINCS+ verification: ~250ms per signature
//! - With 16 cores: ~64 TPS raw verification
//! - With pre-verification: transactions appear instant to users

use std::collections::HashMap;
use std::sync::{Arc, RwLock, Mutex};
use std::time::{Duration, Instant};
use std::thread;
use sp_core::H256;

/// Configuration for the verification system
#[derive(Clone, Debug)]
pub struct VerificationConfig {
    /// Number of parallel verification workers
    pub worker_threads: usize,
    /// Cache expiry for pre-verified signatures
    pub cache_expiry: Duration,
    /// Maximum pending verifications in queue
    pub max_queue_size: usize,
    /// Enable optimistic execution (execute before full verification)
    pub optimistic_execution: bool,
}

impl Default for VerificationConfig {
    fn default() -> Self {
        Self {
            worker_threads: num_cpus::get(),
            cache_expiry: Duration::from_secs(300), // 5 minutes
            max_queue_size: 10_000,
            optimistic_execution: true,
        }
    }
}

/// Result of signature verification
#[derive(Clone, Debug, PartialEq)]
pub enum VerificationResult {
    /// Signature verified successfully
    Valid,
    /// Signature verification failed
    Invalid,
    /// Verification pending (in worker queue)
    Pending,
    /// Verification expired (needs re-verification)
    Expired,
}

/// Cached verification entry
#[derive(Clone, Debug)]
struct CacheEntry {
    result: VerificationResult,
    verified_at: Instant,
}

/// Pending verification job
#[derive(Clone)]
struct PendingVerification {
    tx_hash: H256,
    signature_bytes: Vec<u8>,
    message: Vec<u8>,
    public_key: Vec<u8>,
    queued_at: Instant,
}

/// Pre-verification worker pool for SPHINCS+ signatures
pub struct PreVerificationPool {
    config: VerificationConfig,
    cache: Arc<RwLock<HashMap<H256, CacheEntry>>>,
    pending_queue: Arc<Mutex<Vec<(H256, PendingVerification)>>>,
    workers_running: Arc<Mutex<bool>>,
}

impl PreVerificationPool {
    /// Create a new pre-verification pool
    pub fn new(config: VerificationConfig) -> Self {
        Self {
            config,
            cache: Arc::new(RwLock::new(HashMap::new())),
            pending_queue: Arc::new(Mutex::new(Vec::new())),
            workers_running: Arc::new(Mutex::new(false)),
        }
    }

    /// Start background worker threads for SPHINCS+ verification
    pub fn start_workers(&self) {
        let mut running = self.workers_running.lock().unwrap();
        if *running {
            return;
        }
        *running = true;
        drop(running);

        for worker_id in 0..self.config.worker_threads {
            let cache = Arc::clone(&self.cache);
            let queue = Arc::clone(&self.pending_queue);
            let workers_running = Arc::clone(&self.workers_running);
            let cache_expiry = self.config.cache_expiry;

            thread::spawn(move || {
                log::info!("[PreVerify] SPHINCS+ Worker {} started", worker_id);

                while *workers_running.lock().unwrap() {
                    // Get next job from queue
                    let job = {
                        let mut q = queue.lock().unwrap();
                        if q.is_empty() {
                            drop(q);
                            thread::sleep(Duration::from_millis(10));
                            continue;
                        }
                        q.remove(0)
                    };

                    let (tx_hash, pending) = job;

                    // Perform SPHINCS+ verification
                    let result = Self::verify_sphincs_signature(
                        &pending.signature_bytes,
                        &pending.message,
                        &pending.public_key,
                    );

                    // Cache the result
                    let entry = CacheEntry {
                        result: result.clone(),
                        verified_at: Instant::now(),
                    };

                    {
                        let mut c = cache.write().unwrap();
                        c.insert(tx_hash, entry);
                    }

                    let verification_time = pending.queued_at.elapsed();
                    log::debug!(
                        "[PreVerify] Worker {} verified {:?} -> {:?} in {:?}",
                        worker_id, tx_hash, result, verification_time
                    );
                }

                log::info!("[PreVerify] SPHINCS+ Worker {} stopped", worker_id);
            });
        }
    }

    /// Stop background workers
    pub fn stop_workers(&self) {
        let mut running = self.workers_running.lock().unwrap();
        *running = false;
    }

    /// Submit transaction for pre-verification
    pub fn submit_for_verification(
        &self,
        tx_hash: H256,
        signature: Vec<u8>,
        message: Vec<u8>,
        public_key: Vec<u8>,
    ) -> Result<(), &'static str> {
        // Check if already verified
        {
            let cache = self.cache.read().unwrap();
            if let Some(entry) = cache.get(&tx_hash) {
                if entry.verified_at.elapsed() < self.config.cache_expiry {
                    return Ok(()); // Already verified and not expired
                }
            }
        }

        // Check queue size
        let queue_len = self.pending_queue.lock().unwrap().len();
        if queue_len >= self.config.max_queue_size {
            return Err("Verification queue full");
        }

        let pending = PendingVerification {
            tx_hash,
            signature_bytes: signature,
            message,
            public_key,
            queued_at: Instant::now(),
        };

        self.pending_queue.lock().unwrap().push((tx_hash, pending));
        Ok(())
    }

    /// Check if a transaction is verified (from cache)
    pub fn check_verification(&self, tx_hash: &H256) -> VerificationResult {
        let cache = self.cache.read().unwrap();

        match cache.get(tx_hash) {
            Some(entry) => {
                // Check if expired
                if entry.verified_at.elapsed() > self.config.cache_expiry {
                    VerificationResult::Expired
                } else {
                    entry.result.clone()
                }
            }
            None => {
                // Check if pending
                let pending = self.pending_queue.lock().unwrap();
                if pending.iter().any(|(h, _)| h == tx_hash) {
                    VerificationResult::Pending
                } else {
                    VerificationResult::Invalid // Not in system
                }
            }
        }
    }

    /// Get all verified transaction hashes (for block proposer)
    pub fn get_verified_transactions(&self) -> Vec<H256> {
        let cache = self.cache.read().unwrap();
        let now = Instant::now();

        cache.iter()
            .filter(|(_, entry)| {
                entry.result == VerificationResult::Valid &&
                now.duration_since(entry.verified_at) < self.config.cache_expiry
            })
            .map(|(hash, _)| *hash)
            .collect()
    }

    /// Clean up expired cache entries
    pub fn cleanup_expired(&self) {
        let mut cache = self.cache.write().unwrap();
        let now = Instant::now();

        cache.retain(|_, entry| {
            now.duration_since(entry.verified_at) < self.config.cache_expiry
        });
    }

    /// Get verification statistics
    pub fn get_stats(&self) -> VerificationStats {
        let cache = self.cache.read().unwrap();
        let pending = self.pending_queue.lock().unwrap();

        let mut valid_count = 0;
        let mut invalid_count = 0;

        for entry in cache.values() {
            match entry.result {
                VerificationResult::Valid => valid_count += 1,
                VerificationResult::Invalid => invalid_count += 1,
                _ => {}
            }
        }

        VerificationStats {
            cached_valid: valid_count,
            cached_invalid: invalid_count,
            pending_count: pending.len(),
            worker_threads: self.config.worker_threads,
        }
    }

    /// Verify a SPHINCS+ signature
    fn verify_sphincs_signature(
        signature: &[u8],
        message: &[u8],
        public_key: &[u8],
    ) -> VerificationResult {
        use sp_core::sphincs::{Public, Signature, PUBLIC_KEY_SERIALIZED_SIZE, SIGNATURE_SERIALIZED_SIZE};
        use sp_core::crypto::Pair as PairTrait;

        // Validate sizes
        if signature.len() != SIGNATURE_SERIALIZED_SIZE {
            log::warn!(
                "[PreVerify] Invalid signature size: {} (expected {})",
                signature.len(), SIGNATURE_SERIALIZED_SIZE
            );
            return VerificationResult::Invalid;
        }

        if public_key.len() != PUBLIC_KEY_SERIALIZED_SIZE {
            log::warn!(
                "[PreVerify] Invalid public key size: {} (expected {})",
                public_key.len(), PUBLIC_KEY_SERIALIZED_SIZE
            );
            return VerificationResult::Invalid;
        }

        // Parse signature
        let mut sig_bytes = [0u8; SIGNATURE_SERIALIZED_SIZE];
        sig_bytes.copy_from_slice(signature);
        let sig = Signature::from_raw(sig_bytes);

        // Parse public key
        let mut pk_bytes = [0u8; PUBLIC_KEY_SERIALIZED_SIZE];
        pk_bytes.copy_from_slice(public_key);
        let pk = Public::from_raw(pk_bytes);

        // Verify signature
        if sp_core::sphincs::Pair::verify(&sig, message, &pk) {
            VerificationResult::Valid
        } else {
            VerificationResult::Invalid
        }
    }
}

/// Verification statistics
#[derive(Clone, Debug, Default)]
pub struct VerificationStats {
    pub cached_valid: usize,
    pub cached_invalid: usize,
    pub pending_count: usize,
    pub worker_threads: usize,
}

impl VerificationStats {
    /// Calculate theoretical TPS based on worker count
    /// SPHINCS+ verification takes ~250ms, so each thread does ~4 TPS
    pub fn theoretical_tps(&self) -> f64 {
        // Each thread can verify ~4 signatures per second (250ms each)
        self.worker_threads as f64 * 4.0
    }

    /// Calculate effective TPS based on verification rates
    pub fn calculate_effective_tps(&self, elapsed_secs: f64) -> f64 {
        if elapsed_secs <= 0.0 {
            return 0.0;
        }
        self.cached_valid as f64 / elapsed_secs
    }
}

/// Calculate network-distributed TPS
/// With 3 validators each running verification pools, TPS scales linearly
pub fn calculate_network_tps(
    validators: usize,
    cores_per_validator: usize,
) -> f64 {
    // Each validator can verify signatures in parallel
    // With pre-verification, they share the workload
    let total_cores = validators * cores_per_validator;
    let tps_per_core = 4.0; // ~250ms per SPHINCS+ verification

    total_cores as f64 * tps_per_core
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_network_tps_calculation() {
        // 3 validators with 8 cores each
        let tps = calculate_network_tps(3, 8);
        // 3 * 8 * 4 = 96 TPS
        assert!(tps > 90.0);
        assert!(tps < 100.0);

        // 10 validators with 16 cores each
        let tps_large = calculate_network_tps(10, 16);
        // 10 * 16 * 4 = 640 TPS
        assert!(tps_large > 600.0);
    }

    #[test]
    fn test_verification_stats() {
        let stats = VerificationStats {
            cached_valid: 100,
            cached_invalid: 5,
            pending_count: 10,
            worker_threads: 8,
        };

        // 8 threads * 4 TPS = 32 TPS theoretical
        assert_eq!(stats.theoretical_tps(), 32.0);

        // 100 valid over 10 seconds = 10 TPS effective
        assert_eq!(stats.calculate_effective_tps(10.0), 10.0);
    }
}
