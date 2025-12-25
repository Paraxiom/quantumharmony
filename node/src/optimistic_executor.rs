//! Optimistic Execution for High-TPS SPHINCS+ Transactions
//!
//! This module enables executing transactions BEFORE signature verification completes,
//! dramatically improving perceived TPS by hiding the 250ms SPHINCS+ verification latency.
//!
//! ## How It Works
//!
//! 1. Transaction arrives at mempool
//! 2. Basic validation (format, nonce, balance) - instant
//! 3. Execute transaction optimistically - assume signature is valid
//! 4. Queue signature for background verification
//! 5. If verification fails, rollback state changes
//!
//! ## Safety Guarantees
//!
//! - Invalid transactions are rolled back before finalization
//! - Other validators still verify independently
//! - Only finalized blocks contain verified transactions
//! - No invalid state ever reaches consensus
//!
//! ## Performance
//!
//! - User sees "pending" status instantly
//! - Verification happens in parallel background
//! - Block proposer only finalizes verified transactions
//! - Effective TPS = number of pending transactions that can queue

use std::collections::{HashMap, HashSet};
use std::sync::{Arc, RwLock, Mutex};
use std::time::{Duration, Instant};
use sp_core::H256;

use crate::sphincs_parallel_verify::{ParallelSphincsVerifier, ParallelVerifyConfig};

/// State of an optimistically executed transaction
#[derive(Clone, Debug, PartialEq)]
pub enum OptimisticState {
    /// Transaction executed, verification pending
    Pending,
    /// Signature verified, transaction confirmed
    Confirmed,
    /// Signature invalid, rollback required
    RolledBack,
    /// Transaction expired without confirmation
    Expired,
}

/// An optimistically executed transaction
#[derive(Clone)]
pub struct OptimisticTransaction {
    /// Transaction hash
    pub tx_hash: H256,
    /// When the transaction was received
    pub received_at: Instant,
    /// When execution completed
    pub executed_at: Option<Instant>,
    /// When verification completed
    pub verified_at: Option<Instant>,
    /// Current state
    pub state: OptimisticState,
    /// State changes to rollback if invalid
    pub state_delta: Option<StateDelta>,
    /// Segment this transaction was routed to
    pub segment_id: u32,
}

/// State changes that may need rollback
#[derive(Clone, Default)]
pub struct StateDelta {
    /// Account balances changed
    pub balance_changes: HashMap<Vec<u8>, i128>,
    /// Storage entries modified (key -> (old_value, new_value))
    pub storage_changes: HashMap<Vec<u8>, (Vec<u8>, Vec<u8>)>,
    /// Contracts called
    pub contract_calls: Vec<Vec<u8>>,
}

impl StateDelta {
    /// Check if this delta has any changes
    pub fn is_empty(&self) -> bool {
        self.balance_changes.is_empty() &&
        self.storage_changes.is_empty() &&
        self.contract_calls.is_empty()
    }
}

/// Configuration for optimistic execution
#[derive(Clone, Debug)]
pub struct OptimisticConfig {
    /// Enable optimistic execution
    pub enabled: bool,
    /// Maximum pending optimistic transactions
    pub max_pending: usize,
    /// Timeout for pending verification
    pub pending_timeout: Duration,
    /// Enable state rollback on verification failure
    pub enable_rollback: bool,
}

impl Default for OptimisticConfig {
    fn default() -> Self {
        Self {
            enabled: true,
            max_pending: 10_000,
            pending_timeout: Duration::from_secs(30),
            enable_rollback: true,
        }
    }
}

/// Statistics about optimistic execution
#[derive(Clone, Debug, Default)]
pub struct OptimisticStats {
    /// Transactions executed optimistically
    pub total_optimistic: u64,
    /// Transactions confirmed (verification passed)
    pub total_confirmed: u64,
    /// Transactions rolled back (verification failed)
    pub total_rolled_back: u64,
    /// Transactions expired
    pub total_expired: u64,
    /// Currently pending
    pub current_pending: usize,
    /// Average time from receipt to confirmation
    pub avg_confirmation_ms: f64,
}

/// The Optimistic Executor manages speculative transaction execution
pub struct OptimisticExecutor {
    config: OptimisticConfig,
    /// Parallel verifier for SPHINCS+ signatures
    verifier: Arc<ParallelSphincsVerifier>,
    /// Pending optimistic transactions (tx_hash -> transaction)
    pending: RwLock<HashMap<H256, OptimisticTransaction>>,
    /// Confirmed transactions waiting for block inclusion
    confirmed: RwLock<HashSet<H256>>,
    /// Transactions that need rollback
    rollback_queue: Mutex<Vec<H256>>,
    /// Statistics
    stats: RwLock<OptimisticStats>,
}

impl OptimisticExecutor {
    /// Create a new optimistic executor
    pub fn new(config: OptimisticConfig) -> Self {
        let verify_config = ParallelVerifyConfig::default();
        Self {
            config,
            verifier: Arc::new(ParallelSphincsVerifier::new(verify_config)),
            pending: RwLock::new(HashMap::new()),
            confirmed: RwLock::new(HashSet::new()),
            rollback_queue: Mutex::new(Vec::new()),
            stats: RwLock::new(OptimisticStats::default()),
        }
    }

    /// Create with custom verifier
    pub fn with_verifier(config: OptimisticConfig, verifier: Arc<ParallelSphincsVerifier>) -> Self {
        Self {
            config,
            verifier,
            pending: RwLock::new(HashMap::new()),
            confirmed: RwLock::new(HashSet::new()),
            rollback_queue: Mutex::new(Vec::new()),
            stats: RwLock::new(OptimisticStats::default()),
        }
    }

    /// Execute a transaction optimistically
    ///
    /// Returns immediately with pending status while verification happens in background
    pub fn execute_optimistic(
        &self,
        tx_hash: H256,
        segment_id: u32,
        state_delta: StateDelta,
    ) -> Result<OptimisticState, &'static str> {
        if !self.config.enabled {
            return Err("Optimistic execution disabled");
        }

        // Check capacity
        let pending_count = self.pending.read().unwrap().len();
        if pending_count >= self.config.max_pending {
            return Err("Optimistic execution queue full");
        }

        let now = Instant::now();
        let tx = OptimisticTransaction {
            tx_hash,
            received_at: now,
            executed_at: Some(now),
            verified_at: None,
            state: OptimisticState::Pending,
            state_delta: Some(state_delta),
            segment_id,
        };

        // Add to pending
        {
            let mut pending = self.pending.write().unwrap();
            pending.insert(tx_hash, tx);
        }

        // Update stats
        {
            let mut stats = self.stats.write().unwrap();
            stats.total_optimistic += 1;
            stats.current_pending = pending_count + 1;
        }

        log::debug!(
            "[Optimistic] TX {:?} executed in segment {}, pending verification",
            tx_hash, segment_id
        );

        Ok(OptimisticState::Pending)
    }

    /// Called when verification completes for a transaction
    pub fn on_verification_complete(&self, tx_hash: H256, valid: bool) {
        let mut should_rollback = false;

        {
            let mut pending = self.pending.write().unwrap();
            if let Some(tx) = pending.get_mut(&tx_hash) {
                tx.verified_at = Some(Instant::now());

                if valid {
                    tx.state = OptimisticState::Confirmed;

                    // Move to confirmed set
                    let mut confirmed = self.confirmed.write().unwrap();
                    confirmed.insert(tx_hash);

                    let mut stats = self.stats.write().unwrap();
                    stats.total_confirmed += 1;

                    // Calculate confirmation time
                    if let Some(received) = tx.executed_at {
                        let confirm_time = tx.verified_at.unwrap().duration_since(received);
                        let current_avg = stats.avg_confirmation_ms;
                        let count = stats.total_confirmed as f64;
                        stats.avg_confirmation_ms =
                            (current_avg * (count - 1.0) + confirm_time.as_millis() as f64) / count;
                    }

                    log::debug!(
                        "[Optimistic] TX {:?} CONFIRMED (valid signature)",
                        tx_hash
                    );
                } else {
                    tx.state = OptimisticState::RolledBack;
                    should_rollback = self.config.enable_rollback && tx.state_delta.is_some();

                    let mut stats = self.stats.write().unwrap();
                    stats.total_rolled_back += 1;

                    log::warn!(
                        "[Optimistic] TX {:?} ROLLED BACK (invalid signature)",
                        tx_hash
                    );
                }

                let mut stats = self.stats.write().unwrap();
                stats.current_pending = pending.len().saturating_sub(1);
            }
        }

        if should_rollback {
            let mut rollback = self.rollback_queue.lock().unwrap();
            rollback.push(tx_hash);
        }
    }

    /// Get transactions pending rollback
    pub fn get_rollback_queue(&self) -> Vec<(H256, StateDelta)> {
        let rollback_hashes: Vec<H256> = {
            let mut queue = self.rollback_queue.lock().unwrap();
            std::mem::take(&mut *queue)
        };

        let pending = self.pending.read().unwrap();
        rollback_hashes
            .into_iter()
            .filter_map(|hash| {
                pending.get(&hash).and_then(|tx| {
                    tx.state_delta.clone().map(|delta| (hash, delta))
                })
            })
            .collect()
    }

    /// Get all confirmed transactions ready for block inclusion
    pub fn get_confirmed(&self) -> Vec<H256> {
        let confirmed = self.confirmed.read().unwrap();
        confirmed.iter().cloned().collect()
    }

    /// Check if a transaction is confirmed
    pub fn is_confirmed(&self, tx_hash: &H256) -> bool {
        let confirmed = self.confirmed.read().unwrap();
        confirmed.contains(tx_hash)
    }

    /// Get the state of a transaction
    pub fn get_state(&self, tx_hash: &H256) -> Option<OptimisticState> {
        let pending = self.pending.read().unwrap();
        pending.get(tx_hash).map(|tx| tx.state.clone())
    }

    /// Clean up expired transactions
    pub fn cleanup_expired(&self) {
        let now = Instant::now();
        let mut expired = Vec::new();

        {
            let mut pending = self.pending.write().unwrap();
            pending.retain(|hash, tx| {
                if now.duration_since(tx.received_at) > self.config.pending_timeout {
                    if tx.state == OptimisticState::Pending {
                        expired.push(*hash);
                    }
                    false
                } else {
                    true
                }
            });
        }

        if !expired.is_empty() {
            let mut stats = self.stats.write().unwrap();
            stats.total_expired += expired.len() as u64;
            stats.current_pending = self.pending.read().unwrap().len();

            log::warn!(
                "[Optimistic] Expired {} transactions without verification",
                expired.len()
            );
        }

        // Also clean up confirmed transactions that have been included
        // (This would be called by the block import logic)
    }

    /// Called when transactions are included in a finalized block
    pub fn on_block_finalized(&self, included_hashes: &[H256]) {
        {
            let mut confirmed = self.confirmed.write().unwrap();
            for hash in included_hashes {
                confirmed.remove(hash);
            }
        }

        {
            let mut pending = self.pending.write().unwrap();
            for hash in included_hashes {
                pending.remove(hash);
            }
        }

        log::debug!(
            "[Optimistic] Cleaned up {} finalized transactions",
            included_hashes.len()
        );
    }

    /// Get current statistics
    pub fn get_stats(&self) -> OptimisticStats {
        let stats = self.stats.read().unwrap();
        stats.clone()
    }

    /// Get the underlying verifier for batch operations
    pub fn verifier(&self) -> &Arc<ParallelSphincsVerifier> {
        &self.verifier
    }

    /// Submit signatures for batch verification
    ///
    /// This is the main entry point for high-throughput verification
    pub fn submit_batch_verification(
        &self,
        batch: Vec<(H256, Vec<u8>, Vec<u8>, Vec<u8>)>, // (tx_hash, signature, message, public_key)
    ) {
        if batch.is_empty() {
            return;
        }

        let batch_size = batch.len();
        log::info!(
            "[Optimistic] Submitting {} signatures for batch verification",
            batch_size
        );

        // Extract verification data
        let verifications: Vec<_> = batch
            .iter()
            .map(|(_, sig, msg, pk)| (sig.clone(), msg.clone(), pk.clone()))
            .collect();

        // Run batch verification
        let results = self.verifier.verify_batch(verifications);

        // Process results
        for ((tx_hash, _, _, _), result) in batch.into_iter().zip(results.iter()) {
            self.on_verification_complete(tx_hash, result.valid);
        }

        log::info!(
            "[Optimistic] Batch verification complete: {} valid, {} invalid",
            results.iter().filter(|r| r.valid).count(),
            results.iter().filter(|r| !r.valid).count()
        );
    }
}

/// Calculate effective TPS with optimistic execution
///
/// With optimistic execution, the user-perceived TPS is much higher
/// because they don't wait for signature verification
pub fn calculate_optimistic_tps(
    cores: usize,
    segments: usize,
    queue_depth: usize,
) -> OptimisticTpsEstimate {
    // Base SPHINCS+ verification: 250ms = 4 TPS per core
    let base_verification_tps = cores as f64 * 4.0;

    // With segments, we can process segments * base_verification_tps
    let segment_tps = segments as f64 * base_verification_tps;

    // With optimistic execution, users see instant response
    // Limited only by queue depth and network latency
    // Assume 10ms average network latency for receiving transaction
    let network_receive_tps = 1000.0 / 10.0; // 100 TPS network receive

    // Effective TPS is the verification rate (what can be finalized)
    // But user-perceived TPS is instant (limited by queue depth per second)
    let user_perceived_tps = queue_depth as f64; // All queued transactions appear instant

    OptimisticTpsEstimate {
        cores,
        segments,
        queue_depth,
        base_verification_tps,
        segment_tps,
        network_receive_tps,
        finalization_tps: segment_tps, // Limited by verification throughput
        user_perceived_tps,
    }
}

/// TPS estimate with optimistic execution
#[derive(Clone, Debug)]
pub struct OptimisticTpsEstimate {
    pub cores: usize,
    pub segments: usize,
    pub queue_depth: usize,
    pub base_verification_tps: f64,
    pub segment_tps: f64,
    pub network_receive_tps: f64,
    pub finalization_tps: f64,
    pub user_perceived_tps: f64,
}

impl OptimisticTpsEstimate {
    /// Display formatted estimate
    pub fn display(&self) -> String {
        format!(
            r#"
╔═══════════════════════════════════════════════════════════════╗
║       OPTIMISTIC SPHINCS+ TPS ESTIMATES                       ║
╠═══════════════════════════════════════════════════════════════╣
║ Configuration:                                                ║
║   CPU Cores:     {:>4}                                        ║
║   Segments:      {:>4}                                        ║
║   Queue Depth:   {:>4}                                        ║
╠═══════════════════════════════════════════════════════════════╣
║ Throughput:                                                   ║
║   Base Verification: {:>10.1} TPS                             ║
║   With Segments:     {:>10.1} TPS                             ║
║   Finalization TPS:  {:>10.1} TPS                             ║
║   User Perceived:    {:>10.1} TPS (instant!)                  ║
╚═══════════════════════════════════════════════════════════════╝
"#,
            self.cores,
            self.segments,
            self.queue_depth,
            self.base_verification_tps,
            self.segment_tps,
            self.finalization_tps,
            self.user_perceived_tps
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_optimistic_execution() {
        let config = OptimisticConfig::default();
        let executor = OptimisticExecutor::new(config);

        let tx_hash = H256::random();
        let delta = StateDelta::default();

        // Execute optimistically
        let result = executor.execute_optimistic(tx_hash, 0, delta);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), OptimisticState::Pending);

        // Verify state
        assert_eq!(executor.get_state(&tx_hash), Some(OptimisticState::Pending));

        // Complete verification
        executor.on_verification_complete(tx_hash, true);
        assert_eq!(executor.get_state(&tx_hash), Some(OptimisticState::Confirmed));

        // Check confirmed list
        assert!(executor.is_confirmed(&tx_hash));
    }

    #[test]
    fn test_rollback_on_invalid() {
        let config = OptimisticConfig {
            enable_rollback: true,
            ..Default::default()
        };
        let executor = OptimisticExecutor::new(config);

        let tx_hash = H256::random();
        let mut delta = StateDelta::default();
        delta.balance_changes.insert(vec![1, 2, 3], -100);

        executor.execute_optimistic(tx_hash, 0, delta).unwrap();
        executor.on_verification_complete(tx_hash, false); // Invalid!

        assert_eq!(executor.get_state(&tx_hash), Some(OptimisticState::RolledBack));

        let rollbacks = executor.get_rollback_queue();
        assert_eq!(rollbacks.len(), 1);
        assert_eq!(rollbacks[0].0, tx_hash);
    }

    #[test]
    fn test_tps_estimate() {
        // 8 cores, 512 segments, 10k queue
        let estimate = calculate_optimistic_tps(8, 512, 10_000);

        // 8 cores * 4 TPS = 32 base
        assert_eq!(estimate.base_verification_tps, 32.0);

        // 512 * 32 = 16,384 segment TPS
        assert_eq!(estimate.segment_tps, 16384.0);

        // User perceived = queue depth = 10,000
        assert_eq!(estimate.user_perceived_tps, 10_000.0);
    }
}
