//! Parallel Block Proposer Utilities for Segmented Transaction Processing
//!
//! This module provides utilities for parallel transaction processing across
//! the 512-segment toroidal mesh architecture.
//!
//! Key capabilities:
//! - Group transactions by segment
//! - Calculate optimal processing order
//! - Estimate parallel speedup
//! - Track parallel processing statistics

use std::collections::HashMap;
use std::time::Duration;
use pallet_runtime_segmentation::TOTAL_SEGMENTS;

/// Configuration for parallel block production
#[derive(Clone, Debug)]
pub struct ParallelProposerConfig {
    /// Maximum number of segments to process in parallel
    pub parallel_segments: usize,
    /// Maximum transactions per segment per block
    pub max_txs_per_segment: usize,
    /// Timeout for parallel segment processing
    pub segment_timeout: Duration,
}

impl Default for ParallelProposerConfig {
    fn default() -> Self {
        Self {
            // Process 64 segments in parallel (8 batches for 512 segments)
            parallel_segments: 64,
            // Allow up to 100 TXs per segment per block
            max_txs_per_segment: 100,
            // 500ms timeout per segment batch
            segment_timeout: Duration::from_millis(500),
        }
    }
}

/// Statistics about parallel block production
#[derive(Debug, Clone, Default)]
pub struct ParallelBlockStats {
    /// Number of segments with transactions
    pub active_segments: u32,
    /// Total transactions included
    pub total_txs: u64,
    /// Transactions per segment
    pub txs_per_segment: HashMap<u32, u64>,
    /// Time spent in parallel processing
    pub parallel_time_ms: u64,
    /// Estimated speedup factor
    pub speedup_factor: f64,
}

impl ParallelBlockStats {
    /// Create stats from segment load data
    pub fn from_loads(loads: &[(u32, u64)], parallel_factor: u32) -> Self {
        let active = loads.iter().filter(|(_, load)| *load > 0).count() as u32;
        let total: u64 = loads.iter().map(|(_, load)| load).sum();
        let txs_per_segment: HashMap<u32, u64> = loads
            .iter()
            .filter(|(_, load)| *load > 0)
            .cloned()
            .collect();

        Self {
            active_segments: active,
            total_txs: total,
            txs_per_segment,
            parallel_time_ms: 0,
            speedup_factor: estimate_parallel_speedup(active, parallel_factor),
        }
    }
}

/// Group transactions by segment for parallel processing
pub fn group_transactions_by_segment<H: Clone + Eq + std::hash::Hash>(
    tx_segments: &HashMap<H, u32>,
    tx_hashes: &[H],
) -> HashMap<u32, Vec<H>> {
    let mut groups: HashMap<u32, Vec<H>> = HashMap::new();

    for hash in tx_hashes {
        if let Some(&segment) = tx_segments.get(hash) {
            groups.entry(segment).or_insert_with(Vec::new).push(hash.clone());
        }
    }

    groups
}

/// Calculate optimal segment processing order based on load
/// Returns batches of segment IDs to process together
pub fn calculate_segment_processing_order(
    loads: &[(u32, u64)],
    batch_size: usize,
) -> Vec<Vec<u32>> {
    // Sort segments by load (descending) - process heaviest first
    let mut sorted: Vec<_> = loads.iter()
        .filter(|(_, load)| *load > 0)
        .map(|(id, load)| (*id, *load))
        .collect();

    // Sort by load descending
    sorted.sort_by(|a, b| b.1.cmp(&a.1));

    // Extract just the IDs
    let sorted_ids: Vec<u32> = sorted.into_iter().map(|(id, _)| id).collect();

    // Process in batches
    let mut batches = Vec::new();
    for chunk in sorted_ids.chunks(batch_size) {
        batches.push(chunk.to_vec());
    }

    batches
}

/// Estimate parallel speedup factor based on segment distribution
pub fn estimate_parallel_speedup(active_segments: u32, parallel_factor: u32) -> f64 {
    if active_segments == 0 {
        return 1.0;
    }

    // Ideal speedup is min(active_segments, parallel_factor)
    // Real speedup accounts for ~10% overhead for coordination
    let ideal = std::cmp::min(active_segments, parallel_factor) as f64;
    ideal * 0.9
}

/// Calculate theoretical TPS based on segment distribution
pub fn calculate_theoretical_tps(
    base_tps: f64,
    active_segments: u32,
    parallel_factor: u32,
) -> f64 {
    let speedup = estimate_parallel_speedup(active_segments, parallel_factor);
    base_tps * speedup
}

/// Segment batch processor for parallel execution
#[derive(Debug)]
pub struct SegmentBatchProcessor {
    /// Configuration
    config: ParallelProposerConfig,
    /// Current batch being processed
    current_batch: usize,
    /// Total batches
    total_batches: usize,
    /// Processing order (segment ID batches)
    processing_order: Vec<Vec<u32>>,
}

impl SegmentBatchProcessor {
    /// Create new batch processor from load data
    pub fn new(loads: &[(u32, u64)], config: ParallelProposerConfig) -> Self {
        let processing_order = calculate_segment_processing_order(loads, config.parallel_segments);

        Self {
            config,
            current_batch: 0,
            total_batches: processing_order.len(),
            processing_order,
        }
    }

    /// Get next batch of segments to process
    pub fn next_batch(&mut self) -> Option<&[u32]> {
        if self.current_batch >= self.total_batches {
            return None;
        }

        let batch = &self.processing_order[self.current_batch];
        self.current_batch += 1;
        Some(batch)
    }

    /// Reset processor for new block
    pub fn reset(&mut self) {
        self.current_batch = 0;
    }

    /// Check if all batches processed
    pub fn is_complete(&self) -> bool {
        self.current_batch >= self.total_batches
    }

    /// Get processing progress (0.0 - 1.0)
    pub fn progress(&self) -> f64 {
        if self.total_batches == 0 {
            return 1.0;
        }
        self.current_batch as f64 / self.total_batches as f64
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_group_transactions() {
        let mut tx_segments = HashMap::new();
        tx_segments.insert("tx1", 0);
        tx_segments.insert("tx2", 0);
        tx_segments.insert("tx3", 1);
        tx_segments.insert("tx4", 2);

        let hashes = vec!["tx1", "tx2", "tx3", "tx4"];
        let groups = group_transactions_by_segment(&tx_segments, &hashes);

        assert_eq!(groups.get(&0).unwrap().len(), 2);
        assert_eq!(groups.get(&1).unwrap().len(), 1);
        assert_eq!(groups.get(&2).unwrap().len(), 1);
    }

    #[test]
    fn test_segment_processing_order() {
        let loads = vec![
            (0, 100),
            (1, 50),
            (2, 200),
            (3, 0),  // Empty - should be excluded
            (4, 75),
        ];

        let batches = calculate_segment_processing_order(&loads, 2);

        // Should have 2 batches (4 active segments / 2 batch_size)
        assert_eq!(batches.len(), 2);
        // First batch should have 2 segments (heaviest first: 2, 0)
        assert_eq!(batches[0].len(), 2);
        assert_eq!(batches[0][0], 2); // Segment 2 has 200 load
        assert_eq!(batches[0][1], 0); // Segment 0 has 100 load
    }

    #[test]
    fn test_speedup_estimation() {
        // 64 active segments with 32 parallel workers
        let speedup = estimate_parallel_speedup(64, 32);
        assert!(speedup > 25.0 && speedup < 32.0); // Should be ~28.8 (32 * 0.9)

        // 8 active segments with 32 workers
        let speedup2 = estimate_parallel_speedup(8, 32);
        assert!(speedup2 > 6.0 && speedup2 < 8.0); // Should be ~7.2 (8 * 0.9)
    }

    #[test]
    fn test_theoretical_tps() {
        // With base TPS of 0.5 and 64 segments processing in parallel
        let tps = calculate_theoretical_tps(0.5, 64, 64);
        assert!(tps > 25.0); // Should be ~28.8 TPS (0.5 * 64 * 0.9)
    }

    #[test]
    fn test_batch_processor() {
        let loads = vec![
            (0, 100),
            (1, 50),
            (2, 200),
            (4, 75),
        ];

        let config = ParallelProposerConfig {
            parallel_segments: 2,
            ..Default::default()
        };

        let mut processor = SegmentBatchProcessor::new(&loads, config);

        // First batch
        let batch1 = processor.next_batch().unwrap();
        assert_eq!(batch1.len(), 2);

        // Second batch
        let batch2 = processor.next_batch().unwrap();
        assert_eq!(batch2.len(), 2);

        // No more batches
        assert!(processor.next_batch().is_none());
        assert!(processor.is_complete());
    }
}
