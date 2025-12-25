//! Segmented Transaction Pool for Parallel Processing
//!
//! This module implements a 512-segment transaction pool that enables parallel
//! transaction processing across the toroidal mesh runtime architecture.
//!
//! Key features:
//! - Routes transactions to segments based on sender address hash
//! - Load balances across neighboring segments in the toroidal mesh
//! - Enables parallel block authoring by processing segments concurrently
//! - Integrates with the runtime-segmentation pallet for state partitioning

use std::collections::HashMap;
use std::sync::{Arc, RwLock};
use sp_core::hashing::blake2_256;
use sp_runtime::traits::Block as BlockT;
use sc_transaction_pool_api::{
    TransactionFor, TransactionPool, TransactionSource, TxHash,
};
use pallet_runtime_segmentation::{
    coordinates_to_id, id_to_coordinates, get_adjacent_segments,
    TOTAL_SEGMENTS,
};

/// Transaction with segment assignment
#[derive(Clone, Debug)]
pub struct SegmentedTransaction<Hash, Extrinsic> {
    /// The transaction hash
    pub hash: Hash,
    /// The transaction extrinsic
    pub extrinsic: Extrinsic,
    /// Assigned segment ID (0-511)
    pub segment_id: u32,
    /// Priority for ordering within segment
    pub priority: u64,
}

/// Per-segment transaction queue
pub struct SegmentQueue<Hash, Extrinsic> {
    /// Pending transactions in this segment
    pub pending: Vec<SegmentedTransaction<Hash, Extrinsic>>,
    /// Total transactions ever processed by this segment
    pub total_processed: u64,
    /// Current load factor (0-255)
    pub load_factor: u8,
}

impl<Hash, Extrinsic> Default for SegmentQueue<Hash, Extrinsic> {
    fn default() -> Self {
        Self {
            pending: Vec::new(),
            total_processed: 0,
            load_factor: 0,
        }
    }
}

/// Segment load tracker for routing decisions
pub struct SegmentLoadTracker {
    /// Current pending count per segment (using Vec instead of array for > 32 elements)
    pending_counts: Vec<u64>,
    /// Total routed to each segment
    total_routed: Vec<u64>,
}

impl Default for SegmentLoadTracker {
    fn default() -> Self {
        Self {
            pending_counts: vec![0u64; TOTAL_SEGMENTS],
            total_routed: vec![0u64; TOTAL_SEGMENTS],
        }
    }
}

impl SegmentLoadTracker {
    /// Create a new load tracker
    pub fn new() -> Self {
        Self::default()
    }

    /// Route a transaction based on sender address with load balancing
    pub fn route_transaction(&self, sender: &[u8; 32]) -> u32 {
        // Hash sender to get deterministic base segment
        let hash = blake2_256(sender);
        let base_segment = u32::from_le_bytes([hash[0], hash[1], hash[2], hash[3]]) % TOTAL_SEGMENTS as u32;

        // Get base segment and its 6 toroidal neighbors
        let coords = id_to_coordinates(base_segment);
        let neighbors = get_adjacent_segments(&coords);

        // Find segment with lowest load among candidates
        let mut best_segment = base_segment;
        let mut best_load = self.pending_counts[base_segment as usize];

        for neighbor_coords in neighbors {
            let neighbor_id = coordinates_to_id(&neighbor_coords);
            let neighbor_load = self.pending_counts[neighbor_id as usize];
            if neighbor_load < best_load {
                best_load = neighbor_load;
                best_segment = neighbor_id;
            }
        }

        best_segment
    }

    /// Record a transaction routed to a segment
    pub fn record_transaction(&mut self, segment_id: u32) {
        if (segment_id as usize) < TOTAL_SEGMENTS {
            self.pending_counts[segment_id as usize] += 1;
            self.total_routed[segment_id as usize] += 1;
        }
    }

    /// Called when transactions are included in a block
    pub fn on_transactions_included(&mut self, segment_counts: &[(u32, u64)]) {
        for (segment_id, count) in segment_counts {
            if (*segment_id as usize) < TOTAL_SEGMENTS {
                self.pending_counts[*segment_id as usize] =
                    self.pending_counts[*segment_id as usize].saturating_sub(*count);
            }
        }
    }

    /// Get load for a specific segment
    pub fn get_load(&self, segment_id: u32) -> u64 {
        if (segment_id as usize) < TOTAL_SEGMENTS {
            self.pending_counts[segment_id as usize]
        } else {
            0
        }
    }

    /// Get all loads for monitoring
    pub fn get_all_loads(&self) -> Vec<(u32, u64)> {
        self.pending_counts
            .iter()
            .enumerate()
            .map(|(id, &load)| (id as u32, load))
            .collect()
    }
}

/// Segmented Transaction Pool
///
/// Wraps the underlying transaction pool and adds segment-based routing
/// for parallel processing capability.
pub struct SegmentedTransactionPool<P, Block>
where
    Block: BlockT,
    P: TransactionPool<Block = Block>,
{
    /// The underlying transaction pool
    inner: Arc<P>,
    /// Segment queues for parallel access (using Vec instead of array)
    segment_queues: RwLock<Vec<Vec<TxHash<P>>>>,
    /// Load tracker for routing decisions
    load_tracker: RwLock<SegmentLoadTracker>,
    /// Mapping from tx hash to segment
    tx_to_segment: RwLock<HashMap<TxHash<P>, u32>>,
}

impl<P, Block> SegmentedTransactionPool<P, Block>
where
    Block: BlockT,
    P: TransactionPool<Block = Block>,
{
    /// Create a new segmented transaction pool
    pub fn new(inner: Arc<P>) -> Self {
        // Initialize empty segment queues
        let segment_queues: Vec<Vec<TxHash<P>>> = (0..TOTAL_SEGMENTS)
            .map(|_| Vec::new())
            .collect();

        Self {
            inner,
            segment_queues: RwLock::new(segment_queues),
            load_tracker: RwLock::new(SegmentLoadTracker::default()),
            tx_to_segment: RwLock::new(HashMap::new()),
        }
    }

    /// Route and submit a transaction with segment assignment
    pub async fn submit_with_routing(
        &self,
        at: Block::Hash,
        source: TransactionSource,
        xt: TransactionFor<P>,
        sender: &[u8; 32],
    ) -> Result<(TxHash<P>, u32), P::Error> {
        // Route to optimal segment
        let segment_id = {
            let tracker = self.load_tracker.read().unwrap();
            tracker.route_transaction(sender)
        };

        // Submit to underlying pool
        let hash = self.inner.submit_one(at, source, xt).await?;

        // Record in segment queue
        {
            let mut queues = self.segment_queues.write().unwrap();
            if (segment_id as usize) < queues.len() {
                queues[segment_id as usize].push(hash.clone());
            }
        }

        // Record in mapping
        {
            let mut mapping = self.tx_to_segment.write().unwrap();
            mapping.insert(hash.clone(), segment_id);
        }

        // Update load tracker
        {
            let mut tracker = self.load_tracker.write().unwrap();
            tracker.record_transaction(segment_id);
        }

        log::info!("🎯 TX routed to segment {} (load: {})",
            segment_id,
            self.load_tracker.read().unwrap().get_load(segment_id)
        );

        Ok((hash, segment_id))
    }

    /// Get transactions for a specific segment
    pub fn get_segment_transactions(&self, segment_id: u32) -> Vec<TxHash<P>> {
        if (segment_id as usize) >= TOTAL_SEGMENTS {
            return Vec::new();
        }

        let queues = self.segment_queues.read().unwrap();
        if (segment_id as usize) < queues.len() {
            queues[segment_id as usize].clone()
        } else {
            Vec::new()
        }
    }

    /// Get transactions for multiple segments (for parallel processing)
    pub fn get_segments_transactions(&self, segment_ids: &[u32]) -> HashMap<u32, Vec<TxHash<P>>> {
        let queues = self.segment_queues.read().unwrap();
        segment_ids
            .iter()
            .filter(|&&id| (id as usize) < TOTAL_SEGMENTS && (id as usize) < queues.len())
            .map(|&id| (id, queues[id as usize].clone()))
            .collect()
    }

    /// Get segment assignment for a transaction
    pub fn get_tx_segment(&self, hash: &TxHash<P>) -> Option<u32> {
        let mapping = self.tx_to_segment.read().unwrap();
        mapping.get(hash).copied()
    }

    /// Called when transactions are finalized - clean up tracking
    pub fn on_finalized(&self, hashes: &[TxHash<P>]) {
        let mut segment_counts: HashMap<u32, u64> = HashMap::new();

        // Remove from mapping and count per segment
        {
            let mut mapping = self.tx_to_segment.write().unwrap();
            for hash in hashes {
                if let Some(segment_id) = mapping.remove(hash) {
                    *segment_counts.entry(segment_id).or_insert(0) += 1;
                }
            }
        }

        // Remove from segment queues
        {
            let mut queues = self.segment_queues.write().unwrap();
            for hash in hashes {
                for queue in queues.iter_mut() {
                    queue.retain(|h| h != hash);
                }
            }
        }

        // Update load tracker
        {
            let counts: Vec<(u32, u64)> = segment_counts.into_iter().collect();
            let mut tracker = self.load_tracker.write().unwrap();
            tracker.on_transactions_included(&counts);
        }
    }

    /// Get load distribution across all segments
    pub fn get_load_distribution(&self) -> Vec<(u32, u64)> {
        let tracker = self.load_tracker.read().unwrap();
        tracker.get_all_loads()
    }

    /// Get segments with pending transactions (for parallel processing)
    pub fn get_active_segments(&self) -> Vec<u32> {
        let queues = self.segment_queues.read().unwrap();
        queues
            .iter()
            .enumerate()
            .filter(|(_, queue)| !queue.is_empty())
            .map(|(id, _)| id as u32)
            .collect()
    }

    /// Get the inner pool for direct access
    pub fn inner(&self) -> &Arc<P> {
        &self.inner
    }
}

/// Iterator for parallel segment processing
pub struct ParallelSegmentIterator<'a, P, Block>
where
    Block: BlockT,
    P: TransactionPool<Block = Block>,
{
    pool: &'a SegmentedTransactionPool<P, Block>,
    current_segment: u32,
    segments_per_batch: u32,
}

impl<'a, P, Block> ParallelSegmentIterator<'a, P, Block>
where
    Block: BlockT,
    P: TransactionPool<Block = Block>,
{
    /// Create iterator that processes segments in batches
    pub fn new(pool: &'a SegmentedTransactionPool<P, Block>, segments_per_batch: u32) -> Self {
        Self {
            pool,
            current_segment: 0,
            segments_per_batch,
        }
    }
}

impl<'a, P, Block> Iterator for ParallelSegmentIterator<'a, P, Block>
where
    Block: BlockT,
    P: TransactionPool<Block = Block>,
{
    type Item = HashMap<u32, Vec<TxHash<P>>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.current_segment >= TOTAL_SEGMENTS as u32 {
            return None;
        }

        let end = std::cmp::min(
            self.current_segment + self.segments_per_batch,
            TOTAL_SEGMENTS as u32,
        );

        let segment_ids: Vec<u32> = (self.current_segment..end).collect();
        self.current_segment = end;

        let txs = self.pool.get_segments_transactions(&segment_ids);
        if txs.values().all(|v| v.is_empty()) {
            // Skip empty batches, try next
            self.next()
        } else {
            Some(txs)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_segment_routing_deterministic() {
        let tracker = SegmentLoadTracker::new();

        // Same sender should route to same segment (when loads are equal)
        let sender = [1u8; 32];
        let segment1 = tracker.route_transaction(&sender);
        let segment2 = tracker.route_transaction(&sender);
        assert_eq!(segment1, segment2);
    }

    #[test]
    fn test_load_balancing() {
        let mut tracker = SegmentLoadTracker::new();

        let sender = [1u8; 32];
        let base_segment = tracker.route_transaction(&sender);

        // Add heavy load to base segment
        for _ in 0..100 {
            tracker.record_transaction(base_segment);
        }

        // Should now route to a neighbor with lower load
        let new_segment = tracker.route_transaction(&sender);
        assert_ne!(new_segment, base_segment, "Should route to neighbor when base is loaded");
    }
}
