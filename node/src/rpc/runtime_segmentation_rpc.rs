//! Runtime Segmentation RPC
//!
//! Query interface for 512-segment toroidal mesh runtime:
//! 1. segmentation_getSegmentInfo - Get details about a specific segment
//! 2. segmentation_getAllSegments - Get summary of all segments
//! 3. segmentation_getSegmentsByLoad - Get segments sorted by load
//! 4. segmentation_getNeighbors - Get neighbors of a specific segment
//! 5. segmentation_getTopology - Get mesh topology information
//! 6. segmentation_routeTransaction - Route a transaction to optimal segment
//! 7. segmentation_recordTransaction - Record a transaction for load tracking

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
use sp_core::hashing::blake2_256;
use pallet_runtime_segmentation::{
    SegmentCoordinates, coordinates_to_id, id_to_coordinates,
    get_adjacent_segments, toroidal_distance,
    MESH_SIZE_X, MESH_SIZE_Y, MESH_SIZE_Z, TOTAL_SEGMENTS,
};

/// In-memory segment load tracker for routing decisions
/// This is shared across RPC calls and updated as transactions are submitted
#[derive(Debug, Default)]
pub struct SegmentLoadTracker {
    /// Current pending transaction count per segment
    pending_txs: HashMap<u32, u64>,
    /// Total transactions routed to each segment
    total_txs: HashMap<u32, u64>,
    /// Last block number when load was reset
    last_reset_block: u64,
}

impl SegmentLoadTracker {
    pub fn new() -> Self {
        Self {
            pending_txs: HashMap::new(),
            total_txs: HashMap::new(),
            last_reset_block: 0,
        }
    }

    /// Route a transaction based on sender address, using load balancing
    /// Returns the segment ID with lowest current load among candidates
    pub fn route_transaction(&self, sender: &[u8; 32]) -> u32 {
        // Hash sender to get base segment (deterministic)
        let hash = blake2_256(sender);
        let base_segment = u32::from_le_bytes([hash[0], hash[1], hash[2], hash[3]]) % TOTAL_SEGMENTS as u32;

        // Check load of base segment and its 6 neighbors
        let coords = id_to_coordinates(base_segment);
        let neighbors = get_adjacent_segments(&coords);

        let mut candidates: Vec<(u32, u64)> = vec![(base_segment, self.get_load(base_segment))];
        for neighbor_coords in neighbors {
            let neighbor_id = coordinates_to_id(&neighbor_coords);
            candidates.push((neighbor_id, self.get_load(neighbor_id)));
        }

        // Sort by load (ascending) and pick the lowest
        candidates.sort_by_key(|(_, load)| *load);
        candidates[0].0
    }

    /// Get current load for a segment
    pub fn get_load(&self, segment_id: u32) -> u64 {
        *self.pending_txs.get(&segment_id).unwrap_or(&0)
    }

    /// Record a transaction routed to a segment
    pub fn record_transaction(&mut self, segment_id: u32) {
        *self.pending_txs.entry(segment_id).or_insert(0) += 1;
        *self.total_txs.entry(segment_id).or_insert(0) += 1;
    }

    /// Called when a block is produced - reduce pending counts
    pub fn on_block_produced(&mut self, txs_per_segment: &[(u32, u64)]) {
        for (segment_id, count) in txs_per_segment {
            if let Some(pending) = self.pending_txs.get_mut(segment_id) {
                *pending = pending.saturating_sub(*count);
            }
        }
    }

    /// Get all segment loads for reporting
    pub fn get_all_loads(&self) -> Vec<(u32, u64, u64)> {
        let mut loads: Vec<(u32, u64, u64)> = (0..TOTAL_SEGMENTS as u32)
            .map(|id| {
                let pending = *self.pending_txs.get(&id).unwrap_or(&0);
                let total = *self.total_txs.get(&id).unwrap_or(&0);
                (id, pending, total)
            })
            .collect();
        loads.sort_by_key(|(_, pending, _)| *pending);
        loads
    }
}

/// Global load tracker instance (shared across all RPC calls)
lazy_static::lazy_static! {
    pub static ref SEGMENT_LOAD_TRACKER: RwLock<SegmentLoadTracker> = RwLock::new(SegmentLoadTracker::new());
}

/// Segment information for RPC response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SegmentInfo {
    pub id: u32,
    pub coordinates: CoordinatesJson,
    pub transaction_count: u64,
    pub load_factor: u8,
    pub entangled_segments: Vec<u32>,
    pub state_root: String,
}

/// Coordinates in JSON-friendly format
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CoordinatesJson {
    pub x: u8,
    pub y: u8,
    pub z: u8,
}

/// Load summary for a segment
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LoadSummary {
    pub segment_id: u32,
    pub current_load: u8,
    pub average_load: u8,
    pub peak_load: u8,
}

/// Topology information
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TopologyInfo {
    pub mesh_size_x: usize,
    pub mesh_size_y: usize,
    pub mesh_size_z: usize,
    pub total_segments: usize,
    pub segments_initialized: u32,
    pub average_load: f32,
}

/// Routing result returned by segmentation_routeTransaction
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RoutingResult {
    pub segment_id: u32,
    pub coordinates: CoordinatesJson,
    pub current_load: u64,
    pub neighbors_checked: u32,
}

/// Runtime Segmentation RPC API
#[rpc(client, server)]
pub trait RuntimeSegmentationApi {
    /// Get information about a specific segment
    #[method(name = "segmentation_getSegmentInfo")]
    async fn get_segment_info(&self, segment_id: u32) -> RpcResult<Option<SegmentInfo>>;

    /// Get summary of all segments
    #[method(name = "segmentation_getAllSegments")]
    async fn get_all_segments(&self) -> RpcResult<Vec<SegmentInfo>>;

    /// Get segments sorted by load (ascending)
    #[method(name = "segmentation_getSegmentsByLoad")]
    async fn get_segments_by_load(&self, limit: u32) -> RpcResult<Vec<LoadSummary>>;

    /// Get neighbor segments for a given segment
    #[method(name = "segmentation_getNeighbors")]
    async fn get_neighbors(&self, segment_id: u32) -> RpcResult<Vec<u32>>;

    /// Get topology information
    #[method(name = "segmentation_getTopology")]
    async fn get_topology(&self) -> RpcResult<TopologyInfo>;

    /// Calculate distance between two segments in toroidal space
    #[method(name = "segmentation_calculateDistance")]
    async fn calculate_distance(&self, segment_id_a: u32, segment_id_b: u32) -> RpcResult<u32>;

    /// Route a transaction to the optimal segment based on sender address and load
    /// This is the key method for parallel processing - it assigns transactions to segments
    #[method(name = "segmentation_routeTransaction")]
    async fn route_transaction(&self, sender_hex: String) -> RpcResult<RoutingResult>;

    /// Record that a transaction was submitted to a segment (for load tracking)
    #[method(name = "segmentation_recordTransaction")]
    async fn record_transaction(&self, segment_id: u32) -> RpcResult<bool>;

    /// Get current load across all segments (for monitoring)
    #[method(name = "segmentation_getLoadDistribution")]
    async fn get_load_distribution(&self) -> RpcResult<Vec<LoadSummary>>;
}

/// Runtime Segmentation RPC implementation
pub struct RuntimeSegmentationRpc<Block> {
    _phantom: std::marker::PhantomData<Block>,
}

impl<Block> RuntimeSegmentationRpc<Block> {
    /// Create new runtime segmentation RPC instance
    pub fn new() -> Self {
        Self {
            _phantom: Default::default(),
        }
    }
}

#[async_trait]
impl<Block> RuntimeSegmentationApiServer for RuntimeSegmentationRpc<Block>
where
    Block: BlockT,
{
    async fn get_segment_info(&self, segment_id: u32) -> RpcResult<Option<SegmentInfo>> {
        if segment_id >= TOTAL_SEGMENTS as u32 {
            return Err(ErrorObject::owned(
                ErrorCode::InvalidParams.code(),
                format!("Invalid segment_id: {}. Must be 0-{}", segment_id, TOTAL_SEGMENTS - 1),
                None::<String>,
            ));
        }

        // For now, return calculated information based on segment ID
        // In production, this would query storage
        let coords = id_to_coordinates(segment_id);
        let neighbors = get_adjacent_segments(&coords);
        let entangled_ids: Vec<u32> = neighbors.iter().map(|c| coordinates_to_id(c)).collect();

        let info = SegmentInfo {
            id: segment_id,
            coordinates: CoordinatesJson {
                x: coords.x,
                y: coords.y,
                z: coords.z,
            },
            transaction_count: 0, // Would be queried from storage
            load_factor: 0,       // Would be queried from storage
            entangled_segments: entangled_ids,
            state_root: format!("0x{:064x}", segment_id), // Placeholder
        };

        Ok(Some(info))
    }

    async fn get_all_segments(&self) -> RpcResult<Vec<SegmentInfo>> {
        let mut segments = Vec::with_capacity(TOTAL_SEGMENTS);

        for segment_id in 0..TOTAL_SEGMENTS as u32 {
            if let Some(info) = self.get_segment_info(segment_id).await? {
                segments.push(info);
            }
        }

        Ok(segments)
    }

    async fn get_segments_by_load(&self, limit: u32) -> RpcResult<Vec<LoadSummary>> {
        let limit = limit.min(TOTAL_SEGMENTS as u32);
        let mut summaries = Vec::with_capacity(limit as usize);

        // For now, return placeholder data
        // In production, this would query actual load from storage
        for segment_id in 0..limit {
            summaries.push(LoadSummary {
                segment_id,
                current_load: 0,
                average_load: 0,
                peak_load: 0,
            });
        }

        // Sort by current_load (ascending)
        summaries.sort_by_key(|s| s.current_load);

        Ok(summaries)
    }

    async fn get_neighbors(&self, segment_id: u32) -> RpcResult<Vec<u32>> {
        if segment_id >= TOTAL_SEGMENTS as u32 {
            return Err(ErrorObject::owned(
                ErrorCode::InvalidParams.code(),
                format!("Invalid segment_id: {}. Must be 0-{}", segment_id, TOTAL_SEGMENTS - 1),
                None::<String>,
            ));
        }

        let coords = id_to_coordinates(segment_id);
        let neighbors = get_adjacent_segments(&coords);
        let neighbor_ids: Vec<u32> = neighbors.iter().map(|c| coordinates_to_id(c)).collect();

        Ok(neighbor_ids)
    }

    async fn get_topology(&self) -> RpcResult<TopologyInfo> {
        Ok(TopologyInfo {
            mesh_size_x: MESH_SIZE_X,
            mesh_size_y: MESH_SIZE_Y,
            mesh_size_z: MESH_SIZE_Z,
            total_segments: TOTAL_SEGMENTS,
            segments_initialized: TOTAL_SEGMENTS as u32, // All initialized in genesis
            average_load: 0.0, // Would be calculated from storage
        })
    }

    async fn calculate_distance(&self, segment_id_a: u32, segment_id_b: u32) -> RpcResult<u32> {
        if segment_id_a >= TOTAL_SEGMENTS as u32 || segment_id_b >= TOTAL_SEGMENTS as u32 {
            return Err(ErrorObject::owned(
                ErrorCode::InvalidParams.code(),
                "Invalid segment_id. Must be 0-511",
                None::<String>,
            ));
        }

        let coords_a = id_to_coordinates(segment_id_a);
        let coords_b = id_to_coordinates(segment_id_b);
        let distance = toroidal_distance(&coords_a, &coords_b);

        Ok(distance)
    }

    async fn route_transaction(&self, sender_hex: String) -> RpcResult<RoutingResult> {
        // Parse sender address from hex
        let sender_bytes = hex::decode(sender_hex.trim_start_matches("0x"))
            .map_err(|e| ErrorObject::owned(
                ErrorCode::InvalidParams.code(),
                format!("Invalid sender hex: {}", e),
                None::<String>,
            ))?;

        if sender_bytes.len() != 32 {
            return Err(ErrorObject::owned(
                ErrorCode::InvalidParams.code(),
                format!("Sender must be 32 bytes, got {}", sender_bytes.len()),
                None::<String>,
            ));
        }

        let mut sender: [u8; 32] = [0u8; 32];
        sender.copy_from_slice(&sender_bytes);

        // Route using the load tracker
        let tracker = SEGMENT_LOAD_TRACKER.read().unwrap();
        let segment_id = tracker.route_transaction(&sender);
        let current_load = tracker.get_load(segment_id);
        drop(tracker);

        let coords = id_to_coordinates(segment_id);

        Ok(RoutingResult {
            segment_id,
            coordinates: CoordinatesJson {
                x: coords.x,
                y: coords.y,
                z: coords.z,
            },
            current_load,
            neighbors_checked: 7, // Base segment + 6 neighbors
        })
    }

    async fn record_transaction(&self, segment_id: u32) -> RpcResult<bool> {
        if segment_id >= TOTAL_SEGMENTS as u32 {
            return Err(ErrorObject::owned(
                ErrorCode::InvalidParams.code(),
                format!("Invalid segment_id: {}. Must be 0-{}", segment_id, TOTAL_SEGMENTS - 1),
                None::<String>,
            ));
        }

        let mut tracker = SEGMENT_LOAD_TRACKER.write().unwrap();
        tracker.record_transaction(segment_id);

        log::debug!("📊 Segment {} load: {} pending", segment_id, tracker.get_load(segment_id));

        Ok(true)
    }

    async fn get_load_distribution(&self) -> RpcResult<Vec<LoadSummary>> {
        let tracker = SEGMENT_LOAD_TRACKER.read().unwrap();
        let loads = tracker.get_all_loads();

        let summaries: Vec<LoadSummary> = loads.iter()
            .take(512) // All segments
            .map(|(id, pending, total)| LoadSummary {
                segment_id: *id,
                current_load: *pending as u8,
                average_load: if *total > 0 { (*pending * 100 / total.max(&1)) as u8 } else { 0 },
                peak_load: *pending as u8, // Simplified - would track actual peak
            })
            .collect();

        Ok(summaries)
    }
}

/// Helper function to route and record a transaction in one call
/// Used by transaction_gateway.rs
pub fn route_and_record_transaction(sender: &[u8; 32]) -> u32 {
    let tracker = SEGMENT_LOAD_TRACKER.read().unwrap();
    let segment_id = tracker.route_transaction(sender);
    drop(tracker);

    let mut tracker = SEGMENT_LOAD_TRACKER.write().unwrap();
    tracker.record_transaction(segment_id);

    log::info!("🎯 Routed TX to segment {} (load: {})", segment_id, tracker.get_load(segment_id));

    segment_id
}
