//! Round Coordinator for Threshold QRNG
//!
//! This module manages turn-based share submission for the K-of-M threshold QRNG system.
//! It coordinates validators to ensure:
//! - Each validator submits shares in their designated turn
//! - Pool state is checked before submission to avoid over-collection
//! - Reconstruction happens automatically when K shares are collected
//! - Entropy is gossiped to all peers after reconstruction
//!
//! ## Architecture
//!
//! ```text
//! Round Coordinator
//!         │
//!         ▼
//! ┌───────────────────────────────────────────────────────┐
//! │                    Round N                             │
//! │  ┌─────────┐    ┌─────────┐    ┌─────────┐           │
//! │  │  Alice  │    │   Bob   │    │ Charlie │           │
//! │  │ turn=1  │    │ turn=2  │    │ turn=3  │           │
//! │  └────┬────┘    └────┬────┘    └────┬────┘           │
//! │       │              │              │                 │
//! │       ▼              ▼              ▼                 │
//! │   fetch_share    fetch_share    fetch_share          │
//! │       │              │              │                 │
//! │       └──────────────┼──────────────┘                 │
//! │                      ▼                                │
//! │              SHARE_POOL (K=2 of M=3)                 │
//! │                      │                                │
//! │                      ▼ (when K shares collected)      │
//! │              reconstruct_entropy()                    │
//! │                      │                                │
//! │                      ▼                                │
//! │              gossip_to_all_nodes()                   │
//! └───────────────────────────────────────────────────────┘
//! ```

use std::sync::RwLock;
use std::collections::HashMap;
use serde::{Deserialize, Serialize};
use sp_runtime::AccountId32;

/// Global share pool - imported from threshold_qrng_rpc
use crate::rpc::threshold_qrng_rpc::CollectedShare;

lazy_static::lazy_static! {
    /// Share pool for collecting shares from multiple nodes
    /// Key: round_id, Value: collected shares
    pub static ref COORDINATOR_SHARE_POOL: RwLock<HashMap<String, Vec<CollectedShare>>> = RwLock::new(HashMap::new());

    /// Validator list for the current session
    pub static ref VALIDATORS: RwLock<Vec<ValidatorInfo>> = RwLock::new(Vec::new());
}

/// Information about a validator for coordination
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ValidatorInfo {
    /// Validator account ID
    pub account_id: AccountId32,
    /// Node identifier for gossip
    pub node_id: String,
    /// Index in the validator set (determines turn order)
    pub index: usize,
    /// Priority queue endpoint (for gossip)
    pub queue_endpoint: String,
}

/// State of the current round
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum RoundState {
    /// Waiting for this node's turn to submit
    WaitingForMyTurn,
    /// Currently submitting our share
    SubmittingShare,
    /// Share submitted, waiting for K shares to be collected
    WaitingForKShares,
    /// K shares collected, reconstructing entropy
    Reconstructing,
    /// Broadcasting reconstructed entropy to peers
    Broadcasting,
    /// Round complete
    Complete,
}

impl Default for RoundState {
    fn default() -> Self {
        RoundState::WaitingForMyTurn
    }
}

/// Result of processing a round
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum RoundResult {
    /// Not this node's turn to submit
    NotMyTurn { turn_index: usize, my_index: usize },
    /// Pool already has K shares, no need to submit
    AlreadyHaveKShares { shares_collected: usize, threshold_k: u8 },
    /// Share was submitted successfully
    ShareSubmitted { round_id: String, shares_collected: usize },
    /// Entropy was reconstructed and broadcast
    ReconstructedAndBroadcast {
        round_id: String,
        entropy_hash: String,
        contributors: Vec<String>,
    },
    /// Round is still in progress
    InProgress { state: RoundState, round_id: String },
    /// Error occurred
    Error { message: String },
}

impl RoundResult {
    /// Get status string for RPC response
    pub fn status(&self) -> &'static str {
        match self {
            RoundResult::NotMyTurn { .. } => "NotMyTurn",
            RoundResult::AlreadyHaveKShares { .. } => "AlreadyHaveKShares",
            RoundResult::ShareSubmitted { .. } => "ShareSubmitted",
            RoundResult::ReconstructedAndBroadcast { .. } => "ReconstructedAndBroadcast",
            RoundResult::InProgress { .. } => "InProgress",
            RoundResult::Error { .. } => "Error",
        }
    }
}

/// Round coordinator for managing turn-based share submission
pub struct RoundCoordinator {
    /// Current round number (derived from block number)
    pub current_round: u64,
    /// Current state of the round
    pub round_state: RoundState,
    /// Ordered list of validator node IDs
    pub validators: Vec<String>,
    /// This node's index in the validator list
    pub my_index: usize,
    /// Threshold K for reconstruction
    pub threshold_k: u8,
    /// Total validators M
    pub total_m: u8,
    /// Blocks per round (default: 5)
    pub blocks_per_round: u64,
}

impl RoundCoordinator {
    /// Create a new round coordinator from block number
    pub fn new(block_number: u64) -> Self {
        // Load configuration from environment
        let threshold_k: u8 = std::env::var("QRNG_THRESHOLD_K")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(2);

        let total_m: u8 = std::env::var("QRNG_TOTAL_M")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(3);

        let blocks_per_round: u64 = std::env::var("QRNG_BLOCKS_PER_ROUND")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(5);

        // Get validator list from storage or use defaults
        let validators = Self::get_validator_list();

        // Determine this node's index
        let my_node_id = Self::get_my_node_id();
        let my_index = validators
            .iter()
            .position(|v| v == &my_node_id)
            .unwrap_or(0);

        Self {
            current_round: block_number / blocks_per_round,
            round_state: RoundState::WaitingForMyTurn,
            validators,
            my_index,
            threshold_k,
            total_m,
            blocks_per_round,
        }
    }

    /// Create coordinator with explicit parameters (for testing)
    pub fn with_config(
        block_number: u64,
        validators: Vec<String>,
        my_index: usize,
        threshold_k: u8,
        total_m: u8,
    ) -> Self {
        Self {
            current_round: block_number / 5,
            round_state: RoundState::WaitingForMyTurn,
            validators,
            my_index,
            threshold_k,
            total_m,
            blocks_per_round: 5,
        }
    }

    /// Determine if it's this node's turn to submit a share
    ///
    /// Turn order is determined by: (round_number) % num_validators
    /// This ensures fair rotation across rounds.
    pub fn is_my_turn(&self, block_number: u64) -> bool {
        if self.validators.is_empty() {
            return false;
        }

        let round = block_number / self.blocks_per_round;
        let turn_index = (round as usize) % self.validators.len();
        turn_index == self.my_index
    }

    /// Get the current turn index for a given block
    pub fn get_turn_index(&self, block_number: u64) -> usize {
        if self.validators.is_empty() {
            return 0;
        }
        let round = block_number / self.blocks_per_round;
        (round as usize) % self.validators.len()
    }

    /// Get the validator node ID whose turn it is
    pub fn get_current_turn_validator(&self, block_number: u64) -> Option<&String> {
        let turn_index = self.get_turn_index(block_number);
        self.validators.get(turn_index)
    }

    /// Check if pool has enough shares for reconstruction
    pub fn can_reconstruct(&self, round_id: &str) -> bool {
        let pool = COORDINATOR_SHARE_POOL.read().unwrap();
        pool.get(round_id)
            .map(|shares| shares.len() >= self.threshold_k as usize)
            .unwrap_or(false)
    }

    /// Get current share count for a round
    pub fn get_share_count(&self, round_id: &str) -> usize {
        let pool = COORDINATOR_SHARE_POOL.read().unwrap();
        pool.get(round_id).map(|shares| shares.len()).unwrap_or(0)
    }

    /// Check if this node has already submitted for the round
    pub fn has_submitted(&self, round_id: &str, node_id: &str) -> bool {
        let pool = COORDINATOR_SHARE_POOL.read().unwrap();
        pool.get(round_id)
            .map(|shares| shares.iter().any(|s| s.node_id == node_id))
            .unwrap_or(false)
    }

    /// Get round ID from block number
    ///
    /// Round IDs are based on the round number to ensure all nodes
    /// submit to the same round regardless of exact block timing.
    pub fn get_round_id(block_number: u64) -> String {
        let blocks_per_round: u64 = std::env::var("QRNG_BLOCKS_PER_ROUND")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(5);

        format!("round-{}", block_number / blocks_per_round)
    }

    /// Get round ID for the coordinator's current round
    pub fn current_round_id(&self) -> String {
        format!("round-{}", self.current_round)
    }

    /// Get this node's ID from environment or keystore
    fn get_my_node_id() -> String {
        std::env::var("NODE_ID")
            .or_else(|_| std::env::var("VALIDATOR_NAME"))
            .unwrap_or_else(|_| "unknown".to_string())
    }

    /// Get ordered list of validator node IDs
    fn get_validator_list() -> Vec<String> {
        // Try to load from environment first
        if let Ok(validators_str) = std::env::var("VALIDATOR_LIST") {
            return validators_str
                .split(',')
                .map(|s| s.trim().to_string())
                .collect();
        }

        // Default to canary network validators
        vec![
            "alice".to_string(),
            "bob".to_string(),
            "charlie".to_string(),
        ]
    }

    /// Get my share index (for Shamir share creation)
    pub fn get_my_share_index(&self) -> u8 {
        self.my_index as u8
    }

    /// Add a share to the pool
    pub fn add_share_to_pool(round_id: &str, share: CollectedShare) -> usize {
        let mut pool = COORDINATOR_SHARE_POOL.write().unwrap();
        let round_shares = pool.entry(round_id.to_string()).or_insert_with(Vec::new);

        // Don't add duplicate shares from same node
        if !round_shares.iter().any(|s| s.node_id == share.node_id) {
            round_shares.push(share);
        }

        round_shares.len()
    }

    /// Get shares for a round
    pub fn get_shares(round_id: &str) -> Option<Vec<CollectedShare>> {
        let pool = COORDINATOR_SHARE_POOL.read().unwrap();
        pool.get(round_id).cloned()
    }

    /// Clear shares for a round (after reconstruction)
    pub fn clear_round(round_id: &str) {
        let mut pool = COORDINATOR_SHARE_POOL.write().unwrap();
        pool.remove(round_id);
    }

    /// Get all active rounds
    pub fn get_active_rounds() -> Vec<String> {
        let pool = COORDINATOR_SHARE_POOL.read().unwrap();
        pool.keys().cloned().collect()
    }
}

/// Canary network validator endpoints
pub mod canary_network {
    /// Alice (Montreal) - Sudo account
    pub const ALICE_RPC: &str = "http://51.79.26.123:9944";
    pub const ALICE_P2P: &str = "51.79.26.123:30333";
    pub const ALICE_QUEUE: &str = "http://51.79.26.123:5555";

    /// Bob (Beauharnois)
    pub const BOB_RPC: &str = "http://51.79.26.168:9944";
    pub const BOB_P2P: &str = "51.79.26.168:30333";
    pub const BOB_QUEUE: &str = "http://51.79.26.168:5556";

    /// Charlie (Frankfurt)
    pub const CHARLIE_RPC: &str = "http://209.38.225.4:9944";
    pub const CHARLIE_P2P: &str = "209.38.225.4:30333";
    pub const CHARLIE_QUEUE: &str = "http://209.38.225.4:5557";

    /// Get all RPC endpoints
    pub fn get_all_rpc_endpoints() -> Vec<(&'static str, &'static str)> {
        vec![
            ("alice", ALICE_RPC),
            ("bob", BOB_RPC),
            ("charlie", CHARLIE_RPC),
        ]
    }

    /// Get all priority queue endpoints
    pub fn get_all_queue_endpoints() -> Vec<(&'static str, &'static str)> {
        vec![
            ("alice", ALICE_QUEUE),
            ("bob", BOB_QUEUE),
            ("charlie", CHARLIE_QUEUE),
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_round_id_generation() {
        // Same round ID for blocks in the same round
        assert_eq!(RoundCoordinator::get_round_id(0), "round-0");
        assert_eq!(RoundCoordinator::get_round_id(4), "round-0");
        assert_eq!(RoundCoordinator::get_round_id(5), "round-1");
        assert_eq!(RoundCoordinator::get_round_id(9), "round-1");
        assert_eq!(RoundCoordinator::get_round_id(10), "round-2");
    }

    #[test]
    fn test_turn_calculation() {
        let validators = vec![
            "alice".to_string(),
            "bob".to_string(),
            "charlie".to_string(),
        ];

        // Alice's coordinator (index 0)
        let alice_coord = RoundCoordinator::with_config(0, validators.clone(), 0, 2, 3);

        // Block 0-4: round 0, turn = 0 (alice)
        assert!(alice_coord.is_my_turn(0));
        assert!(alice_coord.is_my_turn(4));

        // Block 5-9: round 1, turn = 1 (bob)
        assert!(!alice_coord.is_my_turn(5));

        // Block 10-14: round 2, turn = 2 (charlie)
        assert!(!alice_coord.is_my_turn(10));

        // Block 15-19: round 3, turn = 0 (alice again)
        assert!(alice_coord.is_my_turn(15));
    }

    #[test]
    fn test_turn_rotation() {
        let validators = vec![
            "alice".to_string(),
            "bob".to_string(),
            "charlie".to_string(),
        ];

        let coord = RoundCoordinator::with_config(0, validators.clone(), 0, 2, 3);

        // Verify turn order
        assert_eq!(coord.get_turn_index(0), 0);   // Round 0: Alice
        assert_eq!(coord.get_turn_index(5), 1);   // Round 1: Bob
        assert_eq!(coord.get_turn_index(10), 2);  // Round 2: Charlie
        assert_eq!(coord.get_turn_index(15), 0);  // Round 3: Alice (wraps)
        assert_eq!(coord.get_turn_index(20), 1);  // Round 4: Bob
    }

    #[test]
    fn test_get_current_turn_validator() {
        let validators = vec![
            "alice".to_string(),
            "bob".to_string(),
            "charlie".to_string(),
        ];

        let coord = RoundCoordinator::with_config(0, validators, 0, 2, 3);

        assert_eq!(coord.get_current_turn_validator(0), Some(&"alice".to_string()));
        assert_eq!(coord.get_current_turn_validator(5), Some(&"bob".to_string()));
        assert_eq!(coord.get_current_turn_validator(10), Some(&"charlie".to_string()));
    }

    #[test]
    fn test_share_pool_operations() {
        // Clear pool first
        {
            let mut pool = COORDINATOR_SHARE_POOL.write().unwrap();
            pool.clear();
        }

        let round_id = "test-round";
        let coord = RoundCoordinator::with_config(0, vec!["alice".to_string()], 0, 2, 3);

        // Initially empty
        assert_eq!(coord.get_share_count(round_id), 0);
        assert!(!coord.can_reconstruct(round_id));

        // Add one share
        let share1 = CollectedShare {
            node_id: "alice".to_string(),
            share_bytes: vec![1, 2, 3],
            share_index: 0,
            qber: 0.005,
            timestamp: 1000,
            device_proof: crate::rpc::threshold_qrng_rpc::DeviceProof {
                commitment: "test".to_string(),
                signature: "test".to_string(),
                public_inputs: crate::rpc::threshold_qrng_rpc::DeviceProofInputs {
                    share_hash: "test".to_string(),
                    qber_scaled: 50,
                    device_id: "test".to_string(),
                    timestamp: 1000,
                },
            },
        };

        RoundCoordinator::add_share_to_pool(round_id, share1);
        assert_eq!(coord.get_share_count(round_id), 1);
        assert!(!coord.can_reconstruct(round_id)); // K=2, only have 1

        // Add second share
        let share2 = CollectedShare {
            node_id: "bob".to_string(),
            share_bytes: vec![4, 5, 6],
            share_index: 1,
            qber: 0.008,
            timestamp: 1001,
            device_proof: crate::rpc::threshold_qrng_rpc::DeviceProof {
                commitment: "test2".to_string(),
                signature: "test2".to_string(),
                public_inputs: crate::rpc::threshold_qrng_rpc::DeviceProofInputs {
                    share_hash: "test2".to_string(),
                    qber_scaled: 80,
                    device_id: "test2".to_string(),
                    timestamp: 1001,
                },
            },
        };

        RoundCoordinator::add_share_to_pool(round_id, share2);
        assert_eq!(coord.get_share_count(round_id), 2);
        assert!(coord.can_reconstruct(round_id)); // K=2, have 2

        // Clean up
        RoundCoordinator::clear_round(round_id);
        assert_eq!(coord.get_share_count(round_id), 0);
    }

    #[test]
    fn test_duplicate_share_prevention() {
        // Clear pool first
        {
            let mut pool = COORDINATOR_SHARE_POOL.write().unwrap();
            pool.clear();
        }

        let round_id = "test-dup-round";

        let share = CollectedShare {
            node_id: "alice".to_string(),
            share_bytes: vec![1, 2, 3],
            share_index: 0,
            qber: 0.005,
            timestamp: 1000,
            device_proof: crate::rpc::threshold_qrng_rpc::DeviceProof {
                commitment: "test".to_string(),
                signature: "test".to_string(),
                public_inputs: crate::rpc::threshold_qrng_rpc::DeviceProofInputs {
                    share_hash: "test".to_string(),
                    qber_scaled: 50,
                    device_id: "test".to_string(),
                    timestamp: 1000,
                },
            },
        };

        // Add same share twice
        RoundCoordinator::add_share_to_pool(round_id, share.clone());
        RoundCoordinator::add_share_to_pool(round_id, share);

        // Should still only have 1
        let coord = RoundCoordinator::with_config(0, vec!["alice".to_string()], 0, 2, 3);
        assert_eq!(coord.get_share_count(round_id), 1);

        // Clean up
        RoundCoordinator::clear_round(round_id);
    }

    #[test]
    fn test_has_submitted() {
        // Clear pool first
        {
            let mut pool = COORDINATOR_SHARE_POOL.write().unwrap();
            pool.clear();
        }

        let round_id = "test-submitted-round";
        let coord = RoundCoordinator::with_config(0, vec!["alice".to_string()], 0, 2, 3);

        assert!(!coord.has_submitted(round_id, "alice"));

        let share = CollectedShare {
            node_id: "alice".to_string(),
            share_bytes: vec![1, 2, 3],
            share_index: 0,
            qber: 0.005,
            timestamp: 1000,
            device_proof: crate::rpc::threshold_qrng_rpc::DeviceProof {
                commitment: "test".to_string(),
                signature: "test".to_string(),
                public_inputs: crate::rpc::threshold_qrng_rpc::DeviceProofInputs {
                    share_hash: "test".to_string(),
                    qber_scaled: 50,
                    device_id: "test".to_string(),
                    timestamp: 1000,
                },
            },
        };

        RoundCoordinator::add_share_to_pool(round_id, share);
        assert!(coord.has_submitted(round_id, "alice"));
        assert!(!coord.has_submitted(round_id, "bob"));

        // Clean up
        RoundCoordinator::clear_round(round_id);
    }
}
