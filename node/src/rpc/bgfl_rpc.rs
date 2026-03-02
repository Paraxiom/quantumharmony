//! Blockchain-Governed Federated Learning (BGFL) RPC
//!
//! In-memory message bus for the BGFL data plane. All FL traffic between
//! the aggregator and clients flows through these RPCs, which ride
//! QuantumHarmony's PQ P2P transport (Falcon-1024 + ML-KEM-1024).
//!
//! No pallet runtime API is needed — this is a pure data plane for
//! ephemeral FL messages. On-chain attestation (model hashes, coherence
//! transitions, governance proposals) uses `system.remark` via the
//! control plane, handled separately by the BGFL client/aggregator.
//!
//! # RPC Methods
//!
//! | Method | Direction | Description |
//! |--------|-----------|-------------|
//! | `bgfl_publishRoundConfig` | Aggregator → Node | Publish round config for clients |
//! | `bgfl_getRoundConfig` | Client ← Node | Fetch current round config |
//! | `bgfl_submitUpdate` | Client → Node | Submit local model update |
//! | `bgfl_getUpdates` | Aggregator ← Node | Fetch all updates for a round |
//! | `bgfl_publishAggregateResult` | Aggregator → Node | Publish aggregation result |
//! | `bgfl_getAggregateResult` | Client ← Node | Fetch aggregation result |
//!
//! # Transport Security
//!
//! These JSON-RPC calls travel over QH's existing PQ P2P mesh — the same
//! transport that carries block announcements and consensus messages.
//! Every inter-node message is encrypted with ML-KEM-1024 and signed
//! with Falcon-1024. Zero classical TLS in the chain.
//!
//! # Memory Management
//!
//! The store retains only the **current round** config and result, plus
//! **one round** of client updates. When a new round config is published,
//! stale updates from previous rounds are pruned automatically.

use jsonrpsee::{
    core::{async_trait, RpcResult},
    proc_macros::rpc,
    types::error::ErrorObject,
};
use serde::{Deserialize, Serialize};
use sp_runtime::traits::Block as BlockT;
use std::collections::HashMap;
use std::sync::RwLock;

// ---------------------------------------------------------------------------
// Message types (mirrors bgfl crate's protocol::messages)
// ---------------------------------------------------------------------------

/// Training hyperparameters for a round.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BgflHyperparams {
    pub learning_rate: f32,
    pub local_epochs: usize,
    pub batch_size: usize,
    pub karmonic_lambda: f32,
    pub karmonic_temperature: f32,
    pub grad_clip: f32,
}

/// Round configuration broadcast by the aggregator.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BgflRoundConfig {
    pub round: u64,
    pub model_hash: String,
    pub min_coherence: f32,
    pub hyperparams: BgflHyperparams,
}

/// Client update submitted after local training.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BgflClientUpdate {
    pub client_id: String,
    pub round: u64,
    pub model_hash: String,
    /// Hex-encoded weight deltas.
    pub weight_deltas: String,
    pub num_samples: usize,
    pub coherence_score: f32,
    pub karmonic_loss: f32,
    pub drift_rate: f32,
    /// Hex-encoded Falcon-512 signature.
    pub signature: String,
}

/// Aggregate result published by the aggregator after KarmonicFedAvg.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BgflAggregateResult {
    pub round: u64,
    pub global_model_hash: String,
    /// Hex-encoded global model weights.
    pub global_weights: String,
    pub num_contributors: usize,
    pub coherence_weights: HashMap<String, f32>,
    pub attestation_tx: Option<String>,
}

/// Status response for publish/submit operations.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BgflStatus {
    pub ok: bool,
    pub message: String,
}

// ---------------------------------------------------------------------------
// In-memory FL message store
// ---------------------------------------------------------------------------

/// Ephemeral store for FL messages. Retains only current-round data.
struct BgflStore {
    /// Current round config (set by aggregator).
    round_config: Option<BgflRoundConfig>,
    /// Client updates for the current round, keyed by client_id.
    updates: HashMap<String, BgflClientUpdate>,
    /// Aggregate result for the current round.
    aggregate_result: Option<BgflAggregateResult>,
}

impl BgflStore {
    fn new() -> Self {
        Self {
            round_config: None,
            updates: HashMap::new(),
            aggregate_result: None,
        }
    }
}

// Global BGFL store, shared across RPC calls.
lazy_static::lazy_static! {
    static ref BGFL_STORE: RwLock<BgflStore> = RwLock::new(BgflStore::new());
}

// ---------------------------------------------------------------------------
// RPC trait definition
// ---------------------------------------------------------------------------

/// BGFL data plane RPC methods.
///
/// These methods provide the ephemeral message bus for federated learning
/// rounds. All messages travel over QH's PQ P2P transport.
#[rpc(server, client)]
pub trait BgflApi {
    /// Publish a new round configuration (aggregator only).
    ///
    /// Clears stale updates from previous rounds and stores the new config.
    /// Clients poll `bgfl_getRoundConfig` to discover new rounds.
    #[method(name = "bgfl_publishRoundConfig")]
    async fn publish_round_config(&self, config: BgflRoundConfig) -> RpcResult<BgflStatus>;

    /// Fetch the current round configuration.
    ///
    /// Returns `null` if no round has been published yet.
    #[method(name = "bgfl_getRoundConfig")]
    async fn get_round_config(&self) -> RpcResult<Option<BgflRoundConfig>>;

    /// Submit a client update after local training.
    ///
    /// The update must reference the current round number. Updates for
    /// stale rounds are rejected. One update per client per round.
    #[method(name = "bgfl_submitUpdate")]
    async fn submit_update(&self, update: BgflClientUpdate) -> RpcResult<BgflStatus>;

    /// Fetch all client updates for a given round (aggregator only).
    ///
    /// Returns an empty vec if no updates have been submitted yet.
    #[method(name = "bgfl_getUpdates")]
    async fn get_updates(&self, round: u64) -> RpcResult<Vec<BgflClientUpdate>>;

    /// Publish the aggregate result after KarmonicFedAvg (aggregator only).
    ///
    /// Clients poll `bgfl_getAggregateResult` to fetch the new global model.
    #[method(name = "bgfl_publishAggregateResult")]
    async fn publish_aggregate_result(&self, result: BgflAggregateResult) -> RpcResult<BgflStatus>;

    /// Fetch the aggregate result for a given round.
    ///
    /// Returns `null` if aggregation hasn't completed yet.
    #[method(name = "bgfl_getAggregateResult")]
    async fn get_aggregate_result(&self, round: u64) -> RpcResult<Option<BgflAggregateResult>>;
}

// ---------------------------------------------------------------------------
// Implementation
// ---------------------------------------------------------------------------

/// BGFL RPC handler. Standalone — no pallet or runtime API dependency.
pub struct BgflRpc<Block> {
    _marker: std::marker::PhantomData<Block>,
}

impl<Block> BgflRpc<Block>
where
    Block: BlockT,
{
    pub fn new() -> Self {
        Self {
            _marker: std::marker::PhantomData,
        }
    }
}

#[async_trait]
impl<Block> BgflApiServer for BgflRpc<Block>
where
    Block: BlockT + Send + Sync + 'static,
{
    async fn publish_round_config(&self, config: BgflRoundConfig) -> RpcResult<BgflStatus> {
        let mut store = BGFL_STORE.write().map_err(|e| {
            ErrorObject::owned(-32603, format!("Lock poisoned: {}", e), None::<()>)
        })?;

        let round = config.round;

        // Prune stale updates from previous rounds
        store.updates.retain(|_, u| u.round == round);
        store.aggregate_result = None;
        store.round_config = Some(config);

        log::info!("📡 BGFL: Published round config for round {}", round);

        Ok(BgflStatus {
            ok: true,
            message: format!("Round {} config published", round),
        })
    }

    async fn get_round_config(&self) -> RpcResult<Option<BgflRoundConfig>> {
        let store = BGFL_STORE.read().map_err(|e| {
            ErrorObject::owned(-32603, format!("Lock poisoned: {}", e), None::<()>)
        })?;

        Ok(store.round_config.clone())
    }

    async fn submit_update(&self, update: BgflClientUpdate) -> RpcResult<BgflStatus> {
        let mut store = BGFL_STORE.write().map_err(|e| {
            ErrorObject::owned(-32603, format!("Lock poisoned: {}", e), None::<()>)
        })?;

        // Reject updates for wrong round
        let current_round = store
            .round_config
            .as_ref()
            .map(|c| c.round)
            .unwrap_or(0);

        if update.round != current_round {
            return Ok(BgflStatus {
                ok: false,
                message: format!(
                    "Round mismatch: update is for round {} but current round is {}",
                    update.round, current_round
                ),
            });
        }

        let client_id = update.client_id.clone();
        store.updates.insert(client_id.clone(), update);

        log::info!(
            "📡 BGFL: Client '{}' submitted update for round {} ({} total)",
            client_id,
            current_round,
            store.updates.len()
        );

        Ok(BgflStatus {
            ok: true,
            message: format!("Update from '{}' accepted for round {}", client_id, current_round),
        })
    }

    async fn get_updates(&self, round: u64) -> RpcResult<Vec<BgflClientUpdate>> {
        let store = BGFL_STORE.read().map_err(|e| {
            ErrorObject::owned(-32603, format!("Lock poisoned: {}", e), None::<()>)
        })?;

        let updates: Vec<BgflClientUpdate> = store
            .updates
            .values()
            .filter(|u| u.round == round)
            .cloned()
            .collect();

        Ok(updates)
    }

    async fn publish_aggregate_result(&self, result: BgflAggregateResult) -> RpcResult<BgflStatus> {
        let mut store = BGFL_STORE.write().map_err(|e| {
            ErrorObject::owned(-32603, format!("Lock poisoned: {}", e), None::<()>)
        })?;

        let round = result.round;
        store.aggregate_result = Some(result);

        log::info!("📡 BGFL: Published aggregate result for round {}", round);

        Ok(BgflStatus {
            ok: true,
            message: format!("Aggregate result published for round {}", round),
        })
    }

    async fn get_aggregate_result(&self, round: u64) -> RpcResult<Option<BgflAggregateResult>> {
        let store = BGFL_STORE.read().map_err(|e| {
            ErrorObject::owned(-32603, format!("Lock poisoned: {}", e), None::<()>)
        })?;

        Ok(store
            .aggregate_result
            .as_ref()
            .filter(|r| r.round == round)
            .cloned())
    }
}
