//! Devonomics RPC
//!
//! Provides RPC methods for querying on-chain quest completion and devonomics scores.
//!
//! Methods:
//! - `devonomics_getScore` - Get devonomics score for an account
//! - `devonomics_getQuests` - Get completed quests for an account
//! - `devonomics_getTier` - Get highest unlocked tier for an account
//! - `devonomics_getLeaderboard` - Get leaderboard sorted by score

use jsonrpsee::{
    core::{async_trait, RpcResult},
    proc_macros::rpc,
    types::error::{ErrorCode, ErrorObject},
};
use sp_api::ProvideRuntimeApi;
use sp_blockchain::HeaderBackend;
use sp_runtime::{traits::Block as BlockT, AccountId32};
use std::sync::Arc;
use serde::{Deserialize, Serialize};
use pallet_devonomics::runtime_api::DevonomicsApi as DevonomicsRuntimeApi;

/// Score response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ScoreResponse {
    pub score: u32,
}

/// Completed quest entry
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct QuestEntry {
    pub id: String,
    pub completed_at: u32,
}

/// Tier response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TierResponse {
    pub tier: u8,
}

/// Leaderboard entry
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LeaderboardEntry {
    pub account: String,
    pub score: u32,
}

/// RPC trait for Devonomics
#[rpc(server, client)]
pub trait DevonomicsApi<BlockHash> {
    /// Get devonomics score for an account
    #[method(name = "devonomics_getScore")]
    async fn get_score(&self, account: String) -> RpcResult<ScoreResponse>;

    /// Get completed quests for an account
    #[method(name = "devonomics_getQuests")]
    async fn get_quests(&self, account: String) -> RpcResult<Vec<QuestEntry>>;

    /// Get highest unlocked tier for an account
    #[method(name = "devonomics_getTier")]
    async fn get_tier(&self, account: String) -> RpcResult<TierResponse>;

    /// Get leaderboard sorted by score descending
    #[method(name = "devonomics_getLeaderboard")]
    async fn get_leaderboard(&self, limit: Option<u32>) -> RpcResult<Vec<LeaderboardEntry>>;
}

/// Devonomics RPC implementation
pub struct DevonomicsRpc<C, Block> {
    client: Arc<C>,
    _marker: std::marker::PhantomData<Block>,
}

impl<C, Block> DevonomicsRpc<C, Block>
where
    Block: BlockT,
    C: ProvideRuntimeApi<Block>,
{
    pub fn new(client: Arc<C>) -> Self {
        Self {
            client,
            _marker: std::marker::PhantomData,
        }
    }
}

fn parse_account(account_str: &str) -> RpcResult<AccountId32> {
    // Try SS58 decode first
    use sp_core::crypto::Ss58Codec;
    if let Ok(account) = AccountId32::from_ss58check(account_str) {
        return Ok(account);
    }
    // Try hex decode
    let hex_str = account_str.trim_start_matches("0x");
    let bytes = hex::decode(hex_str).map_err(|_| {
        ErrorObject::owned(
            ErrorCode::InvalidParams.code(),
            "Invalid account: expected SS58 or hex-encoded AccountId32",
            None::<()>,
        )
    })?;
    if bytes.len() != 32 {
        return Err(ErrorObject::owned(
            ErrorCode::InvalidParams.code(),
            format!("Invalid account length: {} bytes, expected 32", bytes.len()),
            None::<()>,
        ));
    }
    let mut arr = [0u8; 32];
    arr.copy_from_slice(&bytes);
    Ok(AccountId32::from(arr))
}

#[async_trait]
impl<C, Block> DevonomicsApiServer<Block::Hash> for DevonomicsRpc<C, Block>
where
    Block: BlockT,
    C: Send + Sync + 'static + HeaderBackend<Block> + ProvideRuntimeApi<Block>,
    C::Api: DevonomicsRuntimeApi<Block, AccountId32>,
{
    async fn get_score(&self, account: String) -> RpcResult<ScoreResponse> {
        let account_id = parse_account(&account)?;
        let best_hash = self.client.info().best_hash;

        match self.client.runtime_api().get_score(best_hash, account_id) {
            Ok(score) => Ok(ScoreResponse { score }),
            Err(_) => {
                log::warn!("Devonomics runtime API not available - runtime upgrade required");
                Ok(ScoreResponse { score: 0 })
            }
        }
    }

    async fn get_quests(&self, account: String) -> RpcResult<Vec<QuestEntry>> {
        let account_id = parse_account(&account)?;
        let best_hash = self.client.info().best_hash;

        match self.client.runtime_api().get_completed_quests(best_hash, account_id) {
            Ok(quests) => {
                Ok(quests
                    .into_iter()
                    .map(|(id_bytes, block)| QuestEntry {
                        id: String::from_utf8_lossy(&id_bytes).to_string(),
                        completed_at: block,
                    })
                    .collect())
            }
            Err(_) => {
                log::warn!("Devonomics runtime API not available - runtime upgrade required");
                Ok(vec![])
            }
        }
    }

    async fn get_tier(&self, account: String) -> RpcResult<TierResponse> {
        let account_id = parse_account(&account)?;
        let best_hash = self.client.info().best_hash;

        match self.client.runtime_api().get_tier(best_hash, account_id) {
            Ok(tier) => Ok(TierResponse { tier }),
            Err(_) => {
                log::warn!("Devonomics runtime API not available - runtime upgrade required");
                Ok(TierResponse { tier: 0 })
            }
        }
    }

    async fn get_leaderboard(&self, limit: Option<u32>) -> RpcResult<Vec<LeaderboardEntry>> {
        let limit = limit.unwrap_or(50);
        let best_hash = self.client.info().best_hash;

        match self.client.runtime_api().get_leaderboard(best_hash, limit) {
            Ok(entries) => {
                Ok(entries
                    .into_iter()
                    .map(|(account, score)| LeaderboardEntry {
                        account: format!("{}", account),
                        score,
                    })
                    .collect())
            }
            Err(_) => {
                log::warn!("Devonomics runtime API not available - runtime upgrade required");
                Ok(vec![])
            }
        }
    }
}
