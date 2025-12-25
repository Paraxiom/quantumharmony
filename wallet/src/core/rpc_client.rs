//! RPC client for connecting to QuantumHarmony node

use anyhow::Result;
use jsonrpsee::{
    core::client::ClientT,
    rpc_params,
    ws_client::{WsClient, WsClientBuilder},
};
use serde::{Deserialize, Serialize};
use sp_core::H256;
use std::sync::Arc;
use tokio::sync::RwLock;

use super::{ConsensusStatus, NetworkStatus, RuntimeUpgrade};

/// RPC client for blockchain interaction
pub struct RpcClient {
    client: Arc<RwLock<Option<WsClient>>>,
    url: String,
}

impl RpcClient {
    /// Create new RPC client
    pub fn new(url: impl Into<String>) -> Self {
        Self {
            client: Arc::new(RwLock::new(None)),
            url: url.into(),
        }
    }

    /// Connect to the node
    pub async fn connect(&self) -> Result<()> {
        tracing::info!("Connecting to node at {}", self.url);

        let client = WsClientBuilder::default()
            .build(&self.url)
            .await?;

        *self.client.write().await = Some(client);

        tracing::info!("✅ Connected to node");
        Ok(())
    }

    /// Check if connected
    pub async fn is_connected(&self) -> bool {
        self.client.read().await.is_some()
    }

    /// Get runtime version
    pub async fn runtime_version(&self) -> Result<RuntimeVersion> {
        let client = self.client.read().await;
        let client = client.as_ref().ok_or_else(|| anyhow::anyhow!("Not connected"))?;

        let version: RuntimeVersion = client
            .request("state_getRuntimeVersion", rpc_params![])
            .await?;

        Ok(version)
    }

    /// Get current block number
    pub async fn current_block(&self) -> Result<u64> {
        let client = self.client.read().await;
        let client = client.as_ref().ok_or_else(|| anyhow::anyhow!("Not connected"))?;

        let header: BlockHeader = client
            .request("chain_getHeader", rpc_params![])
            .await?;

        Ok(header.number)
    }

    /// Get finalized block number
    pub async fn finalized_block(&self) -> Result<u64> {
        let client = self.client.read().await;
        let client = client.as_ref().ok_or_else(|| anyhow::anyhow!("Not connected"))?;

        let hash: H256 = client
            .request("chain_getFinalizedHead", rpc_params![])
            .await?;

        let header: BlockHeader = client
            .request("chain_getHeader", rpc_params![hash])
            .await?;

        Ok(header.number)
    }

    /// Get network status
    pub async fn network_status(&self) -> Result<NetworkStatus> {
        let best = self.current_block().await?;
        let finalized = self.finalized_block().await?;

        // TODO: Implement actual peer count and latency queries
        Ok(NetworkStatus {
            connected_peers: 3,  // Placeholder
            best_block: best,
            finalized_block: finalized,
            is_syncing: best > finalized + 10,
            average_latency_ms: 23,  // Placeholder
        })
    }

    /// Get consensus status
    pub async fn consensus_status(&self) -> Result<ConsensusStatus> {
        let finalized = self.finalized_block().await?;
        let best = self.current_block().await?;

        // TODO: Query actual validator set from pallet-validator-set
        Ok(ConsensusStatus {
            validator_count: 3,
            online_validators: 3,
            current_epoch: best / 100,  // Assuming 100 blocks per epoch
            finality_lag: best.saturating_sub(finalized),
        })
    }

    /// Check for pending runtime upgrade
    pub async fn check_pending_upgrade(&self) -> Result<Option<RuntimeUpgrade>> {
        // TODO: Query pallet-sudo for authorized upgrade call
        // For now, return None (no pending upgrade)
        Ok(None)
    }

    /// Get account balance
    pub async fn get_balance(&self, account: &str) -> Result<u128> {
        let client = self.client.read().await;
        let client = client.as_ref().ok_or_else(|| anyhow::anyhow!("Not connected"))?;

        // TODO: Implement proper account balance query
        // This would use system.account storage query
        let _account_info: serde_json::Value = client
            .request("system_account", rpc_params![account])
            .await?;

        Ok(500_000_000_000_000)  // Placeholder: 500k tokens
    }

    /// Submit signed transaction
    pub async fn submit_transaction(&self, signed_tx: Vec<u8>) -> Result<H256> {
        let client = self.client.read().await;
        let client = client.as_ref().ok_or_else(|| anyhow::anyhow!("Not connected"))?;

        let tx_hex = format!("0x{}", hex::encode(&signed_tx));
        let hash: H256 = client
            .request("author_submitExtrinsic", rpc_params![tx_hex])
            .await?;

        tracing::info!("Transaction submitted: {:?}", hash);
        Ok(hash)
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RuntimeVersion {
    pub spec_name: String,
    pub impl_name: String,
    pub authoring_version: u32,
    pub spec_version: u32,
    pub impl_version: u32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BlockHeader {
    #[serde(deserialize_with = "deserialize_number")]
    pub number: u64,
    pub parent_hash: H256,
    pub state_root: H256,
    pub extrinsics_root: H256,
}

fn deserialize_number<'de, D>(deserializer: D) -> Result<u64, D::Error>
where
    D: serde::Deserializer<'de>,
{
    let s: String = Deserialize::deserialize(deserializer)?;
    let s = s.trim_start_matches("0x");
    u64::from_str_radix(s, 16).map_err(serde::de::Error::custom)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    #[ignore]  // Requires running node
    async fn test_connect() {
        let client = RpcClient::new("ws://127.0.0.1:9944");
        client.connect().await.unwrap();
        assert!(client.is_connected().await);
    }

    #[tokio::test]
    #[ignore]  // Requires running node
    async fn test_runtime_version() {
        let client = RpcClient::new("ws://127.0.0.1:9944");
        client.connect().await.unwrap();

        let version = client.runtime_version().await.unwrap();
        assert_eq!(version.spec_name, "quantumharmony");
    }
}
