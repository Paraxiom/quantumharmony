//! Runtime upgrade monitoring

use anyhow::Result;
use super::{RpcClient, RuntimeUpgrade};

/// Runtime upgrade monitor
pub struct UpgradeMonitor {
    client: RpcClient,
}

impl UpgradeMonitor {
    pub fn new(client: RpcClient) -> Self {
        Self { client }
    }

    /// Check for pending runtime upgrade
    pub async fn check_pending(&self) -> Result<Option<RuntimeUpgrade>> {
        self.client.check_pending_upgrade().await
    }

    /// Monitor upgrade execution (polls until version changes)
    pub async fn monitor_execution(
        &self,
        target_version: u32,
    ) -> Result<()> {
        use tokio::time::{sleep, Duration};

        loop {
            let current = self.client.runtime_version().await?;

            if current.spec_version == target_version {
                tracing::info!("✅ Runtime upgrade completed: v{}", target_version);
                return Ok(());
            }

            tracing::debug!(
                "Waiting for upgrade: current v{}, target v{}",
                current.spec_version,
                target_version
            );

            sleep(Duration::from_secs(6)).await;  // Poll every block
        }
    }
}
