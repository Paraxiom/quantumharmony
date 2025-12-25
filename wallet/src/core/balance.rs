//! Balance queries

use anyhow::Result;
use super::RpcClient;

/// Balance query helper
pub struct BalanceQuery {
    client: RpcClient,
}

impl BalanceQuery {
    pub fn new(client: RpcClient) -> Self {
        Self { client }
    }

    /// Get account balance
    pub async fn get(&self, account: &str) -> Result<u128> {
        self.client.get_balance(account).await
    }

    /// Format balance for display (with decimal point)
    pub fn format(balance: u128) -> String {
        // Assuming 12 decimal places (like DOT)
        let decimals = 12;
        let divisor = 10u128.pow(decimals);
        let whole = balance / divisor;
        let fract = balance % divisor;

        format!("{}.{:0width$}", whole, fract, width = decimals as usize)
    }
}
