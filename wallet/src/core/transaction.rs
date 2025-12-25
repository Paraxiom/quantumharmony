//! Transaction building and signing

use anyhow::Result;

/// Transaction builder
pub struct TransactionBuilder {
    // TODO: Implement transaction construction
}

impl TransactionBuilder {
    pub fn new() -> Self {
        Self {}
    }

    /// Build transfer transaction
    pub fn transfer(
        &self,
        _from: &str,
        _to: &str,
        _amount: u128,
    ) -> Result<Vec<u8>> {
        // TODO: Implement proper transaction encoding
        // This would use SCALE codec to encode Call::Balances::transfer
        anyhow::bail!("Transaction building not yet implemented");
    }

    /// Build sudo set_code transaction (runtime upgrade)
    pub fn sudo_set_code(
        &self,
        _new_wasm: Vec<u8>,
    ) -> Result<Vec<u8>> {
        // TODO: Implement sudo::set_code call encoding
        anyhow::bail!("Sudo transaction building not yet implemented");
    }
}

impl Default for TransactionBuilder {
    fn default() -> Self {
        Self::new()
    }
}
