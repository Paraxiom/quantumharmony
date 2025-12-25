//! TUI wallet modules for QuantumHarmony self-documenting wallet

pub mod architecture_spiral;

// Use WalletConfig from parent module
use crate::WalletConfig;

/// Launch the TUI wallet
pub async fn run(config: WalletConfig) -> anyhow::Result<()> {
    // For now, directly launch the architecture spiral visualization
    // TODO: Add wallet selector and other TUI features
    Ok(())
}