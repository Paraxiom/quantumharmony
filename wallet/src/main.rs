//! QuantumHarmony Self-Documenting Wallet
//!
//! This wallet is not just a transaction tool—it's an interactive architecture diagram.
//! Users can explore the blockchain's 5-layer spiral architecture, view real-time
//! metrics, and perform runtime upgrades with full transparency.
//!
//! ## Features
//! - 3D spiral visualization of blockchain layers
//! - Interactive documentation (click layers to learn)
//! - Runtime upgrade diff viewer
//! - SPHINCS+ post-quantum signatures
//! - Real-time consensus monitoring

use anyhow::Result;
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

mod core;

#[cfg(feature = "gui")]
mod gui;

#[cfg(feature = "tui")]
mod tui;

#[derive(Debug, Clone)]
pub struct WalletConfig {
    /// RPC endpoint for blockchain node
    pub rpc_url: String,

    /// Path to keystore directory
    pub keystore_path: String,

    /// Display mode (gui or tui)
    pub mode: DisplayMode,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DisplayMode {
    /// 3D graphical interface
    Gui,

    /// Terminal user interface
    Tui,
}

impl Default for WalletConfig {
    fn default() -> Self {
        Self {
            rpc_url: "ws://127.0.0.1:9944".to_string(),
            keystore_path: dirs::home_dir()
                .unwrap_or_else(|| std::path::PathBuf::from("."))
                .join(".quantumharmony")
                .join("keystore")
                .to_string_lossy()
                .to_string(),
            #[cfg(feature = "gui")]
            mode: DisplayMode::Gui,
            #[cfg(not(feature = "gui"))]
            mode: DisplayMode::Tui,
        }
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    // Initialize tracing
    tracing_subscriber::registry()
        .with(
            tracing_subscriber::EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| "info,quantumharmony_wallet=debug".into()),
        )
        .with(tracing_subscriber::fmt::layer())
        .init();

    tracing::info!("🚀 QuantumHarmony Self-Documenting Wallet starting...");

    // Parse command-line arguments
    let config = parse_args()?;

    tracing::info!("📡 Connecting to node at {}", config.rpc_url);
    tracing::info!("🔑 Keystore path: {}", config.keystore_path);

    // Launch appropriate UI mode
    match config.mode {
        DisplayMode::Tui => {
            #[cfg(feature = "tui")]
            {
                tracing::info!("📺 Starting Terminal UI mode...");
                tui::run(config).await
            }
            #[cfg(not(feature = "tui"))]
            {
                anyhow::bail!("TUI feature not enabled. Rebuild with --features tui");
            }
        }
        DisplayMode::Gui => {
            #[cfg(feature = "gui")]
            {
                tracing::info!("🎨 Starting 3D GUI mode...");
                gui::run(config).await
            }
            #[cfg(not(feature = "gui"))]
            {
                anyhow::bail!("GUI feature not enabled. GUI mode not yet implemented.");
            }
        }
    }
}

fn parse_args() -> Result<WalletConfig> {
    let mut config = WalletConfig::default();
    let args: Vec<String> = std::env::args().collect();

    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--rpc" | "-r" => {
                i += 1;
                if i >= args.len() {
                    anyhow::bail!("--rpc requires a URL argument");
                }
                config.rpc_url = args[i].clone();
            }
            "--keystore" | "-k" => {
                i += 1;
                if i >= args.len() {
                    anyhow::bail!("--keystore requires a path argument");
                }
                config.keystore_path = args[i].clone();
            }
            #[cfg(feature = "gui")]
            "--gui" => {
                config.mode = DisplayMode::Gui;
            }
            #[cfg(feature = "tui")]
            "--tui" => {
                config.mode = DisplayMode::Tui;
            }
            "--help" | "-h" => {
                print_help();
                std::process::exit(0);
            }
            arg => {
                anyhow::bail!("Unknown argument: {}", arg);
            }
        }
        i += 1;
    }

    Ok(config)
}

fn print_help() {
    println!(
        r#"QuantumHarmony Self-Documenting Wallet

USAGE:
    qh-wallet [OPTIONS]

OPTIONS:
    -r, --rpc <URL>           RPC endpoint (default: ws://127.0.0.1:9944)
    -k, --keystore <PATH>     Keystore directory (default: ~/.quantumharmony/keystore)
    --tui                     Use terminal UI mode
    --gui                     Use 3D graphical mode (if compiled with 'gui' feature)
    -h, --help                Print help information

FEATURES:
    • Interactive 3D spiral visualization of blockchain architecture
    • Click layers to view embedded documentation
    • Real-time consensus and network metrics
    • Runtime upgrade diff viewer with sudo approval
    • SPHINCS+ post-quantum signature support

EXAMPLES:
    # Connect to local node with TUI
    qh-wallet --tui

    # Connect to remote node
    qh-wallet --rpc ws://validator1.example.com:9944

    # Use 3D GUI mode (requires 'gui' feature)
    qh-wallet --gui
"#
    );
}
