// FRONTIER REMOVED: governance-only node
// use crate::service::EthConfiguration;

/// Available Sealing methods.
#[derive(Copy, Clone, Debug, Default, clap::ValueEnum)]
pub enum Sealing {
    /// Seal using rpc method.
    #[default]
    Manual,
    /// Seal when transaction is executed.
    Instant,
}

#[derive(Debug, clap::Parser)]
pub struct Cli {
    #[command(subcommand)]
    pub subcommand: Option<Subcommand>,

    #[allow(missing_docs)]
    #[command(flatten)]
    pub run: sc_cli::RunCmd,

    /// Choose sealing method.
    #[arg(long, value_enum, ignore_case = true)]
    pub sealing: Option<Sealing>,

    /// PQTG endpoint for quantum device entropy collection
    #[arg(long, default_value = "https://localhost:8443")]
    pub pqtg_endpoint: String,

    /// QKD hardware usage mode: disabled, optional (default), or required
    #[arg(long, default_value = "optional")]
    pub qkd_mode: String,

    /// Specific PQTG devices to use (comma-separated, e.g., "toshiba-qkd,crypto4a")
    /// If not specified, devices will be auto-discovered from PQTG
    #[arg(long)]
    pub pqtg_devices: Option<String>,

    /// Threshold K for Shamir secret sharing (minimum devices needed)
    #[arg(long, default_value = "2")]
    pub pqtg_threshold_k: usize,

    /// P2P identity source for post-quantum secure networking.
    /// - "qkd": Use QKD hardware for key material (Tier 1, requires hardware)
    /// - "falcon" or "pqc": Use Falcon-1024 software keys (Tier 3)
    /// - "hybrid": Use QKD when available, fall back to Falcon (Tier 1/3)
    /// - "auto" (default): Auto-detect best available source
    #[arg(long, default_value = "auto")]
    pub identity_source: String,

    /// Path to Falcon identity key file (optional, will be auto-generated if not specified)
    #[arg(long)]
    pub falcon_key_file: Option<String>,

    /// QKD SAE (Secure Application Entity) ID for this node
    #[arg(long)]
    pub qkd_sae_id: Option<String>,

    // FRONTIER REMOVED: governance-only node
    // #[command(flatten)]
    // pub eth: EthConfiguration,
}

#[derive(Debug, clap::Subcommand)]
pub enum Subcommand {
    /// Key management cli utilities
    #[command(subcommand)]
    Key(sc_cli::KeySubcommand),

    /// Build a chain specification.
    BuildSpec(sc_cli::BuildSpecCmd),

    /// Validate blocks.
    CheckBlock(sc_cli::CheckBlockCmd),

    /// Export blocks.
    ExportBlocks(sc_cli::ExportBlocksCmd),

    /// Export the state of a given block into a chain spec.
    ExportState(sc_cli::ExportStateCmd),

    /// Import blocks.
    ImportBlocks(sc_cli::ImportBlocksCmd),

    /// Remove the whole chain.
    PurgeChain(sc_cli::PurgeChainCmd),

    /// Revert the chain to a previous state.
    Revert(sc_cli::RevertCmd),

    /// SPHINCS+ key management (post-quantum keypair generation)
    SphincsKey(crate::sphincs_keygen::SphincsKeyCmd),

    /// Sub-commands concerned with benchmarking.
    #[cfg(feature = "runtime-benchmarks")]
    #[command(subcommand)]
    Benchmark(frame_benchmarking_cli::BenchmarkCmd),

    /// Sub-commands concerned with benchmarking.
    #[cfg(not(feature = "runtime-benchmarks"))]
    Benchmark,

    // FRONTIER REMOVED: governance-only node
    // /// Db meta columns information.
    // FrontierDb(fc_cli::FrontierDbCmd),
}
