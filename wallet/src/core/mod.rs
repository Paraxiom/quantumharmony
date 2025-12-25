//! Core wallet functionality (RPC, keystore, transactions)

pub mod rpc_client;
pub mod keystore;
pub mod transaction;
pub mod balance;
pub mod upgrade;

pub use rpc_client::RpcClient;
pub use keystore::Keystore;
pub use transaction::TransactionBuilder;
pub use balance::BalanceQuery;
pub use upgrade::UpgradeMonitor;

/// Blockchain layer in the 5-layer spiral architecture
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Layer {
    /// Layer 0: Quantum entropy foundation (QKD devices, HSM, priority queues)
    Entropy = 0,

    /// Layer 1: Consensus & toroidal mesh (Aura, GRANDPA, Coherence)
    Consensus = 1,

    /// Layer 2: Network transport (QUIC, libp2p, vote gossip)
    Network = 2,

    /// Layer 3: Key management (Triple Ratchet, SPQDR, VRF)
    KeyManagement = 3,

    /// Layer 4: Cryptographic signatures (SPHINCS+, Falcon1024, Lamport)
    Signatures = 4,

    /// Layer 5: Application & RPC (QSBR, ternary encoding, quaternary checksums)
    Application = 5,
}

impl Layer {
    /// Get all layers in order
    pub fn all() -> &'static [Layer] {
        &[
            Layer::Entropy,
            Layer::Consensus,
            Layer::Network,
            Layer::KeyManagement,
            Layer::Signatures,
            Layer::Application,
        ]
    }

    /// Get layer name
    pub fn name(&self) -> &'static str {
        match self {
            Layer::Entropy => "Entropy Foundation",
            Layer::Consensus => "Consensus & Toroidal Mesh",
            Layer::Network => "Network Transport",
            Layer::KeyManagement => "Key Management",
            Layer::Signatures => "Cryptographic Signatures",
            Layer::Application => "Application & RPC",
        }
    }

    /// Get layer description (one-liner)
    pub fn description(&self) -> &'static str {
        match self {
            Layer::Entropy => "Quantum entropy from QKD devices, HSM storage, priority queues",
            Layer::Consensus => "Byzantine consensus with toroidal mesh parallelization",
            Layer::Network => "QUIC encrypted transport with P2P gossip protocols",
            Layer::KeyManagement => "Triple Ratchet forward secrecy and VRF shard assignment",
            Layer::Signatures => "Post-quantum SPHINCS+ and Falcon1024 signatures",
            Layer::Application => "QSBR RPC interface with ternary coordinate encoding",
        }
    }

    /// Get documentation file path
    pub fn docs_path(&self) -> &'static str {
        match self {
            Layer::Entropy => "layer_0_entropy.md",
            Layer::Consensus => "layer_1_consensus.md",
            Layer::Network => "layer_2_network.md",
            Layer::KeyManagement => "layer_3_keys.md",
            Layer::Signatures => "layer_4_signatures.md",
            Layer::Application => "layer_5_application.md",
        }
    }

    /// Get layer color (for visualization)
    pub fn color_rgb(&self) -> (u8, u8, u8) {
        match self {
            Layer::Entropy => (138, 43, 226),       // Purple (quantum physics)
            Layer::Consensus => (65, 105, 225),     // Blue (stability)
            Layer::Network => (50, 205, 50),        // Green (connectivity)
            Layer::KeyManagement => (255, 215, 0),  // Gold (security)
            Layer::Signatures => (255, 140, 0),     // Orange (cryptography)
            Layer::Application => (220, 20, 60),    // Red (user-facing)
        }
    }

    /// Get 3D spiral position for this layer
    pub fn spiral_position(&self) -> (f32, f32, f32) {
        use std::f32::consts::PI;

        let z = *self as u8 as f32 * 2.0;  // Vertical spacing
        let angle = (*self as u8 as f32) * (2.0 * PI / 5.0);  // Pentagon distribution
        let radius = 3.0 + (z * 0.3);  // Spiral outward as we ascend

        (
            radius * angle.cos(),  // X
            z,                     // Y (vertical)
            radius * angle.sin(),  // Z
        )
    }

    /// Get layer components (key technologies/modules)
    pub fn components(&self) -> Vec<&'static str> {
        match self {
            Layer::Entropy => vec!["QKD Devices", "HSM", "Priority Queues", "Shamir Secret Sharing"],
            Layer::Consensus => vec!["Aura", "GRANDPA", "Coherence Gadget", "Toroidal Mesh"],
            Layer::Network => vec!["QUIC Transport", "libp2p", "Vote Gossip", "P2P Discovery"],
            Layer::KeyManagement => vec!["Triple Ratchet", "SPQDR", "VRF", "Session Keys"],
            Layer::Signatures => vec!["SPHINCS+", "Falcon1024", "Lamport Chains", "Hybrid Mode"],
            Layer::Application => vec!["QSBR RPC", "Ternary Encoding", "Quaternary Checksums", "Streaming"],
        }
    }

    /// Get layer security features description
    pub fn security_features(&self) -> &'static str {
        match self {
            Layer::Entropy => "Information-theoretic security via QKD, QBER <5% threshold",
            Layer::Consensus => "Byzantine fault tolerance (68% threshold), finality guarantees",
            Layer::Network => "TLS 1.3 encryption, authenticated peers, rate limiting",
            Layer::KeyManagement => "Forward secrecy, per-message key rotation, VRF unpredictability",
            Layer::Signatures => "Post-quantum (NIST Level 5), 2^256 security, stateless",
            Layer::Application => "Batch RPC validation, checksum verification, DoS protection",
        }
    }
}

/// Runtime upgrade information
#[derive(Debug, Clone)]
pub struct RuntimeUpgrade {
    pub from_version: u32,
    pub to_version: u32,
    pub spec_name: String,
    pub wasm_hash: [u8; 32],
    pub affected_layers: Vec<Layer>,
}

/// Network status information
#[derive(Debug, Clone)]
pub struct NetworkStatus {
    pub connected_peers: usize,
    pub best_block: u64,
    pub finalized_block: u64,
    pub is_syncing: bool,
    pub average_latency_ms: u32,
}

/// Consensus status information
#[derive(Debug, Clone)]
pub struct ConsensusStatus {
    pub validator_count: usize,
    pub online_validators: usize,
    pub current_epoch: u64,
    pub finality_lag: u64,
}
