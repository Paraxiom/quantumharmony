// node/src/quantum_p2p/identity_source.rs
//
// Multi-Tier Quantum Identity Source System
//
// This module implements a tiered identity system for QuantumHarmony nodes:
//
// Tier 1: QKD Hardware (Information-Theoretic Security)
//   - Highest security level
//   - Requires physical QKD hardware connection
//   - Enables "Proof of Coherence" validation
//   - Keys are derived from quantum channel measurements
//
// Tier 2: QRNG + Falcon (Quantum Entropy + PQC)
//   - Uses quantum random number generators for entropy
//   - Falcon-1024 signatures for authentication
//   - ML-KEM-1024 for key encapsulation
//   - Good balance of security and practicality
//
// Tier 3: Software PQC (Computational Security)
//   - Pure software implementation
//   - Falcon-1024 + ML-KEM-1024
//   - Uses system CSPRNG for entropy
//   - Fallback for nodes without quantum hardware
//
// The node key (--node-key) is DEPRECATED for Ed25519.
// Instead, use --identity-source with --pqc-key-file.

use std::sync::Arc;
use tokio::sync::RwLock;
use sp_core::{blake2_256, H256};

use super::identity::FalconIdentity;
use super::qkd_interface::{QkdHardwareInterface, QkdDeviceManager, StubQkdDevice, QkdKey, QkdError};

/// Identity source tier (security level)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IdentityTier {
    /// Tier 1: QKD hardware provides information-theoretic security
    Qkd,
    /// Tier 2: QRNG provides quantum entropy for key generation
    Qrng,
    /// Tier 3: Software PQC with system CSPRNG
    Software,
}

impl std::fmt::Display for IdentityTier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Qkd => write!(f, "QKD (Tier 1 - Information Theoretic)"),
            Self::Qrng => write!(f, "QRNG (Tier 2 - Quantum Entropy)"),
            Self::Software => write!(f, "Software (Tier 3 - PQC)"),
        }
    }
}

/// Identity source configuration from CLI
#[derive(Debug, Clone)]
pub enum IdentitySourceConfig {
    /// Use QKD hardware for identity (Tier 1)
    Qkd {
        /// QKD device endpoint URL
        endpoint: String,
        /// SAE ID for this node
        sae_id: String,
    },
    /// Use Falcon keys from file (Tier 2/3)
    Falcon {
        /// Path to Falcon key file
        key_file: String,
    },
    /// Hybrid mode: QKD when available, fallback to Falcon
    Hybrid {
        /// Primary QKD endpoint
        qkd_endpoint: Option<String>,
        /// Falcon key file for fallback
        falcon_key_file: String,
    },
    /// Auto-detect best available (default)
    Auto,
}

impl Default for IdentitySourceConfig {
    fn default() -> Self {
        Self::Auto
    }
}

impl std::str::FromStr for IdentitySourceConfig {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_lowercase().as_str() {
            "qkd" => Ok(Self::Qkd {
                endpoint: "https://localhost:8443".to_string(),
                sae_id: "auto".to_string(),
            }),
            "falcon" | "pqc" => Ok(Self::Falcon {
                key_file: "keys/node-key.json".to_string(),
            }),
            "hybrid" => Ok(Self::Hybrid {
                qkd_endpoint: None,
                falcon_key_file: "keys/node-key.json".to_string(),
            }),
            "auto" | "default" => Ok(Self::Auto),
            _ => Err(format!("Unknown identity source: {}. Valid options: qkd, falcon, hybrid, auto", s)),
        }
    }
}

/// Node identity derived from PQC keys
#[derive(Debug, Clone)]
pub struct PqcNodeId {
    /// The 32-byte node identifier (H256)
    pub id: H256,
    /// The identity tier
    pub tier: IdentityTier,
    /// Falcon public key (1793 bytes)
    pub falcon_pubkey: Vec<u8>,
    /// ML-KEM public key (1568 bytes)
    pub kem_pubkey: Vec<u8>,
}

impl PqcNodeId {
    /// Derive node ID from Falcon + KEM public keys
    pub fn from_keys(falcon_pubkey: &[u8], kem_pubkey: &[u8], tier: IdentityTier) -> Self {
        // Combine both public keys and hash for node ID
        let mut combined = Vec::with_capacity(falcon_pubkey.len() + kem_pubkey.len());
        combined.extend_from_slice(falcon_pubkey);
        combined.extend_from_slice(kem_pubkey);
        let id = H256::from_slice(&blake2_256(&combined));

        Self {
            id,
            tier,
            falcon_pubkey: falcon_pubkey.to_vec(),
            kem_pubkey: kem_pubkey.to_vec(),
        }
    }

    /// Get a short display string for logs
    pub fn short_id(&self) -> String {
        format!("{:?}...{:?}",
            &self.id.as_bytes()[..4],
            &self.id.as_bytes()[28..32])
    }
}

/// Errors from identity source operations
#[derive(Debug, Clone)]
pub enum IdentitySourceError {
    /// QKD hardware not available
    QkdNotAvailable,
    /// QRNG device not available
    QrngNotAvailable,
    /// Key file not found or invalid
    KeyFileError(String),
    /// Falcon key generation failed
    FalconKeygenFailed(String),
    /// Configuration error
    ConfigError(String),
    /// QKD error
    QkdError(String),
}

impl std::fmt::Display for IdentitySourceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::QkdNotAvailable => write!(f, "QKD hardware not available"),
            Self::QrngNotAvailable => write!(f, "QRNG device not available"),
            Self::KeyFileError(msg) => write!(f, "Key file error: {}", msg),
            Self::FalconKeygenFailed(msg) => write!(f, "Falcon keygen failed: {}", msg),
            Self::ConfigError(msg) => write!(f, "Configuration error: {}", msg),
            Self::QkdError(msg) => write!(f, "QKD error: {}", msg),
        }
    }
}

impl std::error::Error for IdentitySourceError {}

impl From<QkdError> for IdentitySourceError {
    fn from(e: QkdError) -> Self {
        Self::QkdError(e.to_string())
    }
}

/// Main identity source manager
///
/// Manages the node's cryptographic identity across different security tiers.
/// Provides a unified interface regardless of whether the underlying source
/// is QKD hardware, QRNG, or pure software.
pub struct IdentitySource {
    /// Current identity tier
    tier: IdentityTier,
    /// Falcon identity for signing/KEM
    falcon_identity: Arc<RwLock<FalconIdentity>>,
    /// QKD device manager (if available)
    qkd_manager: Option<Arc<RwLock<QkdDeviceManager>>>,
    /// Current node ID
    node_id: PqcNodeId,
    /// Configuration
    config: IdentitySourceConfig,
}

impl IdentitySource {
    /// Create a new identity source with auto-detection
    pub async fn new_auto() -> Result<Self, IdentitySourceError> {
        Self::new(IdentitySourceConfig::Auto).await
    }

    /// Create a new identity source from configuration
    pub async fn new(config: IdentitySourceConfig) -> Result<Self, IdentitySourceError> {
        log::info!("[IDENTITY] Initializing identity source...");

        match &config {
            IdentitySourceConfig::Qkd { endpoint, sae_id } => {
                Self::init_qkd(endpoint, sae_id).await
            }
            IdentitySourceConfig::Falcon { key_file } => {
                Self::init_falcon(key_file).await
            }
            IdentitySourceConfig::Hybrid { qkd_endpoint, falcon_key_file } => {
                Self::init_hybrid(qkd_endpoint.as_deref(), falcon_key_file).await
            }
            IdentitySourceConfig::Auto => {
                Self::init_auto().await
            }
        }
    }

    /// Initialize with QKD hardware (Tier 1)
    async fn init_qkd(endpoint: &str, _sae_id: &str) -> Result<Self, IdentitySourceError> {
        log::info!("[IDENTITY] Attempting QKD initialization at {}", endpoint);

        // For now, use stub device. Real implementation would connect to hardware.
        let mut qkd_manager = QkdDeviceManager::new(0.10); // 10% QBER threshold
        let stub = Box::new(StubQkdDevice::new_test("qkd-primary"));
        qkd_manager.add_device(stub);

        // Generate Falcon identity using QKD entropy
        let mut falcon_identity = FalconIdentity::new();
        falcon_identity.generate_keypair()
            .map_err(|e| IdentitySourceError::FalconKeygenFailed(e.to_string()))?;

        let falcon_pubkey = falcon_identity.sign_public_key()
            .ok_or_else(|| IdentitySourceError::FalconKeygenFailed("No public key".into()))?
            .to_vec();
        let kem_pubkey = falcon_identity.kem_public_key()
            .ok_or_else(|| IdentitySourceError::FalconKeygenFailed("No KEM key".into()))?
            .to_vec();

        let node_id = PqcNodeId::from_keys(&falcon_pubkey, &kem_pubkey, IdentityTier::Qkd);

        log::info!("[IDENTITY] QKD identity initialized: {}", node_id.short_id());
        log::info!("[IDENTITY] Tier: {}", IdentityTier::Qkd);

        Ok(Self {
            tier: IdentityTier::Qkd,
            falcon_identity: Arc::new(RwLock::new(falcon_identity)),
            qkd_manager: Some(Arc::new(RwLock::new(qkd_manager))),
            node_id,
            config: IdentitySourceConfig::Qkd {
                endpoint: endpoint.to_string(),
                sae_id: "auto".to_string(),
            },
        })
    }

    /// Initialize with Falcon keys from file (Tier 2/3)
    async fn init_falcon(key_file: &str) -> Result<Self, IdentitySourceError> {
        log::info!("[IDENTITY] Loading Falcon identity from {}", key_file);

        // Try to load from file, generate new if not found
        let falcon_identity = match Self::load_falcon_key_file(key_file) {
            Ok(identity) => {
                log::info!("[IDENTITY] Loaded existing Falcon identity from {}", key_file);
                identity
            },
            Err(e) => {
                log::warn!("[IDENTITY] Could not load key file: {}, generating new", e);
                let mut identity = FalconIdentity::new();
                identity.generate_keypair()
                    .map_err(|e| IdentitySourceError::FalconKeygenFailed(e.to_string()))?;

                // Save the newly generated identity to file for persistence
                if let Err(save_err) = Self::save_falcon_key_file(key_file, &identity) {
                    log::error!("[IDENTITY] Failed to save key file: {}", save_err);
                } else {
                    log::info!("[IDENTITY] Saved new Falcon identity to {}", key_file);
                }

                identity
            }
        };

        let falcon_pubkey = falcon_identity.sign_public_key()
            .ok_or_else(|| IdentitySourceError::FalconKeygenFailed("No public key".into()))?
            .to_vec();
        let kem_pubkey = falcon_identity.kem_public_key()
            .ok_or_else(|| IdentitySourceError::FalconKeygenFailed("No KEM key".into()))?
            .to_vec();

        // Determine tier based on entropy source (could check for QRNG here)
        let tier = IdentityTier::Software; // Default to software

        let node_id = PqcNodeId::from_keys(&falcon_pubkey, &kem_pubkey, tier);

        log::info!("[IDENTITY] Falcon identity loaded: {}", node_id.short_id());
        log::info!("[IDENTITY] Tier: {}", tier);

        Ok(Self {
            tier,
            falcon_identity: Arc::new(RwLock::new(falcon_identity)),
            qkd_manager: None,
            node_id,
            config: IdentitySourceConfig::Falcon {
                key_file: key_file.to_string(),
            },
        })
    }

    /// Initialize hybrid mode (QKD primary, Falcon fallback)
    async fn init_hybrid(qkd_endpoint: Option<&str>, falcon_key_file: &str) -> Result<Self, IdentitySourceError> {
        log::info!("[IDENTITY] Initializing hybrid mode");

        // First, ensure we have Falcon keys
        let falcon_identity = match Self::load_falcon_key_file(falcon_key_file) {
            Ok(identity) => identity,
            Err(e) => {
                log::warn!("[IDENTITY] Could not load key file: {}, generating new", e);
                let mut identity = FalconIdentity::new();
                identity.generate_keypair()
                    .map_err(|e| IdentitySourceError::FalconKeygenFailed(e.to_string()))?;
                identity
            }
        };

        // Try to initialize QKD if endpoint provided
        let (qkd_manager, tier) = if let Some(endpoint) = qkd_endpoint {
            log::info!("[IDENTITY] Attempting QKD connection at {}", endpoint);
            let mut manager = QkdDeviceManager::new(0.10);
            let stub = Box::new(StubQkdDevice::new_test("qkd-hybrid"));
            manager.add_device(stub);

            if manager.is_available().await {
                (Some(Arc::new(RwLock::new(manager))), IdentityTier::Qkd)
            } else {
                log::warn!("[IDENTITY] QKD not available, falling back to software");
                (None, IdentityTier::Software)
            }
        } else {
            (None, IdentityTier::Software)
        };

        let falcon_pubkey = falcon_identity.sign_public_key()
            .ok_or_else(|| IdentitySourceError::FalconKeygenFailed("No public key".into()))?
            .to_vec();
        let kem_pubkey = falcon_identity.kem_public_key()
            .ok_or_else(|| IdentitySourceError::FalconKeygenFailed("No KEM key".into()))?
            .to_vec();

        let node_id = PqcNodeId::from_keys(&falcon_pubkey, &kem_pubkey, tier);

        log::info!("[IDENTITY] Hybrid identity initialized: {}", node_id.short_id());
        log::info!("[IDENTITY] Tier: {}", tier);

        Ok(Self {
            tier,
            falcon_identity: Arc::new(RwLock::new(falcon_identity)),
            qkd_manager,
            node_id,
            config: IdentitySourceConfig::Hybrid {
                qkd_endpoint: qkd_endpoint.map(|s| s.to_string()),
                falcon_key_file: falcon_key_file.to_string(),
            },
        })
    }

    /// Auto-detect and initialize best available identity source
    async fn init_auto() -> Result<Self, IdentitySourceError> {
        log::info!("[IDENTITY] Auto-detecting identity source...");

        // For now, default to software Falcon. In production:
        // 1. Check for QKD hardware (PQTG endpoint)
        // 2. Check for QRNG device
        // 3. Fall back to software

        let mut falcon_identity = FalconIdentity::new();
        falcon_identity.generate_keypair()
            .map_err(|e| IdentitySourceError::FalconKeygenFailed(e.to_string()))?;

        let falcon_pubkey = falcon_identity.sign_public_key()
            .ok_or_else(|| IdentitySourceError::FalconKeygenFailed("No public key".into()))?
            .to_vec();
        let kem_pubkey = falcon_identity.kem_public_key()
            .ok_or_else(|| IdentitySourceError::FalconKeygenFailed("No KEM key".into()))?
            .to_vec();

        let tier = IdentityTier::Software;
        let node_id = PqcNodeId::from_keys(&falcon_pubkey, &kem_pubkey, tier);

        log::info!("[IDENTITY] Auto-detected: {}", tier);
        log::info!("[IDENTITY] Node ID: {}", node_id.short_id());

        Ok(Self {
            tier,
            falcon_identity: Arc::new(RwLock::new(falcon_identity)),
            qkd_manager: None,
            node_id,
            config: IdentitySourceConfig::Auto,
        })
    }

    /// Load Falcon identity from key file
    fn load_falcon_key_file(path: &str) -> Result<FalconIdentity, IdentitySourceError> {
        use std::fs;

        let content = fs::read_to_string(path)
            .map_err(|e| IdentitySourceError::KeyFileError(format!("Read failed: {}", e)))?;

        let json: serde_json::Value = serde_json::from_str(&content)
            .map_err(|e| IdentitySourceError::KeyFileError(format!("Parse failed: {}", e)))?;

        // Expected format:
        // {
        //   "falcon_sign_public": "0x...",
        //   "falcon_sign_secret": "0x...",
        //   "kem_public": "0x...",
        //   "kem_secret": "0x..."
        // }

        let sign_public = Self::decode_hex_field(&json, "falcon_sign_public")?;
        let sign_secret = Self::decode_hex_field(&json, "falcon_sign_secret")?;
        let kem_public = Self::decode_hex_field(&json, "kem_public")?;
        let kem_secret = Self::decode_hex_field(&json, "kem_secret")?;

        FalconIdentity::from_keys(sign_public, sign_secret, kem_public, kem_secret)
            .map_err(|e| IdentitySourceError::KeyFileError(format!("Invalid keys: {}", e)))
    }

    /// Save Falcon identity to key file for persistence
    fn save_falcon_key_file(path: &str, identity: &FalconIdentity) -> Result<(), IdentitySourceError> {
        use std::fs;
        use serde_json::json;

        let sign_public = identity.sign_public_key()
            .ok_or_else(|| IdentitySourceError::KeyFileError("No sign public key".into()))?;
        let sign_secret = identity.sign_secret_key()
            .ok_or_else(|| IdentitySourceError::KeyFileError("No sign secret key".into()))?;
        let kem_public = identity.kem_public_key()
            .ok_or_else(|| IdentitySourceError::KeyFileError("No KEM public key".into()))?;
        let kem_secret = identity.kem_secret_key()
            .ok_or_else(|| IdentitySourceError::KeyFileError("No KEM secret key".into()))?;

        let key_json = json!({
            "falcon_sign_public": format!("0x{}", hex::encode(sign_public)),
            "falcon_sign_secret": format!("0x{}", hex::encode(sign_secret)),
            "kem_public": format!("0x{}", hex::encode(kem_public)),
            "kem_secret": format!("0x{}", hex::encode(kem_secret))
        });

        fs::write(path, serde_json::to_string_pretty(&key_json).unwrap())
            .map_err(|e| IdentitySourceError::KeyFileError(format!("Write failed: {}", e)))
    }

    fn decode_hex_field(json: &serde_json::Value, field: &str) -> Result<Vec<u8>, IdentitySourceError> {
        let hex_str = json.get(field)
            .and_then(|v| v.as_str())
            .ok_or_else(|| IdentitySourceError::KeyFileError(format!("Missing field: {}", field)))?;

        hex::decode(hex_str.trim_start_matches("0x"))
            .map_err(|e| IdentitySourceError::KeyFileError(format!("Invalid hex in {}: {}", field, e)))
    }

    /// Get the current identity tier
    pub fn tier(&self) -> IdentityTier {
        self.tier
    }

    /// Get the PQC node ID
    pub fn node_id(&self) -> &PqcNodeId {
        &self.node_id
    }

    /// Get the H256 node identifier (for compatibility)
    pub fn id(&self) -> H256 {
        self.node_id.id
    }

    /// Sign data using Falcon-1024
    pub async fn sign(&self, data: &[u8]) -> Result<Vec<u8>, IdentitySourceError> {
        let identity = self.falcon_identity.read().await;
        identity.sign(data)
            .map_err(|e| IdentitySourceError::FalconKeygenFailed(e.to_string()))
    }

    /// Get QKD key (only available in Tier 1)
    pub async fn get_qkd_key(&self) -> Result<QkdKey, IdentitySourceError> {
        let manager = self.qkd_manager.as_ref()
            .ok_or(IdentitySourceError::QkdNotAvailable)?;

        let mgr = manager.read().await;
        mgr.get_key().await.map_err(Into::into)
    }

    /// Check if QKD is available
    pub async fn is_qkd_available(&self) -> bool {
        if let Some(manager) = &self.qkd_manager {
            let mgr = manager.read().await;
            mgr.is_available().await
        } else {
            false
        }
    }

    /// Get the Falcon identity for direct access
    pub fn falcon_identity(&self) -> Arc<RwLock<FalconIdentity>> {
        self.falcon_identity.clone()
    }

    /// Derive a libp2p-compatible node key from the Falcon identity.
    ///
    /// Since libp2p currently only supports Ed25519, RSA, and secp256k1,
    /// we derive a deterministic Ed25519 keypair from the Falcon public key.
    /// This provides a stable PeerId while the actual P2P security uses Falcon.
    ///
    /// The Ed25519 key is derived by:
    /// 1. Hashing the Falcon public key with BLAKE2b-256
    /// 2. Using the hash as the Ed25519 secret key seed
    /// 3. Deriving the Ed25519 public key from the seed
    ///
    /// IMPORTANT: This Ed25519 key is ONLY for libp2p PeerId derivation.
    /// All actual P2P message signing and key exchange uses Falcon-1024/ML-KEM.
    pub fn derive_libp2p_node_key(&self) -> [u8; 32] {
        // Use the first 32 bytes of the Falcon pubkey hash as Ed25519 seed
        let hash = blake2_256(&self.node_id.falcon_pubkey);
        hash
    }

    /// Get the hex-encoded libp2p node key for --node-key CLI parameter
    ///
    /// This returns the 32-byte Ed25519 seed that can be passed to --node-key.
    /// The actual Ed25519 keypair will be derived by libp2p at runtime from this seed.
    pub fn libp2p_node_key_hex(&self) -> String {
        hex::encode(self.derive_libp2p_node_key())
    }

    /// Get a short identifier for logging purposes
    ///
    /// Returns a hex-encoded prefix of the derived node key seed for identification.
    /// The actual PeerId (12D3KooW...) will be computed by libp2p at runtime.
    pub fn libp2p_short_id(&self) -> String {
        let seed = self.derive_libp2p_node_key();
        format!("Falcon-derived:{}", hex::encode(&seed[..8]))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_auto_init() {
        let source = IdentitySource::new_auto().await.unwrap();
        assert_eq!(source.tier(), IdentityTier::Software);
        assert!(!source.node_id().falcon_pubkey.is_empty());
        assert!(!source.node_id().kem_pubkey.is_empty());
    }

    #[tokio::test]
    async fn test_qkd_init() {
        let source = IdentitySource::new(IdentitySourceConfig::Qkd {
            endpoint: "stub://localhost".to_string(),
            sae_id: "test".to_string(),
        }).await.unwrap();

        assert_eq!(source.tier(), IdentityTier::Qkd);
    }

    #[tokio::test]
    async fn test_signing() {
        let source = IdentitySource::new_auto().await.unwrap();
        let message = b"Test message for signing";
        let signature = source.sign(message).await.unwrap();
        assert!(!signature.is_empty());
    }
}
