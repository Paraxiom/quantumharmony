//! Unified Quantum Vault
//!
//! Provides a unified interface for quantum entropy management that automatically
//! selects between Hardware Security Module (HSM) or Software Security Module (SSM)
//! based on availability and configuration.

use zeroize::Zeroizing;
use crate::quantum_vault::{QuantumVault, VaultStats, QuantumEntropySource};
use crate::software_entropy_vault::{SoftwareEntropyVault, SoftwareVaultConfig, SoftwareVaultStats};

/// Vault backend type
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum VaultBackend {
    /// Hardware Security Module (Crypto4A)
    HSM,
    /// Software Security Module (fallback)
    SSM,
}

/// Unified vault configuration
#[derive(Clone, Debug)]
pub struct UnifiedVaultConfig {
    /// Preferred backend (will fallback if unavailable)
    pub preferred_backend: VaultBackend,
    /// Crypto4A HSM endpoint (if available)
    pub hsm_endpoint: Option<String>,
    /// Software vault configuration
    pub software_config: SoftwareVaultConfig,
    /// Allow fallback to software if HSM fails
    pub allow_fallback: bool,
}

impl Default for UnifiedVaultConfig {
    fn default() -> Self {
        Self {
            preferred_backend: VaultBackend::SSM, // Default to software for broader compatibility
            hsm_endpoint: None,
            software_config: SoftwareVaultConfig::default(),
            allow_fallback: true,
        }
    }
}

impl UnifiedVaultConfig {
    /// Configuration for HSM-only mode (no fallback)
    pub fn hsm_only(endpoint: String) -> Self {
        Self {
            preferred_backend: VaultBackend::HSM,
            hsm_endpoint: Some(endpoint),
            software_config: SoftwareVaultConfig::default(),
            allow_fallback: false,
        }
    }

    /// Configuration for SSM-only mode
    pub fn software_only() -> Self {
        Self {
            preferred_backend: VaultBackend::SSM,
            hsm_endpoint: None,
            software_config: SoftwareVaultConfig::default(),
            allow_fallback: false,
        }
    }

    /// Configuration with HSM preferred, SSM fallback
    pub fn hsm_with_fallback(endpoint: String) -> Self {
        Self {
            preferred_backend: VaultBackend::HSM,
            hsm_endpoint: Some(endpoint),
            software_config: SoftwareVaultConfig::default(),
            allow_fallback: true,
        }
    }
}

/// Unified vault statistics
#[derive(Debug, Clone)]
pub enum UnifiedVaultStats {
    HSM {
        backend: VaultBackend,
        stats: VaultStats,
    },
    SSM {
        backend: VaultBackend,
        stats: SoftwareVaultStats,
    },
}

/// Unified quantum vault that adapts between HSM and SSM
pub enum UnifiedVault {
    /// Using Hardware Security Module
    HSM(QuantumVault),
    /// Using Software Security Module
    SSM(SoftwareEntropyVault),
}

impl UnifiedVault {
    /// Create new unified vault with configuration
    pub fn new(config: UnifiedVaultConfig) -> Result<Self, String> {
        match config.preferred_backend {
            VaultBackend::HSM => {
                // Try to initialize HSM vault
                if let Some(endpoint) = config.hsm_endpoint.clone() {
                    match QuantumVault::new(Some(endpoint.clone())) {
                        Ok(vault) => {
                            log::info!("🔐 Initialized HSM vault (Crypto4A @ {})", endpoint);
                            return Ok(UnifiedVault::HSM(vault));
                        }
                        Err(e) if config.allow_fallback => {
                            log::warn!("⚠️  HSM initialization failed: {}", e);
                            log::info!("🔄 Falling back to software vault...");
                        }
                        Err(e) => {
                            return Err(format!("HSM initialization failed and fallback disabled: {}", e));
                        }
                    }
                }

                // Fallback to software
                if config.allow_fallback {
                    let software_vault = SoftwareEntropyVault::new(config.software_config)?;
                    log::info!("🔧 Initialized software vault (SSM) as fallback");
                    Ok(UnifiedVault::SSM(software_vault))
                } else {
                    Err("HSM not available and fallback disabled".to_string())
                }
            }

            VaultBackend::SSM => {
                // Use software vault directly
                let software_vault = SoftwareEntropyVault::new(config.software_config)?;
                log::info!("🔧 Initialized software vault (SSM)");
                Ok(UnifiedVault::SSM(software_vault))
            }
        }
    }

    /// Get current backend type
    pub fn backend(&self) -> VaultBackend {
        match self {
            UnifiedVault::HSM(_) => VaultBackend::HSM,
            UnifiedVault::SSM(_) => VaultBackend::SSM,
        }
    }

    /// Get entropy for Falcon1024 operations
    pub fn get_falcon_entropy(&self) -> Result<Zeroizing<[u8; 40]>, String> {
        match self {
            UnifiedVault::HSM(vault) => vault.get_falcon_entropy(),
            UnifiedVault::SSM(vault) => vault.get_falcon_entropy(),
        }
    }

    /// Get entropy for SPHINCS+ operations
    pub fn get_sphincs_entropy(&self) -> Result<Zeroizing<[u8; 32]>, String> {
        match self {
            UnifiedVault::HSM(vault) => vault.get_sphincs_entropy(),
            UnifiedVault::SSM(vault) => vault.get_sphincs_entropy(),
        }
    }

    /// Get entropy for consensus operations
    pub fn get_consensus_entropy(&self) -> Result<Zeroizing<[u8; 32]>, String> {
        match self {
            UnifiedVault::HSM(vault) => vault.get_consensus_entropy(),
            UnifiedVault::SSM(vault) => vault.get_consensus_entropy(),
        }
    }

    /// Add entropy to vault (HSM only)
    pub fn add_entropy(
        &self,
        entropy: Vec<u8>,
        source: QuantumEntropySource,
        quality: u8,
    ) -> Result<(), String> {
        match self {
            UnifiedVault::HSM(vault) => vault.add_entropy(entropy, source, quality),
            UnifiedVault::SSM(_) => {
                Err("Software vault manages its own entropy collection".to_string())
            }
        }
    }

    /// Get vault statistics
    pub fn get_stats(&self) -> UnifiedVaultStats {
        match self {
            UnifiedVault::HSM(vault) => UnifiedVaultStats::HSM {
                backend: VaultBackend::HSM,
                stats: vault.get_stats(),
            },
            UnifiedVault::SSM(vault) => UnifiedVaultStats::SSM {
                backend: VaultBackend::SSM,
                stats: vault.get_stats(),
            },
        }
    }

    /// Seal the vault (emergency shutdown)
    pub fn seal(&self) {
        match self {
            UnifiedVault::HSM(vault) => vault.seal(),
            UnifiedVault::SSM(_) => {
                log::warn!("⚠️  Seal operation not implemented for software vault");
            }
        }
    }
}

/// Global unified vault instance
static UNIFIED_VAULT: once_cell::sync::Lazy<std::sync::Arc<UnifiedVault>> =
    once_cell::sync::Lazy::new(|| {
        // Try to detect HSM endpoint from environment
        let hsm_endpoint = std::env::var("CRYPTO4A_ENDPOINT").ok();

        let config = if let Some(endpoint) = hsm_endpoint {
            log::info!("🔍 Detected CRYPTO4A_ENDPOINT={}", endpoint);
            UnifiedVaultConfig::hsm_with_fallback(endpoint)
        } else {
            log::info!("🔍 No HSM endpoint configured, using software vault");
            UnifiedVaultConfig::software_only()
        };

        std::sync::Arc::new(
            UnifiedVault::new(config).expect("Failed to initialize unified vault")
        )
    });

/// Get reference to global unified vault
pub fn unified_vault() -> &'static std::sync::Arc<UnifiedVault> {
    &UNIFIED_VAULT
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_software_only_vault() {
        let config = UnifiedVaultConfig::software_only();
        let vault = UnifiedVault::new(config).unwrap();

        assert_eq!(vault.backend(), VaultBackend::SSM);

        // Test entropy retrieval
        let falcon = vault.get_falcon_entropy().unwrap();
        assert_eq!(falcon.len(), 40);

        let sphincs = vault.get_sphincs_entropy().unwrap();
        assert_eq!(sphincs.len(), 32);

        let consensus = vault.get_consensus_entropy().unwrap();
        assert_eq!(consensus.len(), 32);
    }

    #[test]
    fn test_hsm_with_fallback_config() {
        // Note: HSM vault currently accepts any endpoint for testing
        // In production, this would connect to real Crypto4A hardware
        let config = UnifiedVaultConfig::hsm_with_fallback("http://test:8132".to_string());
        let vault = UnifiedVault::new(config).unwrap();

        // HSM vault initializes successfully even with test endpoint
        assert_eq!(vault.backend(), VaultBackend::HSM);

        // Add varied entropy to HSM vault (constant bytes fail NIST 800-90B RCT)
        let test_entropy: Vec<u8> = (0u8..128).collect();
        vault.add_entropy(test_entropy, QuantumEntropySource::QKD, 95).unwrap();

        // Should work after entropy added
        let entropy = vault.get_consensus_entropy().unwrap();
        assert_eq!(entropy.len(), 32);
    }

    #[test]
    fn test_software_fallback_mechanism() {
        // Test that software fallback is properly configured
        let config = UnifiedVaultConfig {
            preferred_backend: VaultBackend::HSM,
            hsm_endpoint: None, // No endpoint provided
            software_config: SoftwareVaultConfig::default(),
            allow_fallback: true,
        };
        let vault = UnifiedVault::new(config).unwrap();

        // Should fallback to SSM when no HSM endpoint
        assert_eq!(vault.backend(), VaultBackend::SSM);

        let entropy = vault.get_consensus_entropy().unwrap();
        assert_eq!(entropy.len(), 32);
    }

    #[test]
    fn test_vault_stats() {
        let config = UnifiedVaultConfig::software_only();
        let vault = UnifiedVault::new(config).unwrap();

        let stats = vault.get_stats();
        match stats {
            UnifiedVaultStats::SSM { backend, stats } => {
                assert_eq!(backend, VaultBackend::SSM);
                assert!(stats.pool_size > 0);
                assert!(stats.total_collected > 0);
            }
            UnifiedVaultStats::HSM { .. } => {
                panic!("Expected SSM stats, got HSM");
            }
        }
    }

    #[test]
    fn test_global_unified_vault() {
        let vault = unified_vault();
        let entropy = vault.get_consensus_entropy().unwrap();
        assert_eq!(entropy.len(), 32);

        let stats = vault.get_stats();
        // Should be SSM since no HSM endpoint in test environment
        match stats {
            UnifiedVaultStats::SSM { backend, .. } => {
                assert_eq!(backend, VaultBackend::SSM);
            }
            UnifiedVaultStats::HSM { .. } => {
                // HSM might be available in some test environments
                log::info!("HSM vault available in test environment");
            }
        }
    }

    #[test]
    fn test_multiple_entropy_requests() {
        let config = UnifiedVaultConfig::software_only();
        let vault = UnifiedVault::new(config).unwrap();

        // Request multiple times
        for i in 0..10 {
            let entropy = vault.get_falcon_entropy().unwrap();
            assert_eq!(entropy.len(), 40, "Failed on iteration {}", i);
        }

        let stats = vault.get_stats();
        match stats {
            UnifiedVaultStats::SSM { stats, .. } => {
                assert!(stats.total_dispensed >= 400); // At least 10 * 40 bytes
            }
            _ => {}
        }
    }
}
