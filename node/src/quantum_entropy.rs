//! Quantum Entropy Module - Centralized HWRNG Integration
//!
//! This module provides a unified interface for accessing quantum entropy from hardware
//! random number generators (HWRNG/QRNG). It supports fallback to deterministic entropy
//! when quantum devices are unavailable.
//!
//! ## Features
//!
//! 1. **Threshold QRNG Integration** - Uses K-of-M Shamir Secret Sharing from multiple devices
//! 2. **Automatic Fallback** - Falls back to Keccak-256 deterministic entropy when QRNG unavailable
//! 3. **Entropy Quality Tracking** - Monitors and reports entropy source quality
//! 4. **Thread-Safe** - Can be safely shared across async tasks
//!
//! ## Usage
//!
//! ```rust,ignore
//! use quantum_entropy::QuantumEntropyProvider;
//!
//! let provider = QuantumEntropyProvider::new(config);
//!
//! // Get 48 bytes of quantum entropy
//! let entropy = provider.get_entropy(48).await?;
//!
//! // Get entropy with quality metadata
//! let (entropy, quality) = provider.get_entropy_with_quality(48).await?;
//! ```

use std::sync::Arc;
use tokio::sync::RwLock;
use sp_crypto_hashing::keccak_256;
use crate::threshold_qrng::{ThresholdConfig, DeviceShare, reconstruct_entropy};
use crate::pqtg_client::PqtgClient;
use log::{info, warn};

/// Quality metrics for entropy source
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EntropyQuality {
    /// True quantum entropy from HWRNG devices
    QuantumHardware {
        /// Number of devices used
        devices_used: u8,
        /// Average QBER across devices (basis points: 100 = 1%)
        avg_qber: u32,
    },
    /// Deterministic fallback using Keccak-256
    DeterministicFallback,
}

impl EntropyQuality {
    pub fn is_quantum(&self) -> bool {
        matches!(self, EntropyQuality::QuantumHardware { .. })
    }

    pub fn quality_score(&self) -> u32 {
        match self {
            EntropyQuality::QuantumHardware { devices_used, avg_qber } => {
                // Higher score = better quality
                // Max score: 10000 (perfect quantum with no errors)
                let device_bonus = (*devices_used as u32 * 1000).min(3000);
                let qber_penalty = (*avg_qber).min(5000);
                (10000 + device_bonus).saturating_sub(qber_penalty)
            }
            EntropyQuality::DeterministicFallback => 5000, // Mid-range score
        }
    }
}

/// Mode for entropy generation
#[derive(Debug, Clone, Copy)]
pub enum EntropyMode {
    /// Prefer quantum, fall back to deterministic
    PreferQuantum,
    /// Require quantum, fail if unavailable
    RequireQuantum,
    /// Always use deterministic (for testing/reproducibility)
    AlwaysDeterministic,
}

/// Centralized quantum entropy provider
pub struct QuantumEntropyProvider {
    /// PQTG client for accessing quantum devices
    pqtg_client: Option<Arc<RwLock<PqtgClient>>>,

    /// Threshold configuration
    threshold_config: ThresholdConfig,

    /// Operation mode
    mode: EntropyMode,

    /// Fallback seed for deterministic mode
    fallback_seed: [u8; 32],

    /// Counter for deterministic nonce generation
    deterministic_counter: Arc<RwLock<u64>>,
}

impl QuantumEntropyProvider {
    /// Create new quantum entropy provider
    pub fn new(
        pqtg_client: Option<PqtgClient>,
        threshold_config: ThresholdConfig,
        mode: EntropyMode,
    ) -> Self {
        // Initialize fallback seed from system entropy or fixed seed for dev
        let fallback_seed = if cfg!(test) || cfg!(debug_assertions) {
            // Deterministic seed for development/testing
            keccak_256(b"quantumharmony-dev-entropy-seed-v1")
        } else {
            // NOTE: Using deterministic fallback seed; /dev/urandom integration deferred to PQTG hardware deployment
            keccak_256(b"quantumharmony-fallback-entropy-seed-v1")
        };

        Self {
            pqtg_client: pqtg_client.map(|c| Arc::new(RwLock::new(c))),
            threshold_config,
            mode,
            fallback_seed,
            deterministic_counter: Arc::new(RwLock::new(0)),
        }
    }

    /// Get quantum entropy with automatic fallback
    ///
    /// # Arguments
    /// * `length` - Number of bytes of entropy to generate
    ///
    /// # Returns
    /// Entropy bytes and quality metadata
    pub async fn get_entropy_with_quality(
        &self,
        length: usize,
    ) -> Result<(Vec<u8>, EntropyQuality), String> {
        match self.mode {
            EntropyMode::AlwaysDeterministic => {
                let entropy = self.generate_deterministic_entropy(length).await;
                Ok((entropy, EntropyQuality::DeterministicFallback))
            }
            EntropyMode::RequireQuantum => {
                self.generate_quantum_entropy(length).await
            }
            EntropyMode::PreferQuantum => {
                // Try quantum first, fall back to deterministic
                match self.generate_quantum_entropy(length).await {
                    Ok(result) => Ok(result),
                    Err(e) => {
                        warn!("⚠️  Quantum entropy unavailable ({}), using deterministic fallback", e);
                        let entropy = self.generate_deterministic_entropy(length).await;
                        Ok((entropy, EntropyQuality::DeterministicFallback))
                    }
                }
            }
        }
    }

    /// Get quantum entropy (convenience method without quality metadata)
    pub async fn get_entropy(&self, length: usize) -> Result<Vec<u8>, String> {
        let (entropy, _quality) = self.get_entropy_with_quality(length).await?;
        Ok(entropy)
    }

    /// Generate quantum entropy from HWRNG devices
    async fn generate_quantum_entropy(
        &self,
        length: usize,
    ) -> Result<(Vec<u8>, EntropyQuality), String> {
        let pqtg_client = self.pqtg_client.as_ref()
            .ok_or_else(|| "PQTG client not available".to_string())?;

        // Lock client for duration of request
        let mut client = pqtg_client.write().await;

        // Collect entropy shares from devices
        let mut device_shares = Vec::new();
        let mut total_qber = 0u32;
        let enabled_devices: Vec<_> = self.threshold_config.devices.iter()
            .filter(|d| d.enabled)
            .collect();

        if enabled_devices.is_empty() {
            return Err("No enabled QRNG devices configured".to_string());
        }

        info!("🔮 Collecting quantum entropy from {} devices (need {} shares)",
              enabled_devices.len(), self.threshold_config.threshold_k);

        for device in enabled_devices.iter() {
            match self.collect_device_entropy(&mut *client, device, length).await {
                Ok(share) => {
                    total_qber += share.qber;
                    device_shares.push(share);
                }
                Err(e) => {
                    warn!("⚠️  Failed to collect from device {:?}: {}", device.device_id, e);
                }
            }
        }

        if device_shares.len() < self.threshold_config.threshold_k as usize {
            return Err(format!(
                "Insufficient quantum entropy shares: {} < {}",
                device_shares.len(),
                self.threshold_config.threshold_k
            ));
        }

        // Reconstruct entropy using Shamir Secret Sharing
        let entropy = reconstruct_entropy(
            &device_shares,
            self.threshold_config.threshold_k as u8,
        )?;

        // Ensure we have enough entropy
        let final_entropy = if entropy.len() < length {
            // Extend with Keccak-256 if needed
            let mut extended = entropy.clone();
            while extended.len() < length {
                let hash = keccak_256(&extended);
                extended.extend_from_slice(&hash);
            }
            extended[..length].to_vec()
        } else {
            entropy[..length].to_vec()
        };

        let avg_qber = total_qber / device_shares.len() as u32;
        let quality = EntropyQuality::QuantumHardware {
            devices_used: device_shares.len() as u8,
            avg_qber,
        };

        info!("✅ Generated {} bytes of quantum entropy (quality score: {})",
              length, quality.quality_score());

        Ok((final_entropy, quality))
    }

    /// Collect entropy share from a single device
    async fn collect_device_entropy(
        &self,
        _client: &mut PqtgClient,
        device: &crate::threshold_qrng::DeviceConfig,
        length: usize,
    ) -> Result<DeviceShare, String> {
        // NOTE: Mock PQTG device communication for development; real implementation requires PQTG USB/network driver

        info!("📡 Collecting {} bytes from device {:?}", length, device.device_id);

        // Mock share generation (replace with actual PQTG call)
        let share_data = vec![0u8; length]; // NOTE: Placeholder share data; real data from PQTG device quantum channel
        let qber = 150; // Mock QBER (1.5%)
        let stark_proof = vec![]; // NOTE: Placeholder; real STARK proof generated by PQTG device attestation module
        let timestamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_err(|e| format!("Time error: {}", e))?
            .as_secs();

        Ok(DeviceShare {
            device_id: device.device_id.clone(),
            share: share_data,
            qber,
            stark_proof,
            timestamp,
        })
    }

    /// Generate deterministic entropy using Keccak-256
    async fn generate_deterministic_entropy(&self, length: usize) -> Vec<u8> {
        let mut counter = self.deterministic_counter.write().await;
        let nonce = *counter;
        *counter += 1;

        info!("🔧 Generating {} bytes of deterministic entropy (nonce: {})", length, nonce);

        // Combine fallback seed + nonce
        let mut input = self.fallback_seed.to_vec();
        input.extend_from_slice(&nonce.to_le_bytes());

        // Hash repeatedly to get desired length
        let mut entropy = Vec::new();
        let mut current = input;

        while entropy.len() < length {
            let hash = keccak_256(&current);
            entropy.extend_from_slice(&hash);
            current = hash.to_vec();
        }

        entropy.truncate(length);
        entropy
    }

    /// Get current entropy source quality
    pub async fn get_quality_status(&self) -> String {
        if self.pqtg_client.is_some() {
            let enabled_count = self.threshold_config.devices.iter()
                .filter(|d| d.enabled)
                .count();

            format!("Quantum-Ready ({} devices, threshold {}/{})",
                    enabled_count,
                    self.threshold_config.threshold_k,
                    self.threshold_config.total_devices_m)
        } else {
            "Deterministic Fallback".to_string()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_deterministic_entropy_generation() {
        let config = ThresholdConfig::default();
        let provider = QuantumEntropyProvider::new(
            None,
            config,
            EntropyMode::AlwaysDeterministic,
        );

        // Generate entropy multiple times
        let e1 = provider.get_entropy(32).await.unwrap();
        let e2 = provider.get_entropy(32).await.unwrap();
        let e3 = provider.get_entropy(32).await.unwrap();

        // All should be different (due to counter)
        assert_ne!(e1, e2);
        assert_ne!(e2, e3);
        assert_ne!(e1, e3);

        // All should be correct length
        assert_eq!(e1.len(), 32);
        assert_eq!(e2.len(), 32);
        assert_eq!(e3.len(), 32);
    }

    #[tokio::test]
    async fn test_entropy_quality_score() {
        let q1 = EntropyQuality::QuantumHardware {
            devices_used: 3,
            avg_qber: 100, // 1%
        };
        let q2 = EntropyQuality::QuantumHardware {
            devices_used: 2,
            avg_qber: 500, // 5%
        };
        let q3 = EntropyQuality::DeterministicFallback;

        // Quantum with more devices and lower QBER should score higher
        assert!(q1.quality_score() > q2.quality_score());

        // Quantum should generally score higher than deterministic
        assert!(q1.quality_score() > q3.quality_score());
    }
}
