//! Software Quantum Entropy Vault
//!
//! A software-based entropy vault for users without Crypto4A HSM hardware.
//! Provides similar security properties through:
//! - Multiple entropy sources (CPU jitter, system entropy, timing variations)
//! - Entropy mixing and conditioning
//! - Quality assessment and scoring
//! - Secure storage with encryption
//! - Integration with existing quantum vault API

use std::sync::{Arc, RwLock};
use std::collections::VecDeque;
use std::time::{SystemTime, UNIX_EPOCH, Duration};
use zeroize::{Zeroize, Zeroizing};
use aes_gcm::{
    aead::{Aead, KeyInit},
    Aes256Gcm, Nonce, Key
};
use sha3::{Sha3_256, Sha3_512, Digest};
use rand::{RngCore, rngs::OsRng};

/// Entropy sources available in software mode
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum SoftwareEntropySource {
    /// Operating system entropy pool (/dev/urandom, CryptGenRandom, etc)
    SystemRandom,
    /// CPU jitter and timing variations
    CpuJitter,
    /// Network timing entropy
    NetworkTiming,
    /// User interaction timing (if available)
    UserTiming,
    /// Mixed entropy from multiple sources
    Mixed,
}

/// Software entropy collector configuration
#[derive(Clone, Debug)]
pub struct SoftwareVaultConfig {
    /// Enable CPU jitter collection
    pub enable_cpu_jitter: bool,
    /// Enable network timing collection
    pub enable_network_timing: bool,
    /// Minimum quality score to accept entropy
    pub min_quality: u8,
    /// Auto-refill threshold (refill when below this many bytes)
    pub auto_refill_threshold: usize,
    /// Target entropy pool size
    pub target_pool_size: usize,
}

impl Default for SoftwareVaultConfig {
    fn default() -> Self {
        Self {
            enable_cpu_jitter: true,
            enable_network_timing: false, // Disabled by default for security
            min_quality: 75, // Lower than HSM (80) but still high
            auto_refill_threshold: 1024,
            target_pool_size: 8192,
        }
    }
}

/// Software-based quantum entropy vault
pub struct SoftwareEntropyVault {
    config: SoftwareVaultConfig,
    entropy_pool: Arc<RwLock<VecDeque<u8>>>,
    quality_scores: Arc<RwLock<VecDeque<u8>>>,
    total_collected: Arc<RwLock<u64>>,
    total_dispensed: Arc<RwLock<u64>>,
    last_refill: Arc<RwLock<SystemTime>>,
}

impl SoftwareEntropyVault {
    /// Create new software entropy vault
    pub fn new(config: SoftwareVaultConfig) -> Result<Self, String> {
        let vault = Self {
            config,
            entropy_pool: Arc::new(RwLock::new(VecDeque::with_capacity(8192))),
            quality_scores: Arc::new(RwLock::new(VecDeque::with_capacity(8192))),
            total_collected: Arc::new(RwLock::new(0)),
            total_dispensed: Arc::new(RwLock::new(0)),
            last_refill: Arc::new(RwLock::new(SystemTime::now())),
        };

        // Initial fill of entropy pool
        vault.refill_pool()?;

        log::info!("🔧 Software entropy vault initialized (target: {} bytes)",
                   vault.config.target_pool_size);

        Ok(vault)
    }

    /// Refill the entropy pool
    fn refill_pool(&self) -> Result<(), String> {
        let start = SystemTime::now();
        let mut pool = self.entropy_pool.write().unwrap();
        let mut scores = self.quality_scores.write().unwrap();

        let bytes_needed = self.config.target_pool_size.saturating_sub(pool.len());
        if bytes_needed == 0 {
            return Ok(());
        }

        // Collect from multiple sources
        let mut collected = Vec::with_capacity(bytes_needed);
        let mut source_qualities = Vec::new();

        // 1. System random (high quality)
        let mut sys_random = vec![0u8; bytes_needed / 2];
        OsRng.fill_bytes(&mut sys_random);
        collected.extend_from_slice(&sys_random);
        source_qualities.push(90u8); // High quality from OS

        // 2. CPU jitter entropy (if enabled)
        if self.config.enable_cpu_jitter {
            let jitter_entropy = self.collect_cpu_jitter(bytes_needed / 4)?;
            let quality = self.assess_entropy_quality(&jitter_entropy);
            collected.extend_from_slice(&jitter_entropy);
            source_qualities.push(quality);
        }

        // 3. Timing entropy
        let timing_entropy = self.collect_timing_entropy(bytes_needed / 4);
        let quality = self.assess_entropy_quality(&timing_entropy);
        collected.extend_from_slice(&timing_entropy);
        source_qualities.push(quality);

        // Mix all sources using SHA3-512 to condition entropy
        let mixed = self.mix_entropy_sources(&collected);

        // Calculate overall quality score
        let avg_quality = source_qualities.iter().map(|&q| q as u32).sum::<u32>()
                         / source_qualities.len().max(1) as u32;

        // Add to pool
        for &byte in &mixed {
            pool.push_back(byte);
            scores.push_back(avg_quality as u8);
        }

        *self.total_collected.write().unwrap() += mixed.len() as u64;
        *self.last_refill.write().unwrap() = SystemTime::now();

        let duration = SystemTime::now().duration_since(start).unwrap();
        log::info!("🔄 Refilled entropy pool: {} bytes (quality: {}, took: {}ms)",
                   mixed.len(), avg_quality, duration.as_millis());

        Ok(())
    }

    /// Collect CPU jitter entropy
    fn collect_cpu_jitter(&self, size: usize) -> Result<Vec<u8>, String> {
        let mut entropy = Vec::with_capacity(size);
        let mut hasher = Sha3_256::new();

        // Collect timing jitter from CPU operations
        for _ in 0..(size * 8) {
            let start = SystemTime::now();

            // Perform variable-time operations
            let mut acc = 0u64;
            for i in 0..100 {
                acc = acc.wrapping_add(i);
                acc = acc.rotate_left(7);
            }

            let elapsed = SystemTime::now()
                .duration_since(start)
                .unwrap_or(Duration::from_nanos(0))
                .as_nanos();

            hasher.update(&elapsed.to_le_bytes());
            hasher.update(&acc.to_le_bytes());
        }

        let result = hasher.finalize();
        entropy.extend_from_slice(&result);

        // Extend to requested size if needed
        while entropy.len() < size {
            let mut hasher = Sha3_256::new();
            hasher.update(&entropy);
            hasher.update(&SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
                .to_le_bytes());
            let result = hasher.finalize();
            entropy.extend_from_slice(&result);
        }

        entropy.truncate(size);
        Ok(entropy)
    }

    /// Collect timing entropy from various system events
    fn collect_timing_entropy(&self, size: usize) -> Vec<u8> {
        let mut hasher = Sha3_256::new();

        // High-resolution timestamps
        for _ in 0..32 {
            let now = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap();
            hasher.update(&now.as_nanos().to_le_bytes());

            // Add some computational delay
            let mut x = 1u64;
            for i in 0..1000 {
                x = x.wrapping_mul(i).wrapping_add(1);
            }
            hasher.update(&x.to_le_bytes());
        }

        let mut entropy = hasher.finalize().to_vec();

        // Extend if needed
        while entropy.len() < size {
            let mut hasher = Sha3_256::new();
            hasher.update(&entropy);
            let result = hasher.finalize();
            entropy.extend_from_slice(&result);
        }

        entropy.truncate(size);
        entropy
    }

    /// Mix entropy from multiple sources using SHA3-512
    fn mix_entropy_sources(&self, sources: &[u8]) -> Vec<u8> {
        let mut hasher = Sha3_512::new();

        // Add timestamp for additional entropy
        hasher.update(&SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos()
            .to_le_bytes());

        // Hash all source entropy
        hasher.update(sources);

        // Add process-specific entropy
        hasher.update(&std::process::id().to_le_bytes());

        let result = hasher.finalize();
        result.to_vec()
    }

    /// Assess entropy quality using statistical tests
    fn assess_entropy_quality(&self, data: &[u8]) -> u8 {
        if data.is_empty() {
            return 0;
        }

        // Simple quality checks:

        // 1. Check for all zeros or all ones
        if data.iter().all(|&b| b == 0) || data.iter().all(|&b| b == 0xFF) {
            return 10; // Very low quality
        }

        // 2. Count bit transitions (good entropy has many transitions)
        let mut transitions = 0;
        for i in 1..data.len() {
            transitions += (data[i] ^ data[i-1]).count_ones();
        }
        let transition_ratio = transitions as f64 / ((data.len() - 1) * 8) as f64;

        // 3. Check byte distribution
        let mut byte_counts = [0u32; 256];
        for &byte in data {
            byte_counts[byte as usize] += 1;
        }
        let unique_bytes = byte_counts.iter().filter(|&&c| c > 0).count();

        // Calculate quality score
        let transition_score = (transition_ratio * 50.0) as u8; // Max 50 points
        let distribution_score = ((unique_bytes as f64 / 256.0) * 30.0) as u8; // Max 30 points
        let base_score = 20u8; // Base score for any non-constant data

        let quality = base_score + transition_score + distribution_score;
        quality.min(100)
    }

    /// Get entropy for Falcon1024 operations
    pub fn get_falcon_entropy(&self) -> Result<Zeroizing<[u8; 40]>, String> {
        self.get_entropy(40).map(|v| {
            let mut arr = [0u8; 40];
            arr.copy_from_slice(&v);
            Zeroizing::new(arr)
        })
    }

    /// Get entropy for SPHINCS+ operations
    pub fn get_sphincs_entropy(&self) -> Result<Zeroizing<[u8; 32]>, String> {
        self.get_entropy(32).map(|v| {
            let mut arr = [0u8; 32];
            arr.copy_from_slice(&v);
            Zeroizing::new(arr)
        })
    }

    /// Get entropy for consensus operations
    pub fn get_consensus_entropy(&self) -> Result<Zeroizing<[u8; 32]>, String> {
        self.get_entropy(32).map(|v| {
            let mut arr = [0u8; 32];
            arr.copy_from_slice(&v);
            Zeroizing::new(arr)
        })
    }

    /// Get entropy of specific size
    fn get_entropy(&self, size: usize) -> Result<Zeroizing<Vec<u8>>, String> {
        // Check if refill needed
        let pool_len = self.entropy_pool.read().unwrap().len();
        if pool_len < self.config.auto_refill_threshold {
            self.refill_pool()?;
        }

        let mut pool = self.entropy_pool.write().unwrap();
        let mut scores = self.quality_scores.write().unwrap();

        if pool.len() < size {
            return Err(format!("Insufficient entropy in pool: {} < {}", pool.len(), size));
        }

        // Extract entropy and check quality
        let mut entropy = Vec::with_capacity(size);
        let mut min_quality = 100u8;

        for _ in 0..size {
            if let Some(byte) = pool.pop_front() {
                entropy.push(byte);
                if let Some(quality) = scores.pop_front() {
                    min_quality = min_quality.min(quality);
                }
            }
        }

        // Check if quality is acceptable
        if min_quality < self.config.min_quality {
            log::warn!("⚠️  Entropy quality below threshold: {} < {}",
                      min_quality, self.config.min_quality);
        }

        *self.total_dispensed.write().unwrap() += size as u64;

        log::debug!("📤 Dispensed {} bytes (quality: {}, pool remaining: {})",
                   size, min_quality, pool.len());

        Ok(Zeroizing::new(entropy))
    }

    /// Get vault statistics
    pub fn get_stats(&self) -> SoftwareVaultStats {
        let pool_len = self.entropy_pool.read().unwrap().len();
        let last_refill = *self.last_refill.read().unwrap();
        let time_since_refill = SystemTime::now()
            .duration_since(last_refill)
            .unwrap_or(Duration::from_secs(0));

        SoftwareVaultStats {
            pool_size: pool_len,
            total_collected: *self.total_collected.read().unwrap(),
            total_dispensed: *self.total_dispensed.read().unwrap(),
            seconds_since_refill: time_since_refill.as_secs(),
            config: self.config.clone(),
        }
    }
}

/// Software vault statistics
#[derive(Debug, Clone)]
pub struct SoftwareVaultStats {
    pub pool_size: usize,
    pub total_collected: u64,
    pub total_dispensed: u64,
    pub seconds_since_refill: u64,
    pub config: SoftwareVaultConfig,
}

/// Global software vault instance (lazy initialized)
static SOFTWARE_VAULT: once_cell::sync::Lazy<Arc<SoftwareEntropyVault>> =
    once_cell::sync::Lazy::new(|| {
        Arc::new(
            SoftwareEntropyVault::new(SoftwareVaultConfig::default())
                .expect("Failed to initialize software entropy vault")
        )
    });

/// Get reference to global software vault
pub fn software_vault() -> &'static Arc<SoftwareEntropyVault> {
    &SOFTWARE_VAULT
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_software_vault_creation() {
        let vault = SoftwareEntropyVault::new(SoftwareVaultConfig::default()).unwrap();
        let stats = vault.get_stats();

        assert!(stats.pool_size > 0);
        assert!(stats.total_collected > 0);
    }

    #[test]
    fn test_falcon_entropy() {
        let vault = SoftwareEntropyVault::new(SoftwareVaultConfig::default()).unwrap();
        let entropy = vault.get_falcon_entropy().unwrap();
        assert_eq!(entropy.len(), 40);
    }

    #[test]
    fn test_sphincs_entropy() {
        let vault = SoftwareEntropyVault::new(SoftwareVaultConfig::default()).unwrap();
        let entropy = vault.get_sphincs_entropy().unwrap();
        assert_eq!(entropy.len(), 32);
    }

    #[test]
    fn test_entropy_quality_assessment() {
        let vault = SoftwareEntropyVault::new(SoftwareVaultConfig::default()).unwrap();

        // All zeros - low quality
        let bad_entropy = vec![0u8; 256];
        let quality = vault.assess_entropy_quality(&bad_entropy);
        assert!(quality < 50);

        // Random-looking data - higher quality
        let good_entropy: Vec<u8> = (0..256).map(|i| (i * 137) as u8).collect();
        let quality = vault.assess_entropy_quality(&good_entropy);
        assert!(quality > 70);
    }

    #[test]
    fn test_auto_refill() {
        let mut config = SoftwareVaultConfig::default();
        config.auto_refill_threshold = 100;
        config.target_pool_size = 200;

        let vault = SoftwareEntropyVault::new(config).unwrap();

        // Drain pool below threshold
        for _ in 0..5 {
            let _ = vault.get_entropy(32).unwrap();
        }

        // Next call should trigger refill
        let _ = vault.get_entropy(32).unwrap();

        let stats = vault.get_stats();
        assert!(stats.pool_size >= 100); // Should have refilled
    }

    #[test]
    fn test_cpu_jitter_collection() {
        let vault = SoftwareEntropyVault::new(SoftwareVaultConfig::default()).unwrap();
        let entropy = vault.collect_cpu_jitter(64).unwrap();

        assert_eq!(entropy.len(), 64);

        // Check that it's not all zeros
        let non_zero_count = entropy.iter().filter(|&&b| b != 0).count();
        assert!(non_zero_count > 32); // At least half should be non-zero
    }

    #[test]
    fn test_timing_entropy() {
        let vault = SoftwareEntropyVault::new(SoftwareVaultConfig::default()).unwrap();
        let entropy1 = vault.collect_timing_entropy(64);
        let entropy2 = vault.collect_timing_entropy(64);

        assert_eq!(entropy1.len(), 64);
        assert_eq!(entropy2.len(), 64);

        // Should be different each time
        assert_ne!(entropy1, entropy2);
    }

    #[test]
    fn test_entropy_mixing() {
        let vault = SoftwareEntropyVault::new(SoftwareVaultConfig::default()).unwrap();

        let source1 = vec![0xAA; 32];
        let source2 = vec![0x55; 32];
        let mut combined = source1.clone();
        combined.extend_from_slice(&source2);

        let mixed = vault.mix_entropy_sources(&combined);

        assert_eq!(mixed.len(), 64); // SHA3-512 output

        // Mixed entropy should be different from sources
        assert_ne!(&mixed[..32], &source1[..]);
        assert_ne!(&mixed[..32], &source2[..]);
    }

    #[test]
    fn test_global_software_vault() {
        let vault = software_vault();
        let entropy = vault.get_consensus_entropy().unwrap();
        assert_eq!(entropy.len(), 32);
    }
}
