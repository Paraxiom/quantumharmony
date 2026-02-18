//! Quantum Entropy Vault
//!
//! Secure enclave for quantum entropy that:
//! - Stores entropy in encrypted memory segments
//! - Provides secure channels to cryptographic operations
//! - Integrates with Crypto4A HSM vault
//! - Prevents entropy extraction or replay attacks

use std::sync::{Arc, RwLock};
use std::collections::VecDeque;
use zeroize::{Zeroize, Zeroizing};
use aes_gcm::{
    aead::{Aead, KeyInit, OsRng},
    Aes256Gcm, Nonce, Key
};
use sha3::{Sha3_256, Digest};

/// Maximum entropy segments in vault
const MAX_SEGMENTS: usize = 16;
/// Segment size (32KB)
const SEGMENT_SIZE: usize = 32 * 1024;

/// Secure entropy segment
#[derive(Zeroize)]
#[zeroize(drop)]
struct EntropySegment {
    /// Encrypted entropy data
    ciphertext: Vec<u8>,
    /// Nonce for this segment
    nonce: [u8; 12],
    /// Source of this entropy
    source: QuantumEntropySource,
    /// Quality score
    quality: u8,
    /// Usage counter (prevents replay)
    usage_counter: u64,
    /// Timestamp
    timestamp: u64,
}

/// Quantum entropy source
#[derive(Clone, Copy, Debug, Zeroize)]
pub enum QuantumEntropySource {
    QKD,
    Crypto4aHSM,
    KIRQ,
    DirectMeasurement,
}

/// Secure quantum entropy vault
pub struct QuantumVault {
    /// Master key (derived from HSM)
    master_key: Zeroizing<[u8; 32]>,
    /// Entropy segments
    segments: Arc<RwLock<VecDeque<EntropySegment>>>,
    /// Total entropy consumed
    total_consumed: Arc<RwLock<u64>>,
    /// Vault sealed status
    sealed: Arc<RwLock<bool>>,
    /// HSM connection for key derivation
    hsm_endpoint: Option<String>,
}

impl QuantumVault {
    /// Create new vault with HSM-derived master key
    pub fn new(hsm_endpoint: Option<String>) -> Result<Self, String> {
        // Derive master key from HSM or use secure random
        let master_key = if let Some(ref endpoint) = hsm_endpoint {
            Self::derive_master_key_from_hsm(endpoint)?
        } else {
            Self::generate_master_key()?
        };
        
        Ok(Self {
            master_key: Zeroizing::new(master_key),
            segments: Arc::new(RwLock::new(VecDeque::with_capacity(MAX_SEGMENTS))),
            total_consumed: Arc::new(RwLock::new(0)),
            sealed: Arc::new(RwLock::new(false)),
            hsm_endpoint,
        })
    }
    
    /// Add entropy to the vault
    pub fn add_entropy(
        &self,
        entropy: Vec<u8>,
        source: QuantumEntropySource,
        quality: u8,
    ) -> Result<(), String> {
        // Check if vault is sealed
        if *self.sealed.read().unwrap() {
            return Err("Vault is sealed".into());
        }
        
        // Validate entropy quality
        if quality < 80 {
            return Err("Entropy quality too low for vault storage".into());
        }

        // NIST SP 800-90B health tests (issue #3)
        validate_entropy_health(&entropy)?;
        
        // Encrypt the entropy
        let cipher = Aes256Gcm::new(Key::<Aes256Gcm>::from_slice(&*self.master_key));
        let nonce_bytes = self.generate_nonce();
        let nonce = Nonce::from_slice(&nonce_bytes);
        
        let ciphertext = cipher.encrypt(nonce, entropy.as_ref())
            .map_err(|_| "Encryption failed")?;
        
        // Create segment
        let segment = EntropySegment {
            ciphertext,
            nonce: nonce_bytes,
            source,
            quality,
            usage_counter: 0,
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
        };
        
        // Store in vault
        let mut segments = self.segments.write().unwrap();
        
        // Remove oldest segment if at capacity
        if segments.len() >= MAX_SEGMENTS {
            if let Some(mut old_segment) = segments.pop_front() {
                old_segment.zeroize();
            }
        }
        
        segments.push_back(segment);
        Ok(())
    }
    
    /// Get entropy for SPHINCS+ operations
    pub fn get_sphincs_entropy(&self) -> Result<Zeroizing<[u8; 32]>, String> {
        self.get_entropy_for_purpose(32, "SPHINCS+")
            .map(|v| {
                let mut arr = [0u8; 32];
                arr.copy_from_slice(&v);
                Zeroizing::new(arr)
            })
    }
    
    /// Get entropy for Falcon operations
    pub fn get_falcon_entropy(&self) -> Result<Zeroizing<[u8; 40]>, String> {
        self.get_entropy_for_purpose(40, "Falcon")
            .map(|v| {
                let mut arr = [0u8; 40];
                arr.copy_from_slice(&v);
                Zeroizing::new(arr)
            })
    }
    
    /// Get entropy for consensus operations
    pub fn get_consensus_entropy(&self) -> Result<Zeroizing<[u8; 32]>, String> {
        self.get_entropy_for_purpose(32, "Consensus")
            .map(|v| {
                let mut arr = [0u8; 32];
                arr.copy_from_slice(&v);
                Zeroizing::new(arr)
            })
    }
    
    /// Internal: Get entropy for specific purpose
    fn get_entropy_for_purpose(&self, size: usize, purpose: &str) -> Result<Zeroizing<Vec<u8>>, String> {
        // Check if vault is sealed
        if *self.sealed.read().unwrap() {
            return Err("Vault is sealed".into());
        }
        
        let mut segments = self.segments.write().unwrap();
        
        // Find highest quality segment with enough entropy
        let segment_index = segments.iter()
            .enumerate()
            .filter(|(_, seg)| seg.ciphertext.len() >= size && seg.usage_counter < 100)
            .max_by_key(|(_, seg)| seg.quality)
            .map(|(i, _)| i)
            .ok_or("Insufficient entropy in vault")?;
        
        // Get and decrypt segment
        let segment = &mut segments[segment_index];
        
        let cipher = Aes256Gcm::new(Key::<Aes256Gcm>::from_slice(&*self.master_key));
        let nonce = Nonce::from_slice(&segment.nonce);
        
        let plaintext = cipher.decrypt(nonce, segment.ciphertext.as_ref())
            .map_err(|_| "Decryption failed")?;
        
        // Extract requested entropy
        let mut result = Zeroizing::new(plaintext[..size].to_vec());
        
        // Update segment (remove used entropy)
        let remaining = plaintext[size..].to_vec();
        if remaining.len() < 32 {
            // Not enough entropy left, remove segment
            segments.remove(segment_index);
        } else {
            // Re-encrypt remaining entropy with new nonce
            let new_nonce_bytes = self.generate_nonce();
            let new_nonce = Nonce::from_slice(&new_nonce_bytes);
            
            segment.ciphertext = cipher.encrypt(new_nonce, remaining.as_ref())
                .map_err(|_| "Re-encryption failed")?;
            segment.nonce = new_nonce_bytes;
            segment.usage_counter += 1;
        }
        
        // Update consumption stats
        *self.total_consumed.write().unwrap() += size as u64;
        
        // Log usage
        log::info!("Vault provided {} bytes for {}", size, purpose);
        
        Ok(result)
    }
    
    /// Seal the vault (emergency)
    pub fn seal(&self) {
        *self.sealed.write().unwrap() = true;
        // Clear all segments
        let mut segments = self.segments.write().unwrap();
        for segment in segments.iter_mut() {
            segment.zeroize();
        }
        segments.clear();
        log::warn!("Quantum vault sealed!");
    }
    
    /// Get vault statistics
    pub fn get_stats(&self) -> VaultStats {
        let segments = self.segments.read().unwrap();
        let total_entropy: usize = segments.iter()
            .map(|seg| seg.ciphertext.len())
            .sum();
        
        VaultStats {
            segment_count: segments.len(),
            total_entropy_bytes: total_entropy,
            total_consumed: *self.total_consumed.read().unwrap(),
            sealed: *self.sealed.read().unwrap(),
            average_quality: segments.iter()
                .map(|seg| seg.quality as u32)
                .sum::<u32>() as f32 / segments.len().max(1) as f32,
        }
    }
    
    /// Generate cryptographically secure nonce
    fn generate_nonce(&self) -> [u8; 12] {
        use rand::{RngCore, rngs::OsRng};
        let mut nonce = [0u8; 12];
        OsRng.fill_bytes(&mut nonce);
        nonce
    }
    
    /// Derive master key from HSM
    fn derive_master_key_from_hsm(endpoint: &str) -> Result<[u8; 32], String> {
        // In production, this would connect to Crypto4A HSM
        // For now, derive from endpoint string (NOT SECURE - just for testing)
        let mut hasher = Sha3_256::new();
        hasher.update(endpoint.as_bytes());
        hasher.update(b"quantum_vault_master_key");
        let result = hasher.finalize();
        
        let mut key = [0u8; 32];
        key.copy_from_slice(&result);
        Ok(key)
    }
    
    /// Generate master key (fallback)
    fn generate_master_key() -> Result<[u8; 32], String> {
        use rand::{RngCore, rngs::OsRng};
        let mut key = [0u8; 32];
        OsRng.fill_bytes(&mut key);
        Ok(key)
    }
}

/// Vault statistics
#[derive(Debug, Clone)]
pub struct VaultStats {
    pub segment_count: usize,
    pub total_entropy_bytes: usize,
    pub total_consumed: u64,
    pub sealed: bool,
    pub average_quality: f32,
}

// =============================================================================
// NIST SP 800-90B Health Tests (Issue #3)
// =============================================================================

/// NIST SP 800-90B Repetition Count Test (RCT).
///
/// Detects a noise source failure where the source produces the same value
/// repeatedly. If any byte value appears `cutoff` or more times consecutively,
/// the entropy source is considered unhealthy.
///
/// # Arguments
/// * `data` - Raw entropy bytes to test
/// * `cutoff` - Maximum allowed consecutive repetitions (NIST recommends
///   `1 + ceil(-log2(alpha) / H)` where alpha=2^-20 and H is min-entropy estimate).
///   For a conservative 4 bits/byte min-entropy estimate: cutoff = 6.
///
/// # Returns
/// `true` if the data passes (no excessive repetitions), `false` if it fails.
pub fn repetition_count_test(data: &[u8], cutoff: usize) -> bool {
    if data.len() < 2 {
        return true;
    }

    let mut count = 1usize;
    for i in 1..data.len() {
        if data[i] == data[i - 1] {
            count += 1;
            if count >= cutoff {
                log::warn!(
                    "RCT FAILED: byte 0x{:02x} repeated {} times at offset {}",
                    data[i], count, i
                );
                return false;
            }
        } else {
            count = 1;
        }
    }
    true
}

/// NIST SP 800-90B Adaptive Proportion Test (APT).
///
/// Detects a noise source that produces one symbol value with too-high
/// probability within a window of samples. If the most frequent byte
/// in a sliding window exceeds the cutoff, the source is unhealthy.
///
/// # Arguments
/// * `data` - Raw entropy bytes to test
/// * `window_size` - Size of the sliding window (NIST recommends 512 for binary,
///   64 for non-binary sources; 64 is appropriate for byte-level testing)
/// * `cutoff` - Maximum allowed count of any single byte value within a window.
///   For 8-bit output with H=4 and alpha=2^-20: cutoff ≈ 9 per 64-sample window.
///
/// # Returns
/// `true` if the data passes (no over-represented symbols), `false` if it fails.
pub fn adaptive_proportion_test(data: &[u8], window_size: usize, cutoff: usize) -> bool {
    if data.len() < window_size {
        return true;
    }

    for window_start in 0..=(data.len() - window_size) {
        let window = &data[window_start..window_start + window_size];
        let first_byte = window[0];

        // Count occurrences of the first byte in this window
        let count = window.iter().filter(|&&b| b == first_byte).count();

        if count >= cutoff {
            log::warn!(
                "APT FAILED: byte 0x{:02x} appeared {} times in {}-byte window at offset {}",
                first_byte, count, window_size, window_start
            );
            return false;
        }
    }
    true
}

/// Validate entropy using both NIST SP 800-90B health tests.
///
/// Runs the Repetition Count Test (RCT) and Adaptive Proportion Test (APT)
/// on the raw entropy data before it enters the vault.
///
/// # Arguments
/// * `data` - Raw entropy bytes from QRNG device
///
/// # Returns
/// `Ok(())` if both tests pass, `Err` with the failing test name.
pub fn validate_entropy_health(data: &[u8]) -> Result<(), String> {
    // RCT: cutoff=6 (conservative for 4 bits/byte min-entropy)
    if !repetition_count_test(data, 6) {
        return Err("NIST SP 800-90B Repetition Count Test (RCT) failed".into());
    }

    // APT: window=64, cutoff=9 (8-bit output, H=4, alpha=2^-20)
    if !adaptive_proportion_test(data, 64, 9) {
        return Err("NIST SP 800-90B Adaptive Proportion Test (APT) failed".into());
    }

    Ok(())
}

/// Global vault instance
lazy_static::lazy_static! {
    static ref QUANTUM_VAULT: Arc<QuantumVault> = {
        Arc::new(
            QuantumVault::new(Some("http://192.168.0.41:8132".to_string()))
                .expect("Failed to initialize quantum vault")
        )
    };
}

/// Get reference to global quantum vault
pub fn quantum_vault() -> &'static Arc<QuantumVault> {
    &QUANTUM_VAULT
}

/// Secure channel for entropy delivery
pub struct SecureEntropyChannel {
    vault: Arc<QuantumVault>,
    purpose: String,
}

impl SecureEntropyChannel {
    /// Create channel for specific purpose
    pub fn new(purpose: String) -> Self {
        Self {
            vault: quantum_vault().clone(),
            purpose,
        }
    }
    
    /// Get entropy through secure channel
    pub fn get_entropy(&self, size: usize) -> Result<Zeroizing<Vec<u8>>, String> {
        self.vault.get_entropy_for_purpose(size, &self.purpose)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Generate varied test entropy that passes NIST SP 800-90B health tests.
    /// Uses a simple LCG-like pattern: byte[i] = (i * 0x37 + seed) mod 256.
    fn test_entropy(len: usize, seed: u8) -> Vec<u8> {
        (0..len).map(|i| (i as u8).wrapping_mul(0x37).wrapping_add(seed)).collect()
    }

    #[test]
    fn test_vault_operations() {
        let vault = QuantumVault::new(None).unwrap();

        let entropy = test_entropy(128, 0x42);
        vault.add_entropy(entropy, QuantumEntropySource::KIRQ, 90).unwrap();

        let sphincs_entropy = vault.get_sphincs_entropy().unwrap();
        assert_eq!(sphincs_entropy.len(), 32);

        let falcon_entropy = vault.get_falcon_entropy().unwrap();
        assert_eq!(falcon_entropy.len(), 40);

        let stats = vault.get_stats();
        assert_eq!(stats.segment_count, 1);
        assert_eq!(stats.total_consumed, 72); // 32 + 40
    }

    #[test]
    fn test_vault_quality_threshold() {
        let vault = QuantumVault::new(None).unwrap();

        // Low quality entropy - rejected before health test
        let bad_entropy = test_entropy(64, 0x00);
        let result = vault.add_entropy(bad_entropy, QuantumEntropySource::KIRQ, 50);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), "Entropy quality too low for vault storage");

        // High quality varied entropy - should succeed
        let good_entropy = test_entropy(64, 0xFF);
        let result = vault.add_entropy(good_entropy, QuantumEntropySource::QKD, 95);
        assert!(result.is_ok());

        let stats = vault.get_stats();
        assert_eq!(stats.segment_count, 1);
        assert_eq!(stats.average_quality, 95.0);
    }

    #[test]
    fn test_vault_max_segments() {
        let vault = QuantumVault::new(None).unwrap();

        for i in 0..MAX_SEGMENTS + 1 {
            let entropy = test_entropy(64, i as u8);
            vault.add_entropy(entropy, QuantumEntropySource::KIRQ, 90).unwrap();
        }

        let stats = vault.get_stats();
        assert_eq!(stats.segment_count, MAX_SEGMENTS);
    }

    #[test]
    fn test_vault_entropy_consumption() {
        let vault = QuantumVault::new(None).unwrap();

        let entropy = test_entropy(256, 0x55);
        vault.add_entropy(entropy, QuantumEntropySource::Crypto4aHSM, 98).unwrap();

        let _e1 = vault.get_sphincs_entropy().unwrap();
        let _e2 = vault.get_falcon_entropy().unwrap();
        let _e3 = vault.get_consensus_entropy().unwrap();

        let stats = vault.get_stats();
        assert_eq!(stats.total_consumed, 32 + 40 + 32); // 104 bytes

        assert!(stats.total_entropy_bytes > 0);
        assert!(stats.total_entropy_bytes < 256);
    }

    #[test]
    fn test_vault_segment_removal() {
        let vault = QuantumVault::new(None).unwrap();

        let small_entropy = test_entropy(50, 0x77);
        vault.add_entropy(small_entropy, QuantumEntropySource::DirectMeasurement, 85).unwrap();

        let _falcon = vault.get_falcon_entropy().unwrap();

        let stats = vault.get_stats();
        assert_eq!(stats.segment_count, 0);
    }

    #[test]
    fn test_vault_insufficient_entropy() {
        let vault = QuantumVault::new(None).unwrap();

        let result = vault.get_sphincs_entropy();
        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), "Insufficient entropy in vault");
    }

    #[test]
    fn test_vault_sealing() {
        let vault = QuantumVault::new(None).unwrap();

        let entropy = test_entropy(128, 0x99);
        vault.add_entropy(entropy, QuantumEntropySource::QKD, 99).unwrap();

        vault.seal();

        let stats = vault.get_stats();
        assert!(stats.sealed);
        assert_eq!(stats.segment_count, 0);

        let new_entropy = test_entropy(64, 0xAA);
        let result = vault.add_entropy(new_entropy, QuantumEntropySource::KIRQ, 90);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), "Vault is sealed");

        let result = vault.get_sphincs_entropy();
        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), "Vault is sealed");
    }

    #[test]
    fn test_vault_encryption_decryption() {
        let vault = QuantumVault::new(None).unwrap();

        let original_entropy = (0..128).map(|i| i as u8).collect::<Vec<_>>();
        vault.add_entropy(original_entropy.clone(), QuantumEntropySource::Crypto4aHSM, 92).unwrap();

        let retrieved = vault.get_sphincs_entropy().unwrap();
        assert_eq!(&*retrieved, &original_entropy[..32]);
    }

    #[test]
    fn test_vault_multiple_sources() {
        let vault = QuantumVault::new(None).unwrap();

        vault.add_entropy(test_entropy(64, 0x11), QuantumEntropySource::QKD, 98).unwrap();
        vault.add_entropy(test_entropy(64, 0x22), QuantumEntropySource::Crypto4aHSM, 95).unwrap();
        vault.add_entropy(test_entropy(64, 0x33), QuantumEntropySource::KIRQ, 88).unwrap();
        vault.add_entropy(test_entropy(64, 0x44), QuantumEntropySource::DirectMeasurement, 82).unwrap();

        let stats = vault.get_stats();
        assert_eq!(stats.segment_count, 4);

        // Should select highest quality segment (QKD with 98)
        let entropy = vault.get_sphincs_entropy().unwrap();
        // First byte of test_entropy(64, 0x11) = 0x00 * 0x37 + 0x11 = 0x11
        assert_eq!(entropy[0], 0x11);
    }

    #[test]
    fn test_vault_hsm_endpoint() {
        let vault = QuantumVault::new(Some("http://192.168.0.41:8132".to_string())).unwrap();

        let entropy = test_entropy(96, 0xBB);
        vault.add_entropy(entropy, QuantumEntropySource::Crypto4aHSM, 97).unwrap();

        let _falcon = vault.get_falcon_entropy().unwrap();

        let stats = vault.get_stats();
        assert!(stats.total_consumed > 0);
    }

    #[test]
    fn test_secure_entropy_channel() {
        let channel = SecureEntropyChannel::new("TestPurpose".to_string());

        let vault = quantum_vault();
        let entropy = test_entropy(128, 0xCC);
        vault.add_entropy(entropy, QuantumEntropySource::KIRQ, 91).unwrap();

        let result = channel.get_entropy(32);
        assert!(result.is_ok());

        let entropy = result.unwrap();
        assert_eq!(entropy.len(), 32);
    }

    // ── NIST SP 800-90B Health Tests (Issue #3) ────────────────────

    #[test]
    fn test_rct_passes_varied_data() {
        let data: Vec<u8> = (0..256).map(|i| i as u8).collect();
        assert!(repetition_count_test(&data, 6));
    }

    #[test]
    fn test_rct_fails_constant_data() {
        // 6 consecutive identical bytes should trigger cutoff=6
        let data = vec![0xAA; 10];
        assert!(!repetition_count_test(&data, 6));
    }

    #[test]
    fn test_rct_passes_short_repeat() {
        // 5 consecutive identical bytes is OK with cutoff=6
        let mut data = vec![0xBB; 5];
        data.push(0xCC);
        assert!(repetition_count_test(&data, 6));
    }

    #[test]
    fn test_apt_passes_varied_data() {
        let data: Vec<u8> = (0..128).map(|i| i as u8).collect();
        assert!(adaptive_proportion_test(&data, 64, 9));
    }

    #[test]
    fn test_apt_fails_biased_data() {
        // Window of 64 bytes where one value appears 10 times (exceeds cutoff=9)
        let mut data = vec![0x00; 10];
        data.extend((1..55).map(|i| i as u8));
        assert_eq!(data.len(), 64);
        assert!(!adaptive_proportion_test(&data, 64, 9));
    }

    #[test]
    fn test_validate_entropy_health_passes() {
        let good_data: Vec<u8> = (0..256).map(|i| i as u8).collect();
        assert!(validate_entropy_health(&good_data).is_ok());
    }

    #[test]
    fn test_validate_entropy_health_rejects_constant() {
        let bad_data = vec![0xFF; 128];
        let result = validate_entropy_health(&bad_data);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Repetition Count Test"));
    }

    #[test]
    fn test_vault_rejects_unhealthy_entropy() {
        let vault = QuantumVault::new(None).unwrap();

        // Constant bytes fail RCT even with high quality score
        let constant_entropy = vec![0x42; 128];
        let result = vault.add_entropy(constant_entropy, QuantumEntropySource::QKD, 99);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Repetition Count Test"));
    }
}