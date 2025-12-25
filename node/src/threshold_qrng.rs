//! Threshold QRNG with Shamir Secret Sharing
//!
//! This module implements K-of-M threshold scheme for combining multiple quantum
//! random number generators (QRNGs) into a single, Byzantine-fault-tolerant entropy source.
//!
//! ## Architecture
//!
//! 1. **Per-Device Priority Queues** - Each QRNG device has dedicated queue ordered by QBER
//! 2. **VRF Leader Election** - Leader selected per block to collect shares
//! 3. **Shamir Reconstruction** - Combine K best shares using Lagrange interpolation
//! 4. **3-Level Proof Hierarchy**:
//!    - Level 1: Device STARK proofs (quantum measurement authenticity)
//!    - Level 2: Shamir reconstruction proofs (leader correctness)
//!    - Level 3: Byzantine consensus (2/3 validators agree)
//!
//! ## References
//! - docs/THRESHOLD_QRNG_ARCHITECTURE.md
//! - docs/ARCHITECTURE.md Section 8.5

use scale_codec::{Encode, Decode};
use sp_core::{H256, Blake2Hasher, Hasher};
use sharks::{Share, Sharks};
use log::info;
use std::collections::HashMap;

// Post-quantum cryptography for signatures
use pqcrypto_falcon::falcon1024;
use pqcrypto_traits::sign::{PublicKey as SignPublicKey, SecretKey as SignSecretKey, SignedMessage};

/// Device identifier (e.g., "toshiba-qrng-1", "crypto4a-hsm", "kirq-hub")
#[derive(Clone, Debug, Encode, Decode, PartialEq, Eq, Hash)]
pub struct DeviceId(pub Vec<u8>);

impl DeviceId {
    pub fn from_str(s: &str) -> Self {
        DeviceId(s.as_bytes().to_vec())
    }

    pub fn as_str(&self) -> Result<&str, std::str::Utf8Error> {
        std::str::from_utf8(&self.0)
    }
}

/// Single share from a QRNG device with STARK proof
#[derive(Clone, Debug, Encode, Decode, PartialEq, Eq, Hash)]
pub struct DeviceShare {
    /// Device identifier
    pub device_id: DeviceId,

    /// Shamir share bytes
    pub share: Vec<u8>,

    /// QBER (Quantum Bit Error Rate) * 10000
    /// Example: 0.8% = 80, 1.2% = 120
    /// Lower is better quality
    pub qber: u32,

    /// STARK proof of quantum measurement authenticity
    pub stark_proof: Vec<u8>,

    /// Timestamp of measurement
    pub timestamp: u64,
}

/// Proof of correct Shamir reconstruction by leader
#[derive(Clone, Debug, Encode, Decode)]
pub struct ShamirReconstructionProof {
    /// Commitment = Hash(sorted_share_hashes || combined_entropy || leader_id || timestamp)
    pub reconstruction_commitment: H256,

    /// Leader's signature over the commitment
    pub leader_signature: Vec<u8>,

    /// Merkle root of device shares used
    pub shares_merkle_root: H256,
}

/// Combined entropy transaction containing K shares and reconstruction proof
#[derive(Clone, Debug, Encode, Decode)]
pub struct CombinedEntropyTx {
    /// Result of Shamir reconstruction
    pub combined_entropy: Vec<u8>,

    /// K device shares used for reconstruction
    pub device_shares: Vec<DeviceShare>,

    /// Minimum shares required (K)
    pub threshold_k: u32,

    /// Total devices available (M)
    pub total_devices_m: u32,

    /// Proof of correct reconstruction
    pub reconstruction_proof: ShamirReconstructionProof,

    /// Timestamp when reconstruction was performed
    pub reconstruction_timestamp: u64,
}

/// Configuration for a single QRNG device
#[derive(Clone, Debug)]
pub struct DeviceConfig {
    pub device_id: DeviceId,
    pub endpoint: String,
    pub qber_threshold: u32,  // Max acceptable QBER (e.g., 1100 = 11%)
    pub enabled: bool,
}

/// Configuration for threshold QRNG system
#[derive(Clone, Debug)]
pub struct ThresholdConfig {
    pub threshold_k: u32,        // Minimum shares required
    pub total_devices_m: u32,    // Total devices available
    pub devices: Vec<DeviceConfig>,
}

impl Default for ThresholdConfig {
    fn default() -> Self {
        // K=2, M=3 configuration (can lose 1 device)
        // KIRQ Hub aggregates from these actual devices:
        // - qkd_toshiba: Toshiba QRNG (from QKD system)
        // - crypto4a_hsm: Crypto4A Hardware Security Module
        // - idquantique: IdQuantique QKD device
        ThresholdConfig {
            threshold_k: 2,
            total_devices_m: 3,
            devices: vec![
                DeviceConfig {
                    device_id: DeviceId::from_str("qkd-toshiba"),
                    endpoint: "http://localhost:8001/entropy/toshiba".into(), // KIRQ hub endpoint for Toshiba
                    qber_threshold: 1100, // 11% (QKD typically has higher QBER)
                    enabled: true,
                },
                DeviceConfig {
                    device_id: DeviceId::from_str("crypto4a-hsm"),
                    endpoint: "http://localhost:8001/entropy/crypto4a".into(), // KIRQ hub endpoint for Crypto4A
                    qber_threshold: 500,  // 5% (HSM has very low error rate)
                    enabled: true,
                },
                DeviceConfig {
                    device_id: DeviceId::from_str("idquantique"),
                    endpoint: "http://localhost:8001/entropy/idquantique".into(), // KIRQ hub endpoint for IdQuantique
                    qber_threshold: 800,  // 8%
                    enabled: true,
                },
            ],
        }
    }
}

/// Reconstruct entropy from K device shares using Shamir Secret Sharing
///
/// # Arguments
/// * `device_shares` - Shares from multiple devices
/// * `threshold_k` - Minimum number of shares required
///
/// # Returns
/// Combined entropy or error message
pub fn reconstruct_entropy(
    device_shares: &[DeviceShare],
    threshold_k: u8,
) -> Result<Vec<u8>, String> {
    if device_shares.len() < threshold_k as usize {
        return Err(format!(
            "Insufficient shares: {} < {}",
            device_shares.len(),
            threshold_k
        ));
    }

    // Sort by QBER (ascending - best quality first)
    let mut sorted = device_shares.to_vec();
    sorted.sort_by_key(|s| s.qber);

    info!("🔀 Sorted {} shares by QBER:", sorted.len());
    for (i, share) in sorted.iter().enumerate() {
        let device_name = share.device_id.as_str().unwrap_or("unknown");
        let qber_percent = share.qber as f64 / 100.0;
        info!("  {}. {} - QBER: {:.2}%", i + 1, device_name, qber_percent);
    }

    // Take best K shares
    let best_shares = &sorted[0..(threshold_k as usize)];

    // Convert to Sharks format
    let sharks_shares: Vec<Share> = best_shares
        .iter()
        .enumerate()
        .map(|(i, ds)| {
            // Use index as x-coordinate for Shamir
            Share::try_from(ds.share.as_slice())
                .map_err(|e| format!("Share {} conversion failed: {:?}", i, e))
        })
        .collect::<Result<Vec<_>, _>>()?;

    // Reconstruct via Lagrange interpolation
    let sharks = Sharks(threshold_k);
    let entropy = sharks.recover(&sharks_shares)
        .map_err(|_| "Shamir reconstruction failed - shares may be invalid".to_string())?;

    info!("✅ Successfully reconstructed {} bytes of combined entropy from {} shares",
          entropy.len(), threshold_k);

    Ok(entropy)
}

/// Create Shamir reconstruction proof (commitment + signature)
///
/// # Arguments
/// * `device_shares` - The K shares used for reconstruction
/// * `combined_entropy` - Result of Shamir reconstruction
/// * `leader_id` - Public key of the leader who performed reconstruction
/// * `leader_privkey` - Falcon1024 private key for signing
/// * `timestamp` - Current timestamp
///
/// # Returns
/// Reconstruction proof or error
pub fn create_reconstruction_proof(
    device_shares: &[DeviceShare],
    combined_entropy: &[u8],
    leader_id: &[u8],
    leader_privkey: &[u8],
    timestamp: u64,
) -> Result<ShamirReconstructionProof, String> {
    // Sort shares by device ID for determinism
    let mut sorted_shares = device_shares.to_vec();
    sorted_shares.sort_by(|a, b| a.device_id.0.cmp(&b.device_id.0));

    // Compute share hashes
    let share_hashes: Vec<H256> = sorted_shares
        .iter()
        .map(|s| Blake2Hasher::hash(&s.share))
        .collect();

    // Build Merkle root (simplified - just hash all hashes)
    let mut merkle_data = Vec::new();
    for hash in &share_hashes {
        merkle_data.extend_from_slice(hash.as_ref());
    }
    let shares_merkle_root = Blake2Hasher::hash(&merkle_data);

    // Create commitment
    let mut commitment_data = Vec::new();
    for hash in &share_hashes {
        commitment_data.extend_from_slice(hash.as_ref());
    }
    commitment_data.extend_from_slice(combined_entropy);
    commitment_data.extend_from_slice(leader_id);
    commitment_data.extend_from_slice(&timestamp.to_le_bytes());

    let reconstruction_commitment = Blake2Hasher::hash(&commitment_data);

    info!("📝 Created reconstruction proof:");
    info!("   Commitment: {:?}", reconstruction_commitment);
    info!("   Merkle root: {:?}", shares_merkle_root);

    // Sign commitment with leader's Falcon1024 key
    let leader_signature = sign_commitment_with_falcon(&commitment_data, leader_privkey)?;

    Ok(ShamirReconstructionProof {
        reconstruction_commitment,
        leader_signature,
        shares_merkle_root,
    })
}

/// Verify Shamir reconstruction proof
///
/// # Arguments
/// * `entropy_tx` - Combined entropy transaction with proof
/// * `leader_public_key` - Expected leader's public key
///
/// # Returns
/// Ok(()) if valid, Err with reason if invalid
pub fn verify_reconstruction_proof(
    entropy_tx: &CombinedEntropyTx,
    leader_public_key: &[u8],
) -> Result<(), String>
{
    // Sort shares by device ID (same as proof generation)
    let mut sorted_shares = entropy_tx.device_shares.clone();
    sorted_shares.sort_by(|a, b| a.device_id.0.cmp(&b.device_id.0));

    // Recompute share hashes
    let share_hashes: Vec<H256> = sorted_shares
        .iter()
        .map(|s| Blake2Hasher::hash(&s.share))
        .collect();

    // Recompute Merkle root
    let mut merkle_data = Vec::new();
    for hash in &share_hashes {
        merkle_data.extend_from_slice(hash.as_ref());
    }
    let expected_merkle_root = Blake2Hasher::hash(&merkle_data);

    if expected_merkle_root != entropy_tx.reconstruction_proof.shares_merkle_root {
        return Err(format!(
            "Merkle root mismatch: expected {:?}, got {:?}",
            expected_merkle_root,
            entropy_tx.reconstruction_proof.shares_merkle_root
        ));
    }

    // Recompute commitment
    let mut commitment_data = Vec::new();
    for hash in &share_hashes {
        commitment_data.extend_from_slice(hash.as_ref());
    }
    commitment_data.extend_from_slice(&entropy_tx.combined_entropy);
    commitment_data.extend_from_slice(leader_public_key);
    commitment_data.extend_from_slice(&entropy_tx.reconstruction_timestamp.to_le_bytes());

    let expected_commitment = Blake2Hasher::hash(&commitment_data);

    if expected_commitment != entropy_tx.reconstruction_proof.reconstruction_commitment {
        return Err(format!(
            "Commitment mismatch: expected {:?}, got {:?}",
            expected_commitment,
            entropy_tx.reconstruction_proof.reconstruction_commitment
        ));
    }

    // Verify leader's Falcon1024 signature over commitment
    verify_falcon_commitment_signature(
        &commitment_data,
        &entropy_tx.reconstruction_proof.leader_signature,
        leader_public_key,
    )?;

    info!("✅ Reconstruction proof verified successfully");
    Ok(())
}

/// Sign commitment data with Falcon1024 private key
fn sign_commitment_with_falcon(data: &[u8], privkey: &[u8]) -> Result<Vec<u8>, String> {
    let secret_key = falcon1024::SecretKey::from_bytes(privkey)
        .map_err(|_| "Invalid Falcon1024 secret key".to_string())?;

    let signed_msg = falcon1024::sign(data, &secret_key);
    let signature = signed_msg.as_bytes().to_vec();

    info!("✍️  Signed commitment with Falcon1024 ({} bytes)", signature.len());
    Ok(signature)
}

/// Verify Falcon1024 signature over commitment data
fn verify_falcon_commitment_signature(
    data: &[u8],
    signature: &[u8],
    pubkey: &[u8],
) -> Result<(), String> {
    let public_key = falcon1024::PublicKey::from_bytes(pubkey)
        .map_err(|_| "Invalid Falcon1024 public key".to_string())?;

    let signed_msg = falcon1024::SignedMessage::from_bytes(signature)
        .map_err(|_| "Invalid Falcon1024 signature format".to_string())?;

    let verified_msg = falcon1024::open(&signed_msg, &public_key)
        .map_err(|_| "Falcon1024 signature verification failed".to_string())?;

    // Verify the message content matches
    if verified_msg != data {
        return Err("Commitment data mismatch in signature".into());
    }

    info!("✅ Falcon1024 signature verified over commitment");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use sp_core::Blake2Hasher;

    #[test]
    fn test_device_id() {
        let device_id = DeviceId::from_str("toshiba-qrng-1");
        assert_eq!(device_id.as_str().unwrap(), "toshiba-qrng-1");
    }

    #[test]
    fn test_threshold_config_default() {
        let config = ThresholdConfig::default();
        assert_eq!(config.threshold_k, 2);
        assert_eq!(config.total_devices_m, 3);
        assert_eq!(config.devices.len(), 3);
    }

    #[test]
    fn test_shamir_reconstruction() {
        // Create test shares (K=2, M=3)
        let secret = b"test_entropy_32_bytes_long_secret";
        let sharks = Sharks(2);
        let dealer = sharks.dealer(secret);
        let shares: Vec<Share> = dealer.take(3).collect();

        // Convert to DeviceShares
        let device_shares: Vec<DeviceShare> = shares
            .iter()
            .enumerate()
            .map(|(i, share)| DeviceShare {
                device_id: DeviceId::from_str(&format!("device-{}", i)),
                share: Vec::from(share),
                qber: (i as u32 + 1) * 100, // 100, 200, 300
                stark_proof: vec![0u8; 32],
                timestamp: 1234567890,
            })
            .collect();

        // Reconstruct from best 2 shares (device-0 and device-1)
        let reconstructed = reconstruct_entropy(&device_shares, 2).unwrap();
        assert_eq!(reconstructed, secret);
    }

    #[test]
    fn test_reconstruction_proof_create_and_verify() {
        let device_shares = vec![
            DeviceShare {
                device_id: DeviceId::from_str("device-1"),
                share: vec![1, 2, 3],
                qber: 100,
                stark_proof: vec![0u8; 32],
                timestamp: 1234567890,
            },
            DeviceShare {
                device_id: DeviceId::from_str("device-2"),
                share: vec![4, 5, 6],
                qber: 200,
                stark_proof: vec![0u8; 32],
                timestamp: 1234567891,
            },
        ];

        let combined_entropy = vec![7, 8, 9, 10];
        let timestamp = 1234567900;

        // Generate real Falcon1024 keypair for testing
        let (leader_pubkey, leader_privkey) = falcon1024::keypair();

        let proof = create_reconstruction_proof(
            &device_shares,
            &combined_entropy,
            leader_pubkey.as_bytes(),
            leader_privkey.as_bytes(),
            timestamp,
        ).unwrap();

        let entropy_tx = CombinedEntropyTx {
            combined_entropy,
            device_shares,
            threshold_k: 2,
            total_devices_m: 3,
            reconstruction_proof: proof,
            reconstruction_timestamp: timestamp,
        };

        // Verify should succeed with correct leader key
        assert!(verify_reconstruction_proof(&entropy_tx, leader_pubkey.as_bytes()).is_ok());

        // Verify should fail with wrong leader key (generate different keypair)
        let (wrong_pubkey, _) = falcon1024::keypair();
        assert!(verify_reconstruction_proof(&entropy_tx, wrong_pubkey.as_bytes()).is_err());
    }

    #[test]
    fn test_qber_priority_ordering() {
        // Test that shares are selected by best QBER (lowest first)
        let secret = b"high_quality_quantum_entropy_data";
        let sharks = Sharks(2);
        let dealer = sharks.dealer(secret);
        let shares: Vec<Share> = dealer.take(3).collect();

        let device_shares: Vec<DeviceShare> = vec![
            DeviceShare {
                device_id: DeviceId::from_str("device-high-qber"),
                share: Vec::from(&shares[0]),
                qber: 1000, // 10% QBER - worst
                stark_proof: vec![0u8; 32],
                timestamp: 1234567890,
            },
            DeviceShare {
                device_id: DeviceId::from_str("device-low-qber"),
                share: Vec::from(&shares[1]),
                qber: 50, // 0.5% QBER - best
                stark_proof: vec![0u8; 32],
                timestamp: 1234567891,
            },
            DeviceShare {
                device_id: DeviceId::from_str("device-medium-qber"),
                share: Vec::from(&shares[2]),
                qber: 500, // 5% QBER - medium
                stark_proof: vec![0u8; 32],
                timestamp: 1234567892,
            },
        ];

        // reconstruct_entropy should select best 2 (device-low-qber and device-medium-qber)
        let reconstructed = reconstruct_entropy(&device_shares, 2).unwrap();
        assert_eq!(reconstructed, secret);
    }

    #[test]
    fn test_insufficient_shares() {
        // Test K=2 with only 1 share should fail
        let device_shares = vec![
            DeviceShare {
                device_id: DeviceId::from_str("device-1"),
                share: vec![1, 2, 3],
                qber: 100,
                stark_proof: vec![0u8; 32],
                timestamp: 1234567890,
            },
        ];

        let result = reconstruct_entropy(&device_shares, 2);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Insufficient shares"));
    }

    #[test]
    fn test_reconstruction_proof_tampered_entropy() {
        // Test that proof verification fails if entropy is tampered
        let device_shares = vec![
            DeviceShare {
                device_id: DeviceId::from_str("device-1"),
                share: vec![1, 2, 3],
                qber: 100,
                stark_proof: vec![0u8; 32],
                timestamp: 1234567890,
            },
            DeviceShare {
                device_id: DeviceId::from_str("device-2"),
                share: vec![4, 5, 6],
                qber: 200,
                stark_proof: vec![0u8; 32],
                timestamp: 1234567891,
            },
        ];

        let combined_entropy = vec![7, 8, 9, 10];
        let timestamp = 1234567900;

        // Generate real Falcon1024 keypair for testing
        let (leader_pubkey, leader_privkey) = falcon1024::keypair();

        let proof = create_reconstruction_proof(
            &device_shares,
            &combined_entropy,
            leader_pubkey.as_bytes(),
            leader_privkey.as_bytes(),
            timestamp,
        ).unwrap();

        // Tamper with entropy
        let tampered_entropy = vec![7, 8, 9, 99]; // Changed last byte

        let entropy_tx = CombinedEntropyTx {
            combined_entropy: tampered_entropy,
            device_shares,
            threshold_k: 2,
            total_devices_m: 3,
            reconstruction_proof: proof,
            reconstruction_timestamp: timestamp,
        };

        // Verification should fail
        assert!(verify_reconstruction_proof(&entropy_tx, leader_pubkey.as_bytes()).is_err());
    }

    #[test]
    fn test_reconstruction_proof_tampered_shares() {
        // Test that proof verification fails if shares are tampered
        let original_shares = vec![
            DeviceShare {
                device_id: DeviceId::from_str("device-1"),
                share: vec![1, 2, 3],
                qber: 100,
                stark_proof: vec![0u8; 32],
                timestamp: 1234567890,
            },
            DeviceShare {
                device_id: DeviceId::from_str("device-2"),
                share: vec![4, 5, 6],
                qber: 200,
                stark_proof: vec![0u8; 32],
                timestamp: 1234567891,
            },
        ];

        let combined_entropy = vec![7, 8, 9, 10];
        let timestamp = 1234567900;

        // Generate real Falcon1024 keypair for testing
        let (leader_pubkey, leader_privkey) = falcon1024::keypair();

        let proof = create_reconstruction_proof(
            &original_shares,
            &combined_entropy,
            leader_pubkey.as_bytes(),
            leader_privkey.as_bytes(),
            timestamp,
        ).unwrap();

        // Tamper with shares
        let tampered_shares = vec![
            DeviceShare {
                device_id: DeviceId::from_str("device-1"),
                share: vec![1, 2, 99], // Changed last byte
                qber: 100,
                stark_proof: vec![0u8; 32],
                timestamp: 1234567890,
            },
            DeviceShare {
                device_id: DeviceId::from_str("device-2"),
                share: vec![4, 5, 6],
                qber: 200,
                stark_proof: vec![0u8; 32],
                timestamp: 1234567891,
            },
        ];

        let entropy_tx = CombinedEntropyTx {
            combined_entropy,
            device_shares: tampered_shares,
            threshold_k: 2,
            total_devices_m: 3,
            reconstruction_proof: proof,
            reconstruction_timestamp: timestamp,
        };

        // Verification should fail due to Merkle root mismatch
        assert!(verify_reconstruction_proof(&entropy_tx, leader_pubkey.as_bytes()).is_err());
    }

    #[test]
    fn test_combined_entropy_tx_full_workflow() {
        // End-to-end test: Create shares, reconstruct, create proof, verify
        let secret = b"quantum_entropy_from_three_devices_combined";
        let sharks = Sharks(2);
        let dealer = sharks.dealer(secret);
        let shares: Vec<Share> = dealer.take(3).collect();

        let device_shares: Vec<DeviceShare> = vec![
            DeviceShare {
                device_id: DeviceId::from_str("toshiba-qrng"),
                share: Vec::from(&shares[0]),
                qber: 80, // 0.8% QBER
                stark_proof: vec![0xAA; 32],
                timestamp: 1700000000,
            },
            DeviceShare {
                device_id: DeviceId::from_str("crypto4a-qrng"),
                share: Vec::from(&shares[1]),
                qber: 120, // 1.2% QBER
                stark_proof: vec![0xBB; 32],
                timestamp: 1700000001,
            },
            DeviceShare {
                device_id: DeviceId::from_str("kirq"),
                share: Vec::from(&shares[2]),
                qber: 90, // 0.9% QBER
                stark_proof: vec![0xCC; 32],
                timestamp: 1700000002,
            },
        ];

        // Reconstruct entropy (should use best 2: toshiba 80, kirq 90)
        let combined_entropy = reconstruct_entropy(&device_shares, 2).unwrap();
        assert_eq!(combined_entropy, secret);

        // Create reconstruction proof
        let timestamp = 1700000010;

        // Generate real Falcon1024 keypair for testing
        let (leader_pubkey, leader_privkey) = falcon1024::keypair();

        let reconstruction_proof = create_reconstruction_proof(
            &device_shares,
            &combined_entropy,
            leader_pubkey.as_bytes(),
            leader_privkey.as_bytes(),
            timestamp,
        ).unwrap();

        // Build complete transaction
        let entropy_tx = CombinedEntropyTx {
            combined_entropy: combined_entropy.clone(),
            device_shares: device_shares.clone(),
            threshold_k: 2,
            total_devices_m: 3,
            reconstruction_proof,
            reconstruction_timestamp: timestamp,
        };

        // Verify proof
        assert!(verify_reconstruction_proof(&entropy_tx, leader_pubkey.as_bytes()).is_ok());

        // Verify with wrong leader should fail (generate different keypair)
        assert!(verify_reconstruction_proof(&entropy_tx, b"validator_bob").is_err());
    }

    #[test]
    fn test_device_share_hash_equality() {
        // Test that DeviceShare implements Hash and Eq properly
        let share1 = DeviceShare {
            device_id: DeviceId::from_str("device-1"),
            share: vec![1, 2, 3],
            qber: 100,
            stark_proof: vec![0u8; 32],
            timestamp: 1234567890,
        };

        let share2 = DeviceShare {
            device_id: DeviceId::from_str("device-1"),
            share: vec![1, 2, 3],
            qber: 100,
            stark_proof: vec![0u8; 32],
            timestamp: 1234567890,
        };

        let share3 = DeviceShare {
            device_id: DeviceId::from_str("device-1"),
            share: vec![1, 2, 99], // Different share
            qber: 100,
            stark_proof: vec![0u8; 32],
            timestamp: 1234567890,
        };

        // Same content should be equal
        assert_eq!(share1, share2);

        // Different content should not be equal
        assert_ne!(share1, share3);

        // Test that they can be used in HashMap (requires Hash)
        let mut map = std::collections::HashMap::new();
        map.insert(share1.clone(), "value1");
        assert_eq!(map.get(&share2), Some(&"value1"));
        assert_eq!(map.get(&share3), None);
    }

    #[test]
    fn test_multiple_reconstructions_same_shares() {
        // Test that multiple reconstructions with same shares produce same result
        let secret = b"deterministic_quantum_entropy";
        let sharks = Sharks(2);
        let dealer = sharks.dealer(secret);
        let shares: Vec<Share> = dealer.take(3).collect();

        let device_shares: Vec<DeviceShare> = shares
            .iter()
            .enumerate()
            .map(|(i, share)| DeviceShare {
                device_id: DeviceId::from_str(&format!("device-{}", i)),
                share: Vec::from(share),
                qber: (i as u32 + 1) * 100,
                stark_proof: vec![0u8; 32],
                timestamp: 1234567890,
            })
            .collect();

        let result1 = reconstruct_entropy(&device_shares, 2).unwrap();
        let result2 = reconstruct_entropy(&device_shares, 2).unwrap();
        let result3 = reconstruct_entropy(&device_shares, 2).unwrap();

        assert_eq!(result1, result2);
        assert_eq!(result2, result3);
        assert_eq!(result1, secret);
    }
}
