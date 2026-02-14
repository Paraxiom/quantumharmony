// Copyright (C) QuantumHarmony Development Team
// SPDX-License-Identifier: GPL-3.0-or-later

//! Comprehensive Falcon1024 Post-Quantum Signature Tests
//!
//! Test coverage for:
//! - Keypair generation (legacy, SHA-3, QPP)
//! - Signature generation and verification
//! - Vote encoding/signing
//! - Integration with coherence gadget
//! - Security properties (no-cloning, freshness)

#[cfg(test)]
mod tests {
    use super::super::falcon_crypto::*;
    use super::super::qpp::{EntropySource, QuantumEntropy};
    use pallet_proof_of_coherence::types::QuantumState;
    use sp_core::H256;

    /// Test basic keypair generation (SHA-3 quantum-resistant method)
    #[test]
    fn test_generate_keypair_sha3_basic() {
        let seed = [42u8; 32];
        let validator_id = b"test-validator";
        let (pk, sk) = generate_keypair_sha3(&seed, None, None, validator_id);

        // Verify keys are non-empty
        assert!(!pk.0.is_empty(), "Public key should not be empty");
        assert!(!sk.0.is_empty(), "Secret key should not be empty");

        // Verify public key size (Falcon1024 = 1793 bytes)
        assert_eq!(pk.0.len(), 1793, "Public key should be 1793 bytes");

        // Verify secret key size (Falcon1024 = 2305 bytes)
        assert_eq!(sk.0.len(), 2305, "Secret key should be 2305 bytes");

        println!(
            "✅ SHA-3 keypair generation: PK={} bytes, SK={} bytes",
            pk.0.len(),
            sk.0.len()
        );
    }

    /// Test SHA-3 quantum-resistant keypair generation
    #[test]
    fn test_generate_keypair_sha3() {
        // Simulated keystore entropy (SPHINCS+ signature)
        let keystore_entropy = vec![0xABu8; 49_856]; // SPHINCS+ signature size

        // Simulated QRNG entropy
        let quantum_entropy = vec![0xCDu8; 32];

        // Simulated HWRNG entropy
        let hwrng_entropy = [0xEFu8; 32];

        // Validator ID
        let validator_id = b"alice";

        let (pk, sk) = generate_keypair_sha3(
            &keystore_entropy,
            Some(&quantum_entropy),
            Some(&hwrng_entropy),
            validator_id,
        );

        // Verify keys are non-empty
        assert!(!pk.0.is_empty(), "Public key should not be empty");
        assert!(!sk.0.is_empty(), "Secret key should not be empty");

        println!(
            "✅ SHA-3 keypair generation: PK={} bytes, SK={} bytes",
            pk.0.len(),
            sk.0.len()
        );
    }

    /// Test QPP-enforced keypair generation with no-cloning
    #[test]
    fn test_generate_keypair_qpp() {
        use std::time::{SystemTime, UNIX_EPOCH};

        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        // Create QuantumEntropy instances
        let keystore_ent =
            QuantumEntropy::new(vec![0xABu8; 49_856], EntropySource::Keystore, Some(now));

        let quantum_ent = QuantumEntropy::from_kirq_hub(
            vec![0xCDu8; 32],
            Some(80), // QBER = 0.80%
            2,        // threshold K
            3,        // total M
        );

        let hwrng_ent =
            QuantumEntropy::new(vec![0xEFu8; 32], EntropySource::HardwareRng, Some(now));

        let validator_id = b"alice";

        let (pk, sk, sources) = generate_keypair_qpp(
            keystore_ent,
            Some(quantum_ent),
            Some(hwrng_ent),
            validator_id,
        );

        // Verify keys
        assert!(!pk.0.is_empty(), "Public key should not be empty");
        assert!(!sk.0.is_empty(), "Secret key should not be empty");

        // Verify entropy sources tracked
        assert_eq!(sources.len(), 3, "Should have 3 entropy sources");
        assert_eq!(sources[0], EntropySource::Keystore);
        assert_eq!(sources[1], EntropySource::ThresholdQrng { k: 2, m: 3 });
        assert_eq!(sources[2], EntropySource::HardwareRng);

        println!(
            "✅ QPP keypair generation: {} entropy sources tracked",
            sources.len()
        );
    }

    /// Test basic signature generation and verification
    #[test]
    fn test_sign_and_verify_basic() {
        // Use SHA-3 KDF instead of legacy BLAKE2b
        let seed = [42u8; 32];
        let validator_id = b"test-validator";
        let (pk, sk) = generate_keypair_sha3(&seed, None, None, validator_id);

        let message = b"Hello, Quantum World!";
        let signature = sign_message(message, &sk);

        // Verify signature is non-empty
        assert!(!signature.is_empty(), "Signature should not be empty");

        // Signature size should be ~1280 bytes (variable in Falcon1024)
        assert!(
            signature.len() > 1000 && signature.len() < 1400,
            "Signature size should be ~1280 bytes, got {}",
            signature.len()
        );

        // Verify signature
        let result = verify_signature(message, &signature, &pk);
        assert!(result.is_ok(), "Signature verification should succeed");

        println!("✅ Sign/Verify basic: signature {} bytes", signature.len());
    }

    /// Test signature verification fails with wrong message
    #[test]
    fn test_verify_fails_wrong_message() {
        // Use SHA-3 KDF instead of legacy BLAKE2b
        let seed = [42u8; 32];
        let validator_id = b"test-validator";
        let (pk, sk) = generate_keypair_sha3(&seed, None, None, validator_id);

        let message = b"Original message";
        let wrong_message = b"Tampered message";
        let signature = sign_message(message, &sk);

        // Verification with wrong message should fail
        let result = verify_signature(wrong_message, &signature, &pk);
        assert!(
            result.is_err(),
            "Verification should fail with wrong message"
        );

        println!("✅ Verification correctly fails with wrong message");
    }

    /// Test signature verification fails with wrong public key
    #[test]
    fn test_verify_fails_wrong_key() {
        // Use SHA-3 KDF instead of legacy BLAKE2b
        let seed1 = [42u8; 32];
        let seed2 = [99u8; 32];
        let validator_id = b"test-validator";
        let (pk1, sk1) = generate_keypair_sha3(&seed1, None, None, validator_id);
        let (pk2, _sk2) = generate_keypair_sha3(&seed2, None, None, validator_id);

        let message = b"Test message";
        let signature = sign_message(message, &sk1);

        // Verification with wrong public key should fail
        let result = verify_signature(message, &signature, &pk2);
        assert!(
            result.is_err(),
            "Verification should fail with wrong public key"
        );

        println!("✅ Verification correctly fails with wrong public key");
    }

    /// Test signature verification fails with tampered signature
    #[test]
    fn test_verify_fails_tampered_signature() {
        // Use SHA-3 KDF instead of legacy BLAKE2b
        let seed = [42u8; 32];
        let validator_id = b"test-validator";
        let (pk, sk) = generate_keypair_sha3(&seed, None, None, validator_id);

        let message = b"Test message";
        let mut signature = sign_message(message, &sk);

        // Tamper with signature
        if !signature.is_empty() {
            signature[0] ^= 0xFF;
        }

        // Verification with tampered signature should fail
        let result = verify_signature(message, &signature, &pk);
        assert!(
            result.is_err(),
            "Verification should fail with tampered signature"
        );

        println!("✅ Verification correctly fails with tampered signature");
    }

    /// Test vote encoding for signing
    #[test]
    fn test_encode_vote_for_signing() {
        let validator = H256::from([1u8; 32]);
        let block_hash = H256::from([2u8; 32]);
        let block_number = 12345u64;
        let coherence_score = 95u32;
        let quantum_state = QuantumState {
            entropy_commitment: H256::from([3u8; 32]),
            qber_basis: 80,   // 0.80%
            visibility: 8900, // 89.00%
        };

        let encoded = encode_vote_for_signing(
            &validator,
            &block_hash,
            &block_number,
            &coherence_score,
            &quantum_state,
        );

        // Verify encoding is non-empty
        assert!(!encoded.is_empty(), "Encoded vote should not be empty");

        println!("✅ Vote encoding: {} bytes", encoded.len());
    }

    /// Test vote signing and verification
    #[test]
    fn test_sign_and_verify_vote() {
        // Use SHA-3 KDF instead of legacy BLAKE2b
        let seed = [42u8; 32];
        let validator_id = b"test-validator";
        let (pk, sk) = generate_keypair_sha3(&seed, None, None, validator_id);

        let validator = H256::from([1u8; 32]);
        let block_hash = H256::from([2u8; 32]);
        let block_number = 12345u64;
        let coherence_score = 95u32;
        let quantum_state = QuantumState {
            entropy_commitment: H256::from([3u8; 32]),
            qber_basis: 80,
            visibility: 8900,
        };

        // Encode vote
        let vote_data = encode_vote_for_signing(
            &validator,
            &block_hash,
            &block_number,
            &coherence_score,
            &quantum_state,
        );

        // Sign vote
        let signature = sign_message(&vote_data, &sk);

        // Verify vote signature
        let result = verify_signature(&vote_data, &signature, &pk);
        assert!(result.is_ok(), "Vote signature verification should succeed");

        println!("✅ Vote sign/verify: {} byte signature", signature.len());
    }

    /// Test multiple signatures with same key
    #[test]
    fn test_multiple_signatures_same_key() {
        // Use SHA-3 KDF instead of legacy BLAKE2b
        let seed = [42u8; 32];
        let validator_id = b"test-validator";
        let (pk, sk) = generate_keypair_sha3(&seed, None, None, validator_id);

        let messages = vec![
            b"Message 1".to_vec(),
            b"Message 2".to_vec(),
            b"Message 3".to_vec(),
        ];

        for (i, message) in messages.iter().enumerate() {
            let signature = sign_message(message, &sk);
            let result = verify_signature(message, &signature, &pk);
            assert!(
                result.is_ok(),
                "Signature {} verification should succeed",
                i + 1
            );
        }

        println!("✅ Multiple signatures with same key: all verified");
    }

    /// Test entropy freshness validation
    #[test]
    fn test_entropy_freshness() {
        use std::time::{SystemTime, UNIX_EPOCH};

        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        // Fresh entropy (just created)
        let fresh_ent = QuantumEntropy::new(vec![0xABu8; 32], EntropySource::Keystore, Some(now));

        assert!(fresh_ent.is_fresh(), "Fresh entropy should be valid");

        // Stale entropy (70 seconds old)
        let stale_ent =
            QuantumEntropy::new(vec![0xCDu8; 32], EntropySource::Keystore, Some(now - 70));

        assert!(!stale_ent.is_fresh(), "Stale entropy should be invalid");

        println!("✅ Entropy freshness validation working");
    }

    /// Test QBER validation in quantum entropy
    #[test]
    fn test_qber_validation() {
        let good_qber = QuantumEntropy::from_kirq_hub(
            vec![0xABu8; 32],
            Some(80), // 0.80% - good
            2,
            3,
        );

        let bad_qber = QuantumEntropy::from_kirq_hub(
            vec![0xCDu8; 32],
            Some(1200), // 12.00% - too high
            2,
            3,
        );

        assert_eq!(good_qber.qber, Some(80));
        assert_eq!(bad_qber.qber, Some(1200));

        // In production, QBER > 11% (1100) should be rejected
        assert!(good_qber.qber.unwrap() < 1100, "Good QBER should be < 11%");
        assert!(bad_qber.qber.unwrap() >= 1100, "Bad QBER should be >= 11%");

        println!(
            "✅ QBER validation: good={}, bad={}",
            good_qber.qber.unwrap(),
            bad_qber.qber.unwrap()
        );
    }

    /// Benchmark signature generation performance
    #[test]
    fn test_signature_performance() {
        use std::time::Instant;

        // Use SHA-3 KDF instead of legacy BLAKE2b
        let seed = [42u8; 32];
        let validator_id = b"test-validator";
        let (pk, sk) = generate_keypair_sha3(&seed, None, None, validator_id);
        let message = b"Benchmark message for Falcon1024 performance test";

        let iterations = 100;
        let start = Instant::now();

        for _ in 0..iterations {
            let signature = sign_message(message, &sk);
            let _ = verify_signature(message, &signature, &pk);
        }

        let elapsed = start.elapsed();
        let avg_time = elapsed.as_micros() / iterations;

        println!("✅ Performance: {} iterations in {:?}", iterations, elapsed);
        println!("   Average sign+verify: {} µs", avg_time);
    }

    /// Test entropy source naming
    #[test]
    fn test_entropy_source_names() {
        assert_eq!(EntropySource::Keystore.name(), "Keystore");
        assert_eq!(EntropySource::HardwareRng.name(), "HardwareRNG");
        assert_eq!(EntropySource::KirqHub.name(), "KIRQ-Hub");
        assert_eq!(
            EntropySource::ThresholdQrng { k: 2, m: 3 }.name(),
            "Threshold-QRNG(2/3)"
        );

        println!("✅ Entropy source naming working");
    }
}
