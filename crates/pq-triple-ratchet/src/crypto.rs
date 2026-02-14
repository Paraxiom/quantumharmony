//! Low-level cryptographic primitives for the protocol.

use chacha20poly1305::{
    aead::{Aead, KeyInit},
    ChaCha20Poly1305, Nonce,
};
use hkdf::Hkdf;
use hmac::{digest::KeyInit as HmacKeyInit, Hmac, Mac};
use sha2::Sha256;
use zeroize::Zeroize;

use crate::error::{Error, Result};

/// ChaCha20-Poly1305 key size
pub const AEAD_KEY_SIZE: usize = 32;
/// ChaCha20-Poly1305 nonce size
pub const AEAD_NONCE_SIZE: usize = 12;
/// ChaCha20-Poly1305 tag size
pub const AEAD_TAG_SIZE: usize = 16;
/// HKDF output size for chain keys
pub const CHAIN_KEY_SIZE: usize = 32;
/// Root key size
pub const ROOT_KEY_SIZE: usize = 32;

/// Derive keys using HKDF-SHA256.
///
/// # Arguments
/// * `ikm` - Input keying material
/// * `salt` - Optional salt (use None for X3DH, Some for ratchet)
/// * `info` - Context info string
/// * `output` - Output buffer to fill
pub fn hkdf_derive(ikm: &[u8], salt: Option<&[u8]>, info: &[u8], output: &mut [u8]) -> Result<()> {
    let hk = Hkdf::<Sha256>::new(salt, ikm);
    hk.expand(info, output)
        .map_err(|_| Error::KeyGeneration("HKDF expansion failed".into()))
}

/// Derive multiple keys from input keying material.
///
/// Returns (root_key, chain_key) for ratchet operations.
pub fn kdf_rk(
    root_key: &[u8; ROOT_KEY_SIZE],
    dh_output: &[u8],
) -> ([u8; ROOT_KEY_SIZE], [u8; CHAIN_KEY_SIZE]) {
    let mut output = [0u8; ROOT_KEY_SIZE + CHAIN_KEY_SIZE];
    hkdf_derive(dh_output, Some(root_key), b"QuantumHarmony_RK", &mut output)
        .expect("HKDF should not fail with correct sizes");

    let mut new_root = [0u8; ROOT_KEY_SIZE];
    let mut chain_key = [0u8; CHAIN_KEY_SIZE];
    new_root.copy_from_slice(&output[..ROOT_KEY_SIZE]);
    chain_key.copy_from_slice(&output[ROOT_KEY_SIZE..]);

    output.zeroize();
    (new_root, chain_key)
}

/// Derive message keys from chain key.
///
/// Returns (new_chain_key, message_key).
pub fn kdf_ck(chain_key: &[u8; CHAIN_KEY_SIZE]) -> ([u8; CHAIN_KEY_SIZE], [u8; AEAD_KEY_SIZE]) {
    // Use HMAC for chain key derivation (Signal protocol style)
    let mut mac: Hmac<Sha256> =
        HmacKeyInit::new_from_slice(chain_key).expect("HMAC accepts any key size");
    mac.update(&[0x01]); // Constant for new chain key
    let new_chain = mac.finalize().into_bytes();

    let mut mac: Hmac<Sha256> =
        HmacKeyInit::new_from_slice(chain_key).expect("HMAC accepts any key size");
    mac.update(&[0x02]); // Constant for message key
    let message_key = mac.finalize().into_bytes();

    let mut new_chain_arr = [0u8; CHAIN_KEY_SIZE];
    let mut message_key_arr = [0u8; AEAD_KEY_SIZE];
    new_chain_arr.copy_from_slice(&new_chain);
    message_key_arr.copy_from_slice(&message_key);

    (new_chain_arr, message_key_arr)
}

/// Encrypt data using ChaCha20-Poly1305.
///
/// # Arguments
/// * `key` - 32-byte encryption key
/// * `nonce` - 12-byte nonce (must be unique per key)
/// * `plaintext` - Data to encrypt
/// * `aad` - Additional authenticated data
pub fn aead_encrypt(
    key: &[u8; AEAD_KEY_SIZE],
    nonce: &[u8; AEAD_NONCE_SIZE],
    plaintext: &[u8],
    aad: &[u8],
) -> Result<Vec<u8>> {
    let cipher = ChaCha20Poly1305::new_from_slice(key)
        .map_err(|_| Error::Encryption("invalid key".into()))?;

    let nonce = Nonce::from_slice(nonce);

    cipher
        .encrypt(
            nonce,
            chacha20poly1305::aead::Payload {
                msg: plaintext,
                aad,
            },
        )
        .map_err(|e| Error::Encryption(format!("AEAD encryption failed: {}", e)))
}

/// Decrypt data using ChaCha20-Poly1305.
///
/// # Arguments
/// * `key` - 32-byte encryption key
/// * `nonce` - 12-byte nonce
/// * `ciphertext` - Data to decrypt (includes tag)
/// * `aad` - Additional authenticated data (must match encryption)
pub fn aead_decrypt(
    key: &[u8; AEAD_KEY_SIZE],
    nonce: &[u8; AEAD_NONCE_SIZE],
    ciphertext: &[u8],
    aad: &[u8],
) -> Result<Vec<u8>> {
    let cipher = ChaCha20Poly1305::new_from_slice(key)
        .map_err(|_| Error::Decryption("invalid key".into()))?;

    let nonce = Nonce::from_slice(nonce);

    cipher
        .decrypt(
            nonce,
            chacha20poly1305::aead::Payload {
                msg: ciphertext,
                aad,
            },
        )
        .map_err(|_| {
            Error::Decryption(
                "AEAD decryption failed (bad key, corrupted data, or tampering)".into(),
            )
        })
}

/// Perform X25519 Diffie-Hellman.
pub fn x25519_dh(secret: &[u8; 32], public: &[u8; 32]) -> [u8; 32] {
    let secret = x25519_dalek::StaticSecret::from(*secret);
    let public = x25519_dalek::PublicKey::from(*public);
    *secret.diffie_hellman(&public).as_bytes()
}

// ============================================================================
// ML-KEM Security Level Configuration
// ============================================================================

/// ML-KEM security level for configurable key exchange
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KemSecurityLevel {
    /// NIST Level 3 - 128-bit quantum security (default)
    Level3_ML_KEM768,
    /// NIST Level 5 - 256-bit quantum security (high-security contexts)
    Level5_ML_KEM1024,
}

impl KemSecurityLevel {
    /// Get the security level from string name
    pub fn from_str(s: &str) -> Option<Self> {
        match s.to_lowercase().as_str() {
            "ml-kem-768" | "mlkem768" | "level3" | "3" => Some(Self::Level3_ML_KEM768),
            "ml-kem-1024" | "mlkem1024" | "level5" | "5" => Some(Self::Level5_ML_KEM1024),
            _ => None,
        }
    }

    /// Get the name of this security level
    pub fn name(&self) -> &'static str {
        match self {
            Self::Level3_ML_KEM768 => "ML-KEM-768",
            Self::Level5_ML_KEM1024 => "ML-KEM-1024",
        }
    }

    /// Check if this is the high-security Level 5
    pub fn is_high_security(&self) -> bool {
        matches!(self, Self::Level5_ML_KEM1024)
    }
}

impl Default for KemSecurityLevel {
    fn default() -> Self {
        Self::Level3_ML_KEM768
    }
}

/// ML-KEM key sizes for different security levels
pub mod kem_sizes {
    /// ML-KEM-768 (Level 3) - Public key size
    pub const ML_KEM_768_PUBLIC_KEY_SIZE: usize = 1184;
    /// ML-KEM-768 (Level 3) - Secret key size
    pub const ML_KEM_768_SECRET_KEY_SIZE: usize = 2400;
    /// ML-KEM-768 (Level 3) - Ciphertext size
    pub const ML_KEM_768_CIPHERTEXT_SIZE: usize = 1088;
    /// ML-KEM-768 (Level 3) - Shared secret size
    pub const ML_KEM_768_SHARED_SECRET_SIZE: usize = 32;

    /// ML-KEM-1024 (Level 5) - Public key size
    pub const ML_KEM_1024_PUBLIC_KEY_SIZE: usize = 1568;
    /// ML-KEM-1024 (Level 5) - Secret key size
    pub const ML_KEM_1024_SECRET_KEY_SIZE: usize = 3168;
    /// ML-KEM-1024 (Level 5) - Ciphertext size
    pub const ML_KEM_1024_CIPHERTEXT_SIZE: usize = 1568;
    /// ML-KEM-1024 (Level 5) - Shared secret size
    pub const ML_KEM_1024_SHARED_SECRET_SIZE: usize = 32;
}

/// Detect the ML-KEM security level from public key size
pub fn detect_kem_level(public_key: &[u8]) -> Option<KemSecurityLevel> {
    match public_key.len() {
        kem_sizes::ML_KEM_768_PUBLIC_KEY_SIZE => Some(KemSecurityLevel::Level3_ML_KEM768),
        kem_sizes::ML_KEM_1024_PUBLIC_KEY_SIZE => Some(KemSecurityLevel::Level5_ML_KEM1024),
        _ => None,
    }
}

/// Detect the ML-KEM security level from secret key size
pub fn detect_kem_level_from_secret(secret_key: &[u8]) -> Option<KemSecurityLevel> {
    match secret_key.len() {
        kem_sizes::ML_KEM_768_SECRET_KEY_SIZE => Some(KemSecurityLevel::Level3_ML_KEM768),
        kem_sizes::ML_KEM_1024_SECRET_KEY_SIZE => Some(KemSecurityLevel::Level5_ML_KEM1024),
        _ => None,
    }
}

/// Detect the ML-KEM security level from ciphertext size
pub fn detect_kem_level_from_ciphertext(ciphertext: &[u8]) -> Option<KemSecurityLevel> {
    match ciphertext.len() {
        kem_sizes::ML_KEM_768_CIPHERTEXT_SIZE => Some(KemSecurityLevel::Level3_ML_KEM768),
        kem_sizes::ML_KEM_1024_CIPHERTEXT_SIZE => Some(KemSecurityLevel::Level5_ML_KEM1024),
        _ => None,
    }
}

/// Unified ML-KEM encapsulate function that supports both 768 and 1024
///
/// # Arguments
/// * `public_key` - ML-KEM public key (detects level automatically)
/// * `security_level` - Optional explicit security level (auto-detected if None)
///
/// Returns (shared_secret, ciphertext)
pub fn mlkem_encapsulate_ex(
    public_key: &[u8],
    security_level: Option<KemSecurityLevel>,
) -> Result<(Vec<u8>, Vec<u8>)> {
    // Auto-detect security level if not specified
    let level = security_level.unwrap_or_else(|| {
        detect_kem_level(public_key).unwrap_or(KemSecurityLevel::Level3_ML_KEM768)
    });

    match level {
        KemSecurityLevel::Level3_ML_KEM768 => mlkem768_encapsulate(public_key),
        KemSecurityLevel::Level5_ML_KEM1024 => mlkem1024_encapsulate(public_key),
    }
}

/// Unified ML-KEM decapsulate function that supports both 768 and 1024
///
/// # Arguments
/// * `secret_key` - ML-KEM secret key (detects level automatically)
/// * `ciphertext` - ML-KEM ciphertext
/// * `security_level` - Optional explicit security level (auto-detected if None)
pub fn mlkem_decapsulate_ex(
    secret_key: &[u8],
    ciphertext: &[u8],
    security_level: Option<KemSecurityLevel>,
) -> Result<Vec<u8>> {
    // Auto-detect security level if not specified
    let level = security_level.unwrap_or_else(|| {
        detect_kem_level_from_secret(secret_key)
            .or_else(|| detect_kem_level_from_ciphertext(ciphertext))
            .unwrap_or(KemSecurityLevel::Level3_ML_KEM768)
    });

    match level {
        KemSecurityLevel::Level3_ML_KEM768 => mlkem768_decapsulate(secret_key, ciphertext),
        KemSecurityLevel::Level5_ML_KEM1024 => mlkem1024_decapsulate(secret_key, ciphertext),
    }
}

/// Encapsulate using ML-KEM-768 (Level 3 - 128-bit quantum security).
///
/// Returns (shared_secret, ciphertext).
#[deprecated(
    since = "0.2.0",
    note = "Use mlkem_encapsulate_ex() for configurable security level"
)]
pub fn mlkem_encapsulate(public_key: &[u8]) -> Result<(Vec<u8>, Vec<u8>)> {
    mlkem768_encapsulate(public_key)
}

/// Decapsulate using ML-KEM-768 (Level 3).
///
/// Returns shared_secret.
#[deprecated(
    since = "0.2.0",
    note = "Use mlkem_decapsulate_ex() for configurable security level"
)]
pub fn mlkem_decapsulate(secret_key: &[u8], ciphertext: &[u8]) -> Result<Vec<u8>> {
    mlkem768_decapsulate(secret_key, ciphertext)
}

/// Encapsulate using ML-KEM-768 (Level 3 - 128-bit quantum security).
///
/// Returns (shared_secret, ciphertext).
pub fn mlkem768_encapsulate(public_key: &[u8]) -> Result<(Vec<u8>, Vec<u8>)> {
    use kem::Encapsulate;
    use ml_kem::kem::EncapsulationKey as EK;
    use ml_kem::{EncodedSizeUser, MlKem768Params};

    let mut rng = rand::thread_rng();

    // Parse public key
    let ek_array: ml_kem::Encoded<EK<MlKem768Params>> = public_key
        .try_into()
        .map_err(|_| Error::KeyExchange("invalid ML-KEM-768 public key size".into()))?;
    let ek = EK::<MlKem768Params>::from_bytes(&ek_array);

    // Encapsulate - returns (Ciphertext, SharedSecret)
    let (ct, ss) = ek
        .encapsulate(&mut rng)
        .map_err(|_| Error::KeyExchange("ML-KEM-768 encapsulation failed".into()))?;

    // Convert to Vec<u8> - both are hybrid_array::Array types
    Ok((ss.as_slice().to_vec(), ct.as_slice().to_vec()))
}

/// Decapsulate using ML-KEM-768 (Level 3).
///
/// Returns shared_secret.
pub fn mlkem768_decapsulate(secret_key: &[u8], ciphertext: &[u8]) -> Result<Vec<u8>> {
    use kem::Decapsulate;
    use ml_kem::kem::DecapsulationKey as DK;
    use ml_kem::{EncodedSizeUser, MlKem768Params};

    // ML-KEM-768 ciphertext size is 1088 bytes
    const CIPHERTEXT_SIZE: usize = 1088;

    // Parse secret key
    let dk_array: ml_kem::Encoded<DK<MlKem768Params>> = secret_key
        .try_into()
        .map_err(|_| Error::KeyExchange("invalid ML-KEM-768 secret key size".into()))?;
    let dk = DK::<MlKem768Params>::from_bytes(&dk_array);

    // Parse ciphertext - it's just a byte array
    if ciphertext.len() != CIPHERTEXT_SIZE {
        return Err(Error::KeyExchange(format!(
            "invalid ML-KEM-768 ciphertext size: expected {}, got {}",
            CIPHERTEXT_SIZE,
            ciphertext.len()
        )));
    }
    let ct_array: [u8; CIPHERTEXT_SIZE] = ciphertext.try_into().unwrap();
    let ct = ml_kem::array::Array::from(ct_array);

    // Decapsulate
    let ss = dk
        .decapsulate(&ct)
        .map_err(|_| Error::KeyExchange("ML-KEM-768 decapsulation failed".into()))?;

    Ok(ss.as_slice().to_vec())
}

/// Encapsulate using ML-KEM-1024 (Level 5 - 256-bit quantum security).
///
/// Returns (shared_secret, ciphertext).
pub fn mlkem1024_encapsulate(public_key: &[u8]) -> Result<(Vec<u8>, Vec<u8>)> {
    use kem::Encapsulate;
    use ml_kem::kem::EncapsulationKey as EK;
    use ml_kem::{EncodedSizeUser, MlKem1024Params};

    let mut rng = rand::thread_rng();

    // Parse public key
    let ek_array: ml_kem::Encoded<EK<MlKem1024Params>> = public_key
        .try_into()
        .map_err(|_| Error::KeyExchange("invalid ML-KEM-1024 public key size".into()))?;
    let ek = EK::<MlKem1024Params>::from_bytes(&ek_array);

    // Encapsulate - returns (Ciphertext, SharedSecret)
    let (ct, ss) = ek
        .encapsulate(&mut rng)
        .map_err(|_| Error::KeyExchange("ML-KEM-1024 encapsulation failed".into()))?;

    // Convert to Vec<u8> - both are hybrid_array::Array types
    Ok((ss.as_slice().to_vec(), ct.as_slice().to_vec()))
}

/// Decapsulate using ML-KEM-1024 (Level 5).
///
/// Returns shared_secret.
pub fn mlkem1024_decapsulate(secret_key: &[u8], ciphertext: &[u8]) -> Result<Vec<u8>> {
    use kem::Decapsulate;
    use ml_kem::kem::DecapsulationKey as DK;
    use ml_kem::{EncodedSizeUser, MlKem1024Params};

    // ML-KEM-1024 ciphertext size is 1568 bytes
    const CIPHERTEXT_SIZE: usize = 1568;

    // Parse secret key
    let dk_array: ml_kem::Encoded<DK<MlKem1024Params>> = secret_key
        .try_into()
        .map_err(|_| Error::KeyExchange("invalid ML-KEM-1024 secret key size".into()))?;
    let dk = DK::<MlKem1024Params>::from_bytes(&dk_array);

    // Parse ciphertext - it's just a byte array
    if ciphertext.len() != CIPHERTEXT_SIZE {
        return Err(Error::KeyExchange(format!(
            "invalid ML-KEM-1024 ciphertext size: expected {}, got {}",
            CIPHERTEXT_SIZE,
            ciphertext.len()
        )));
    }
    let ct_array: [u8; CIPHERTEXT_SIZE] = ciphertext.try_into().unwrap();
    let ct = ml_kem::array::Array::from(ct_array);

    // Decapsulate
    let ss = dk
        .decapsulate(&ct)
        .map_err(|_| Error::KeyExchange("ML-KEM-1024 decapsulation failed".into()))?;

    Ok(ss.as_slice().to_vec())
}

/// Generate nonce from message counter and direction.
///
/// This ensures unique nonces without coordination:
/// - Sender uses even counters
/// - Receiver uses odd counters
pub fn generate_nonce(counter: u64, is_sender: bool) -> [u8; AEAD_NONCE_SIZE] {
    let mut nonce = [0u8; AEAD_NONCE_SIZE];
    // First 8 bytes: counter
    nonce[..8].copy_from_slice(&counter.to_le_bytes());
    // Last 4 bytes: direction flag
    nonce[8] = if is_sender { 0x00 } else { 0x01 };
    nonce
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hkdf_derive() {
        let ikm = [0x42u8; 32];
        let mut output = [0u8; 64];
        hkdf_derive(&ikm, None, b"test", &mut output).unwrap();
        assert_ne!(output, [0u8; 64]);
    }

    #[test]
    fn test_kdf_rk() {
        let root_key = [0x42u8; ROOT_KEY_SIZE];
        let dh_output = [0x43u8; 32];
        let (new_root, chain_key) = kdf_rk(&root_key, &dh_output);
        assert_ne!(new_root, root_key);
        assert_ne!(chain_key, [0u8; CHAIN_KEY_SIZE]);
    }

    #[test]
    fn test_kdf_ck() {
        let chain_key = [0x42u8; CHAIN_KEY_SIZE];
        let (new_chain, message_key) = kdf_ck(&chain_key);
        assert_ne!(new_chain, chain_key);
        assert_ne!(message_key, [0u8; AEAD_KEY_SIZE]);
    }

    #[test]
    fn test_aead_roundtrip() {
        let key = [0x42u8; AEAD_KEY_SIZE];
        let nonce = [0x43u8; AEAD_NONCE_SIZE];
        let plaintext = b"Hello, post-quantum world!";
        let aad = b"additional data";

        let ciphertext = aead_encrypt(&key, &nonce, plaintext, aad).unwrap();
        let decrypted = aead_decrypt(&key, &nonce, &ciphertext, aad).unwrap();

        assert_eq!(decrypted, plaintext);
    }

    #[test]
    fn test_aead_tamper_detection() {
        let key = [0x42u8; AEAD_KEY_SIZE];
        let nonce = [0x43u8; AEAD_NONCE_SIZE];
        let plaintext = b"Hello, post-quantum world!";
        let aad = b"additional data";

        let mut ciphertext = aead_encrypt(&key, &nonce, plaintext, aad).unwrap();
        ciphertext[0] ^= 0x01; // Tamper with ciphertext

        let result = aead_decrypt(&key, &nonce, &ciphertext, aad);
        assert!(result.is_err());
    }

    #[test]
    fn test_x25519_dh() {
        let secret_a = [0x42u8; 32];
        let secret_b = [0x43u8; 32];

        let public_a =
            *x25519_dalek::PublicKey::from(&x25519_dalek::StaticSecret::from(secret_a)).as_bytes();
        let public_b =
            *x25519_dalek::PublicKey::from(&x25519_dalek::StaticSecret::from(secret_b)).as_bytes();

        let shared_ab = x25519_dh(&secret_a, &public_b);
        let shared_ba = x25519_dh(&secret_b, &public_a);

        assert_eq!(shared_ab, shared_ba);
    }

    #[test]
    fn test_mlkem_roundtrip() {
        use ml_kem::{EncodedSizeUser, KemCore, MlKem768};

        let mut rng = rand::thread_rng();
        let (dk, ek) = MlKem768::generate(&mut rng);

        let ek_bytes = EncodedSizeUser::as_bytes(&ek).to_vec();
        let dk_bytes = EncodedSizeUser::as_bytes(&dk).to_vec();

        let (ss1, ct) = mlkem_encapsulate(&ek_bytes).unwrap();
        let ss2 = mlkem_decapsulate(&dk_bytes, &ct).unwrap();

        assert_eq!(ss1, ss2);
    }

    #[test]
    fn test_mlkem1024_roundtrip() {
        use ml_kem::{EncodedSizeUser, KemCore, MlKem1024};

        let mut rng = rand::thread_rng();
        let (dk, ek) = MlKem1024::generate(&mut rng);

        let ek_bytes = EncodedSizeUser::as_bytes(&ek).to_vec();
        let dk_bytes = EncodedSizeUser::as_bytes(&dk).to_vec();

        let (ss1, ct) = mlkem1024_encapsulate(&ek_bytes).unwrap();
        let ss2 = mlkem1024_decapsulate(&dk_bytes, &ct).unwrap();

        assert_eq!(ss1, ss2);
    }

    #[test]
    fn test_mlkem_ex_level_detection() {
        // Test auto-detection from key sizes
        use ml_kem::{EncodedSizeUser, KemCore, MlKem1024, MlKem768};

        let mut rng = rand::thread_rng();

        // Test ML-KEM-768 detection
        let (_, ek768) = MlKem768::generate(&mut rng);
        let ek768_bytes = EncodedSizeUser::as_bytes(&ek768).to_vec();
        assert_eq!(
            detect_kem_level(&ek768_bytes),
            Some(KemSecurityLevel::Level3_ML_KEM768)
        );

        // Test ML-KEM-1024 detection
        let (_, ek1024) = MlKem1024::generate(&mut rng);
        let ek1024_bytes = EncodedSizeUser::as_bytes(&ek1024).to_vec();
        assert_eq!(
            detect_kem_level(&ek1024_bytes),
            Some(KemSecurityLevel::Level5_ML_KEM1024)
        );
    }

    #[test]
    fn test_mlkem_ex_unified_encapsulate() {
        use ml_kem::{EncodedSizeUser, KemCore, MlKem1024, MlKem768};

        let mut rng = rand::thread_rng();

        // Test unified encapsulate with ML-KEM-768
        let (dk768, ek768) = MlKem768::generate(&mut rng);
        let ek768_bytes = EncodedSizeUser::as_bytes(&ek768).to_vec();
        let dk768_bytes = EncodedSizeUser::as_bytes(&dk768).to_vec();

        let (ss1, ct768) = mlkem_encapsulate_ex(&ek768_bytes, None).unwrap();
        let ss2 = mlkem_decapsulate_ex(&dk768_bytes, &ct768, None).unwrap();
        assert_eq!(ss1, ss2);

        // Test unified encapsulate with ML-KEM-1024
        let (dk1024, ek1024) = MlKem1024::generate(&mut rng);
        let ek1024_bytes = EncodedSizeUser::as_bytes(&ek1024).to_vec();
        let dk1024_bytes = EncodedSizeUser::as_bytes(&dk1024).to_vec();

        let (ss3, ct1024) = mlkem_encapsulate_ex(&ek1024_bytes, None).unwrap();
        let ss4 = mlkem_decapsulate_ex(&dk1024_bytes, &ct1024, None).unwrap();
        assert_eq!(ss3, ss4);
    }

    #[test]
    fn test_kem_security_level_default() {
        let level = KemSecurityLevel::default();
        assert_eq!(level, KemSecurityLevel::Level3_ML_KEM768);

        let level_str = KemSecurityLevel::from_str("level5");
        assert_eq!(level_str, Some(KemSecurityLevel::Level5_ML_KEM1024));

        assert!(!KemSecurityLevel::Level3_ML_KEM768.is_high_security());
        assert!(KemSecurityLevel::Level5_ML_KEM1024.is_high_security());
    }
}
