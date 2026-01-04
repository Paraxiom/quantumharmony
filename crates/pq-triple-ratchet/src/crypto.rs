//! Low-level cryptographic primitives for the protocol.

use chacha20poly1305::{
    aead::{Aead, KeyInit},
    ChaCha20Poly1305, Nonce,
};
use hkdf::Hkdf;
use hmac::{Hmac, Mac, digest::KeyInit as HmacKeyInit};
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
pub fn kdf_rk(root_key: &[u8; ROOT_KEY_SIZE], dh_output: &[u8]) -> ([u8; ROOT_KEY_SIZE], [u8; CHAIN_KEY_SIZE]) {
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
    let mut mac: Hmac<Sha256> = HmacKeyInit::new_from_slice(chain_key).expect("HMAC accepts any key size");
    mac.update(&[0x01]); // Constant for new chain key
    let new_chain = mac.finalize().into_bytes();

    let mut mac: Hmac<Sha256> = HmacKeyInit::new_from_slice(chain_key).expect("HMAC accepts any key size");
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
        .encrypt(nonce, chacha20poly1305::aead::Payload { msg: plaintext, aad })
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
        .decrypt(nonce, chacha20poly1305::aead::Payload { msg: ciphertext, aad })
        .map_err(|_| Error::Decryption("AEAD decryption failed (bad key, corrupted data, or tampering)".into()))
}

/// Perform X25519 Diffie-Hellman.
pub fn x25519_dh(secret: &[u8; 32], public: &[u8; 32]) -> [u8; 32] {
    let secret = x25519_dalek::StaticSecret::from(*secret);
    let public = x25519_dalek::PublicKey::from(*public);
    *secret.diffie_hellman(&public).as_bytes()
}

/// Encapsulate using ML-KEM-768.
///
/// Returns (shared_secret, ciphertext).
pub fn mlkem_encapsulate(public_key: &[u8]) -> Result<(Vec<u8>, Vec<u8>)> {
    use kem::Encapsulate;
    use ml_kem::kem::EncapsulationKey as EK;
    use ml_kem::{EncodedSizeUser, MlKem768Params};

    let mut rng = rand::thread_rng();

    // Parse public key
    let ek_array: ml_kem::Encoded<EK<MlKem768Params>> = public_key
        .try_into()
        .map_err(|_| Error::KeyExchange("invalid ML-KEM public key size".into()))?;
    let ek = EK::<MlKem768Params>::from_bytes(&ek_array);

    // Encapsulate - returns (Ciphertext, SharedSecret)
    let (ct, ss) = ek.encapsulate(&mut rng)
        .map_err(|_| Error::KeyExchange("ML-KEM encapsulation failed".into()))?;

    // Convert to Vec<u8> - both are hybrid_array::Array types
    Ok((ss.as_slice().to_vec(), ct.as_slice().to_vec()))
}

/// Decapsulate using ML-KEM-768.
///
/// Returns shared_secret.
pub fn mlkem_decapsulate(secret_key: &[u8], ciphertext: &[u8]) -> Result<Vec<u8>> {
    use kem::Decapsulate;
    use ml_kem::kem::DecapsulationKey as DK;
    use ml_kem::{EncodedSizeUser, MlKem768Params};

    // ML-KEM-768 ciphertext size is 1088 bytes
    const CIPHERTEXT_SIZE: usize = 1088;

    // Parse secret key
    let dk_array: ml_kem::Encoded<DK<MlKem768Params>> = secret_key
        .try_into()
        .map_err(|_| Error::KeyExchange("invalid ML-KEM secret key size".into()))?;
    let dk = DK::<MlKem768Params>::from_bytes(&dk_array);

    // Parse ciphertext - it's just a byte array
    if ciphertext.len() != CIPHERTEXT_SIZE {
        return Err(Error::KeyExchange(format!(
            "invalid ML-KEM ciphertext size: expected {}, got {}",
            CIPHERTEXT_SIZE, ciphertext.len()
        )));
    }
    let ct_array: [u8; CIPHERTEXT_SIZE] = ciphertext.try_into().unwrap();
    let ct = ml_kem::array::Array::from(ct_array);

    // Decapsulate
    let ss = dk.decapsulate(&ct)
        .map_err(|_| Error::KeyExchange("ML-KEM decapsulation failed".into()))?;

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

        let public_a = *x25519_dalek::PublicKey::from(
            &x25519_dalek::StaticSecret::from(secret_a)
        ).as_bytes();
        let public_b = *x25519_dalek::PublicKey::from(
            &x25519_dalek::StaticSecret::from(secret_b)
        ).as_bytes();

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
}
