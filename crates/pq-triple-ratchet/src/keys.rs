//! Cryptographic key types for the PQ-Triple-Ratchet protocol.
//!
//! ## Key Hierarchy
//!
//! ```text
//! Identity Key (long-term)
//! ├── SPHINCS+ keypair (PQ signatures)
//! ├── X25519 keypair (classical DH)
//! └── ML-KEM-768 keypair (PQ KEM)
//!
//! Signed PreKey (medium-term, rotated weekly)
//! ├── X25519 keypair
//! ├── ML-KEM-768 keypair
//! └── SPHINCS+ signature from identity key
//!
//! One-Time PreKey (single use)
//! ├── X25519 keypair
//! └── ML-KEM-768 keypair
//! ```

use rand::RngCore;
use serde::{Deserialize, Serialize};
use zeroize::{Zeroize, ZeroizeOnDrop};

use crate::error::{Error, Result};

/// Size of X25519 public key in bytes
pub const X25519_PUBLIC_KEY_SIZE: usize = 32;
/// Size of X25519 secret key in bytes
pub const X25519_SECRET_KEY_SIZE: usize = 32;
/// Size of ML-KEM-768 public key in bytes (NIST Level 3)
pub const MLKEM_PUBLIC_KEY_SIZE: usize = 1184;
/// Size of ML-KEM-768 secret key in bytes
pub const MLKEM_SECRET_KEY_SIZE: usize = 2400;
/// Size of ML-KEM-1024 public key in bytes (NIST Level 5, issue #5)
pub const MLKEM_1024_PUBLIC_KEY_SIZE: usize = 1568;
/// Size of ML-KEM-1024 secret key in bytes
pub const MLKEM_1024_SECRET_KEY_SIZE: usize = 3168;
/// Size of SPHINCS+ public key in bytes
pub const SPHINCS_PUBLIC_KEY_SIZE: usize = 64;
/// Size of SPHINCS+ signature in bytes
pub const SPHINCS_SIGNATURE_SIZE: usize = 17088;

/// Long-term identity keypair.
///
/// Contains both classical (X25519) and post-quantum (ML-KEM-768, SPHINCS+) keys.
/// The SPHINCS+ key is used to sign prekeys.
#[derive(Clone, Zeroize, ZeroizeOnDrop)]
pub struct IdentityKeyPair {
    /// X25519 secret key (classical DH)
    pub x25519_secret: [u8; X25519_SECRET_KEY_SIZE],
    /// X25519 public key
    #[zeroize(skip)]
    pub x25519_public: [u8; X25519_PUBLIC_KEY_SIZE],
    /// ML-KEM-768 secret key (post-quantum KEM)
    pub mlkem_secret: Vec<u8>,
    /// ML-KEM-768 public key
    #[zeroize(skip)]
    pub mlkem_public: Vec<u8>,
    /// SPHINCS+ secret key (post-quantum signatures)
    pub sphincs_secret: Vec<u8>,
    /// SPHINCS+ public key
    #[zeroize(skip)]
    pub sphincs_public: Vec<u8>,
}

/// Public portion of an identity key (for sharing with peers).
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct IdentityPublicKey {
    /// X25519 public key
    pub x25519: [u8; X25519_PUBLIC_KEY_SIZE],
    /// ML-KEM-768 public key
    pub mlkem: Vec<u8>,
    /// SPHINCS+ public key (for verifying signatures)
    pub sphincs: Vec<u8>,
}

impl IdentityKeyPair {
    /// Generate a new random identity keypair.
    pub fn generate() -> Result<Self> {
        let mut rng = rand::thread_rng();

        // Generate X25519 keypair
        let mut x25519_secret = [0u8; X25519_SECRET_KEY_SIZE];
        rng.fill_bytes(&mut x25519_secret);
        let x25519_static = x25519_dalek::StaticSecret::from(x25519_secret);
        let x25519_public_point = x25519_dalek::PublicKey::from(&x25519_static);
        let x25519_public = *x25519_public_point.as_bytes();

        // Generate ML-KEM-768 keypair
        let (mlkem_public, mlkem_secret) = Self::generate_mlkem_keypair(&mut rng)?;

        // Generate SPHINCS+ keypair
        let (sphincs_public, sphincs_secret) = Self::generate_sphincs_keypair()?;

        Ok(Self {
            x25519_secret,
            x25519_public,
            mlkem_secret,
            mlkem_public,
            sphincs_secret,
            sphincs_public,
        })
    }

    /// Get the public key portion for sharing.
    pub fn public_key(&self) -> IdentityPublicKey {
        IdentityPublicKey {
            x25519: self.x25519_public,
            mlkem: self.mlkem_public.clone(),
            sphincs: self.sphincs_public.clone(),
        }
    }

    /// Sign data using SPHINCS+.
    pub fn sign(&self, data: &[u8]) -> Result<Vec<u8>> {
        use pqcrypto_sphincsplus::sphincssha2256fsimple::*;
        use pqcrypto_traits::sign::{DetachedSignature, SecretKey};

        let sk = SecretKey::from_bytes(&self.sphincs_secret)
            .map_err(|e| Error::KeyGeneration(format!("invalid SPHINCS+ secret key: {:?}", e)))?;

        let sig = detached_sign(data, &sk);
        Ok(DetachedSignature::as_bytes(&sig).to_vec())
    }

    fn generate_mlkem_keypair(rng: &mut (impl RngCore + rand::CryptoRng)) -> Result<(Vec<u8>, Vec<u8>)> {
        use ml_kem::kem::{DecapsulationKey, EncapsulationKey};
        use ml_kem::{EncodedSizeUser, KemCore, MlKem768, MlKem768Params};

        let (dk, ek): (DecapsulationKey<MlKem768Params>, EncapsulationKey<MlKem768Params>) = MlKem768::generate(rng);

        // Serialize keys - EncodedSizeUser provides as_bytes()
        let ek_bytes = EncodedSizeUser::as_bytes(&ek).to_vec();
        let dk_bytes = EncodedSizeUser::as_bytes(&dk).to_vec();

        Ok((ek_bytes, dk_bytes))
    }

    /// Generate ML-KEM-1024 keypair (NIST Level 5, ~192-bit PQ security).
    ///
    /// Use this instead of `generate_mlkem_keypair` for high-security channels
    /// (issue #5). The returned keys are larger but provide stronger PQ guarantees.
    pub(crate) fn generate_mlkem_1024_keypair(rng: &mut (impl RngCore + rand::CryptoRng)) -> Result<(Vec<u8>, Vec<u8>)> {
        use ml_kem::kem::{DecapsulationKey, EncapsulationKey};
        use ml_kem::{EncodedSizeUser, KemCore, MlKem1024, MlKem1024Params};

        let (dk, ek): (DecapsulationKey<MlKem1024Params>, EncapsulationKey<MlKem1024Params>) = MlKem1024::generate(rng);

        let ek_bytes = EncodedSizeUser::as_bytes(&ek).to_vec();
        let dk_bytes = EncodedSizeUser::as_bytes(&dk).to_vec();

        Ok((ek_bytes, dk_bytes))
    }

    fn generate_sphincs_keypair() -> Result<(Vec<u8>, Vec<u8>)> {
        use pqcrypto_sphincsplus::sphincssha2256fsimple::*;
        use pqcrypto_traits::sign::{PublicKey, SecretKey};

        let (pk, sk) = keypair();
        Ok((pk.as_bytes().to_vec(), sk.as_bytes().to_vec()))
    }
}

impl IdentityPublicKey {
    /// Verify a SPHINCS+ signature.
    pub fn verify(&self, data: &[u8], signature: &[u8]) -> Result<()> {
        use pqcrypto_sphincsplus::sphincssha2256fsimple::*;
        use pqcrypto_traits::sign::{DetachedSignature, PublicKey};

        let pk = PublicKey::from_bytes(&self.sphincs)
            .map_err(|_| Error::SignatureVerification)?;
        let sig = DetachedSignature::from_bytes(signature)
            .map_err(|_| Error::SignatureVerification)?;

        verify_detached_signature(&sig, data, &pk)
            .map_err(|_| Error::SignatureVerification)
    }

    /// Serialize to bytes.
    pub fn to_bytes(&self) -> Vec<u8> {
        bincode::serialize(self).expect("serialization should not fail")
    }

    /// Deserialize from bytes.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
        bincode::deserialize(bytes).map_err(|e| Error::Serialization(e.to_string()))
    }

    /// Get a compact identifier (first 8 bytes of SHA-256 hash).
    pub fn fingerprint(&self) -> [u8; 8] {
        use sha2::{Digest, Sha256};
        let mut hasher = Sha256::new();
        hasher.update(&self.x25519);
        hasher.update(&self.mlkem);
        hasher.update(&self.sphincs);
        let hash = hasher.finalize();
        let mut fp = [0u8; 8];
        fp.copy_from_slice(&hash[..8]);
        fp
    }
}

/// Signed pre-key bundle for key exchange.
///
/// Contains both classical and PQ keys, signed by the identity key.
#[derive(Clone, Serialize, Deserialize)]
pub struct SignedPreKey {
    /// Unique identifier for this prekey
    pub id: u32,
    /// X25519 public key
    pub x25519_public: [u8; X25519_PUBLIC_KEY_SIZE],
    /// ML-KEM-768 public key
    pub mlkem_public: Vec<u8>,
    /// SPHINCS+ signature over (id || x25519_public || mlkem_public)
    pub signature: Vec<u8>,
    /// Timestamp when this prekey was generated (Unix seconds)
    pub timestamp: u64,
}

/// Secret portion of a signed prekey (kept by owner).
#[derive(Clone, Zeroize, ZeroizeOnDrop)]
pub struct SignedPreKeySecret {
    /// Prekey ID
    #[zeroize(skip)]
    pub id: u32,
    /// X25519 secret key
    pub x25519_secret: [u8; X25519_SECRET_KEY_SIZE],
    /// ML-KEM-768 secret key
    pub mlkem_secret: Vec<u8>,
}

/// One-time prekey (consumed after single use).
#[derive(Clone, Serialize, Deserialize)]
pub struct OneTimePreKey {
    /// Unique identifier
    pub id: u32,
    /// X25519 public key
    pub x25519_public: [u8; X25519_PUBLIC_KEY_SIZE],
    /// ML-KEM-768 public key
    pub mlkem_public: Vec<u8>,
}

/// Secret portion of a one-time prekey.
#[derive(Clone, Zeroize, ZeroizeOnDrop)]
pub struct OneTimePreKeySecret {
    /// Prekey ID
    #[zeroize(skip)]
    pub id: u32,
    /// X25519 secret key
    pub x25519_secret: [u8; X25519_SECRET_KEY_SIZE],
    /// ML-KEM-768 secret key
    pub mlkem_secret: Vec<u8>,
}

/// Complete prekey bundle published by a validator.
///
/// Contains everything needed to initiate a session with this validator.
#[derive(Clone, Serialize, Deserialize)]
pub struct PreKeyBundle {
    /// Identity public key
    pub identity: IdentityPublicKey,
    /// Signed prekey (medium-term)
    pub signed_prekey: SignedPreKey,
    /// Available one-time prekeys
    pub one_time_prekeys: Vec<OneTimePreKey>,
}

impl PreKeyBundle {
    /// Verify the signed prekey signature.
    pub fn verify(&self) -> Result<()> {
        // Construct the signed data
        let mut data = Vec::new();
        data.extend_from_slice(&self.signed_prekey.id.to_le_bytes());
        data.extend_from_slice(&self.signed_prekey.x25519_public);
        data.extend_from_slice(&self.signed_prekey.mlkem_public);
        data.extend_from_slice(&self.signed_prekey.timestamp.to_le_bytes());

        self.identity.verify(&data, &self.signed_prekey.signature)
    }

    /// Serialize to bytes.
    pub fn to_bytes(&self) -> Vec<u8> {
        bincode::serialize(self).expect("serialization should not fail")
    }

    /// Deserialize from bytes.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
        let bundle: Self = bincode::deserialize(bytes)?;
        bundle.verify()?;
        Ok(bundle)
    }
}

/// Generate a signed prekey pair.
pub fn generate_signed_prekey(
    identity: &IdentityKeyPair,
    id: u32,
) -> Result<(SignedPreKey, SignedPreKeySecret)> {
    let mut rng = rand::thread_rng();

    // Generate X25519 keypair
    let mut x25519_secret = [0u8; X25519_SECRET_KEY_SIZE];
    rng.fill_bytes(&mut x25519_secret);
    let x25519_static = x25519_dalek::StaticSecret::from(x25519_secret);
    let x25519_public = *x25519_dalek::PublicKey::from(&x25519_static).as_bytes();

    // Generate ML-KEM-768 keypair
    let (mlkem_public, mlkem_secret) = IdentityKeyPair::generate_mlkem_keypair(&mut rng)?;

    // Get timestamp
    let timestamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_secs();

    // Sign the prekey
    let mut data = Vec::new();
    data.extend_from_slice(&id.to_le_bytes());
    data.extend_from_slice(&x25519_public);
    data.extend_from_slice(&mlkem_public);
    data.extend_from_slice(&timestamp.to_le_bytes());
    let signature = identity.sign(&data)?;

    let public = SignedPreKey {
        id,
        x25519_public,
        mlkem_public,
        signature,
        timestamp,
    };

    let secret = SignedPreKeySecret {
        id,
        x25519_secret,
        mlkem_secret,
    };

    Ok((public, secret))
}

/// Generate a one-time prekey pair.
pub fn generate_one_time_prekey(id: u32) -> Result<(OneTimePreKey, OneTimePreKeySecret)> {
    let mut rng = rand::thread_rng();

    // Generate X25519 keypair
    let mut x25519_secret = [0u8; X25519_SECRET_KEY_SIZE];
    rng.fill_bytes(&mut x25519_secret);
    let x25519_static = x25519_dalek::StaticSecret::from(x25519_secret);
    let x25519_public = *x25519_dalek::PublicKey::from(&x25519_static).as_bytes();

    // Generate ML-KEM-768 keypair
    let (mlkem_public, mlkem_secret) = IdentityKeyPair::generate_mlkem_keypair(&mut rng)?;

    let public = OneTimePreKey {
        id,
        x25519_public,
        mlkem_public,
    };

    let secret = OneTimePreKeySecret {
        id,
        x25519_secret,
        mlkem_secret,
    };

    Ok((public, secret))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_identity_keypair_generation() {
        let keypair = IdentityKeyPair::generate().unwrap();
        assert_eq!(keypair.x25519_public.len(), X25519_PUBLIC_KEY_SIZE);
        assert!(!keypair.mlkem_public.is_empty());
        assert!(!keypair.sphincs_public.is_empty());
    }

    #[test]
    fn test_sphincs_sign_verify() {
        let keypair = IdentityKeyPair::generate().unwrap();
        let message = b"test message";
        let signature = keypair.sign(message).unwrap();

        let public_key = keypair.public_key();
        public_key.verify(message, &signature).unwrap();
    }

    #[test]
    fn test_signed_prekey_generation() {
        let identity = IdentityKeyPair::generate().unwrap();
        let (signed_pk, _secret) = generate_signed_prekey(&identity, 1).unwrap();

        // Verify the signature
        let mut data = Vec::new();
        data.extend_from_slice(&signed_pk.id.to_le_bytes());
        data.extend_from_slice(&signed_pk.x25519_public);
        data.extend_from_slice(&signed_pk.mlkem_public);
        data.extend_from_slice(&signed_pk.timestamp.to_le_bytes());

        identity.public_key().verify(&data, &signed_pk.signature).unwrap();
    }

    #[test]
    fn test_prekey_bundle_verify() {
        let identity = IdentityKeyPair::generate().unwrap();
        let (signed_pk, _) = generate_signed_prekey(&identity, 1).unwrap();
        let (otpk, _) = generate_one_time_prekey(1).unwrap();

        let bundle = PreKeyBundle {
            identity: identity.public_key(),
            signed_prekey: signed_pk,
            one_time_prekeys: vec![otpk],
        };

        bundle.verify().unwrap();
    }
}
