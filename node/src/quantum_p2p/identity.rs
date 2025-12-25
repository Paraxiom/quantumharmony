// node/src/quantum_p2p/identity.rs
//
// Post-quantum identity using real Falcon-1024 signatures
// and ML-KEM-1024 for key encapsulation.

use pqcrypto_falcon::falcon1024;
use pqcrypto_kyber::kyber1024;
use pqcrypto_traits::kem::{
    Ciphertext, PublicKey as KemPublicKey, SecretKey as KemSecretKey, SharedSecret,
};
use pqcrypto_traits::sign::{
    PublicKey as SignPublicKey, SecretKey as SignSecretKey, SignedMessage,
};
use sp_core::{blake2_256, H256};
use std::fmt;

/// Falcon-1024 signature key sizes
pub const FALCON_PUBLIC_KEY_SIZE: usize = 1793;
pub const FALCON_SECRET_KEY_SIZE: usize = 2305;
pub const FALCON_SIGNATURE_SIZE: usize = 1330; // Max size, actual varies

/// ML-KEM-1024 key sizes
pub const KEM_PUBLIC_KEY_SIZE: usize = 1568;
pub const KEM_SECRET_KEY_SIZE: usize = 3168;
pub const KEM_CIPHERTEXT_SIZE: usize = 1568;
pub const KEM_SHARED_SECRET_SIZE: usize = 32;

/// A node identity based on real Falcon-1024 post-quantum signatures
/// and ML-KEM-1024 for key encapsulation.
#[derive(Clone)]
pub struct FalconIdentity {
    /// Falcon-1024 signing keypair
    pub(crate) sign_public_key: Option<Vec<u8>>,
    pub(crate) sign_secret_key: Option<Vec<u8>>,

    /// ML-KEM-1024 encryption keypair
    pub(crate) kem_public_key: Option<Vec<u8>>,
    pub(crate) kem_secret_key: Option<Vec<u8>>,

    /// Node ID derived from public keys
    pub(crate) node_id: Option<H256>,
}

impl fmt::Debug for FalconIdentity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("FalconIdentity")
            .field("node_id", &self.node_id)
            .field("has_sign_keys", &self.sign_public_key.is_some())
            .field("has_kem_keys", &self.kem_public_key.is_some())
            .finish()
    }
}

impl Default for FalconIdentity {
    fn default() -> Self {
        Self::new()
    }
}

impl FalconIdentity {
    /// Create a new Falcon identity instance (keys not yet generated)
    pub fn new() -> Self {
        Self {
            sign_public_key: None,
            sign_secret_key: None,
            kem_public_key: None,
            kem_secret_key: None,
            node_id: None,
        }
    }

    /// Generate new keypairs using the pqcrypto libraries
    pub fn generate_keypair(&mut self) -> Result<(), FalconIdentityError> {
        // Generate Falcon-1024 signing keypair
        let (sign_pk, sign_sk) = falcon1024::keypair();
        self.sign_public_key = Some(sign_pk.as_bytes().to_vec());
        self.sign_secret_key = Some(sign_sk.as_bytes().to_vec());

        // Generate ML-KEM-1024 encryption keypair
        let (kem_pk, kem_sk) = kyber1024::keypair();
        self.kem_public_key = Some(kem_pk.as_bytes().to_vec());
        self.kem_secret_key = Some(kem_sk.as_bytes().to_vec());

        // Derive node ID from both public keys
        let mut combined = Vec::with_capacity(FALCON_PUBLIC_KEY_SIZE + KEM_PUBLIC_KEY_SIZE);
        combined.extend_from_slice(sign_pk.as_bytes());
        combined.extend_from_slice(kem_pk.as_bytes());
        self.node_id = Some(H256::from_slice(&blake2_256(&combined)));

        log::info!(
            "Generated Falcon-1024 + ML-KEM-1024 identity with node ID: {:?}",
            self.node_id
        );

        Ok(())
    }

    /// Create identity from existing key bytes
    pub fn from_keys(
        sign_public_key: Vec<u8>,
        sign_secret_key: Vec<u8>,
        kem_public_key: Vec<u8>,
        kem_secret_key: Vec<u8>,
    ) -> Result<Self, FalconIdentityError> {
        // Validate key sizes
        if sign_public_key.len() != FALCON_PUBLIC_KEY_SIZE {
            return Err(FalconIdentityError::InvalidKeySize {
                expected: FALCON_PUBLIC_KEY_SIZE,
                actual: sign_public_key.len(),
                key_type: "Falcon public key",
            });
        }
        if sign_secret_key.len() != FALCON_SECRET_KEY_SIZE {
            return Err(FalconIdentityError::InvalidKeySize {
                expected: FALCON_SECRET_KEY_SIZE,
                actual: sign_secret_key.len(),
                key_type: "Falcon secret key",
            });
        }
        if kem_public_key.len() != KEM_PUBLIC_KEY_SIZE {
            return Err(FalconIdentityError::InvalidKeySize {
                expected: KEM_PUBLIC_KEY_SIZE,
                actual: kem_public_key.len(),
                key_type: "ML-KEM public key",
            });
        }
        if kem_secret_key.len() != KEM_SECRET_KEY_SIZE {
            return Err(FalconIdentityError::InvalidKeySize {
                expected: KEM_SECRET_KEY_SIZE,
                actual: kem_secret_key.len(),
                key_type: "ML-KEM secret key",
            });
        }

        // Validate keys by parsing them
        falcon1024::PublicKey::from_bytes(&sign_public_key)
            .map_err(|_| FalconIdentityError::InvalidKey("Invalid Falcon public key"))?;
        falcon1024::SecretKey::from_bytes(&sign_secret_key)
            .map_err(|_| FalconIdentityError::InvalidKey("Invalid Falcon secret key"))?;
        kyber1024::PublicKey::from_bytes(&kem_public_key)
            .map_err(|_| FalconIdentityError::InvalidKey("Invalid ML-KEM public key"))?;
        kyber1024::SecretKey::from_bytes(&kem_secret_key)
            .map_err(|_| FalconIdentityError::InvalidKey("Invalid ML-KEM secret key"))?;

        // Derive node ID
        let mut combined = Vec::with_capacity(FALCON_PUBLIC_KEY_SIZE + KEM_PUBLIC_KEY_SIZE);
        combined.extend_from_slice(&sign_public_key);
        combined.extend_from_slice(&kem_public_key);
        let node_id = H256::from_slice(&blake2_256(&combined));

        Ok(Self {
            sign_public_key: Some(sign_public_key),
            sign_secret_key: Some(sign_secret_key),
            kem_public_key: Some(kem_public_key),
            kem_secret_key: Some(kem_secret_key),
            node_id: Some(node_id),
        })
    }

    /// Get the node ID, generating keypairs if needed
    pub fn node_id(&mut self) -> Result<H256, FalconIdentityError> {
        if self.node_id.is_none() {
            self.generate_keypair()?;
        }
        Ok(self.node_id.expect("Node ID should be set after generate_keypair"))
    }

    /// Get the Falcon-1024 public key for signatures
    pub fn sign_public_key(&self) -> Option<&[u8]> {
        self.sign_public_key.as_deref()
    }

    /// Get the ML-KEM-1024 public key for encryption
    pub fn kem_public_key(&self) -> Option<&[u8]> {
        self.kem_public_key.as_deref()
    }

    /// Get the Falcon signing secret key bytes
    pub fn sign_secret_key(&self) -> Option<&[u8]> {
        self.sign_secret_key.as_deref()
    }

    /// Get the KEM secret key bytes
    pub fn kem_secret_key(&self) -> Option<&[u8]> {
        self.kem_secret_key.as_deref()
    }

    /// Save identity to a JSON file for persistence
    pub fn save_to_file(&self, path: &str) -> Result<(), FalconIdentityError> {
        use std::fs;

        let sign_public = self.sign_public_key.as_ref()
            .ok_or(FalconIdentityError::KeyNotGenerated)?;
        let sign_secret = self.sign_secret_key.as_ref()
            .ok_or(FalconIdentityError::KeyNotGenerated)?;
        let kem_public = self.kem_public_key.as_ref()
            .ok_or(FalconIdentityError::KeyNotGenerated)?;
        let kem_secret = self.kem_secret_key.as_ref()
            .ok_or(FalconIdentityError::KeyNotGenerated)?;

        let key_json = serde_json::json!({
            "falcon_sign_public": format!("0x{}", hex::encode(sign_public)),
            "falcon_sign_secret": format!("0x{}", hex::encode(sign_secret)),
            "kem_public": format!("0x{}", hex::encode(kem_public)),
            "kem_secret": format!("0x{}", hex::encode(kem_secret))
        });

        // Create parent directory if needed
        if let Some(parent) = std::path::Path::new(path).parent() {
            fs::create_dir_all(parent).map_err(|e| {
                FalconIdentityError::IoError(format!("Failed to create directory: {}", e))
            })?;
        }

        fs::write(path, serde_json::to_string_pretty(&key_json).unwrap())
            .map_err(|e| FalconIdentityError::IoError(format!("Write failed: {}", e)))?;

        log::info!("Saved Falcon identity to {}", path);
        Ok(())
    }

    /// Load identity from a JSON file
    pub fn load_from_file(path: &str) -> Result<Self, FalconIdentityError> {
        use std::fs;

        let contents = fs::read_to_string(path)
            .map_err(|e| FalconIdentityError::IoError(format!("Read failed: {}", e)))?;

        let json: serde_json::Value = serde_json::from_str(&contents)
            .map_err(|e| FalconIdentityError::IoError(format!("Parse failed: {}", e)))?;

        let sign_public = hex::decode(
            json["falcon_sign_public"].as_str()
                .ok_or_else(|| FalconIdentityError::IoError("Missing falcon_sign_public".into()))?
                .trim_start_matches("0x")
        ).map_err(|e| FalconIdentityError::IoError(format!("Hex decode error: {}", e)))?;

        let sign_secret = hex::decode(
            json["falcon_sign_secret"].as_str()
                .ok_or_else(|| FalconIdentityError::IoError("Missing falcon_sign_secret".into()))?
                .trim_start_matches("0x")
        ).map_err(|e| FalconIdentityError::IoError(format!("Hex decode error: {}", e)))?;

        let kem_public = hex::decode(
            json["kem_public"].as_str()
                .ok_or_else(|| FalconIdentityError::IoError("Missing kem_public".into()))?
                .trim_start_matches("0x")
        ).map_err(|e| FalconIdentityError::IoError(format!("Hex decode error: {}", e)))?;

        let kem_secret = hex::decode(
            json["kem_secret"].as_str()
                .ok_or_else(|| FalconIdentityError::IoError("Missing kem_secret".into()))?
                .trim_start_matches("0x")
        ).map_err(|e| FalconIdentityError::IoError(format!("Hex decode error: {}", e)))?;

        log::info!("Loaded Falcon identity from {}", path);
        Self::from_keys(sign_public, sign_secret, kem_public, kem_secret)
    }

    /// Sign data using Falcon-1024
    ///
    /// Returns a signed message (signature + original message) as per pqcrypto convention
    pub fn sign(&self, data: &[u8]) -> Result<Vec<u8>, FalconIdentityError> {
        let secret_key_bytes = self
            .sign_secret_key
            .as_ref()
            .ok_or(FalconIdentityError::KeyNotGenerated)?;

        let secret_key = falcon1024::SecretKey::from_bytes(secret_key_bytes)
            .map_err(|_| FalconIdentityError::InvalidKey("Invalid Falcon secret key"))?;

        let signed_message = falcon1024::sign(data, &secret_key);
        Ok(signed_message.as_bytes().to_vec())
    }

    /// Sign data and return only the detached signature
    ///
    /// Returns just the signature bytes without the message
    pub fn sign_detached(&self, data: &[u8]) -> Result<Vec<u8>, FalconIdentityError> {
        let signed_message = self.sign(data)?;
        // The signed message format is: signature || message
        // We need to extract just the signature part
        if signed_message.len() <= data.len() {
            return Err(FalconIdentityError::SignatureError(
                "Signed message too short".into(),
            ));
        }
        let signature_len = signed_message.len() - data.len();
        Ok(signed_message[..signature_len].to_vec())
    }

    /// Verify a Falcon-1024 signature (signed message format)
    ///
    /// Takes a signed message (signature + original message) and verifies it
    pub fn verify(&self, signed_message: &[u8]) -> Result<Vec<u8>, FalconIdentityError> {
        let public_key_bytes = self
            .sign_public_key
            .as_ref()
            .ok_or(FalconIdentityError::KeyNotGenerated)?;

        let public_key = falcon1024::PublicKey::from_bytes(public_key_bytes)
            .map_err(|_| FalconIdentityError::InvalidKey("Invalid Falcon public key"))?;

        let sm = falcon1024::SignedMessage::from_bytes(signed_message)
            .map_err(|_| FalconIdentityError::InvalidKey("Invalid signed message format"))?;

        let verified_message = falcon1024::open(&sm, &public_key)
            .map_err(|_| FalconIdentityError::SignatureVerificationFailed)?;

        Ok(verified_message)
    }

    /// Verify a Falcon-1024 signature against specific data using another party's public key
    pub fn verify_with_pubkey(
        data: &[u8],
        signed_message: &[u8],
        public_key_bytes: &[u8],
    ) -> Result<bool, FalconIdentityError> {
        let public_key = falcon1024::PublicKey::from_bytes(public_key_bytes)
            .map_err(|_| FalconIdentityError::InvalidKey("Invalid Falcon public key"))?;

        let sm = falcon1024::SignedMessage::from_bytes(signed_message)
            .map_err(|_| FalconIdentityError::InvalidKey("Invalid signed message format"))?;

        match falcon1024::open(&sm, &public_key) {
            Ok(verified_message) => Ok(verified_message == data),
            Err(_) => Ok(false),
        }
    }

    /// Encapsulate: Generate a shared secret for a recipient using their ML-KEM public key
    ///
    /// Returns (ciphertext, shared_secret) - send ciphertext to recipient
    pub fn encapsulate(
        recipient_kem_pubkey: &[u8],
    ) -> Result<(Vec<u8>, Vec<u8>), FalconIdentityError> {
        let public_key = kyber1024::PublicKey::from_bytes(recipient_kem_pubkey)
            .map_err(|_| FalconIdentityError::InvalidKey("Invalid ML-KEM public key"))?;

        let (shared_secret, ciphertext) = kyber1024::encapsulate(&public_key);

        Ok((
            ciphertext.as_bytes().to_vec(),
            shared_secret.as_bytes().to_vec(),
        ))
    }

    /// Decapsulate: Recover the shared secret from a ciphertext using our secret key
    pub fn decapsulate(&self, ciphertext: &[u8]) -> Result<Vec<u8>, FalconIdentityError> {
        let secret_key_bytes = self
            .kem_secret_key
            .as_ref()
            .ok_or(FalconIdentityError::KeyNotGenerated)?;

        let secret_key = kyber1024::SecretKey::from_bytes(secret_key_bytes)
            .map_err(|_| FalconIdentityError::InvalidKey("Invalid ML-KEM secret key"))?;

        let ct = kyber1024::Ciphertext::from_bytes(ciphertext)
            .map_err(|_| FalconIdentityError::InvalidKey("Invalid ML-KEM ciphertext"))?;

        let shared_secret = kyber1024::decapsulate(&ct, &secret_key);

        Ok(shared_secret.as_bytes().to_vec())
    }
}

/// Errors that can occur with FalconIdentity operations
#[derive(Debug, Clone)]
pub enum FalconIdentityError {
    KeyNotGenerated,
    InvalidKeySize {
        expected: usize,
        actual: usize,
        key_type: &'static str,
    },
    InvalidKey(&'static str),
    SignatureError(String),
    SignatureVerificationFailed,
    EncapsulationError(String),
    DecapsulationError(String),
    IoError(String),
}

impl std::fmt::Display for FalconIdentityError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::KeyNotGenerated => write!(f, "Keypair not generated yet"),
            Self::InvalidKeySize {
                expected,
                actual,
                key_type,
            } => {
                write!(
                    f,
                    "Invalid {} size: expected {}, got {}",
                    key_type, expected, actual
                )
            }
            Self::InvalidKey(msg) => write!(f, "Invalid key: {}", msg),
            Self::SignatureError(msg) => write!(f, "Signature error: {}", msg),
            Self::SignatureVerificationFailed => write!(f, "Signature verification failed"),
            Self::EncapsulationError(msg) => write!(f, "Encapsulation error: {}", msg),
            Self::DecapsulationError(msg) => write!(f, "Decapsulation error: {}", msg),
            Self::IoError(msg) => write!(f, "IO error: {}", msg),
        }
    }
}

impl std::error::Error for FalconIdentityError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_keypair_generation() {
        let mut identity = FalconIdentity::new();
        assert!(identity.sign_public_key().is_none());
        assert!(identity.kem_public_key().is_none());

        identity.generate_keypair().expect("Keypair generation failed");

        assert!(identity.sign_public_key().is_some());
        assert!(identity.kem_public_key().is_some());
        assert!(identity.node_id.is_some());

        // Verify key sizes
        assert_eq!(
            identity.sign_public_key().unwrap().len(),
            FALCON_PUBLIC_KEY_SIZE
        );
        assert_eq!(
            identity.kem_public_key().unwrap().len(),
            KEM_PUBLIC_KEY_SIZE
        );
    }

    #[test]
    fn test_sign_and_verify() {
        let mut identity = FalconIdentity::new();
        identity.generate_keypair().unwrap();

        let message = b"Hello, quantum world!";
        let signed_message = identity.sign(message).expect("Signing failed");

        // Verify the signature
        let verified_message = identity.verify(&signed_message).expect("Verification failed");
        assert_eq!(verified_message, message);
    }

    #[test]
    fn test_sign_verify_with_pubkey() {
        let mut identity = FalconIdentity::new();
        identity.generate_keypair().unwrap();

        let message = b"Test message for external verification";
        let signed_message = identity.sign(message).expect("Signing failed");

        let pubkey = identity.sign_public_key().unwrap();
        let result = FalconIdentity::verify_with_pubkey(message, &signed_message, pubkey)
            .expect("Verification failed");
        assert!(result);

        // Wrong message should fail
        let wrong_message = b"Wrong message";
        let result = FalconIdentity::verify_with_pubkey(wrong_message, &signed_message, pubkey)
            .expect("Verification should complete");
        assert!(!result);
    }

    #[test]
    fn test_invalid_signature_fails() {
        let mut identity = FalconIdentity::new();
        identity.generate_keypair().unwrap();

        let message = b"Original message";
        let mut signed_message = identity.sign(message).expect("Signing failed");

        // Corrupt the signature
        if !signed_message.is_empty() {
            signed_message[0] ^= 0xFF;
        }

        // Verification should fail
        let result = identity.verify(&signed_message);
        assert!(result.is_err());
    }

    #[test]
    fn test_encapsulate_decapsulate() {
        let mut alice = FalconIdentity::new();
        alice.generate_keypair().unwrap();

        let mut bob = FalconIdentity::new();
        bob.generate_keypair().unwrap();

        // Alice encapsulates a shared secret for Bob
        let bob_kem_pubkey = bob.kem_public_key().unwrap();
        let (ciphertext, alice_shared_secret) =
            FalconIdentity::encapsulate(bob_kem_pubkey).expect("Encapsulation failed");

        // Bob decapsulates to get the same shared secret
        let bob_shared_secret = bob.decapsulate(&ciphertext).expect("Decapsulation failed");

        // Both should have the same shared secret
        assert_eq!(alice_shared_secret, bob_shared_secret);
        assert_eq!(alice_shared_secret.len(), KEM_SHARED_SECRET_SIZE);
    }

    #[test]
    fn test_node_id_deterministic() {
        let mut identity1 = FalconIdentity::new();
        identity1.generate_keypair().unwrap();

        // Create another identity from the same keys
        let identity2 = FalconIdentity::from_keys(
            identity1.sign_public_key.clone().unwrap(),
            identity1.sign_secret_key.clone().unwrap(),
            identity1.kem_public_key.clone().unwrap(),
            identity1.kem_secret_key.clone().unwrap(),
        )
        .unwrap();

        assert_eq!(identity1.node_id, identity2.node_id);
    }

    #[test]
    fn test_from_keys_validates_sizes() {
        let result = FalconIdentity::from_keys(
            vec![0u8; 100], // Wrong size
            vec![0u8; FALCON_SECRET_KEY_SIZE],
            vec![0u8; KEM_PUBLIC_KEY_SIZE],
            vec![0u8; KEM_SECRET_KEY_SIZE],
        );
        assert!(matches!(
            result,
            Err(FalconIdentityError::InvalidKeySize { .. })
        ));
    }

    #[test]
    fn test_sign_without_keypair_fails() {
        let identity = FalconIdentity::new();
        let result = identity.sign(b"test");
        assert!(matches!(result, Err(FalconIdentityError::KeyNotGenerated)));
    }

    #[test]
    fn test_decapsulate_without_keypair_fails() {
        let identity = FalconIdentity::new();
        let result = identity.decapsulate(&[0u8; KEM_CIPHERTEXT_SIZE]);
        assert!(matches!(result, Err(FalconIdentityError::KeyNotGenerated)));
    }
}
