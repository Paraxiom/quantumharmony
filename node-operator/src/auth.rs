//! Authentication using SPHINCS+ signatures
//!
//! Provides request authentication and authorization for the operator API.

use pqcrypto_sphincsplus::sphincsshake256ssimple::{
    verify_detached_signature, DetachedSignature, PublicKey,
};
use pqcrypto_traits::sign::{
    DetachedSignature as DetachedSigTrait,
    PublicKey as PubKeyTrait,
    SignedMessage as SignedMsgTrait,
};
use sha2::{Sha256, Digest};
use std::collections::HashSet;
use std::sync::RwLock;
use std::time::{SystemTime, UNIX_EPOCH};
use tracing::{info, warn, debug};

/// Authentication manager for SPHINCS+ signed requests
pub struct AuthManager {
    /// Allow unauthenticated access (development only)
    allow_unauthenticated: bool,
    /// Set of authorized public keys
    authorized_keys: RwLock<HashSet<String>>,
    /// Maximum age for request timestamps (seconds)
    max_timestamp_age: u64,
}

impl AuthManager {
    pub fn new(allow_unauthenticated: bool) -> Self {
        Self {
            allow_unauthenticated,
            authorized_keys: RwLock::new(HashSet::new()),
            max_timestamp_age: 300, // 5 minutes
        }
    }

    /// Verify a SPHINCS+ signed request
    pub fn verify_request(
        &self,
        payload: &[u8],
        signature_hex: &str,
        public_key_hex: &str,
        timestamp: u64,
    ) -> Result<(), AuthError> {
        // Check if unauthenticated access is allowed
        if self.allow_unauthenticated {
            debug!("Allowing unauthenticated request (dev mode)");
            return Ok(());
        }

        // Verify timestamp is recent
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        if now.saturating_sub(timestamp) > self.max_timestamp_age {
            return Err(AuthError::TimestampExpired);
        }

        if timestamp > now + 60 {
            return Err(AuthError::TimestampInFuture);
        }

        // Check if public key is authorized
        {
            let authorized = self.authorized_keys.read().unwrap();
            if !authorized.is_empty() && !authorized.contains(public_key_hex) {
                return Err(AuthError::Unauthorized);
            }
        }

        // Decode signature and public key
        let signature_bytes = hex::decode(public_key_hex.trim_start_matches("0x"))
            .map_err(|_| AuthError::InvalidSignature)?;

        let public_key_bytes = hex::decode(public_key_hex.trim_start_matches("0x"))
            .map_err(|_| AuthError::InvalidPublicKey)?;

        // Verify SPHINCS+ signature
        // Create message to verify: payload || timestamp
        let mut message = payload.to_vec();
        message.extend_from_slice(&timestamp.to_le_bytes());

        // Hash the message
        let mut hasher = Sha256::new();
        hasher.update(&message);
        let hash = hasher.finalize();

        // Verify signature
        let sig = DetachedSignature::from_bytes(&signature_bytes)
            .map_err(|_| AuthError::InvalidSignature)?;
        let pk = PublicKey::from_bytes(&public_key_bytes)
            .map_err(|_| AuthError::InvalidPublicKey)?;

        verify_detached_signature(&sig, &hash, &pk)
            .map_err(|_| AuthError::SignatureVerificationFailed)?;

        Ok(())
    }

    /// Add an authorized public key
    pub fn add_authorized_key(&self, public_key_hex: &str) {
        let mut authorized = self.authorized_keys.write().unwrap();
        authorized.insert(public_key_hex.to_string());
        info!("Added authorized key: {}...", &public_key_hex[..32.min(public_key_hex.len())]);
    }

    /// Remove an authorized public key
    pub fn remove_authorized_key(&self, public_key_hex: &str) {
        let mut authorized = self.authorized_keys.write().unwrap();
        authorized.remove(public_key_hex);
    }

    /// Check if a public key is authorized
    pub fn is_authorized(&self, public_key_hex: &str) -> bool {
        if self.allow_unauthenticated {
            return true;
        }
        let authorized = self.authorized_keys.read().unwrap();
        authorized.is_empty() || authorized.contains(public_key_hex)
    }

    /// Sign a message with a secret key (for testing/admin)
    pub fn sign_message(secret_key_hex: &str, message: &[u8]) -> Result<String, AuthError> {
        use pqcrypto_sphincsplus::sphincsshake256ssimple::{sign, SecretKey};
        use pqcrypto_traits::sign::SecretKey as SecKeyTrait;

        let sk_bytes = hex::decode(secret_key_hex.trim_start_matches("0x"))
            .map_err(|_| AuthError::InvalidSecretKey)?;

        let sk = SecretKey::from_bytes(&sk_bytes)
            .map_err(|_| AuthError::InvalidSecretKey)?;

        // Hash the message first
        let mut hasher = Sha256::new();
        hasher.update(message);
        let hash = hasher.finalize();

        let signed = sign(&hash, &sk);
        let sig_bytes = signed.as_bytes();

        // Extract just the signature (first part, without the message)
        // SPHINCS+ detached signature size for shake256ssimple is 29792 bytes
        let sig_only = &sig_bytes[..29792.min(sig_bytes.len())];

        Ok(hex::encode(sig_only))
    }
}

#[derive(Debug)]
pub enum AuthError {
    TimestampExpired,
    TimestampInFuture,
    Unauthorized,
    InvalidSignature,
    InvalidPublicKey,
    InvalidSecretKey,
    SignatureVerificationFailed,
}

impl std::fmt::Display for AuthError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AuthError::TimestampExpired => write!(f, "Request timestamp expired"),
            AuthError::TimestampInFuture => write!(f, "Request timestamp is in the future"),
            AuthError::Unauthorized => write!(f, "Public key not authorized"),
            AuthError::InvalidSignature => write!(f, "Invalid signature format"),
            AuthError::InvalidPublicKey => write!(f, "Invalid public key format"),
            AuthError::InvalidSecretKey => write!(f, "Invalid secret key format"),
            AuthError::SignatureVerificationFailed => write!(f, "Signature verification failed"),
        }
    }
}

impl std::error::Error for AuthError {}
