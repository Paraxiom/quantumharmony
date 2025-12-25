//! SPHINCS+ keystore management

use anyhow::Result;
use sp_core::{
    crypto::{Ss58Codec, Ss58AddressFormat},
    sphincs::{Pair as SphincsPair, Public as SphincsPublic, Signature as SphincsSignature},
    Pair,
};
use std::path::{Path, PathBuf};

/// Keystore for managing SPHINCS+ keys
pub struct Keystore {
    path: PathBuf,
    keys: Vec<KeyPair>,
}

#[derive(Clone)]
pub struct KeyPair {
    pub public: SphincsPublic,
    pub pair: SphincsPair,
    pub name: String,
}

impl Keystore {
    /// Create or open keystore at path
    pub fn new(path: impl AsRef<Path>) -> Result<Self> {
        let path = path.as_ref().to_path_buf();

        // Create directory if it doesn't exist
        std::fs::create_dir_all(&path)?;

        tracing::info!("📁 Keystore opened at {}", path.display());

        Ok(Self {
            path,
            keys: Vec::new(),
        })
    }

    /// Generate new SPHINCS+ keypair
    pub fn generate(&mut self, name: impl Into<String>) -> Result<SphincsPublic> {
        tracing::info!("🔐 Generating new SPHINCS+ keypair...");

        let (pair, seed) = SphincsPair::generate();
        let public = pair.public();
        let name = name.into();

        // Save to disk
        self.save_key(&name, &seed)?;

        // Add to in-memory cache
        self.keys.push(KeyPair {
            public: public.clone(),
            pair,
            name,
        });

        tracing::info!("✅ Generated keypair: {}", public.to_ss58check_with_version(Ss58AddressFormat::custom(42)));

        Ok(public)
    }

    /// Load existing keypair by name
    pub fn load(&mut self, name: &str) -> Result<SphincsPublic> {
        let seed = self.load_seed(name)?;
        let pair = SphincsPair::from_seed(&seed);
        let public = pair.public();

        self.keys.push(KeyPair {
            public: public.clone(),
            pair,
            name: name.to_string(),
        });

        tracing::info!("✅ Loaded keypair: {}", public.to_ss58check_with_version(Ss58AddressFormat::custom(42)));

        Ok(public)
    }

    /// List all keypairs
    pub fn list(&self) -> Vec<(String, String)> {
        self.keys
            .iter()
            .map(|k| {
                (
                    k.name.clone(),
                    k.public.to_ss58check_with_version(Ss58AddressFormat::custom(42)),
                )
            })
            .collect()
    }

    /// Sign message with keypair
    pub fn sign(&self, name: &str, message: &[u8]) -> Result<SphincsSignature> {
        let keypair = self
            .keys
            .iter()
            .find(|k| k.name == name)
            .ok_or_else(|| anyhow::anyhow!("Keypair '{}' not found", name))?;

        Ok(keypair.pair.sign(message))
    }

    /// Verify signature
    pub fn verify(
        public: &SphincsPublic,
        message: &[u8],
        signature: &SphincsSignature,
    ) -> bool {
        sp_core::sphincs::Pair::verify(signature, message, public)
    }

    /// Save key seed to disk (encrypted in production)
    fn save_key(&self, name: &str, seed: &<SphincsPair as Pair>::Seed) -> Result<()> {
        let key_path = self.path.join(format!("{}.key", name));

        // WARNING: In production, this should be encrypted!
        // For now, storing raw seed for development
        std::fs::write(&key_path, seed.as_ref())?;

        tracing::warn!("⚠️  Key saved UNENCRYPTED at {}", key_path.display());
        tracing::warn!("⚠️  TODO: Implement key encryption for production");

        Ok(())
    }

    /// Load key seed from disk
    fn load_seed(&self, name: &str) -> Result<<SphincsPair as Pair>::Seed> {
        let key_path = self.path.join(format!("{}.key", name));
        let seed_bytes = std::fs::read(&key_path)?;

        if seed_bytes.len() != 48 {
            anyhow::bail!("Invalid seed length: expected 48 bytes, got {}", seed_bytes.len());
        }

        let mut seed = [0u8; 48];
        seed.copy_from_slice(&seed_bytes);

        // Convert to Pair::Seed type
        let seed_ref: &<SphincsPair as Pair>::Seed = unsafe {
            &*(seed.as_ptr() as *const <SphincsPair as Pair>::Seed)
        };

        Ok(seed_ref.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    #[test]
    fn test_generate_and_sign() {
        let temp_dir = tempdir().unwrap();
        let mut keystore = Keystore::new(temp_dir.path()).unwrap();

        // Generate keypair
        let public = keystore.generate("test").unwrap();

        // Sign message
        let message = b"Hello, QuantumHarmony!";
        let signature = keystore.sign("test", message).unwrap();

        // Verify signature
        assert!(Keystore::verify(&public, message, &signature));
    }

    #[test]
    fn test_save_and_load() {
        let temp_dir = tempdir().unwrap();

        // Generate and save
        let public1 = {
            let mut keystore = Keystore::new(temp_dir.path()).unwrap();
            keystore.generate("test").unwrap()
        };

        // Load in new keystore instance
        let public2 = {
            let mut keystore = Keystore::new(temp_dir.path()).unwrap();
            keystore.load("test").unwrap()
        };

        assert_eq!(public1, public2);
    }
}
