//! Keystore management with SPHINCS+ support
//!
//! Manages validator keys and provides key generation, injection, and listing.

use pqcrypto_sphincsplus::sphincsshake256ssimple::{
    keypair, PublicKey, SecretKey,
};
use pqcrypto_traits::sign::{PublicKey as PubKeyTrait, SecretKey as SecKeyTrait};
use serde::{Deserialize, Serialize};
use std::path::PathBuf;
use tracing::{info, warn, error};

use crate::KeyInfo;

/// Manages cryptographic keys for the node operator
pub struct KeystoreManager {
    keystore_path: Option<PathBuf>,
    cached_keys: Vec<KeyInfo>,
}

impl KeystoreManager {
    pub fn new(keystore_path: Option<PathBuf>) -> Self {
        // Use default path if none specified
        let path = keystore_path.or_else(|| {
            dirs::data_local_dir().map(|d| d.join("quantumharmony").join("operator-keystore"))
        });

        // Create directory if it doesn't exist
        if let Some(ref p) = path {
            if let Err(e) = std::fs::create_dir_all(p) {
                warn!("Failed to create keystore directory: {}", e);
            } else {
                info!("Keystore path: {}", p.display());
            }
        }

        Self {
            keystore_path: path,
            cached_keys: Vec::new(),
        }
    }

    /// Get the keystore path as a string
    pub fn get_keystore_path(&self) -> Option<String> {
        self.keystore_path.as_ref().map(|p| p.display().to_string())
    }

    /// List all keys in the keystore
    pub async fn list_keys(&self) -> Vec<KeyInfo> {
        let mut keys = Vec::new();

        // Check local keystore directory
        if let Some(ref path) = self.keystore_path {
            if let Ok(entries) = std::fs::read_dir(path) {
                for entry in entries.flatten() {
                    if let Some(filename) = entry.file_name().to_str() {
                        // Keystore files are named: <key_type_hex><public_key_hex>
                        // aura = 61757261
                        if filename.starts_with("61757261") {
                            let public_key = &filename[8..]; // Skip "aura" prefix
                            let file_path = entry.path().display().to_string();
                            keys.push(KeyInfo {
                                key_type: "aura".to_string(),
                                public_key: format!("0x{}", public_key),
                                algorithm: "SPHINCS+-256s".to_string(),
                                path: Some(file_path),
                            });
                        }
                    }
                }
            }
        }

        keys
    }

    /// Generate a new SPHINCS+ keypair
    pub async fn generate_sphincs_key(&mut self) -> Result<KeyInfo, String> {
        info!("Generating new SPHINCS+-256s keypair...");

        // Generate keypair
        let (pk, sk) = keypair();

        let pk_bytes = pk.as_bytes();
        let sk_bytes = sk.as_bytes();

        let pk_hex = hex::encode(pk_bytes);
        let sk_hex = hex::encode(sk_bytes);

        info!("Generated SPHINCS+ key: 0x{}...", &pk_hex[..32]);

        // Save to keystore if path is configured
        let saved_path = if let Some(ref keystore_path) = self.keystore_path {
            let filename = format!("61757261{}", pk_hex); // "aura" prefix + public key
            let filepath = keystore_path.join(&filename);

            // Create keystore directory if needed
            std::fs::create_dir_all(keystore_path)
                .map_err(|e| format!("Failed to create keystore directory: {}", e))?;

            // Write secret key (JSON format with hex)
            let content = format!("\"0x{}\"", sk_hex);
            std::fs::write(&filepath, content)
                .map_err(|e| format!("Failed to write key file: {}", e))?;

            info!("Saved key to: {}", filepath.display());
            Some(filepath.display().to_string())
        } else {
            None
        };

        let key_info = KeyInfo {
            key_type: "aura".to_string(),
            public_key: format!("0x{}", pk_hex),
            algorithm: "SPHINCS+-256s".to_string(),
            path: saved_path,
        };

        self.cached_keys.push(key_info.clone());

        Ok(key_info)
    }

    /// Inject a key into the node's keystore via RPC
    pub async fn inject_key(&mut self, seed: &str, rpc_port: u16) -> Result<KeyInfo, String> {
        info!("Injecting key from seed: {}", if seed.starts_with("//") { seed } else { "***" });

        // Normalize the seed - accept "Alice" or "//Alice"
        let normalized_seed = if seed.starts_with("//") {
            seed.to_string()
        } else if seed.starts_with("0x") {
            return Err("Raw hex keys not supported. Use dev seed like //Alice or generate a new key.".to_string());
        } else {
            // Check if it's a known dev name without slashes
            let upper = seed.to_uppercase();
            if ["ALICE", "BOB", "CHARLIE", "DAVE", "EVE", "FERDIE"].contains(&upper.as_str()) {
                format!("//{}", seed.chars().next().unwrap().to_uppercase().collect::<String>() + &seed[1..].to_lowercase())
            } else {
                return Err(format!(
                    "Unknown seed format. Use dev seeds like //Alice, //Bob, //Charlie, or generate a new key."
                ));
            }
        };

        info!("Using normalized seed: {}", &normalized_seed);

        // Generate keypair for dev seed
        let (pk_hex, _sk_hex) = self.derive_dev_key(&normalized_seed)?;

        // Call node RPC to inject key
        let rpc_url = format!("http://localhost:{}", rpc_port);
        let client = reqwest::Client::new();

        let params = serde_json::json!([
            "aura",                         // key type
            normalized_seed,                // suri (seed phrase or //Dev)
            format!("0x{}", pk_hex)         // public key
        ]);

        let response = client
            .post(&rpc_url)
            .json(&serde_json::json!({
                "jsonrpc": "2.0",
                "id": 1,
                "method": "author_insertKey",
                "params": params
            }))
            .send()
            .await
            .map_err(|e| format!("RPC request failed: {}", e))?;

        let result: serde_json::Value = response
            .json()
            .await
            .map_err(|e| format!("Failed to parse response: {}", e))?;

        if let Some(error) = result.get("error") {
            return Err(format!("RPC error: {}", error));
        }

        let key_info = KeyInfo {
            key_type: "aura".to_string(),
            public_key: format!("0x{}", pk_hex),
            algorithm: "SPHINCS+-256s".to_string(),
            path: None, // Injected keys are stored in node's keystore
        };

        info!("Key injected successfully: 0x{}...", &pk_hex[..32]);
        Ok(key_info)
    }

    /// Derive keys for development accounts (//Alice, //Bob, etc.)
    fn derive_dev_key(&self, seed: &str) -> Result<(String, String), String> {
        // These are the well-known dev keys for QuantumHarmony
        // In production, these would be derived using proper key derivation
        match seed {
            "//Alice" => {
                // Alice's known SPHINCS+ keys (from validators.json or similar)
                // This is a placeholder - real implementation would use actual derivation
                let (pk, sk) = keypair(); // Generate deterministically in real impl
                Ok((hex::encode(pk.as_bytes()), hex::encode(sk.as_bytes())))
            }
            "//Bob" => {
                let (pk, sk) = keypair();
                Ok((hex::encode(pk.as_bytes()), hex::encode(sk.as_bytes())))
            }
            "//Charlie" => {
                let (pk, sk) = keypair();
                Ok((hex::encode(pk.as_bytes()), hex::encode(sk.as_bytes())))
            }
            _ => {
                // For unknown dev seeds, generate a new keypair
                // (In production, this would use deterministic derivation)
                let (pk, sk) = keypair();
                Ok((hex::encode(pk.as_bytes()), hex::encode(sk.as_bytes())))
            }
        }
    }

    /// Check if the node has session keys configured
    pub async fn check_session_keys(&self, rpc_port: u16) -> Result<bool, String> {
        let rpc_url = format!("http://localhost:{}", rpc_port);
        let client = reqwest::Client::new();

        let response = client
            .post(&rpc_url)
            .json(&serde_json::json!({
                "jsonrpc": "2.0",
                "id": 1,
                "method": "author_hasSessionKeys",
                "params": ["0x"] // Empty session keys check
            }))
            .send()
            .await
            .map_err(|e| format!("RPC request failed: {}", e))?;

        let result: serde_json::Value = response
            .json()
            .await
            .map_err(|e| format!("Failed to parse response: {}", e))?;

        if let Some(error) = result.get("error") {
            return Err(format!("RPC error: {}", error));
        }

        Ok(result.get("result").and_then(|r| r.as_bool()).unwrap_or(false))
    }

    /// Rotate session keys
    pub async fn rotate_keys(&self, rpc_port: u16) -> Result<String, String> {
        let rpc_url = format!("http://localhost:{}", rpc_port);
        let client = reqwest::Client::new();

        let response = client
            .post(&rpc_url)
            .json(&serde_json::json!({
                "jsonrpc": "2.0",
                "id": 1,
                "method": "author_rotateKeys",
                "params": []
            }))
            .send()
            .await
            .map_err(|e| format!("RPC request failed: {}", e))?;

        let result: serde_json::Value = response
            .json()
            .await
            .map_err(|e| format!("Failed to parse response: {}", e))?;

        if let Some(error) = result.get("error") {
            return Err(format!("RPC error: {}", error));
        }

        result
            .get("result")
            .and_then(|r| r.as_str())
            .map(|s| s.to_string())
            .ok_or_else(|| "No session keys returned".to_string())
    }
}
