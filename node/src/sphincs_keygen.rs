//! SPHINCS+ Key Generation CLI
//!
//! Generate SPHINCS+-SHAKE-256s keypairs for validator nodes.
//!
//! Usage:
//!   quantumharmony-node sphincs-key generate
//!   quantumharmony-node sphincs-key generate --count 3 --output-dir ./keys
//!   quantumharmony-node sphincs-key inspect <secret-key-hex>

use clap::{Parser, Subcommand};
use sp_core::{crypto::Ss58Codec, Pair};
use sp_core::sphincs::{Pair as SphincsPair, Public as SphincsPublic};
use sp_runtime::traits::IdentifyAccount;
use sp_runtime::MultiSigner;
use std::fs;
use std::path::PathBuf;

/// SPHINCS+ key management commands
#[derive(Debug, Parser)]
pub struct SphincsKeyCmd {
    #[command(subcommand)]
    pub subcommand: SphincsKeySubcommand,
}

#[derive(Debug, Subcommand)]
pub enum SphincsKeySubcommand {
    /// Generate new SPHINCS+ keypair(s)
    Generate(GenerateCmd),
    /// Inspect a SPHINCS+ secret key
    Inspect(InspectCmd),
    /// Generate a validator set for chain spec
    ValidatorSet(ValidatorSetCmd),
}

/// Generate new SPHINCS+ keypair
#[derive(Debug, Parser)]
pub struct GenerateCmd {
    /// Number of keypairs to generate
    #[arg(long, default_value = "1")]
    pub count: usize,

    /// Output directory for key files (if not specified, prints to stdout)
    #[arg(long)]
    pub output_dir: Option<PathBuf>,

    /// Validator name prefix (e.g., "validator" generates validator-1, validator-2, etc.)
    #[arg(long, default_value = "validator")]
    pub name_prefix: String,

    /// Output format: json or text
    #[arg(long, default_value = "text")]
    pub format: String,
}

/// Inspect a SPHINCS+ secret key
#[derive(Debug, Parser)]
pub struct InspectCmd {
    /// Secret key (128 bytes hex-encoded, with or without 0x prefix)
    pub secret_key: String,
}

/// Generate a complete validator set for chain spec
#[derive(Debug, Parser)]
pub struct ValidatorSetCmd {
    /// Number of validators
    #[arg(long, default_value = "3")]
    pub count: usize,

    /// Output directory for all files
    #[arg(long, default_value = "./validator-keys")]
    pub output_dir: PathBuf,

    /// Initial balance per validator (in QH, will be multiplied by 10^18)
    #[arg(long, default_value = "1000000")]
    pub balance: u128,
}

impl SphincsKeyCmd {
    pub fn run(&self) -> Result<(), String> {
        match &self.subcommand {
            SphincsKeySubcommand::Generate(cmd) => cmd.run(),
            SphincsKeySubcommand::Inspect(cmd) => cmd.run(),
            SphincsKeySubcommand::ValidatorSet(cmd) => cmd.run(),
        }
    }
}

impl GenerateCmd {
    pub fn run(&self) -> Result<(), String> {
        let mut keys = Vec::new();

        for i in 1..=self.count {
            let keypair = SphincsPair::generate().0;
            let public = keypair.public();
            let secret = keypair.to_raw_vec();

            // Derive SS58 address
            let account_id = MultiSigner::from(public.clone()).into_account();
            let ss58_address = account_id.to_ss58check();

            let name = if self.count == 1 {
                self.name_prefix.clone()
            } else {
                format!("{}-{}", self.name_prefix, i)
            };

            let key_info = KeyInfo {
                name: name.clone(),
                public_key: format!("0x{}", hex::encode(public.as_ref())),
                secret_key: format!("0x{}", hex::encode(&secret)),
                ss58_address: ss58_address.clone(),
                account_id: format!("0x{}", hex::encode(account_id.as_ref() as &[u8])),
            };

            if let Some(ref output_dir) = self.output_dir {
                fs::create_dir_all(output_dir)
                    .map_err(|e| format!("Failed to create output directory: {}", e))?;

                // Write secret key file
                let secret_path = output_dir.join(format!("{}.secret", name));
                fs::write(&secret_path, &key_info.secret_key)
                    .map_err(|e| format!("Failed to write secret key: {}", e))?;

                // Write public key file
                let public_path = output_dir.join(format!("{}.public", name));
                fs::write(&public_path, &key_info.public_key)
                    .map_err(|e| format!("Failed to write public key: {}", e))?;

                // Write full info JSON
                let json_path = output_dir.join(format!("{}.json", name));
                let json = serde_json::to_string_pretty(&key_info)
                    .map_err(|e| format!("Failed to serialize key info: {}", e))?;
                fs::write(&json_path, json)
                    .map_err(|e| format!("Failed to write JSON: {}", e))?;

                println!("Generated keypair: {}", name);
                println!("  SS58 Address: {}", ss58_address);
                println!("  Files written to: {}/", output_dir.display());
            }

            keys.push(key_info);
        }

        // Print output if not writing to files
        if self.output_dir.is_none() {
            if self.format == "json" {
                let output = if keys.len() == 1 {
                    serde_json::to_string_pretty(&keys[0])
                } else {
                    serde_json::to_string_pretty(&keys)
                }.map_err(|e| format!("Failed to serialize: {}", e))?;
                println!("{}", output);
            } else {
                for key in &keys {
                    println!("=== {} ===", key.name);
                    println!("SS58 Address:  {}", key.ss58_address);
                    println!("Account ID:    {}", key.account_id);
                    println!("Public Key:    {}", key.public_key);
                    println!("Secret Key:    {}", key.secret_key);
                    println!();
                }
            }
        }

        Ok(())
    }
}

impl InspectCmd {
    pub fn run(&self) -> Result<(), String> {
        let secret_hex = self.secret_key.trim_start_matches("0x");
        let secret_bytes = hex::decode(secret_hex)
            .map_err(|e| format!("Invalid hex: {}", e))?;

        if secret_bytes.len() != 128 {
            return Err(format!(
                "Invalid secret key length: {} bytes (expected 128)",
                secret_bytes.len()
            ));
        }

        let secret_array: [u8; 128] = secret_bytes.try_into()
            .map_err(|_| "Failed to convert to array")?;

        let keypair = SphincsPair::from_secret(secret_array);
        let public = keypair.public();
        let account_id = MultiSigner::from(public.clone()).into_account();
        let ss58_address = account_id.to_ss58check();

        println!("=== SPHINCS+ Key Info ===");
        println!("SS58 Address:  {}", ss58_address);
        println!("Account ID:    0x{}", hex::encode(account_id.as_ref() as &[u8]));
        println!("Public Key:    0x{}", hex::encode(public.as_ref()));
        println!("Secret Key:    0x{}", hex::encode(&secret_array));
        println!();
        println!("Key Type:      SPHINCS+-SHAKE-256s (post-quantum)");
        println!("Public Size:   64 bytes");
        println!("Secret Size:   128 bytes");
        println!("Signature:     ~50KB");

        Ok(())
    }
}

impl ValidatorSetCmd {
    pub fn run(&self) -> Result<(), String> {
        fs::create_dir_all(&self.output_dir)
            .map_err(|e| format!("Failed to create output directory: {}", e))?;

        let mut validators = Vec::new();
        let mut chain_spec_accounts = Vec::new();

        println!("Generating {} validator keypairs...\n", self.count);

        for i in 1..=self.count {
            let name = format!("validator-{}", i);
            let keypair = SphincsPair::generate().0;
            let public = keypair.public();
            let secret = keypair.to_raw_vec();
            let account_id = MultiSigner::from(public.clone()).into_account();
            let ss58_address = account_id.to_ss58check();

            // Write individual key files
            let key_dir = self.output_dir.join(&name);
            fs::create_dir_all(&key_dir)
                .map_err(|e| format!("Failed to create key directory: {}", e))?;

            let secret_hex = format!("0x{}", hex::encode(&secret));
            let public_hex = format!("0x{}", hex::encode(public.as_ref()));
            let account_hex = format!("0x{}", hex::encode(account_id.as_ref() as &[u8]));

            fs::write(key_dir.join("secret.key"), &secret_hex)
                .map_err(|e| format!("Failed to write secret key: {}", e))?;
            fs::write(key_dir.join("public.key"), &public_hex)
                .map_err(|e| format!("Failed to write public key: {}", e))?;
            fs::write(key_dir.join("address.txt"), &ss58_address)
                .map_err(|e| format!("Failed to write address: {}", e))?;

            let key_info = KeyInfo {
                name: name.clone(),
                public_key: public_hex.clone(),
                secret_key: secret_hex,
                ss58_address: ss58_address.clone(),
                account_id: account_hex.clone(),
            };

            let json = serde_json::to_string_pretty(&key_info)
                .map_err(|e| format!("Failed to serialize: {}", e))?;
            fs::write(key_dir.join("key.json"), json)
                .map_err(|e| format!("Failed to write JSON: {}", e))?;

            println!("  {}: {}", name, ss58_address);

            validators.push(ValidatorInfo {
                name,
                ss58_address: ss58_address.clone(),
                public_key: public_hex,
                account_id: account_hex.clone(),
            });

            // For chain spec
            chain_spec_accounts.push(ChainSpecAccount {
                account_id: account_hex,
                balance: self.balance * 1_000_000_000_000_000_000u128, // Convert QH to planck
            });
        }

        // Write summary file
        let summary = ValidatorSetSummary {
            count: self.count,
            validators: validators.clone(),
        };
        let summary_json = serde_json::to_string_pretty(&summary)
            .map_err(|e| format!("Failed to serialize summary: {}", e))?;
        fs::write(self.output_dir.join("validators.json"), summary_json)
            .map_err(|e| format!("Failed to write summary: {}", e))?;

        // Write chain spec snippet
        let chain_spec_snippet = ChainSpecSnippet {
            aura_authorities: validators.iter().map(|v| v.public_key.clone()).collect(),
            balances: chain_spec_accounts,
            sudo_key: validators[0].account_id.clone(),
        };
        let snippet_json = serde_json::to_string_pretty(&chain_spec_snippet)
            .map_err(|e| format!("Failed to serialize snippet: {}", e))?;
        fs::write(self.output_dir.join("chain-spec-snippet.json"), &snippet_json)
            .map_err(|e| format!("Failed to write chain spec snippet: {}", e))?;

        println!("\n=== Summary ===");
        println!("Generated {} validator keypairs", self.count);
        println!("Output directory: {}", self.output_dir.display());
        println!();
        println!("Files created:");
        println!("  validators.json         - Summary of all validators");
        println!("  chain-spec-snippet.json - For chain spec generation");
        for v in &validators {
            println!("  {}/                - Individual key files", v.name);
        }
        println!();
        println!("IMPORTANT: Keep the secret.key files secure!");
        println!("           These are the validator signing keys.");

        Ok(())
    }
}

#[derive(Debug, serde::Serialize, serde::Deserialize)]
struct KeyInfo {
    name: String,
    public_key: String,
    secret_key: String,
    ss58_address: String,
    account_id: String,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
struct ValidatorInfo {
    name: String,
    ss58_address: String,
    public_key: String,
    account_id: String,
}

#[derive(Debug, serde::Serialize, serde::Deserialize)]
struct ValidatorSetSummary {
    count: usize,
    validators: Vec<ValidatorInfo>,
}

#[derive(Debug, serde::Serialize, serde::Deserialize)]
struct ChainSpecAccount {
    account_id: String,
    balance: u128,
}

#[derive(Debug, serde::Serialize, serde::Deserialize)]
struct ChainSpecSnippet {
    aura_authorities: Vec<String>,
    balances: Vec<ChainSpecAccount>,
    sudo_key: String,
}
