//! Generate a single production SPHINCS+ keypair and save to files
//!
//! This generates one keypair and outputs:
//! - Public key (64 bytes hex) to stdout (for chain spec)
//! - Secret key (128 bytes) to a file for keystore injection
//! - Seed (48 bytes) for cache pre-population
//! - AccountId (32 bytes hex) to stdout
//!
//! Usage:
//!   cargo run --release --bin generate-prod-key [name]
//!
//! Example:
//!   ./target/release/generate-prod-key validator1
//!   # Outputs public key and AccountId to stdout
//!   # Saves secret key to /tmp/validator1-sphincs-secret.key
//!
//! IMPORTANT: For SPHINCS+ in this implementation, we must save the FULL SECRET KEY (128 bytes)
//! because from_seed() does NOT deterministically regenerate keypairs - it uses a cache!
//! The keystore must contain the actual secret key.

use sp_core::{
    sphincs::Pair,
    Pair as TraitPair,
    crypto::Ss58Codec,
};
use sp_runtime::{traits::IdentifyAccount, MultiSigner};
use std::env;
use std::fs::File;
use std::io::Write;

fn main() {
    let args: Vec<String> = env::args().collect();
    let name = if args.len() > 1 {
        args[1].clone()
    } else {
        "validator".to_string()
    };

    eprintln!("=== Generating Production SPHINCS+ Keypair for {} ===", name);

    // Generate a new SPHINCS+ keypair
    let (pair, seed) = Pair::generate();

    let public = pair.public();
    let public_bytes = public.as_ref();

    // Get the raw seed bytes (48 bytes) - used as cache key
    let seed_bytes = seed.as_ref();

    // Get the FULL SECRET KEY (128 bytes) - this is what we need to store!
    let secret_bytes = pair.secret();

    // Calculate AccountId using Keccak-256 hash of public key
    let signer = MultiSigner::from(public.clone());
    let account_id = signer.into_account();
    let account_bytes: &[u8] = account_id.as_ref();

    // Output public key as hex (for chain spec)
    let public_hex = hex::encode(public_bytes);

    // Output AccountId as hex
    let account_hex = hex::encode(account_bytes);

    // SS58 address
    let ss58 = account_id.to_ss58check();

    // Save FULL SECRET KEY (128 bytes) to file - this is what we need to sign!
    let secret_path = format!("/tmp/{}-sphincs-secret.key", name);
    let mut file = File::create(&secret_path).expect("Failed to create secret file");
    file.write_all(secret_bytes).expect("Failed to write secret");
    eprintln!("Secret key saved to: {} ({} bytes)", secret_path, secret_bytes.len());

    // Also save the seed (for cache pre-population)
    let seed_path = format!("/tmp/{}-sphincs-seed.key", name);
    let mut seed_file = File::create(&seed_path).expect("Failed to create seed file");
    seed_file.write_all(seed_bytes).expect("Failed to write seed");
    eprintln!("Seed saved to: {} ({} bytes)", seed_path, seed_bytes.len());

    // Output JSON format for easy parsing
    println!("{{");
    println!("  \"name\": \"{}\",", name);
    println!("  \"public_key_hex\": \"{}\",", public_hex);
    println!("  \"public_key_len\": {},", public_bytes.len());
    println!("  \"seed_hex\": \"{}\",", hex::encode(seed_bytes));
    println!("  \"seed_len\": {},", seed_bytes.len());
    println!("  \"secret_key_hex\": \"{}\",", hex::encode(secret_bytes));
    println!("  \"secret_key_len\": {},", secret_bytes.len());
    println!("  \"account_id_hex\": \"{}\",", account_hex);
    println!("  \"ss58_address\": \"{}\",", ss58);
    println!("  \"secret_path\": \"{}\",", secret_path);
    println!("  \"seed_path\": \"{}\"", seed_path);
    println!("}}");

    eprintln!("\nKey generation complete for {}!", name);
    eprintln!("IMPORTANT: For keystore, use the SECRET KEY (128 bytes), NOT the seed!");
}
