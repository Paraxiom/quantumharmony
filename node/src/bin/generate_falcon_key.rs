//! Generate Falcon-1024 keypair for wallet authentication
//!
//! Usage:
//! ```bash
//! cargo run --bin generate-falcon-key
//! ```
//!
//! Outputs:
//! - wallet-falcon.pub (public key, 1793 bytes)
//! - wallet-falcon.sec (secret key, 2305 bytes)

use pqcrypto_falcon::falcon1024;
use pqcrypto_traits::sign::{PublicKey, SecretKey};
use std::fs;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🔐 Generating Falcon-1024 keypair for wallet authentication...");
    println!();

    // Generate keypair
    let (public_key, secret_key) = falcon1024::keypair();

    println!("✅ Keypair generated!");
    println!("   Algorithm: Falcon-1024 (NIST PQC Round 3)");
    println!("   Public key size: {} bytes", public_key.as_bytes().len());
    println!("   Secret key size: {} bytes", secret_key.as_bytes().len());
    println!();

    // Save public key
    fs::write("wallet-falcon.pub", public_key.as_bytes())?;
    println!("📝 Public key saved to: wallet-falcon.pub");

    // Save secret key (WARNING: Keep this secure!)
    fs::write("wallet-falcon.sec", secret_key.as_bytes())?;
    println!("🔑 Secret key saved to: wallet-falcon.sec");
    println!();

    println!("⚠️  WARNING: Keep wallet-falcon.sec SECURE!");
    println!("   This key is used to authenticate wallet commands.");
    println!("   Anyone with this key can submit runtime upgrades.");
    println!();

    // Print public key in hex for node config
    println!("🔧 Add this to your node startup:");
    println!("   --wallet-public-key={}", hex::encode(public_key.as_bytes()));
    println!();

    println!("✅ Done! Use these keys to start the wallet server.");

    Ok(())
}
