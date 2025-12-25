//! Verify SPHINCS+ seed regeneration
//!
//! This tool takes a seed hex string and regenerates the keypair to verify
//! that the public key matches what was originally generated.
//!
//! Usage:
//!   cargo run --release --bin verify-seed-keypair <seed_hex> [expected_public_key_hex]
//!
//! Example:
//!   ./target/release/verify-seed-keypair 7ab3b370d684c1c6... 5649aad5d67da077...

use sp_core::{
    sphincs::Pair,
    Pair as TraitPair,
    crypto::Ss58Codec,
};
use sp_runtime::{traits::IdentifyAccount, MultiSigner};
use std::env;

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        eprintln!("Usage: {} <seed_hex> [expected_public_key_hex]", args[0]);
        eprintln!("  seed_hex: The seed in hex format (should be 96 chars for 48 bytes)");
        eprintln!("  expected_public_key_hex: Optional expected public key to compare");
        std::process::exit(1);
    }

    let seed_hex = args[1].trim_start_matches("0x");
    let expected_pubkey = if args.len() > 2 {
        Some(args[2].trim_start_matches("0x").to_string())
    } else {
        None
    };

    eprintln!("=== SPHINCS+ Seed Verification ===");
    eprintln!("Input seed hex: {}", seed_hex);
    eprintln!("Seed hex length: {} chars", seed_hex.len());

    // Parse the seed hex
    let seed_bytes = match hex::decode(seed_hex) {
        Ok(bytes) => bytes,
        Err(e) => {
            eprintln!("Error: Failed to decode seed hex: {}", e);
            std::process::exit(1);
        }
    };

    eprintln!("Seed byte length: {} bytes", seed_bytes.len());

    // Try to create a seed array
    if seed_bytes.len() != 48 {
        eprintln!("Warning: Expected 48 bytes for SPHINCS+ seed, got {} bytes", seed_bytes.len());
    }

    // Convert to fixed-size array for from_seed
    let mut seed_array = [0u8; 48];
    let copy_len = std::cmp::min(seed_bytes.len(), 48);
    seed_array[..copy_len].copy_from_slice(&seed_bytes[..copy_len]);

    eprintln!("\nRegenerating keypair from seed...");

    // Regenerate the keypair from the seed using from_seed_slice
    // Note: If 128 bytes are provided, this will use from_secret() for proper reconstruction
    let pair = Pair::from_seed_slice(&seed_bytes).expect("Failed to regenerate keypair from seed");
    let public = pair.public();
    let public_bytes = public.as_ref();
    let regenerated_pubkey_hex = hex::encode(public_bytes);

    eprintln!("Regenerated public key hex: {}", regenerated_pubkey_hex);
    eprintln!("Regenerated public key length: {} bytes", public_bytes.len());

    // Calculate AccountId
    let signer = MultiSigner::from(public.clone());
    let account_id = signer.into_account();
    let account_bytes: &[u8] = account_id.as_ref();
    let account_hex = hex::encode(account_bytes);
    let ss58 = account_id.to_ss58check();

    println!("{{");
    println!("  \"seed_hex\": \"{}\",", seed_hex);
    println!("  \"seed_len\": {},", seed_bytes.len());
    println!("  \"regenerated_public_key_hex\": \"{}\",", regenerated_pubkey_hex);
    println!("  \"public_key_len\": {},", public_bytes.len());
    println!("  \"account_id_hex\": \"{}\",", account_hex);
    println!("  \"ss58_address\": \"{}\"", ss58);

    // Compare with expected if provided
    if let Some(expected) = expected_pubkey {
        let matches = regenerated_pubkey_hex.to_lowercase() == expected.to_lowercase();
        println!("  ,\"expected_public_key_hex\": \"{}\",", expected);
        println!("  \"public_keys_match\": {}", matches);

        if !matches {
            eprintln!("\n*** WARNING: PUBLIC KEY MISMATCH! ***");
            eprintln!("Expected: {}", expected);
            eprintln!("Got:      {}", regenerated_pubkey_hex);
        } else {
            eprintln!("\n✓ Public keys match!");
        }
    }

    println!("}}");

    // Also test what happens with generate()
    eprintln!("\n=== Additional Test: Fresh Generation ===");
    let (fresh_pair, fresh_seed) = Pair::generate();
    let fresh_public = fresh_pair.public();
    let fresh_seed_bytes = fresh_seed.as_ref();

    eprintln!("Fresh seed length: {} bytes", fresh_seed_bytes.len());
    eprintln!("Fresh seed hex: {}", hex::encode(fresh_seed_bytes));
    eprintln!("Fresh public key hex: {}", hex::encode(fresh_public.as_ref()));

    // Now regenerate from the fresh seed using from_seed_slice
    let regen_pair = Pair::from_seed_slice(fresh_seed_bytes).expect("Failed to regenerate from fresh seed");
    let regen_public = regen_pair.public();

    let fresh_matches = hex::encode(fresh_public.as_ref()) == hex::encode(regen_public.as_ref());
    eprintln!("Regenerated public key hex: {}", hex::encode(regen_public.as_ref()));
    eprintln!("Fresh generate/regenerate match: {}", fresh_matches);

    if !fresh_matches {
        eprintln!("\n*** CRITICAL: from_seed() does not reproduce generate() output! ***");
        eprintln!("This is a bug in the SPHINCS+ implementation!");
    }
}
