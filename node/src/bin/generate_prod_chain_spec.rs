//! Generate production chain spec with custom SPHINCS+ keys
//!
//! This binary takes 3 SPHINCS+ public keys as hex strings and generates
//! a production-ready chain spec JSON file.
//!
//! Usage:
//!   cargo run --release --bin generate-prod-chain-spec -- \
//!     <validator1_public_key_hex> \
//!     <validator2_public_key_hex> \
//!     <validator3_public_key_hex>
//!
//! Example:
//!   ./target/release/generate-prod-chain-spec \
//!     a1b35b8c34a7267ca9a806b8072672c4bcc445d890f605bacace254456ffd68f7fae586fe98e97f171030276c35adc8ddd309c4450e0db82b0cce369f5f70766 \
//!     e9d1044c7d1642f3dcbc8e0cb6aee9222795f6e3564fca4b4932598ea52537a126cb524ec901185a141c06fca5b4b746c4b4f9127db52ba5a7078ebe8d5bceaa \
//!     09734ef566258145115c97c910e2f7a01f96f57275fc2f5aed4e9a1820b6bc1a4f2f648029b430521b021f2dc8f5dfad512d59cfa8fdcfb91df9b2e8612b43df

use std::env;

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() != 4 {
        eprintln!("Usage: {} <validator1_pubkey_hex> <validator2_pubkey_hex> <validator3_pubkey_hex>", args[0]);
        eprintln!("Each public key should be 128 hex characters (64 bytes)");
        std::process::exit(1);
    }

    let v1_hex = args[1].trim_start_matches("0x");
    let v2_hex = args[2].trim_start_matches("0x");
    let v3_hex = args[3].trim_start_matches("0x");

    // Validate key lengths
    if v1_hex.len() != 128 || v2_hex.len() != 128 || v3_hex.len() != 128 {
        eprintln!("Error: Each public key must be exactly 128 hex characters (64 bytes)");
        eprintln!("  validator1: {} chars", v1_hex.len());
        eprintln!("  validator2: {} chars", v2_hex.len());
        eprintln!("  validator3: {} chars", v3_hex.len());
        std::process::exit(1);
    }

    // Import chain spec builder
    use quantumharmony_node::chain_spec::production_3validators_config;

    let chain_spec = production_3validators_config(v1_hex, v2_hex, v3_hex);

    // Output as JSON
    let json = chain_spec.as_json(false).expect("Failed to serialize chain spec");
    println!("{}", json);
}
