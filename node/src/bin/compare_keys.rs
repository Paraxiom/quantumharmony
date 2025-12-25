use sp_core::{Pair, crypto::Ss58Codec};

fn main() {
    println!("=== SPHINCS+ Key Generation Analysis ===\n");

    // This is what chain_spec.rs does in authority_keys_from_seed_aura("Alice")
    // Line 60: let public = get_from_seed::<sphincs::Public>(s);
    // get_from_seed does: from_string(&format!("//{}", seed), None)
    use sp_core::sphincs;
    let pair_genesis = sphincs::Pair::from_string("//Alice", None)
        .expect("Failed to generate sphincs keypair from //Alice");
    let public_genesis = pair_genesis.public();
    let genesis_bytes: &[u8] = public_genesis.as_ref();

    println!("GENESIS CONFIGURATION (chain_spec.rs):");
    println!("  Method: sp_core::sphincs::Pair::from_string(\"//Alice\", None)");
    println!("  Public key (hex): 0x{}", hex::encode(genesis_bytes));
    println!("  First 32 bytes: {:?}", &genesis_bytes[..32]);

    // Convert to AuraId (this is what goes into genesis)
    use sp_consensus_aura::sphincs::AuthorityId as AuraId;
    let aura_id_genesis: AuraId = public_genesis.clone().into();
    let aura_id_bytes: &[u8] = aura_id_genesis.as_ref();
    println!("  As AuraId (hex): 0x{}", hex::encode(aura_id_bytes));
    println!("  SS58 address: {}\n", aura_id_genesis.to_ss58check_with_version(sp_core::crypto::Ss58AddressFormat::custom(42)));

    // This is what service.rs does with sphincs_generate_new
    // The keystore implementation should generate the same key
    println!("KEYSTORE AUTO-INSERTION (service.rs):");
    println!("  Method: keystore.sphincs_generate_new(aura_keytype, Some(\"//Alice\"))");
    println!("  Expected to match genesis key above");
    println!("\n  ⚠️  If these don't match, that's why block production fails!");

    // Let's also check what happens with different seed formats
    println!("\n=== Testing Different Seed Formats ===\n");

    let test_seeds = vec![
        "//Alice",
        "Alice",
        "//alice",
        "alice",
    ];

    for seed in test_seeds {
        match sphincs::Pair::from_string(seed, None) {
            Ok(pair) => {
                let pub_key = pair.public();
                let pub_bytes: &[u8] = pub_key.as_ref();
                println!("Seed: {:?}", seed);
                println!("  Public key: 0x{}", hex::encode(&pub_bytes[..16]));
                if pub_bytes == genesis_bytes {
                    println!("  ✅ MATCHES GENESIS KEY");
                } else {
                    println!("  ❌ Different from genesis");
                }
                println!();
            }
            Err(e) => {
                println!("Seed: {:?} - ERROR: {:?}\n", seed, e);
            }
        }
    }

    println!("=== Expected Genesis Authority ===");
    println!("The runtime should show this authority:");
    println!("0x{}", hex::encode(genesis_bytes));
}
