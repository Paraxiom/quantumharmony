use sp_core::{Pair, crypto::{Ss58Codec, Ss58AddressFormat}};
use sp_consensus_aura::sphincs::AuthorityPair;

fn main() {
    // Generate Alice's SPHINCS+ keypair using the same method as chain_spec.rs
    let alice_pair = AuthorityPair::from_string("//Alice", None)
        .expect("Failed to generate Alice keypair from seed");

    let public_key = alice_pair.public();
    let public_bytes: &[u8] = public_key.as_ref();

    println!("Generated SPHINCS+ keypair for Alice:");
    println!("Public key (hex): 0x{}", hex::encode(public_bytes));
    println!("Public key (SS58): {}", public_key.to_ss58check_with_version(Ss58AddressFormat::custom(42)));
    println!("\nFirst 32 bytes: {:?}", &public_bytes[..32]);

    // The keypair seed for RPC insertion
    println!("\nTo insert this key via RPC, use:");
    println!("curl -H 'Content-Type: application/json' -d '{{");
    println!("  \"id\":1,");
    println!("  \"jsonrpc\":\"2.0\",");
    println!("  \"method\": \"author_insertKey\",");
    println!("  \"params\":[\"aura\", \"//Alice\", \"0x{}\"]", hex::encode(public_bytes));
    println!("}}' http://localhost:9944");
}
