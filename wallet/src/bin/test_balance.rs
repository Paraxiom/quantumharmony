//! Simple test to query Alice's balance using the RPC client

use wallet::rpc_wallet::RpcClient;
use sp_core::crypto::{AccountId32, Ss58Codec};
use hex_literal::hex;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Alice's AccountId from genesis config
    let alice_bytes = hex!("d43593c715fdd31c61141abd04a99fd6822c8558854ccde39a5684e7a56da27d");
    let alice_account: AccountId32 = alice_bytes.into();
    let alice_ss58 = alice_account.to_ss58check();

    // Connect to local node
    let rpc = RpcClient::new("http://localhost:9944".to_string());

    println!("Querying balance for Alice");
    println!("  AccountId: {}", hex::encode(&alice_bytes));
    println!("  SS58: {}", alice_ss58);

    match rpc.get_balance(&alice_ss58).await {
        Ok(balance) => {
            let tokens = balance as f64 / 1_000_000_000_000.0;
            println!("\n✓ Alice's balance: {} ({} tokens)", balance, tokens);
        }
        Err(e) => {
            println!("\n✗ Error querying balance: {}", e);
        }
    }

    Ok(())
}
