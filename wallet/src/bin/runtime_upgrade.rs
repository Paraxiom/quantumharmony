//! Runtime Upgrade CLI Tool
//!
//! This tool submits a runtime upgrade transaction using SPHINCS+ signing.
//!
//! Usage:
//!   cargo run --bin runtime-upgrade -- \
//!     --wasm path/to/runtime.wasm \
//!     --keystore path/to/keystore \
//!     --key-name Alice \
//!     --rpc ws://localhost:9944

use anyhow::{Context, Result};
use clap::Parser;
use jsonrpsee::{
    core::client::ClientT,
    rpc_params,
    ws_client::{WsClient, WsClientBuilder},
};
use scale_codec::{Compact, Encode};
use sp_core::{
    crypto::Ss58Codec,
    sphincs::{Pair as SphincsPair, Public as SphincsPublic, Signature as SphincsSignature},
    Pair,
};
use sp_runtime::{generic::Era, MultiAddress};
use std::path::PathBuf;

#[derive(Parser)]
#[command(name = "runtime-upgrade")]
#[command(about = "Submit runtime upgrade with SPHINCS+ signature")]
struct Args {
    /// Path to compiled WASM runtime
    #[arg(long)]
    wasm: PathBuf,

    /// Path to keystore directory containing <key-name>.key file
    #[arg(long)]
    keystore: PathBuf,

    /// Key name in keystore (e.g., "Alice")
    #[arg(long)]
    key_name: String,

    /// RPC endpoint
    #[arg(long, default_value = "ws://127.0.0.1:9944")]
    rpc: String,
}

/// Runtime Call indices (from runtime/src/lib.rs construct_runtime! macro)
/// The indices are determined by the order pallets appear in construct_runtime!
const PALLET_SUDO_INDEX: u8 = 7;  // Sudo is the 8th pallet (0-indexed)
const SUDO_CALL: u8 = 0;  // sudo is call index 0
const PALLET_SYSTEM_INDEX: u8 = 0;  // System is always index 0
const SYSTEM_SET_CODE_CALL: u8 = 3;  // set_code is call index 3 in frame_system

/// Transaction version
const TX_VERSION: u32 = 1;

/// Encode the sudo.sudo(system.setCode(wasm)) call
fn encode_sudo_set_code(wasm: Vec<u8>) -> Vec<u8> {
    let mut encoded = Vec::new();

    // Pallet index: Sudo
    encoded.push(PALLET_SUDO_INDEX);

    // Call index: sudo
    encoded.push(SUDO_CALL);

    // Inner call: system.set_code (as RuntimeCall)
    let mut inner_call = Vec::new();
    inner_call.push(PALLET_SYSTEM_INDEX);
    inner_call.push(SYSTEM_SET_CODE_CALL);

    // WASM code (SCALE-encoded Vec<u8>)
    let wasm_encoded = wasm.encode();
    inner_call.extend_from_slice(&wasm_encoded);

    // The inner_call is already a complete RuntimeCall::System::set_code
    // We need to encode it directly, NOT as Vec<u8>
    encoded.extend_from_slice(&inner_call);

    encoded
}

/// Create signed extrinsic
fn create_signed_extrinsic(
    call: Vec<u8>,
    nonce: u32,
    spec_version: u32,
    tx_version: u32,
    genesis_hash: [u8; 32],
    block_hash: [u8; 32],
    pair: &SphincsPair,
) -> Result<Vec<u8>> {
    let public = pair.public();
    // SPHINCS+ public key is 64 bytes, but AccountId32 is 32 bytes
    // We use the first 32 bytes as the account ID
    let mut account_id_bytes = [0u8; 32];
    account_id_bytes.copy_from_slice(&public.as_ref()[..32]);
    let account_id = sp_runtime::AccountId32::from(account_id_bytes);

    // Create the transaction payload to sign
    let mut payload = Vec::new();

    // 1. Call
    payload.extend_from_slice(&call);

    // 2. Extra (signed extensions)
    // CheckNonZeroSender - no data
    // CheckSpecVersion
    payload.extend_from_slice(&spec_version.encode());
    // CheckTxVersion
    payload.extend_from_slice(&tx_version.encode());
    // CheckGenesis
    payload.extend_from_slice(&genesis_hash);
    // CheckMortality - use immortal era
    payload.extend_from_slice(&Era::Immortal.encode());
    // CheckNonce
    payload.extend_from_slice(&Compact(nonce).encode());
    // CheckWeight - no data
    // ChargeTransactionPayment - tip = 0
    payload.extend_from_slice(&Compact(0u128).encode());

    // If payload is longer than 256 bytes, hash it
    let payload_to_sign = if payload.len() > 256 {
        sp_core::blake2_256(&payload).to_vec()
    } else {
        payload
    };

    // Sign the payload
    let signature = pair.sign(&payload_to_sign);

    // Construct the signed extrinsic
    let mut extrinsic = Vec::new();

    // Version byte (0x84 = signed transaction version 4)
    extrinsic.push(0x84);

    // Sender (MultiAddress::Id)
    extrinsic.push(0x00); // MultiAddress::Id variant
    extrinsic.extend_from_slice(account_id.as_ref());

    // Signature (MultiSignature::SphincsPlus variant)
    extrinsic.push(0x00); // SphincsPlus is the only variant (index 0)
    extrinsic.extend_from_slice(signature.as_ref());

    // Extra (signed extensions again, for inclusion in extrinsic)
    extrinsic.extend_from_slice(&Era::Immortal.encode());
    extrinsic.extend_from_slice(&Compact(nonce).encode());
    extrinsic.extend_from_slice(&Compact(0u128).encode()); // tip

    // Call
    extrinsic.extend_from_slice(&call);

    // Prepend length as compact encoding
    let length = Compact(extrinsic.len() as u32);
    let mut final_extrinsic = length.encode();
    final_extrinsic.extend_from_slice(&extrinsic);

    Ok(final_extrinsic)
}

#[tokio::main]
async fn main() -> Result<()> {
    // Initialize logging
    tracing_subscriber::fmt()
        .with_env_filter("runtime_upgrade=info")
        .init();

    let args = Args::parse();

    println!("===================================");
    println!("QuantumHarmony Runtime Upgrade Tool");
    println!("===================================\n");

    // Load WASM file
    println!("📦 Loading WASM runtime...");
    let wasm_code = std::fs::read(&args.wasm)
        .with_context(|| format!("Failed to read WASM file: {}", args.wasm.display()))?;
    println!("   Size: {} KB\n", wasm_code.len() / 1024);

    // Load keypair from keystore
    println!("🔐 Loading SPHINCS+ keypair from keystore...");
    let key_path = args.keystore.join(format!("{}.key", args.key_name));
    let seed_bytes = std::fs::read(&key_path)
        .with_context(|| format!("Failed to read key file: {}", key_path.display()))?;

    if seed_bytes.len() != 48 {
        anyhow::bail!("Invalid seed length: expected 48 bytes, got {}", seed_bytes.len());
    }

    let mut seed = [0u8; 48];
    seed.copy_from_slice(&seed_bytes);

    // Create keypair from seed
    let pair = SphincsPair::from_seed(unsafe {
        &*(seed.as_ptr() as *const <SphincsPair as Pair>::Seed)
    });
    let public = pair.public();

    // SPHINCS+ public key is 64 bytes, but AccountId32 is 32 bytes
    // We use the first 32 bytes as the account ID
    let mut account_id_bytes = [0u8; 32];
    account_id_bytes.copy_from_slice(&public.as_ref()[..32]);
    let account_id = sp_runtime::AccountId32::from(account_id_bytes);

    println!("   Account: {}", account_id.to_ss58check());
    println!("   Public key (first 32 bytes): {:?}\n", &public.as_ref()[..32]);

    // Connect to RPC
    println!("🌐 Connecting to RPC at {}...", args.rpc);
    let client = WsClientBuilder::default()
        .build(&args.rpc)
        .await
        .context("Failed to connect to RPC endpoint")?;
    println!("   Connected!\n");

    // Get runtime version
    println!("📊 Querying chain state...");
    let runtime_version: serde_json::Value = client
        .request("state_getRuntimeVersion", rpc_params![])
        .await
        .context("Failed to get runtime version")?;

    let spec_version = runtime_version["specVersion"]
        .as_u64()
        .context("Missing spec_version")? as u32;

    println!("   Current spec_version: {}", spec_version);

    // Get genesis hash
    let genesis_hash: String = client
        .request("chain_getBlockHash", rpc_params![0])
        .await
        .context("Failed to get genesis hash")?;

    let genesis_hash_bytes = hex::decode(genesis_hash.trim_start_matches("0x"))
        .context("Failed to decode genesis hash")?;
    let mut genesis_hash_array = [0u8; 32];
    genesis_hash_array.copy_from_slice(&genesis_hash_bytes);

    println!("   Genesis hash: 0x{}", hex::encode(&genesis_hash_array[..8]));

    // Get current block hash (for mortality)
    let block_hash: String = client
        .request("chain_getBlockHash", rpc_params![])
        .await
        .context("Failed to get current block hash")?;

    let block_hash_bytes = hex::decode(block_hash.trim_start_matches("0x"))
        .context("Failed to decode block hash")?;
    let mut block_hash_array = [0u8; 32];
    block_hash_array.copy_from_slice(&block_hash_bytes);

    // Use nonce 0 for dev chain (Alice starts with nonce 0)
    let nonce = 0u32;
    println!("   Account nonce: {} (dev chain default)\n", nonce);

    // Create the call
    println!("🔨 Building transaction...");
    let call = encode_sudo_set_code(wasm_code.clone());
    println!("   Call: sudo.sudo(system.setCode(wasm))");
    println!("   Call data size: {} bytes", call.len());

    // Create signed extrinsic
    println!("\n🔏 Signing transaction with SPHINCS+...");
    let signed_extrinsic = create_signed_extrinsic(
        call,
        nonce,
        spec_version,
        TX_VERSION,
        genesis_hash_array,
        block_hash_array,
        &pair,
    )?;

    println!("   Signature created (SPHINCS+ signature: ~49KB)");
    println!("   Signed extrinsic size: {} KB", signed_extrinsic.len() / 1024);

    // Submit extrinsic
    println!("\n📤 Submitting runtime upgrade transaction...");
    let extrinsic_hex = format!("0x{}", hex::encode(&signed_extrinsic));

    let tx_hash: String = client
        .request("author_submitExtrinsic", rpc_params![extrinsic_hex])
        .await
        .context("Failed to submit extrinsic")?;

    println!("\n✅ Transaction submitted!");
    println!("   Transaction hash: {}", tx_hash);
    println!("\n🎯 Monitoring for inclusion in block...");

    // Wait for finalization
    // Note: We can't use author_submitAndWatchExtrinsic with jsonrpsee client easily
    // so we'll just poll for the new runtime version

    for i in 1..=30 {
        tokio::time::sleep(tokio::time::Duration::from_secs(2)).await;

        let current_version: serde_json::Value = client
            .request("state_getRuntimeVersion", rpc_params![])
            .await
            .context("Failed to get runtime version")?;

        let current_spec = current_version["specVersion"]
            .as_u64()
            .context("Missing spec_version")? as u32;

        if current_spec != spec_version {
            println!("\n🎉 Runtime upgrade successful!");
            println!("   Old spec_version: {}", spec_version);
            println!("   New spec_version: {}", current_spec);
            println!("\n✨ Forkless runtime upgrade complete!");
            return Ok(());
        }

        if i % 5 == 0 {
            println!("   Still waiting... ({}s)", i * 2);
        }
    }

    println!("\n⚠️  Timeout waiting for upgrade to take effect.");
    println!("   Transaction was submitted but upgrade may still be processing.");
    println!("   Check the node logs or query the runtime version manually.");

    Ok(())
}
