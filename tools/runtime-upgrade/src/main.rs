use clap::Parser;
use std::fs;
use std::path::PathBuf;
use std::time::Duration;
use anyhow::{Context, Result, bail};
use jsonrpsee::{
    core::client::ClientT,
    http_client::HttpClientBuilder,
    rpc_params,
};
use serde::{Deserialize, Serialize};

/// SPHINCS+ secret keys for test accounts (128 bytes each)
///
/// ⚠️  WARNING: DEVELOPMENT/TEST KEYS ONLY ⚠️
///
/// These keys are for LOCAL DEVELOPMENT and TESTING purposes only.
/// They are publicly known and must NEVER be used for:
/// - Production deployments
/// - Mainnet validators
/// - Any system holding real value
///
/// For production, generate fresh keys using `generate_prod_key` tool.
mod test_accounts {
    /// Alice's 128-byte SPHINCS+ secret key (from test_accounts.rs)
    /// ⚠️  DEV KEY - DO NOT USE IN PRODUCTION
    pub const ALICE_SECRET: [u8; 128] = [
        0xe7, 0x17, 0x5a, 0x54, 0x1e, 0xe0, 0x55, 0xe4, 0x23, 0xe0, 0x70, 0xee, 0xe2, 0xcf, 0xd2, 0xa9,
        0xf4, 0x47, 0xa8, 0x20, 0xf4, 0xe6, 0x1b, 0xf0, 0x31, 0x80, 0x80, 0x5d, 0xbc, 0x8c, 0x4a, 0x7f,
        0x1a, 0xd3, 0x43, 0x7c, 0x05, 0xc2, 0xda, 0x62, 0xed, 0x34, 0x2e, 0xef, 0x62, 0xe8, 0xca, 0xc2,
        0x85, 0xcf, 0x81, 0x34, 0xd2, 0x9b, 0x49, 0xc6, 0x8a, 0x9e, 0x57, 0x5f, 0x3c, 0x27, 0x59, 0x91,
        0xd7, 0xd0, 0xbd, 0x47, 0x54, 0x17, 0xa9, 0x3f, 0xa6, 0x12, 0x16, 0xa1, 0xe4, 0x02, 0x4f, 0x8d,
        0x1a, 0x21, 0x1f, 0x79, 0x5e, 0x6a, 0xb1, 0x11, 0xa1, 0xee, 0xf0, 0xd5, 0xe4, 0xf3, 0xf4, 0xb1,
        0x56, 0xe4, 0x7e, 0x5c, 0x8d, 0x41, 0x85, 0xce, 0x4a, 0x30, 0x84, 0x23, 0xeb, 0x31, 0x0b, 0xb3,
        0xb7, 0xf2, 0x6e, 0x6d, 0x50, 0x41, 0x91, 0x66, 0x2d, 0x22, 0x41, 0xaa, 0xfa, 0xf9, 0x14, 0xcd,
    ];

    /// Bob's 128-byte SPHINCS+ secret key
    pub const BOB_SECRET: [u8; 128] = [
        0xec, 0xb2, 0xcd, 0x60, 0x74, 0x12, 0x2a, 0x9f, 0xee, 0xcd, 0xf3, 0xb7, 0x94, 0x35, 0x43, 0x5f,
        0x5d, 0x98, 0xc8, 0x9b, 0xaf, 0x60, 0x92, 0x8b, 0x02, 0xa4, 0x1d, 0x28, 0x8b, 0xee, 0x96, 0xe2,
        0x28, 0xa2, 0x9e, 0xd7, 0xe8, 0x13, 0x69, 0x64, 0x8d, 0x54, 0x76, 0xe6, 0x6d, 0x76, 0x64, 0x10,
        0x0b, 0x8e, 0xae, 0x2c, 0xcc, 0x06, 0xf8, 0x23, 0x91, 0x2b, 0xa9, 0xc7, 0x1f, 0xfa, 0xdc, 0xe8,
        0x12, 0xf6, 0x88, 0xd8, 0x90, 0x5b, 0x2b, 0x67, 0xc0, 0xfe, 0x33, 0x87, 0x24, 0xa5, 0xa4, 0x44,
        0xb6, 0x1d, 0xc9, 0x49, 0xe8, 0x5f, 0x51, 0xf8, 0x50, 0x30, 0xb9, 0xc3, 0xf4, 0x1e, 0xe6, 0x61,
        0xea, 0xc6, 0x64, 0x30, 0x0e, 0x9a, 0xfc, 0x55, 0xbf, 0x15, 0x15, 0xdf, 0x53, 0x82, 0x7d, 0x28,
        0x1c, 0xe2, 0xce, 0x29, 0x5e, 0x18, 0xc2, 0x98, 0xe4, 0x89, 0x65, 0xff, 0x9e, 0xf3, 0xf0, 0x79,
    ];

    /// Charlie's 128-byte SPHINCS+ secret key
    pub const CHARLIE_SECRET: [u8; 128] = [
        0x7a, 0xeb, 0x22, 0xdf, 0xb2, 0x96, 0xc7, 0x8a, 0x18, 0xe5, 0x6b, 0x73, 0xe1, 0xf4, 0x0e, 0x21,
        0x47, 0x8b, 0x4c, 0x70, 0x9d, 0x86, 0x61, 0x2c, 0x41, 0x66, 0xb2, 0xb7, 0x12, 0xca, 0x75, 0x8b,
        0xdb, 0x97, 0x8b, 0xab, 0xad, 0x1c, 0x9f, 0x12, 0x21, 0x38, 0x39, 0x12, 0x84, 0x4b, 0xb5, 0xdc,
        0x35, 0xd6, 0x85, 0xfb, 0x38, 0x24, 0xb4, 0x70, 0x61, 0xf8, 0xa1, 0x7f, 0xad, 0x09, 0x9a, 0x40,
        0x8f, 0x60, 0x07, 0x22, 0xcd, 0x08, 0x87, 0xfc, 0xea, 0x1f, 0x98, 0xa2, 0x6e, 0x45, 0xc1, 0x44,
        0x9d, 0xaf, 0x02, 0x43, 0x95, 0x33, 0x55, 0x55, 0x48, 0xfb, 0x3c, 0xb3, 0xd6, 0xb0, 0x39, 0x22,
        0xd7, 0x37, 0x98, 0x35, 0x1f, 0x7a, 0x13, 0x57, 0x57, 0x4d, 0xd4, 0x24, 0x1b, 0xd8, 0x13, 0x3b,
        0xe9, 0x71, 0x82, 0x71, 0x19, 0xb2, 0x9e, 0x7a, 0x07, 0x08, 0x96, 0xde, 0xc7, 0xf3, 0x85, 0x98,
    ];

    pub fn get_secret(name: &str) -> Option<[u8; 128]> {
        match name.to_lowercase().as_str() {
            "alice" => Some(ALICE_SECRET),
            "bob" => Some(BOB_SECRET),
            "charlie" => Some(CHARLIE_SECRET),
            _ => None,
        }
    }
}

#[derive(Parser, Debug)]
#[command(name = "runtime-upgrade")]
#[command(about = "Perform a SPHINCS+ signed runtime upgrade on QuantumHarmony", long_about = None)]
struct Args {
    /// HTTP RPC endpoint of the node
    #[arg(short, long, default_value = "http://127.0.0.1:9944")]
    endpoint: String,

    /// Path to the runtime WASM file
    #[arg(short, long)]
    wasm: PathBuf,

    /// Sudo account name (alice, bob, or charlie)
    #[arg(short, long, default_value = "alice")]
    signer: String,

    /// Custom secret key in hex (128 bytes / 256 hex chars)
    /// If not provided, uses the test account key
    #[arg(long)]
    secret_key: Option<String>,

    /// Block time in seconds (for chunk upload timing)
    #[arg(long, default_value = "6")]
    block_time: u64,

    /// Cancel any pending upgrade before starting
    #[arg(long)]
    cancel_pending: bool,

    /// Dry run - only show what would be done
    #[arg(long)]
    dry_run: bool,
}

/// Response from chunkedUpgrade_initiate
#[derive(Debug, Deserialize)]
struct InitiateResult {
    upgrade_id: String,
    chunks_received: u32,
    total_chunks: u32,
    expected_size: u64,
    ready_to_finalize: bool,
}

/// Response from chunkedUpgrade_status
#[derive(Debug, Deserialize)]
struct StatusResult {
    pending: bool,
    upgrade_id: Option<String>,
    chunks_received: Option<u32>,
    total_chunks: Option<u32>,
    expected_size: Option<u64>,
}

/// Response from chunkedUpgrade_uploadChunk
#[derive(Debug, Deserialize)]
struct ChunkResult {
    chunks_received: u32,
    total_chunks: u32,
    ready_to_finalize: bool,
}

const CHUNK_SIZE: usize = 65536; // 64KB chunks

#[tokio::main]
async fn main() -> Result<()> {
    let args = Args::parse();

    println!("╔════════════════════════════════════════════════════════════╗");
    println!("║     QuantumHarmony Runtime Upgrade Tool (SPHINCS+)         ║");
    println!("╚════════════════════════════════════════════════════════════╝");
    println!();

    // Get secret key
    let secret_key = if let Some(ref hex_key) = args.secret_key {
        let hex_clean = hex_key.strip_prefix("0x").unwrap_or(hex_key);
        let bytes = hex::decode(hex_clean)
            .context("Invalid hex format for secret key")?;
        if bytes.len() != 128 {
            bail!("Secret key must be 128 bytes (256 hex chars), got {} bytes", bytes.len());
        }
        let mut arr = [0u8; 128];
        arr.copy_from_slice(&bytes);
        arr
    } else {
        test_accounts::get_secret(&args.signer)
            .with_context(|| format!("Unknown signer '{}'. Use alice, bob, charlie, or provide --secret-key", args.signer))?
    };

    let secret_hex = format!("0x{}", hex::encode(&secret_key));
    println!("🔑 Using {} SPHINCS+ secret key ({} bytes)", args.signer, secret_key.len());
    println!();

    // Read WASM file
    println!("📦 Reading WASM file: {:?}", args.wasm);
    let wasm_code = fs::read(&args.wasm)
        .context("Failed to read WASM file")?;
    let wasm_hex = format!("0x{}", hex::encode(&wasm_code));
    let num_chunks = (wasm_code.len() + CHUNK_SIZE - 1) / CHUNK_SIZE;

    println!("   Size: {} bytes ({} KB)", wasm_code.len(), wasm_code.len() / 1024);
    println!("   Chunks: {} ({}KB each)", num_chunks, CHUNK_SIZE / 1024);
    println!();

    // Build HTTP client with longer timeout
    let http_endpoint = if args.endpoint.starts_with("ws://") {
        args.endpoint.replace("ws://", "http://")
    } else if args.endpoint.starts_with("wss://") {
        args.endpoint.replace("wss://", "https://")
    } else {
        args.endpoint.clone()
    };

    println!("🌐 Connecting to: {}", http_endpoint);
    let client = HttpClientBuilder::default()
        .request_timeout(Duration::from_secs(120))
        .build(&http_endpoint)
        .context("Failed to create HTTP client")?;

    // Get current runtime version
    let version: serde_json::Value = client
        .request("state_getRuntimeVersion", rpc_params![])
        .await
        .context("Failed to get runtime version")?;

    let current_version = version["specVersion"].as_u64().unwrap_or(0);
    println!("   Current spec_version: {}", current_version);
    println!();

    if args.dry_run {
        println!("🔍 DRY RUN - No transactions will be submitted");
        println!();
        println!("Would perform:");
        println!("  1. Cancel any pending upgrade");
        println!("  2. Initiate chunked upgrade");
        for i in 0..num_chunks {
            let start = i * CHUNK_SIZE;
            let end = std::cmp::min(start + CHUNK_SIZE, wasm_code.len());
            println!("  {}. Upload chunk {} ({} bytes)", i + 3, i, end - start);
        }
        println!("  {}. Finalize upgrade", num_chunks + 3);
        return Ok(());
    }

    // Cancel any pending upgrade if requested or by default
    if args.cancel_pending {
        println!("🗑️  Cancelling any pending upgrade...");
        let cancel_result: Result<serde_json::Value, _> = client
            .request("chunkedUpgrade_cancel", rpc_params![&secret_hex])
            .await;
        match cancel_result {
            Ok(_) => println!("   Cancelled"),
            Err(e) => println!("   No pending upgrade or cancel failed: {}", e),
        }
        println!();

        // Wait for transaction to clear
        tokio::time::sleep(Duration::from_secs(args.block_time)).await;
    }

    // Check status - may return null if no pending upgrade
    println!("📊 Checking upgrade status...");
    let status: Option<StatusResult> = client
        .request("chunkedUpgrade_status", rpc_params![])
        .await
        .context("Failed to get upgrade status")?;

    match status {
        Some(s) if s.pending => {
            println!("   ⚠️  Pending upgrade detected: {:?}", s.upgrade_id);
            println!("   Use --cancel-pending to cancel it first");
            bail!("Pending upgrade exists");
        }
        Some(_) => println!("   No pending upgrades"),
        None => println!("   No pending upgrades (empty)"),
    }
    println!();

    // Step 1: Initiate
    println!("[1/3] Initiating chunked upgrade...");
    let init_result: InitiateResult = client
        .request("chunkedUpgrade_initiate", rpc_params![&wasm_hex, &secret_hex])
        .await
        .context("Failed to initiate upgrade")?;

    println!("   Upgrade ID: {}", init_result.upgrade_id);
    println!("   Expected chunks: {}", init_result.total_chunks);
    println!();

    // Step 2: Upload chunks
    // IMPORTANT: Wait for the initiate transaction to be included first
    println!("   Waiting for initiate tx to be included...");
    tokio::time::sleep(Duration::from_secs(args.block_time + 2)).await;

    println!("[2/3] Uploading {} chunks...", num_chunks);
    for i in 0..num_chunks {
        let start = i * CHUNK_SIZE;
        let end = std::cmp::min(start + CHUNK_SIZE, wasm_code.len());
        let chunk = &wasm_code[start..end];
        let chunk_hex = format!("0x{}", hex::encode(chunk));

        // Retry loop for transaction priority issues
        let mut retries = 3;
        let mut success = false;
        while retries > 0 && !success {
            // The RPC returns a transaction hash string, not a ChunkResult struct
            let chunk_result: Result<String, _> = client
                .request("chunkedUpgrade_uploadChunk", rpc_params![i as u32, &chunk_hex, &secret_hex])
                .await;

            match chunk_result {
                Ok(tx_hash) => {
                    println!("   ✓ Chunk {}/{} ({} bytes) - tx: {}",
                        i + 1, num_chunks, chunk.len(), tx_hash);
                    success = true;
                }
                Err(e) => {
                    let err_str = format!("{}", e);
                    if err_str.contains("priority") || err_str.contains("Too low") {
                        retries -= 1;
                        if retries > 0 {
                            println!("   ⚠ Chunk {} priority conflict, waiting and retrying...", i);
                            tokio::time::sleep(Duration::from_secs(args.block_time)).await;
                        } else {
                            println!("   ❌ Chunk {} failed after retries: {}", i, e);
                            bail!("Chunk upload failed after retries");
                        }
                    } else {
                        println!("   ❌ Chunk {} failed: {}", i, e);
                        bail!("Chunk upload failed");
                    }
                }
            }
        }

        // Wait for block inclusion between chunks
        if i < num_chunks - 1 {
            tokio::time::sleep(Duration::from_secs(args.block_time)).await;
        }
    }
    println!();

    // Step 3: Finalize
    println!("[3/3] Finalizing upgrade...");
    let finalize_result: serde_json::Value = client
        .request("chunkedUpgrade_finalize", rpc_params![&secret_hex])
        .await
        .context("Failed to finalize upgrade")?;

    println!("   Transaction submitted: {:?}", finalize_result);
    println!();

    // Wait and verify
    println!("⏳ Waiting for upgrade to take effect...");
    for i in 0..12 {
        tokio::time::sleep(Duration::from_secs(10)).await;

        let new_version: serde_json::Value = client
            .request("state_getRuntimeVersion", rpc_params![])
            .await
            .context("Failed to get runtime version")?;

        let new_spec = new_version["specVersion"].as_u64().unwrap_or(0);

        if new_spec != current_version {
            println!();
            println!("🎉 UPGRADE SUCCESSFUL!");
            println!("   Old version: {}", current_version);
            println!("   New version: {}", new_spec);
            return Ok(());
        }

        println!("   {}s - still at version {}", (i + 1) * 10, new_spec);
    }

    println!();
    println!("⚠️  Timeout - upgrade may still be processing");
    println!("   Check node logs for errors");
    Ok(())
}
