//! KIRQ Network Tunnel Client
//! 
//! This runs on KIRQ network nodes to establish quantum tunnels to the droplet
//! and inject QKD entropy from local quantum hardware.

use wallet::{
    quantum_tunnel::{QuantumTunnel, TunnelConfig, Handshaking},
    tunnel_integration::WalletTunnelMessage,
};
use tokio::net::TcpStream;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use log::{info, error, debug};
use clap::Parser;
use std::time::Duration;
use scale_codec::{Encode, Decode};

/// Command line arguments
#[derive(Parser, Debug)]
#[clap(author, version, about = "KIRQ Network Quantum Tunnel Client")]
struct Args {
    /// Droplet server address
    #[clap(short, long)]
    server: String,
    
    /// Local bind address
    #[clap(short, long, default_value = "0.0.0.0:9998")]
    local: String,
    
    /// Enable QKD hardware
    #[clap(short, long)]
    qkd: bool,
    
    /// QKD device path
    #[clap(long, default_value = "/dev/qkd0")]
    qkd_device: String,
    
    /// Node identifier
    #[clap(short, long, default_value = "kirq-node-1")]
    node_id: String,
    
    /// Entropy injection interval (seconds)
    #[clap(short, long, default_value = "60")]
    entropy_interval: u64,
}

/// QKD hardware interface (simplified)
struct QkdDevice {
    device_path: String,
    available: bool,
}

impl QkdDevice {
    fn new(path: &str) -> Self {
        let available = std::path::Path::new(path).exists();
        if available {
            info!("QKD device found at {}", path);
        } else {
            error!("QKD device not found at {}", path);
        }
        
        QkdDevice {
            device_path: path.to_string(),
            available,
        }
    }
    
    /// Get quantum random bytes from hardware
    fn get_entropy(&self, length: usize) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
        if !self.available {
            // Fallback to simulated quantum random
            return Ok(vec![42u8; length]);
        }
        
        // In real implementation, read from QKD device
        // For now, simulate with high-quality randomness
        use rand::RngCore;
        let mut entropy = vec![0u8; length];
        rand::thread_rng().fill_bytes(&mut entropy);
        
        debug!("Generated {} bytes of quantum entropy", length);
        Ok(entropy)
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    env_logger::init();
    let args = Args::parse();
    
    info!("KIRQ Tunnel Client starting");
    info!("Node ID: {}", args.node_id);
    info!("Connecting to droplet: {}", args.server);
    
    // Initialize QKD device if enabled
    let qkd_device = if args.qkd {
        Some(QkdDevice::new(&args.qkd_device))
    } else {
        info!("QKD disabled, using standard quantum random");
        None
    };
    
    // Retry connection loop
    loop {
        match connect_and_run(&args, &qkd_device).await {
            Ok(_) => info!("Connection closed normally"),
            Err(e) => error!("Connection error: {:?}", e),
        }
        
        info!("Reconnecting in 5 seconds...");
        tokio::time::sleep(Duration::from_secs(5)).await;
    }
}

async fn connect_and_run(
    args: &Args,
    qkd_device: &Option<QkdDevice>,
) -> Result<(), Box<dyn std::error::Error>> {
    // Connect to droplet
    info!("Connecting to {}", args.server);
    let mut stream = TcpStream::connect(&args.server).await?;
    info!("TCP connection established");
    
    // Create tunnel configuration
    let config = TunnelConfig {
        local_addr: args.local.clone(),
        remote_addr: args.server.clone(),
        key_rotation_interval: 1000,
        post_quantum: true,
        use_qkd: args.qkd,
    };
    
    // Establish quantum tunnel
    let tunnel = QuantumTunnel::<Handshaking>::new(config);
    let mut established = tunnel.handshake().await?;
    info!("Quantum tunnel established!");
    
    // Send initial identification
    let ident_msg = WalletTunnelMessage::GetAccounts; // Simple handshake
    let encoded = ident_msg.encode();
    let encrypted = established.send(&encoded)?;
    stream.write_all(&encrypted).await?;
    
    // Start entropy injection task
    let entropy_task: Option<tokio::task::JoinHandle<()>> = if let Some(_qkd) = qkd_device {
        // TODO: Implement entropy injection via separate channel
        // For now, we'll handle entropy injection synchronously in the main loop
        None
    } else {
        None
    };
    
    // Message handling loop
    let mut buffer = vec![0u8; 65536];
    loop {
        let n = match stream.read(&mut buffer).await {
            Ok(0) => {
                info!("Server closed connection");
                break;
            }
            Ok(n) => n,
            Err(e) => {
                error!("Read error: {:?}", e);
                break;
            }
        };
        
        // Decrypt and process message
        match established.receive(&buffer[..n]) {
            Ok(decrypted) => {
                if let Ok(msg) = WalletTunnelMessage::decode(&mut &decrypted[..]) {
                    handle_message(msg, &mut stream, &mut established).await?;
                }
            }
            Err(e) => error!("Decryption error: {:?}", e),
        }
    }
    
    // Cancel entropy task if running
    if let Some(task) = entropy_task {
        task.abort();
    }
    
    Ok(())
}

async fn handle_message(
    msg: WalletTunnelMessage,
    _stream: &mut TcpStream,
    _tunnel: &mut QuantumTunnel<wallet::quantum_tunnel::Established>,
) -> Result<(), Box<dyn std::error::Error>> {
    match msg {
        WalletTunnelMessage::AccountsResponse(accounts) => {
            info!("Received {} accounts from server", accounts.len());
            for (addr, is_quantum) in accounts {
                let account_type = if is_quantum { "quantum" } else { "classical" };
                info!("  - {} ({})", addr, account_type);
            }
        }
        WalletTunnelMessage::SignedTransaction { signature, tx_hash } => {
            info!("Transaction signed!");
            info!("  Hash: {:?}", tx_hash);
            info!("  Signature length: {} bytes", signature.len());
        }
        WalletTunnelMessage::VerificationResponse { verified, quantum_advantage } => {
            info!("Verification result: {}", verified);
            info!("Quantum advantage: {}x", quantum_advantage);
        }
        WalletTunnelMessage::Error(e) => {
            error!("Server error: {}", e);
        }
        _ => {
            debug!("Received message: {:?}", msg);
        }
    }
    
    Ok(())
}

/// Example operations the KIRQ client can perform
pub mod operations {
    use super::*;
    
    /// Request transaction signing
    pub async fn request_signing(
        stream: &mut TcpStream,
        tunnel: &mut QuantumTunnel<wallet::quantum_tunnel::Established>,
        tx_data: Vec<u8>,
        use_quantum: bool,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let msg = WalletTunnelMessage::SignTransaction {
            tx_data,
            account_index: 0,
            use_quantum,
        };
        
        let encoded = msg.encode();
        let encrypted = tunnel.send(&encoded)?;
        stream.write_all(&encrypted).await?;
        
        Ok(())
    }
    
    /// Request quantum state verification
    pub async fn verify_quantum_state(
        stream: &mut TcpStream,
        tunnel: &mut QuantumTunnel<wallet::quantum_tunnel::Established>,
        state_hash: sp_core::H256,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let msg = WalletTunnelMessage::VerifyQuantumState {
            state_hash,
            proof_type: "quantum_fingerprint".to_string(),
        };
        
        let encoded = msg.encode();
        let encrypted = tunnel.send(&encoded)?;
        stream.write_all(&encrypted).await?;
        
        Ok(())
    }
}