//! Quantum Tunnel Server for Droplet Deployment
//! 
//! This runs on your cloud droplet to accept quantum tunnel connections
//! from KIRQ network nodes.

use wallet::{
    quantum_tunnel::{TunnelConfig, TunnelMessage},
    TunneledWallet,
};
use std::sync::{Arc, Mutex};
use tokio::net::TcpListener;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use log::{info, error, debug};
use clap::Parser;
use std::collections::HashMap;
use scale_codec::Encode;

/// Command line arguments
#[derive(Parser, Debug)]
#[clap(author, version, about = "Quantum Tunnel Server for QPP Wallet")]
struct Args {
    /// Address to listen on
    #[clap(short, long, default_value = "0.0.0.0:9999")]
    listen: String,
    
    /// Enable QKD support
    #[clap(short, long)]
    qkd: bool,
    
    /// Key rotation interval in blocks
    #[clap(short, long, default_value = "1000")]
    rotation_interval: u64,
    
    /// Allowed KIRQ network IPs (comma separated)
    #[clap(short, long)]
    allowed_ips: Option<String>,
}

/// Global state for tunnel connections
struct TunnelState {
    /// Active tunnels mapped by peer address
    tunnels: HashMap<String, Arc<Mutex<TunneledWallet>>>,
    /// Statistics
    stats: TunnelStats,
}

#[derive(Default)]
struct TunnelStats {
    total_connections: u64,
    active_connections: u64,
    total_messages: u64,
    total_qkd_injections: u64,
    last_activity: Option<std::time::Instant>,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    env_logger::init();
    let args = Args::parse();
    
    info!("Starting Quantum Tunnel Server on {}", args.listen);
    
    // Parse allowed IPs
    let allowed_ips: Vec<String> = args.allowed_ips
        .map(|ips| ips.split(',').map(|s| s.trim().to_string()).collect())
        .unwrap_or_default();
    
    if !allowed_ips.is_empty() {
        info!("Restricting connections to IPs: {:?}", allowed_ips);
    }
    
    // Global state
    let state = Arc::new(Mutex::new(TunnelState {
        tunnels: HashMap::new(),
        stats: TunnelStats::default(),
    }));
    
    // Start metrics server
    let metrics_state = state.clone();
    tokio::spawn(async move {
        start_metrics_server(metrics_state).await;
    });
    
    // Create listener
    let listener = TcpListener::bind(&args.listen).await?;
    info!("Quantum tunnel server listening on {}", args.listen);
    
    // Accept connections
    loop {
        let (stream, addr) = listener.accept().await?;
        let peer_addr = addr.to_string();
        let peer_ip = addr.ip().to_string();
        
        // Check if IP is allowed
        if !allowed_ips.is_empty() && !allowed_ips.contains(&peer_ip) {
            error!("Rejecting connection from unauthorized IP: {}", peer_ip);
            continue;
        }
        
        info!("New tunnel connection from {}", peer_addr);
        
        // Update stats
        {
            let mut s = state.lock().unwrap();
            s.stats.total_connections += 1;
            s.stats.active_connections += 1;
            s.stats.last_activity = Some(std::time::Instant::now());
        }
        
        // Handle connection
        let state_clone = state.clone();
        let state_cleanup = state.clone();
        let config = TunnelConfig {
            local_addr: args.listen.clone(),
            remote_addr: peer_addr.clone(),
            key_rotation_interval: args.rotation_interval,
            post_quantum: true,
            use_qkd: args.qkd,
        };
        
        tokio::spawn(async move {
            if let Err(e) = handle_tunnel_connection(stream, config, state_clone, peer_addr.clone()).await {
                error!("Tunnel error for {}: {:?}", peer_addr, e);
            }
            
            // Clean up on disconnect
            let mut s = state_cleanup.lock().unwrap();
            s.tunnels.remove(&peer_addr);
            s.stats.active_connections -= 1;
            info!("Tunnel disconnected: {}", peer_addr);
        });
    }
}

/// Handle individual tunnel connection
async fn handle_tunnel_connection(
    mut stream: tokio::net::TcpStream,
    config: TunnelConfig,
    state: Arc<Mutex<TunnelState>>,
    peer_addr: String,
) -> Result<(), Box<dyn std::error::Error>> {
    // Create wallet for this connection
    let wallet = wallet::QPPWallet::new();
    let wallet = wallet.unlock("server_wallet_password")?; // In production, use env var
    
    // Create tunneled wallet
    let tunneled = TunneledWallet::new(wallet, config.local_addr.clone(), config.use_qkd);
    let tunneled = Arc::new(Mutex::new(tunneled));
    
    // Store in state
    {
        let mut s = state.lock().unwrap();
        s.tunnels.insert(peer_addr.clone(), tunneled.clone());
    }
    
    // Message handling loop
    let mut buffer = vec![0u8; 65536];
    loop {
        // Read message length
        let n = match stream.read(&mut buffer).await {
            Ok(0) => break, // Connection closed
            Ok(n) => n,
            Err(e) => {
                error!("Read error: {:?}", e);
                break;
            }
        };
        
        // Process message through tunnel
        let process_result = tunneled.lock().unwrap().process_incoming(&buffer[..n], &peer_addr);
        
        match process_result {
            Ok(_) => {
                let mut s = state.lock().unwrap();
                s.stats.total_messages += 1;
                s.stats.last_activity = Some(std::time::Instant::now());
                
                debug!("Processed message from {}", peer_addr);
            }
            Err(e) => {
                error!("Message processing error: {:?}", e);
                
                // Send error response
                let error_msg = TunnelMessage::Error {
                    code: 500,
                    message: format!("Processing error: {:?}", e),
                };
                
                let encoded = error_msg.encode();
                let _ = stream.write_all(&encoded).await;
            }
        }
    }
    
    Ok(())
}

/// Start metrics server for monitoring
async fn start_metrics_server(state: Arc<Mutex<TunnelState>>) {
    use warp::Filter;
    
    let metrics = warp::path("metrics")
        .map(move || {
            let s = state.lock().unwrap();
            let uptime = s.stats.last_activity
                .map(|t| std::time::Instant::now().duration_since(t).as_secs())
                .unwrap_or(0);
            
            format!(
                r#"# HELP quantum_tunnel_connections_total Total tunnel connections
# TYPE quantum_tunnel_connections_total counter
quantum_tunnel_connections_total {}

# HELP quantum_tunnel_active_connections Active tunnel connections
# TYPE quantum_tunnel_active_connections gauge
quantum_tunnel_active_connections {}

# HELP quantum_tunnel_messages_total Total messages processed
# TYPE quantum_tunnel_messages_total counter
quantum_tunnel_messages_total {}

# HELP quantum_tunnel_qkd_injections_total Total QKD entropy injections
# TYPE quantum_tunnel_qkd_injections_total counter
quantum_tunnel_qkd_injections_total {}

# HELP quantum_tunnel_uptime_seconds Tunnel server uptime
# TYPE quantum_tunnel_uptime_seconds gauge
quantum_tunnel_uptime_seconds {}
"#,
                s.stats.total_connections,
                s.stats.active_connections,
                s.stats.total_messages,
                s.stats.total_qkd_injections,
                uptime
            )
        });
    
    let health = warp::path("health")
        .map(|| warp::reply::json(&serde_json::json!({
            "status": "healthy",
            "service": "quantum-tunnel-server"
        })));
    
    let routes = metrics.or(health);
    
    info!("Metrics server listening on :9090");
    warp::serve(routes)
        .run(([0, 0, 0, 0], 9090))
        .await;
}