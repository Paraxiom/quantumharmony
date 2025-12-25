# Quantum Tunnel Deployment Architecture

## KIRQ Network ↔ Droplet Tunnel Configuration

### Overview

This architecture allows you to:
1. Run the QPP wallet on your cloud droplet
2. Establish quantum-secure tunnels to KIRQ network nodes
3. Serve the wallet UI publicly while keeping quantum operations secure
4. Bridge between your local KIRQ network and cloud infrastructure

```
┌─────────────────────────┐         ┌─────────────────────────┐
│     KIRQ Network        │         │    Cloud Droplet        │
│   (Local/Private)       │         │    (Public IP)          │
│                         │         │                         │
│  ┌─────────────────┐   │         │  ┌─────────────────┐   │
│  │ Quantum Node    │   │         │  │  QPP Wallet     │   │
│  │ (Substrate)     │   │         │  │  (Web Server)   │   │
│  └────────┬────────┘   │         │  └────────┬────────┘   │
│           │            │         │           │            │
│  ┌────────▼────────┐   │         │  ┌────────▼────────┐   │
│  │ Quantum Tunnel  │◄──┼─────────┼──►│ Quantum Tunnel  │   │
│  │ (Client)        │   │ INTERNET│  │ (Server)        │   │
│  └─────────────────┘   │         │  └─────────────────┘   │
│                         │         │                         │
│  ┌─────────────────┐   │         │  ┌─────────────────┐   │
│  │ QKD Hardware    │   │         │  │  Public Web UI  │   │
│  │ (Optional)      │   │         │  │  (Port 443)     │   │
│  └─────────────────┘   │         │  └─────────────────┘   │
└─────────────────────────┘         └─────────────────────────┘
```

## Implementation Steps

### 1. Droplet Setup

```bash
# On your droplet
cd /opt/quantum-harmony

# Install dependencies
sudo apt update
sudo apt install -y build-essential pkg-config libssl-dev

# Install Rust
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
source $HOME/.cargo/env

# Clone and build QPP wallet
git clone https://github.com/QuantumVerseProtocols/quantumharmony.git
cd quantumharmony/active-projects/quantum-harmony/quantum-node-fresh/quantum-substrate/quantum-qpp-wallet
cargo build --release --features std
```

### 2. Tunnel Server Configuration

Create a tunnel server configuration file:

```rust
// tunnel-server-config.rs
use quantum_qpp_wallet::{TunnelConfig, TunnelServer};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    env_logger::init();

    let config = TunnelConfig {
        local_addr: "0.0.0.0:9999".to_string(), // Listen on all interfaces
        remote_addr: String::new(), // Will be set per connection
        key_rotation_interval: 1000,
        post_quantum: true,
        use_qkd: false, // Enable if you have QKD hardware
    };

    // Create tunnel server
    let server = TunnelServer::new(config);
    
    // Start listening
    tokio::runtime::Runtime::new()?
        .block_on(server.listen())?;

    Ok(())
}
```

### 3. Web UI Server

Create a web server that uses the tunneled wallet:

```rust
// wallet-web-server.rs
use quantum_qpp_wallet::{QPPWallet, TunneledWallet};
use warp::Filter;

#[tokio::main]
async fn main() {
    // Initialize wallet
    let wallet = QPPWallet::new();
    let wallet = wallet.unlock(std::env::var("WALLET_PASSWORD").unwrap()).unwrap();
    
    // Create tunneled wallet
    let tunneled = TunneledWallet::new(
        wallet,
        "127.0.0.1:9999".to_string(),
        false, // QKD via tunnel from KIRQ network
    );

    // Web routes
    let routes = warp::path("api")
        .and(warp::path("accounts"))
        .map(move || {
            // Handle account requests via tunnel
            warp::reply::json(&"accounts")
        });

    // Serve on port 443 with TLS (initial connection only)
    warp::serve(routes)
        .tls()
        .cert_path("/etc/letsencrypt/live/yourdomain/fullchain.pem")
        .key_path("/etc/letsencrypt/live/yourdomain/privkey.pem")
        .run(([0, 0, 0, 0], 443))
        .await;
}
```

### 4. KIRQ Network Client

On your KIRQ network node:

```rust
// kirq-tunnel-client.rs
use quantum_qpp_wallet::{QuantumTunnel, TunnelConfig};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let config = TunnelConfig {
        local_addr: "192.168.0.100:9998".to_string(), // Your KIRQ IP
        remote_addr: "your.droplet.ip:9999".to_string(),
        key_rotation_interval: 1000,
        post_quantum: true,
        use_qkd: true, // Use local QKD hardware
    };

    // Connect to droplet
    let tunnel = QuantumTunnel::new(config);
    let established = tunnel.handshake().await?;
    
    println!("Quantum tunnel established to droplet!");
    
    // Inject QKD entropy periodically
    loop {
        let entropy = get_qkd_entropy_from_hardware()?;
        established.inject_quantum_entropy(
            entropy,
            "KIRQ_QKD_001".to_string(),
            255,
        )?;
        
        tokio::time::sleep(Duration::from_secs(60)).await;
    }
}
```

## Security Architecture

### Network Isolation

1. **KIRQ Network (Private)**
   - Quantum hardware access
   - Substrate node operations
   - QKD key generation

2. **Quantum Tunnel (Encrypted)**
   - Post-quantum secure channel
   - Key rotation every 1000 blocks
   - QKD entropy injection

3. **Droplet (Public)**
   - Web UI serving
   - API endpoints
   - No direct quantum hardware access

### Firewall Configuration

```bash
# On droplet
sudo ufw allow 22/tcp    # SSH
sudo ufw allow 443/tcp   # HTTPS
sudo ufw allow 9999/tcp  # Quantum tunnel
sudo ufw enable

# Restrict tunnel port to KIRQ network
sudo iptables -A INPUT -p tcp --dport 9999 -s YOUR_KIRQ_IP -j ACCEPT
sudo iptables -A INPUT -p tcp --dport 9999 -j DROP
```

## Deployment Script

Create a systemd service for the tunnel server:

```ini
# /etc/systemd/system/quantum-tunnel.service
[Unit]
Description=Quantum Tunnel Server
After=network.target

[Service]
Type=simple
User=quantum
WorkingDirectory=/opt/quantum-harmony
ExecStart=/opt/quantum-harmony/target/release/tunnel-server
Restart=always
RestartSec=10
Environment="RUST_LOG=info"

[Install]
WantedBy=multi-user.target
```

Enable and start:
```bash
sudo systemctl enable quantum-tunnel
sudo systemctl start quantum-tunnel
sudo systemctl status quantum-tunnel
```

## Monitoring

### Tunnel Health Check

```rust
// Add to your tunnel server
async fn health_check() -> impl warp::Reply {
    let stats = TUNNEL_STATS.lock().unwrap();
    warp::reply::json(&json!({
        "status": "healthy",
        "active_tunnels": stats.active_tunnels,
        "total_messages": stats.total_messages,
        "last_qkd_injection": stats.last_qkd_injection,
        "uptime": stats.uptime_seconds,
    }))
}
```

### Prometheus Metrics

```rust
use prometheus::{Counter, Gauge, Registry};

lazy_static! {
    static ref TUNNEL_CONNECTIONS: Gauge = Gauge::new(
        "quantum_tunnel_active_connections",
        "Number of active quantum tunnels"
    ).unwrap();
    
    static ref QKD_INJECTIONS: Counter = Counter::new(
        "quantum_tunnel_qkd_injections_total",
        "Total QKD entropy injections"
    ).unwrap();
}
```

## Advanced Features

### 1. Multi-Region Tunneling

Connect multiple KIRQ networks to your droplet:

```rust
let mut multi_tunnel = MultiRegionTunnel::new();
multi_tunnel.add_region("kirq-us", "192.168.1.100:9998");
multi_tunnel.add_region("kirq-eu", "192.168.2.100:9998");
multi_tunnel.add_region("kirq-asia", "192.168.3.100:9998");
```

### 2. Load Balancing

Distribute requests across tunnels:

```rust
impl LoadBalancer {
    fn select_tunnel(&self) -> &EstablishedTunnel {
        // Round-robin or least-loaded selection
        self.tunnels[self.current % self.tunnels.len()]
    }
}
```

### 3. Failover

Automatic failover between tunnels:

```rust
async fn send_with_failover(&self, msg: Message) -> Result<()> {
    for tunnel in &self.tunnels {
        match tunnel.send(msg.clone()).await {
            Ok(_) => return Ok(()),
            Err(e) => log::warn!("Tunnel failed: {:?}, trying next", e),
        }
    }
    Err("All tunnels failed")
}
```

## Testing

1. **Local Testing**
   ```bash
   # Terminal 1: Run tunnel server
   cargo run --example tunnel_server

   # Terminal 2: Run KIRQ client
   cargo run --example kirq_client

   # Terminal 3: Test web UI
   curl https://localhost/api/accounts
   ```

2. **Network Testing**
   ```bash
   # Test tunnel connectivity
   nc -zv your.droplet.ip 9999

   # Monitor tunnel traffic
   sudo tcpdump -i any port 9999
   ```

## Conclusion

This architecture provides:
- ✅ Quantum-secure communication between KIRQ and cloud
- ✅ Public web interface without exposing quantum operations
- ✅ QKD entropy distribution from hardware to cloud
- ✅ Post-quantum security throughout the stack
- ✅ Scalable multi-region support

The quantum tunnel ensures that even if traditional TLS is compromised by quantum computers, your KIRQ↔Droplet communication remains secure.