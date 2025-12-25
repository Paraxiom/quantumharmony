//! Quantum Wallet Web Server
//! 
//! Serves the QPP wallet UI and API, using quantum tunnels for secure
//! communication with KIRQ network nodes.

use wallet::{QPPWallet, TunneledWallet, wallet::{Locked}};
use warp::{Filter, Reply, Rejection};
use serde::{Serialize, Deserialize};
use std::sync::{Arc, Mutex};
use log::info;
use clap::Parser;

/// Command line arguments
#[derive(Parser, Debug)]
#[clap(author, version, about = "Quantum Wallet Web Server")]
struct Args {
    /// Port to listen on
    #[clap(short, long, default_value = "3030")]
    port: u16,
    
    /// TLS certificate path
    #[clap(long)]
    cert: Option<String>,
    
    /// TLS key path
    #[clap(long)]
    key: Option<String>,
    
    /// Tunnel server address
    #[clap(short, long, default_value = "127.0.0.1:9999")]
    tunnel: String,
    
    /// Enable CORS for development
    #[clap(long)]
    cors: bool,
}

/// API response types
#[derive(Serialize)]
struct AccountsResponse {
    accounts: Vec<AccountInfo>,
}

#[derive(Serialize)]
struct AccountInfo {
    address: String,
    name: String,
    account_type: String,
    balance: String,
}

#[derive(Deserialize)]
struct SignRequest {
    tx_data: String,
    account_index: u32,
    use_quantum: bool,
}

#[derive(Serialize)]
struct SignResponse {
    signature: String,
    tx_hash: String,
}

#[derive(Serialize)]
struct HealthResponse {
    status: String,
    version: String,
    tunnel_active: bool,
    accounts_loaded: bool,
}

/// Shared application state
struct AppState {
    wallet: Arc<Mutex<TunneledWallet>>,
    tunnel_connected: Arc<Mutex<bool>>,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    env_logger::init();
    let args = Args::parse();
    
    info!("Starting Quantum Wallet Web Server on port {}", args.port);
    
    // Initialize wallet
    let wallet = QPPWallet::<Locked>::new();
    let password = std::env::var("WALLET_PASSWORD")
        .unwrap_or_else(|_| "default_password".to_string());
    let wallet = wallet.unlock(&password)?;
    
    // Create tunneled wallet
    let tunneled = TunneledWallet::new(
        wallet,
        args.tunnel.clone(),
        false, // QKD comes from KIRQ clients
    );
    
    // Application state
    let state = Arc::new(AppState {
        wallet: Arc::new(Mutex::new(tunneled)),
        tunnel_connected: Arc::new(Mutex::new(false)),
    });
    
    // API routes
    let api = warp::path("api");
    
    // Health check endpoint
    let health = api
        .and(warp::path("health"))
        .and(warp::get())
        .and(with_state(state.clone()))
        .and_then(health_handler);
    
    // Get accounts
    let accounts = api
        .and(warp::path("accounts"))
        .and(warp::get())
        .and(with_state(state.clone()))
        .and_then(accounts_handler);
    
    // Sign transaction
    let sign = api
        .and(warp::path("sign"))
        .and(warp::post())
        .and(warp::body::json())
        .and(with_state(state.clone()))
        .and_then(sign_handler);
    
    // Tunnel statistics
    let tunnel_stats = api
        .and(warp::path("tunnel"))
        .and(warp::path("stats"))
        .and(warp::get())
        .and(with_state(state.clone()))
        .and_then(tunnel_stats_handler);

    // Docker management endpoints
    let docker_status = api
        .and(warp::path("docker"))
        .and(warp::path("status"))
        .and(warp::get())
        .and_then(docker_status_handler);

    let docker_start = api
        .and(warp::path("docker"))
        .and(warp::path("start"))
        .and(warp::post())
        .and(warp::body::json())
        .and_then(docker_start_handler);

    let docker_stop = api
        .and(warp::path("docker"))
        .and(warp::path("stop"))
        .and(warp::post())
        .and(warp::body::json())
        .and_then(docker_stop_handler);

    let docker_purge = api
        .and(warp::path("docker"))
        .and(warp::path("purge"))
        .and(warp::post())
        .and(warp::body::json())
        .and_then(docker_purge_handler);

    let docker_deep_clean = api
        .and(warp::path("docker"))
        .and(warp::path("deep-clean"))
        .and(warp::post())
        .and_then(docker_deep_clean_handler);

    let docker_nuke = api
        .and(warp::path("docker"))
        .and(warp::path("nuke-all"))
        .and(warp::post())
        .and_then(docker_nuke_handler);

    // Static files (wallet UI)
    let static_files = warp::fs::dir("./wallet/static");

    // Combine routes
    let routes = health
        .or(accounts)
        .or(sign)
        .or(tunnel_stats)
        .or(docker_status)
        .or(docker_start)
        .or(docker_stop)
        .or(docker_purge)
        .or(docker_deep_clean)
        .or(docker_nuke)
        .or(static_files);
    
    // Add CORS if enabled
    let routes = if args.cors {
        routes.with(warp::cors().allow_any_origin())
    } else {
        routes.with(warp::cors().allow_origins(vec!["https://yourdomain.com"]))
    };
    
    // Start server
    if let (Some(_cert), Some(_key)) = (args.cert, args.key) {
        // TODO: HTTPS support requires warp-tls feature
        info!("TLS not yet implemented - starting HTTP server");
        warp::serve(routes)
            .run(([0, 0, 0, 0], args.port))
            .await;
    } else {
        // HTTP server (development only)
        info!("Starting HTTP server (development mode)");
        warp::serve(routes)
            .run(([0, 0, 0, 0], args.port))
            .await;
    }
    
    Ok(())
}

/// Helper to pass state to handlers
fn with_state(
    state: Arc<AppState>,
) -> impl Filter<Extract = (Arc<AppState>,), Error = std::convert::Infallible> + Clone {
    warp::any().map(move || state.clone())
}

/// Health check handler
async fn health_handler(state: Arc<AppState>) -> Result<impl Reply, Rejection> {
    let wallet = state.wallet.lock().unwrap();
    let stats = wallet.tunnel_stats();
    
    Ok(warp::reply::json(&HealthResponse {
        status: "healthy".to_string(),
        version: env!("CARGO_PKG_VERSION").to_string(),
        tunnel_active: stats.active_tunnels > 0,
        accounts_loaded: true,
    }))
}

/// Get accounts handler
async fn accounts_handler(_state: Arc<AppState>) -> Result<impl Reply, Rejection> {
    
    // In real implementation, get from wallet
    let accounts = vec![
        AccountInfo {
            address: "5GrwvaEF5zXb26Fz9rcQpDWS57CtERHpNehXCPcNoHGKutQY".to_string(),
            name: "Alice".to_string(),
            account_type: "quantum".to_string(),
            balance: "1000000".to_string(),
        },
        AccountInfo {
            address: "5FHneW46xGXgs5mUiveU4sbTyGBzmstUspZC92UhjJM694ty".to_string(),
            name: "Bob".to_string(),
            account_type: "hybrid".to_string(),
            balance: "500000".to_string(),
        },
    ];
    
    Ok(warp::reply::json(&AccountsResponse { accounts }))
}

/// Sign transaction handler
async fn sign_handler(
    req: SignRequest,
    _state: Arc<AppState>,
) -> Result<impl Reply, Rejection> {
    let tx_data = hex::decode(&req.tx_data)
        .map_err(|_| warp::reject::custom(InvalidInput))?;
    
    // In real implementation, sign with wallet
    let signature = if req.use_quantum {
        // Quantum signature (SPHINCS+)
        hex::encode(vec![0u8; 49152])
    } else {
        // Classical signature
        hex::encode(vec![0u8; 64])
    };
    
    let tx_hash = sp_core::blake2_256(&tx_data);
    
    Ok(warp::reply::json(&SignResponse {
        signature,
        tx_hash: hex::encode(tx_hash),
    }))
}

/// Tunnel statistics handler
async fn tunnel_stats_handler(state: Arc<AppState>) -> Result<impl Reply, Rejection> {
    let wallet = state.wallet.lock().unwrap();
    let stats = wallet.tunnel_stats();

    Ok(warp::reply::json(&serde_json::json!({
        "active_tunnels": stats.active_tunnels,
        "total_uptime": stats.total_uptime,
        "average_idle": stats.average_idle,
        "using_qkd": stats.using_qkd,
    })))
}

/// Docker status handler
async fn docker_status_handler() -> Result<impl Reply, Rejection> {
    let status = wallet::docker::get_status().await;
    Ok(warp::reply::json(&status))
}

/// Docker start handler
async fn docker_start_handler(req: wallet::docker::DockerStartRequest) -> Result<impl Reply, Rejection> {
    match wallet::docker::start_containers(&req.network_type).await {
        Ok(status) => Ok(warp::reply::json(&status)),
        Err(e) => Ok(warp::reply::json(&serde_json::json!({
            "error": e,
            "running": false,
            "containers": 0,
            "network_type": "none",
        }))),
    }
}

/// Docker stop handler
async fn docker_stop_handler(req: wallet::docker::DockerStopRequest) -> Result<impl Reply, Rejection> {
    match wallet::docker::stop_containers(&req.network_type).await {
        Ok(status) => Ok(warp::reply::json(&status)),
        Err(e) => Ok(warp::reply::json(&serde_json::json!({
            "error": e,
            "running": false,
            "containers": 0,
            "network_type": "none",
        }))),
    }
}

/// Docker purge handler
async fn docker_purge_handler(req: wallet::docker::DockerStopRequest) -> Result<impl Reply, Rejection> {
    match wallet::docker::purge_containers(&req.network_type).await {
        Ok(message) => Ok(warp::reply::json(&serde_json::json!({
            "success": true,
            "message": message,
        }))),
        Err(e) => Ok(warp::reply::json(&serde_json::json!({
            "success": false,
            "error": e,
        }))),
    }
}

/// Docker deep clean handler
async fn docker_deep_clean_handler() -> Result<impl Reply, Rejection> {
    match wallet::docker::deep_clean().await {
        Ok(message) => Ok(warp::reply::json(&serde_json::json!({
            "success": true,
            "message": message,
        }))),
        Err(e) => Ok(warp::reply::json(&serde_json::json!({
            "success": false,
            "error": e,
        }))),
    }
}

/// Docker nuclear clean handler
async fn docker_nuke_handler() -> Result<impl Reply, Rejection> {
    match wallet::docker::nuke_all().await {
        Ok(message) => Ok(warp::reply::json(&serde_json::json!({
            "success": true,
            "message": message,
        }))),
        Err(e) => Ok(warp::reply::json(&serde_json::json!({
            "success": false,
            "error": e,
        }))),
    }
}

/// Custom rejection for invalid input
#[derive(Debug)]
struct InvalidInput;
impl warp::reject::Reject for InvalidInput {}

/// Create the wallet UI HTML
pub fn create_wallet_ui() -> &'static str {
    r#"<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>QuantumHarmony QPP Wallet</title>
    <style>
        :root {
            --quantum-blue: #1a237e;
            --quantum-purple: #4a148c;
            --quantum-teal: #00796b;
            --bg-dark: #121212;
            --bg-card: #1e1e1e;
            --text-primary: #ffffff;
            --text-secondary: #b0b0b0;
        }
        
        body {
            font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;
            background: var(--bg-dark);
            color: var(--text-primary);
            margin: 0;
            padding: 0;
        }
        
        .container {
            max-width: 1200px;
            margin: 0 auto;
            padding: 20px;
        }
        
        .header {
            text-align: center;
            padding: 40px 0;
            background: linear-gradient(135deg, var(--quantum-blue), var(--quantum-purple));
            margin: -20px -20px 40px -20px;
        }
        
        .header h1 {
            margin: 0;
            font-size: 2.5em;
            font-weight: 300;
        }
        
        .card {
            background: var(--bg-card);
            border-radius: 12px;
            padding: 24px;
            margin-bottom: 24px;
            box-shadow: 0 4px 6px rgba(0, 0, 0, 0.3);
        }
        
        .accounts-grid {
            display: grid;
            grid-template-columns: repeat(auto-fill, minmax(300px, 1fr));
            gap: 20px;
            margin-bottom: 40px;
        }
        
        .account-card {
            background: linear-gradient(135deg, var(--quantum-teal), var(--quantum-blue));
            padding: 20px;
            border-radius: 8px;
            cursor: pointer;
            transition: transform 0.2s;
        }
        
        .account-card:hover {
            transform: translateY(-2px);
        }
        
        .quantum-badge {
            background: rgba(255, 255, 255, 0.2);
            padding: 4px 8px;
            border-radius: 4px;
            font-size: 0.8em;
            display: inline-block;
            margin-top: 8px;
        }
        
        .tunnel-status {
            position: fixed;
            bottom: 20px;
            right: 20px;
            background: var(--bg-card);
            padding: 16px;
            border-radius: 8px;
            display: flex;
            align-items: center;
            gap: 12px;
        }
        
        .status-indicator {
            width: 12px;
            height: 12px;
            border-radius: 50%;
            background: #4caf50;
            animation: pulse 2s infinite;
        }
        
        @keyframes pulse {
            0%, 100% { opacity: 1; }
            50% { opacity: 0.5; }
        }
        
        button {
            background: linear-gradient(135deg, var(--quantum-purple), var(--quantum-teal));
            border: none;
            color: white;
            padding: 12px 24px;
            border-radius: 6px;
            cursor: pointer;
            font-size: 16px;
            transition: opacity 0.2s;
        }
        
        button:hover {
            opacity: 0.9;
        }
    </style>
</head>
<body>
    <div class="header">
        <h1>QuantumHarmony QPP Wallet</h1>
        <p>Quantum-Safe Wallet with Post-Quantum Cryptography</p>
    </div>
    
    <div class="container">
        <div class="card">
            <h2>Your Accounts</h2>
            <div class="accounts-grid" id="accounts"></div>
        </div>
        
        <div class="card">
            <h2>Send Transaction</h2>
            <div>
                <textarea id="txData" placeholder="Enter transaction data..." rows="4" style="width: 100%;"></textarea>
                <br><br>
                <label>
                    <input type="checkbox" id="useQuantum" checked> Use Quantum Signature (SPHINCS+)
                </label>
                <br><br>
                <button onclick="signTransaction()">Sign Transaction</button>
            </div>
        </div>
    </div>
    
    <div class="tunnel-status">
        <div class="status-indicator"></div>
        <span>Quantum Tunnel Active</span>
    </div>
    
    <script>
        async function loadAccounts() {
            const response = await fetch('/api/accounts');
            const data = await response.json();
            
            const container = document.getElementById('accounts');
            container.innerHTML = data.accounts.map(account => `
                <div class="account-card">
                    <h3>${account.name}</h3>
                    <p style="font-size: 0.8em; word-break: break-all;">${account.address}</p>
                    <p>Balance: ${account.balance}</p>
                    <span class="quantum-badge">${account.account_type}</span>
                </div>
            `).join('');
        }
        
        async function signTransaction() {
            const txData = document.getElementById('txData').value;
            const useQuantum = document.getElementById('useQuantum').checked;
            
            const response = await fetch('/api/sign', {
                method: 'POST',
                headers: { 'Content-Type': 'application/json' },
                body: JSON.stringify({
                    tx_data: txData,
                    account_index: 0,
                    use_quantum: useQuantum
                })
            });
            
            const result = await response.json();
            alert(`Transaction signed!\nHash: ${result.tx_hash}`);
        }
        
        // Load accounts on page load
        loadAccounts();
        
        // Refresh every 30 seconds
        setInterval(loadAccounts, 30000);
    </script>
</body>
</html>"#
}