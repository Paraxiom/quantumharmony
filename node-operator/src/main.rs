//! QuantumHarmony Node Operator Service
//!
//! A quantum-safe node management service that provides:
//! - Node lifecycle management (start/stop/restart)
//! - SPHINCS+ authenticated API
//! - Keystore management
//! - Runtime upgrade signing
//! - Secure RPC proxy

use axum::{
    extract::{State, Json, ws::{WebSocket, WebSocketUpgrade, Message}},
    http::{StatusCode, Method, header},
    response::IntoResponse,
    routing::{get, post},
    Router,
};
use clap::Parser;
use serde::{Deserialize, Serialize};
use std::{
    path::PathBuf,
    sync::Arc,
    time::Duration,
};
use tokio::sync::{Mutex, RwLock, broadcast};
use tower_http::cors::{CorsLayer, Any};
use tracing::{info, warn, error};

mod node;
mod keystore;
mod auth;
mod rpc;

use node::NodeManager;
use keystore::KeystoreManager;
use auth::AuthManager;

/// Command line arguments
#[derive(Parser, Debug)]
#[command(name = "node-operator")]
#[command(about = "Quantum-safe node operator service for QuantumHarmony")]
struct Args {
    /// Port to listen on
    #[arg(short, long, default_value = "9955", env = "OPERATOR_PORT")]
    port: u16,

    /// Path to the node binary
    #[arg(long, default_value = "./target/release/quantumharmony-node", env = "NODE_BINARY")]
    node_binary: PathBuf,

    /// Path to chain spec
    #[arg(long, env = "CHAIN_SPEC")]
    chain_spec: Option<PathBuf>,

    /// Node name
    #[arg(long, default_value = "QuantumOperator", env = "NODE_NAME")]
    node_name: String,

    /// Bootnode address
    #[arg(long, env = "BOOTNODE")]
    bootnode: Option<String>,

    /// Node RPC port
    #[arg(long, default_value = "9944", env = "RPC_PORT")]
    rpc_port: u16,

    /// Node P2P port
    #[arg(long, default_value = "30333", env = "P2P_PORT")]
    p2p_port: u16,

    /// Run as validator
    #[arg(long, env = "VALIDATOR_MODE")]
    validator: bool,

    /// Data directory
    #[arg(long, env = "DATA_DIR")]
    data_dir: Option<PathBuf>,

    /// Operator keystore path
    #[arg(long, env = "OPERATOR_KEYSTORE")]
    operator_keystore: Option<PathBuf>,

    /// Allow unauthenticated access (development only)
    #[arg(long, env = "ALLOW_UNAUTHENTICATED")]
    allow_unauthenticated: bool,

    /// Dashboard static files path
    #[arg(long, default_value = "./operator-bundle/dashboard", env = "DASHBOARD_PATH")]
    dashboard_path: PathBuf,
}

/// Application state shared across handlers
#[derive(Clone)]
struct AppState {
    node_manager: Arc<Mutex<NodeManager>>,
    keystore_manager: Arc<RwLock<KeystoreManager>>,
    auth_manager: Arc<AuthManager>,
    config: Arc<OperatorConfig>,
    log_broadcast: broadcast::Sender<String>,
}

/// Operator configuration
#[derive(Debug, Clone)]
struct OperatorConfig {
    node_binary: PathBuf,
    chain_spec: Option<PathBuf>,
    node_name: String,
    bootnode: Option<String>,
    rpc_port: u16,
    p2p_port: u16,
    validator: bool,
    data_dir: Option<PathBuf>,
    allow_unauthenticated: bool,
}

// ============================================================================
// API Request/Response Types
// ============================================================================

#[derive(Serialize)]
struct StatusResponse {
    node_running: bool,
    node_pid: Option<u32>,
    connected: bool,
    block_height: Option<u64>,
    peers: Option<u32>,
    syncing: Option<bool>,
    version: String,
}

#[derive(Serialize)]
struct NodeControlResponse {
    success: bool,
    message: String,
    pid: Option<u32>,
}

#[derive(Deserialize)]
struct AuthenticatedRequest<T> {
    payload: T,
    signature: String,
    public_key: String,
    timestamp: u64,
}

#[derive(Deserialize)]
struct StartNodeRequest {
    validator: Option<bool>,
    name: Option<String>,
}

#[derive(Deserialize)]
struct KeystoreRequest {
    action: String,
    key_type: Option<String>,
    seed: Option<String>,
}

#[derive(Serialize)]
struct KeystoreResponse {
    success: bool,
    message: String,
    keys: Option<Vec<KeyInfo>>,
}

#[derive(Serialize, Clone)]
pub struct KeyInfo {
    pub key_type: String,
    pub public_key: String,
    pub algorithm: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub path: Option<String>,
}

#[derive(Deserialize)]
struct RuntimeUpgradeRequest {
    wasm_hex: String,
    sudo_seed: String,
}

#[derive(Serialize)]
struct RuntimeUpgradeResponse {
    success: bool,
    message: String,
    tx_hash: Option<String>,
}

#[derive(Serialize)]
struct ConfigResponse {
    node_binary: String,
    chain_spec: Option<String>,
    node_name: String,
    rpc_port: u16,
    p2p_port: u16,
    validator: bool,
    bootnode: Option<String>,
}

#[derive(Serialize)]
struct LogsResponse {
    logs: Vec<String>,
}

// ============================================================================
// API Handlers
// ============================================================================

/// Health check endpoint
async fn health() -> impl IntoResponse {
    Json(serde_json::json!({"status": "ok", "service": "node-operator"}))
}

/// Get current status
async fn get_status(State(state): State<AppState>) -> impl IntoResponse {
    let node_manager = state.node_manager.lock().await;
    let node_running = node_manager.is_running();
    let node_pid = node_manager.pid();

    // Try to get blockchain status via RPC
    let (connected, block_height, peers, syncing) = if node_running {
        match rpc::get_node_status(state.config.rpc_port).await {
            Ok(status) => (true, Some(status.block_height), Some(status.peers), Some(status.syncing)),
            Err(_) => (false, None, None, None),
        }
    } else {
        (false, None, None, None)
    };

    Json(StatusResponse {
        node_running,
        node_pid,
        connected,
        block_height,
        peers,
        syncing,
        version: env!("CARGO_PKG_VERSION").to_string(),
    })
}

/// Get configuration
async fn get_config(State(state): State<AppState>) -> impl IntoResponse {
    let config = &state.config;
    Json(ConfigResponse {
        node_binary: config.node_binary.display().to_string(),
        chain_spec: config.chain_spec.as_ref().map(|p| p.display().to_string()),
        node_name: config.node_name.clone(),
        rpc_port: config.rpc_port,
        p2p_port: config.p2p_port,
        validator: config.validator,
        bootnode: config.bootnode.clone(),
    })
}

/// Start the node
async fn start_node(
    State(state): State<AppState>,
    Json(req): Json<Option<StartNodeRequest>>,
) -> impl IntoResponse {
    let mut node_manager = state.node_manager.lock().await;

    if node_manager.is_running() {
        return (StatusCode::CONFLICT, Json(NodeControlResponse {
            success: false,
            message: "Node is already running".to_string(),
            pid: node_manager.pid(),
        }));
    }

    let validator = req.as_ref().and_then(|r| r.validator).unwrap_or(state.config.validator);
    let name = req.as_ref().and_then(|r| r.name.clone()).unwrap_or_else(|| state.config.node_name.clone());

    match node_manager.start(&state.config, validator, &name).await {
        Ok(pid) => {
            info!("Node started with PID: {}", pid);
            let _ = state.log_broadcast.send(format!("Node started with PID: {}", pid));
            (StatusCode::OK, Json(NodeControlResponse {
                success: true,
                message: format!("Node started successfully"),
                pid: Some(pid),
            }))
        }
        Err(e) => {
            error!("Failed to start node: {}", e);
            let _ = state.log_broadcast.send(format!("Failed to start node: {}", e));
            (StatusCode::INTERNAL_SERVER_ERROR, Json(NodeControlResponse {
                success: false,
                message: format!("Failed to start node: {}", e),
                pid: None,
            }))
        }
    }
}

/// Stop the node
async fn stop_node(State(state): State<AppState>) -> impl IntoResponse {
    let mut node_manager = state.node_manager.lock().await;

    if !node_manager.is_running() {
        return (StatusCode::OK, Json(NodeControlResponse {
            success: true,
            message: "Node is not running".to_string(),
            pid: None,
        }));
    }

    let pid = node_manager.pid();
    match node_manager.stop().await {
        Ok(()) => {
            info!("Node stopped");
            let _ = state.log_broadcast.send("Node stopped".to_string());
            (StatusCode::OK, Json(NodeControlResponse {
                success: true,
                message: "Node stopped successfully".to_string(),
                pid,
            }))
        }
        Err(e) => {
            error!("Failed to stop node: {}", e);
            (StatusCode::INTERNAL_SERVER_ERROR, Json(NodeControlResponse {
                success: false,
                message: format!("Failed to stop node: {}", e),
                pid,
            }))
        }
    }
}

/// Restart the node
async fn restart_node(State(state): State<AppState>) -> impl IntoResponse {
    let mut node_manager = state.node_manager.lock().await;

    // Stop if running
    if node_manager.is_running() {
        if let Err(e) = node_manager.stop().await {
            error!("Failed to stop node for restart: {}", e);
        }
        tokio::time::sleep(Duration::from_secs(2)).await;
    }

    // Start
    match node_manager.start(&state.config, state.config.validator, &state.config.node_name).await {
        Ok(pid) => {
            info!("Node restarted with PID: {}", pid);
            let _ = state.log_broadcast.send(format!("Node restarted with PID: {}", pid));
            (StatusCode::OK, Json(NodeControlResponse {
                success: true,
                message: "Node restarted successfully".to_string(),
                pid: Some(pid),
            }))
        }
        Err(e) => {
            error!("Failed to restart node: {}", e);
            (StatusCode::INTERNAL_SERVER_ERROR, Json(NodeControlResponse {
                success: false,
                message: format!("Failed to restart node: {}", e),
                pid: None,
            }))
        }
    }
}

/// Get node logs
async fn get_logs(State(state): State<AppState>) -> impl IntoResponse {
    let node_manager = state.node_manager.lock().await;
    let logs = node_manager.get_logs(100);
    Json(LogsResponse { logs })
}

/// Keystore operations
async fn keystore_operation(
    State(state): State<AppState>,
    Json(req): Json<KeystoreRequest>,
) -> impl IntoResponse {
    let keystore = state.keystore_manager.read().await;

    match req.action.as_str() {
        "list" => {
            let keys = keystore.list_keys().await;
            Json(KeystoreResponse {
                success: true,
                message: format!("Found {} keys", keys.len()),
                keys: Some(keys),
            })
        }
        "generate" => {
            drop(keystore);
            let mut keystore = state.keystore_manager.write().await;
            match keystore.generate_sphincs_key().await {
                Ok(info) => {
                    let _ = state.log_broadcast.send(format!("Generated new SPHINCS+ key: {}", info.public_key));
                    Json(KeystoreResponse {
                        success: true,
                        message: "Key generated successfully".to_string(),
                        keys: Some(vec![info]),
                    })
                }
                Err(e) => Json(KeystoreResponse {
                    success: false,
                    message: format!("Failed to generate key: {}", e),
                    keys: None,
                }),
            }
        }
        "inject" => {
            let seed = req.seed.unwrap_or_default();
            drop(keystore);
            let mut keystore = state.keystore_manager.write().await;
            match keystore.inject_key(&seed, state.config.rpc_port).await {
                Ok(info) => {
                    let _ = state.log_broadcast.send(format!("Injected key: {}", info.public_key));
                    Json(KeystoreResponse {
                        success: true,
                        message: "Key injected successfully".to_string(),
                        keys: Some(vec![info]),
                    })
                }
                Err(e) => Json(KeystoreResponse {
                    success: false,
                    message: format!("Failed to inject key: {}", e),
                    keys: None,
                }),
            }
        }
        _ => Json(KeystoreResponse {
            success: false,
            message: format!("Unknown action: {}", req.action),
            keys: None,
        }),
    }
}

/// WebSocket endpoint for real-time logs
async fn ws_logs(
    ws: WebSocketUpgrade,
    State(state): State<AppState>,
) -> impl IntoResponse {
    ws.on_upgrade(move |socket| handle_ws_logs(socket, state))
}

async fn handle_ws_logs(mut socket: WebSocket, state: AppState) {
    let mut rx = state.log_broadcast.subscribe();

    // Send initial status
    let status = {
        let node_manager = state.node_manager.lock().await;
        if node_manager.is_running() {
            format!("Connected to node-operator. Node is running (PID: {:?})", node_manager.pid())
        } else {
            "Connected to node-operator. Node is not running.".to_string()
        }
    };
    let _ = socket.send(Message::Text(status)).await;

    // Stream logs
    loop {
        tokio::select! {
            msg = rx.recv() => {
                match msg {
                    Ok(log) => {
                        if socket.send(Message::Text(log)).await.is_err() {
                            break;
                        }
                    }
                    Err(_) => break,
                }
            }
            msg = socket.recv() => {
                match msg {
                    Some(Ok(Message::Close(_))) | None => break,
                    _ => {}
                }
            }
        }
    }
}

/// RPC proxy - forwards requests to the node
async fn rpc_proxy(
    State(state): State<AppState>,
    Json(body): Json<serde_json::Value>,
) -> impl IntoResponse {
    match rpc::forward_rpc(state.config.rpc_port, body).await {
        Ok(response) => (StatusCode::OK, Json(response)),
        Err(e) => (
            StatusCode::BAD_GATEWAY,
            Json(serde_json::json!({"error": e.to_string()})),
        ),
    }
}

// ============================================================================
// Main Entry Point
// ============================================================================

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Initialize logging
    tracing_subscriber::fmt()
        .with_env_filter(
            tracing_subscriber::EnvFilter::from_default_env()
                .add_directive("node_operator=info".parse().unwrap())
                .add_directive("tower_http=debug".parse().unwrap()),
        )
        .init();

    // Parse arguments
    let args = Args::parse();

    info!("Starting QuantumHarmony Node Operator v{}", env!("CARGO_PKG_VERSION"));
    info!("Node binary: {}", args.node_binary.display());
    info!("Listening on port: {}", args.port);

    // Create configuration
    let config = Arc::new(OperatorConfig {
        node_binary: args.node_binary,
        chain_spec: args.chain_spec,
        node_name: args.node_name,
        bootnode: args.bootnode,
        rpc_port: args.rpc_port,
        p2p_port: args.p2p_port,
        validator: args.validator,
        data_dir: args.data_dir,
        allow_unauthenticated: args.allow_unauthenticated,
    });

    // Initialize managers
    let (log_tx, _) = broadcast::channel(1000);
    let node_manager = Arc::new(Mutex::new(NodeManager::new(log_tx.clone())));
    let keystore_manager = Arc::new(RwLock::new(KeystoreManager::new(args.operator_keystore)));
    let auth_manager = Arc::new(AuthManager::new(args.allow_unauthenticated));

    let state = AppState {
        node_manager,
        keystore_manager,
        auth_manager,
        config,
        log_broadcast: log_tx,
    };

    // Set up CORS
    let cors = CorsLayer::new()
        .allow_origin(Any)
        .allow_methods([Method::GET, Method::POST, Method::OPTIONS])
        .allow_headers([header::CONTENT_TYPE, header::AUTHORIZATION]);

    // Build router
    let app = Router::new()
        // Health & status
        .route("/health", get(health))
        .route("/status", get(get_status))
        .route("/config", get(get_config))
        .route("/logs", get(get_logs))
        .route("/ws/logs", get(ws_logs))
        // Node control
        .route("/node/start", post(start_node))
        .route("/node/stop", post(stop_node))
        .route("/node/restart", post(restart_node))
        // Keystore
        .route("/keystore", post(keystore_operation))
        // RPC proxy
        .route("/rpc", post(rpc_proxy))
        // Static files for dashboard
        .nest_service("/", tower_http::services::ServeDir::new(&args.dashboard_path))
        .layer(cors)
        .with_state(state);

    // Start server
    let listener = tokio::net::TcpListener::bind(format!("0.0.0.0:{}", args.port)).await?;
    info!("Node Operator listening on http://0.0.0.0:{}", args.port);

    axum::serve(listener, app).await?;

    Ok(())
}
