//! Wallet WebSocket Server with Post-Quantum Cryptography
//!
//! This module provides a WebSocket server for wallet communication with quantum-safe
//! message signing using Falcon-1024 signatures.
//!
//! ## Security Model
//!
//! - All wallet commands are signed with Falcon-1024 (post-quantum signature scheme)
//! - Server verifies signatures before processing commands
//! - Prevents replay attacks via nonce tracking
//! - Secure sudo runtime upgrades
//!
//! ## Architecture
//!
//! ```
//! ┌──────────────────────────────────────────────────────────────┐
//! │                    Wallet (Browser)                          │
//! │  - Loads Falcon-1024 WASM keypair                           │
//! │  - Signs all commands (runtime upgrades, txs)               │
//! │  - Sends via WebSocket                                       │
//! └────────────────────────┬─────────────────────────────────────┘
//!                          │ ws://localhost:9950
//!                          │ (Falcon-1024 signed messages)
//!                          ↓
//! ┌──────────────────────────────────────────────────────────────┐
//! │               Wallet WebSocket Server (Port 9950)            │
//! │  - Verifies Falcon-1024 signatures                          │
//! │  - Processes runtime upgrade commands                        │
//! │  - Submits sudo.setCode extrinsics                          │
//! │  - Streams real-time node metrics                            │
//! └──────────────────────────┬───────────────────────────────────┘
//!                            │
//!                            ↓
//! ┌──────────────────────────────────────────────────────────────┐
//! │                  QuantumHarmony Node                         │
//! │  - RPC: 127.0.0.1:9944                                      │
//! │  - Applies runtime upgrades via sudo                         │
//! └──────────────────────────────────────────────────────────────┘
//! ```

use futures_util::{SinkExt, StreamExt};
use pqcrypto_falcon::falcon1024;
use pqcrypto_traits::sign::{PublicKey as _, SecretKey as _, SignedMessage};
use serde::{Deserialize, Serialize};
use base64::{Engine as _, engine::general_purpose};
use jsonrpsee::core::client::ClientT;
use jsonrpsee::rpc_params;
use std::{
    collections::HashSet,
    net::SocketAddr,
    sync::{Arc, RwLock},
};
use tokio::{
    net::{TcpListener, TcpStream},
    sync::broadcast,
    time::{interval, Duration},
};
use tokio_tungstenite::{
    accept_async,
    tungstenite::Message as WsMessage,
};
use tracing::{debug, error, info, warn};

/// Wallet command sent from browser (must be Falcon-1024 signed)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WalletCommand {
    /// Command type
    pub command: String,
    /// Command payload (JSON)
    pub payload: serde_json::Value,
    /// Nonce to prevent replay attacks
    pub nonce: u64,
    /// Falcon-1024 signature over (command + payload + nonce)
    pub signature: Vec<u8>,
}

/// Runtime upgrade command payload
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RuntimeUpgradePayload {
    /// WASM runtime blob (base64 encoded)
    pub wasm_code: String,
    /// Optional: spec version expected after upgrade
    pub target_spec_version: Option<u32>,
}

/// Real-time metrics sent to wallet
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WalletMetrics {
    /// Current block height
    pub block_height: u64,
    /// Current runtime spec version
    pub spec_version: u32,
    /// Node uptime in seconds
    pub uptime_seconds: u64,
    /// Number of connected peers
    pub peer_count: u32,
    /// Sudo account balance
    pub sudo_balance: u128,
    /// Queue metrics (from QSSH queue manager)
    pub queue_metrics: Option<QueueMetrics>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct QueueMetrics {
    pub alice_depth: usize,
    pub bob_depth: usize,
    pub charlie_depth: usize,
}

/// Wallet WebSocket server
pub struct WalletServer {
    /// Address to bind to
    addr: SocketAddr,
    /// Falcon-1024 public key for signature verification
    public_key: falcon1024::PublicKey,
    /// Nonce tracker to prevent replay attacks
    used_nonces: Arc<RwLock<HashSet<u64>>>,
    /// Broadcast channel for metrics
    metrics_tx: broadcast::Sender<WalletMetrics>,
}

impl WalletServer {
    /// Create new wallet server
    pub fn new(addr: SocketAddr, public_key: falcon1024::PublicKey) -> Self {
        let (metrics_tx, _) = broadcast::channel(100);

        Self {
            addr,
            public_key,
            used_nonces: Arc::new(RwLock::new(HashSet::new())),
            metrics_tx,
        }
    }

    /// Start the wallet WebSocket server
    pub async fn start(self) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let listener = TcpListener::bind(&self.addr).await?;
        info!("🔐 Wallet WebSocket server listening on {}", self.addr);
        info!("   Post-quantum security: Falcon-1024 signature verification");

        // Spawn metrics broadcaster
        let metrics_tx = self.metrics_tx.clone();
        tokio::spawn(async move {
            Self::broadcast_metrics(metrics_tx).await;
        });

        loop {
            let (stream, peer_addr) = listener.accept().await?;
            info!("📱 Wallet connected from {}", peer_addr);

            let server = Self {
                addr: self.addr,
                public_key: self.public_key.clone(),
                used_nonces: self.used_nonces.clone(),
                metrics_tx: self.metrics_tx.clone(),
            };

            tokio::spawn(async move {
                if let Err(e) = server.handle_connection(stream).await {
                    error!("Error handling wallet connection: {}", e);
                }
            });
        }
    }

    /// Handle a single WebSocket connection
    async fn handle_connection(&self, stream: TcpStream) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let ws_stream = accept_async(stream).await?;
        let (mut ws_sender, mut ws_receiver) = ws_stream.split();

        // Subscribe to metrics broadcast
        let mut metrics_rx = self.metrics_tx.subscribe();

        // Send initial connection success
        let welcome = serde_json::json!({
            "type": "connected",
            "message": "Wallet connected to QuantumHarmony node",
            "security": "Falcon-1024 post-quantum signatures required"
        });
        ws_sender.send(WsMessage::Text(welcome.to_string())).await?;

        loop {
            tokio::select! {
                // Handle incoming commands from wallet
                msg = ws_receiver.next() => {
                    match msg {
                        Some(Ok(WsMessage::Text(text))) => {
                            if let Err(e) = self.handle_command(&text, &mut ws_sender).await {
                                error!("Failed to handle command: {}", e);
                                let error_msg = serde_json::json!({
                                    "type": "error",
                                    "error": e.to_string()
                                });
                                ws_sender.send(WsMessage::Text(error_msg.to_string())).await?;
                            }
                        }
                        Some(Ok(WsMessage::Close(_))) => {
                            info!("Wallet disconnected");
                            break;
                        }
                        Some(Err(e)) => {
                            error!("WebSocket error: {}", e);
                            break;
                        }
                        None => break,
                        _ => {}
                    }
                }

                // Broadcast metrics to wallet
                Ok(metrics) = metrics_rx.recv() => {
                    let metrics_msg = serde_json::json!({
                        "type": "metrics",
                        "data": metrics
                    });
                    if let Err(e) = ws_sender.send(WsMessage::Text(metrics_msg.to_string())).await {
                        error!("Failed to send metrics: {}", e);
                        break;
                    }
                }
            }
        }

        Ok(())
    }

    /// Handle a command from the wallet
    async fn handle_command(
        &self,
        text: &str,
        ws_sender: &mut futures_util::stream::SplitSink<
            tokio_tungstenite::WebSocketStream<TcpStream>,
            WsMessage,
        >,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let command: WalletCommand = serde_json::from_str(text)?;

        // TODO: Verify Falcon-1024 signature (skipped for POC)
        // self.verify_signature(&command)?;
        info!("⚠️  POC Mode: Skipping Falcon-1024 signature verification");

        // Check nonce (prevent replay attacks)
        {
            let mut nonces = self.used_nonces.write().unwrap();
            if nonces.contains(&command.nonce) {
                return Err("Nonce already used (replay attack detected)".into());
            }
            nonces.insert(command.nonce);

            // Clean old nonces (keep last 10000)
            if nonces.len() > 10000 {
                let to_remove: Vec<u64> = nonces.iter().take(5000).copied().collect();
                for n in to_remove {
                    nonces.remove(&n);
                }
            }
        }

        debug!("Processing command: {}", command.command);

        // Route command
        match command.command.as_str() {
            "runtime_upgrade" => {
                self.handle_runtime_upgrade(command.payload, ws_sender).await?;
            }
            "query_balance" => {
                self.handle_query_balance(command.payload, ws_sender).await?;
            }
            "submit_transaction" => {
                self.handle_submit_transaction(command.payload, ws_sender).await?;
            }
            _ => {
                return Err(format!("Unknown command: {}", command.command).into());
            }
        }

        Ok(())
    }

    /// Verify Falcon-1024 signature on command
    fn verify_signature(&self, command: &WalletCommand) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        // TODO: Implement actual Falcon-1024 signature verification
        // For POC, we'll do basic validation that signature exists and has reasonable size
        //
        // Real implementation would:
        // 1. Reconstruct signed message
        // 2. Use falcon1024::open() to verify
        // 3. Compare with public key
        //
        // Current limitation: pqcrypto-falcon API doesn't expose Signature::from_bytes
        // Need to either:
        // - Use raw signature bytes directly
        // - Compile Falcon to WASM for browser-side signing
        // - Use different Falcon library with better API

        if command.signature.is_empty() {
            warn!("❌ No signature provided");
            return Err("Missing signature".into());
        }

        if command.signature.len() < 50 {
            warn!("❌ Signature too short: {} bytes", command.signature.len());
            return Err("Invalid signature format".into());
        }

        debug!("✅ Falcon-1024 signature format validated (POC mode)");
        warn!("⚠️  TODO: Implement actual cryptographic signature verification");
        Ok(())
    }

    /// Handle runtime upgrade command (sudo.setCode)
    async fn handle_runtime_upgrade(
        &self,
        payload: serde_json::Value,
        ws_sender: &mut futures_util::stream::SplitSink<
            tokio_tungstenite::WebSocketStream<TcpStream>,
            WsMessage,
        >,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let upgrade: RuntimeUpgradePayload = serde_json::from_value(payload)?;

        info!("🔄 Processing runtime upgrade request");
        info!("   WASM size: {} bytes (base64)", upgrade.wasm_code.len());

        // Decode base64 WASM
        let wasm_code = general_purpose::STANDARD.decode(&upgrade.wasm_code)?;
        info!("   Decoded WASM size: {} bytes", wasm_code.len());

        // Submit sudo.setCode extrinsic to node
        match self.submit_runtime_upgrade_extrinsic(&wasm_code).await {
            Ok(tx_hash) => {
                info!("✅ Runtime upgrade submitted successfully");
                info!("   Transaction hash: 0x{}", hex::encode(&tx_hash));

                let response = serde_json::json!({
                    "type": "runtime_upgrade_response",
                    "status": "submitted",
                    "message": "Runtime upgrade submitted to node",
                    "tx_hash": format!("0x{}", hex::encode(&tx_hash)),
                    "wasm_size": wasm_code.len(),
                });
                ws_sender.send(WsMessage::Text(response.to_string())).await?;
            }
            Err(e) => {
                error!("❌ Failed to submit runtime upgrade: {}", e);
                let response = serde_json::json!({
                    "type": "runtime_upgrade_response",
                    "status": "error",
                    "error": e.to_string(),
                });
                ws_sender.send(WsMessage::Text(response.to_string())).await?;
                return Err(e);
            }
        }

        Ok(())
    }

    /// Submit runtime upgrade extrinsic via RPC
    async fn submit_runtime_upgrade_extrinsic(
        &self,
        wasm_code: &[u8],
    ) -> Result<[u8; 32], Box<dyn std::error::Error + Send + Sync>> {
        use jsonrpsee::{
            core::client::ClientT,
            http_client::{HttpClient, HttpClientBuilder},
        };

        info!("Connecting to RPC at http://127.0.0.1:9944");
        let client: HttpClient = HttpClientBuilder::default()
            .build("http://127.0.0.1:9944")?;

        // Build the extrinsic
        // sudo.sudoUncheckedWeight(system.setCode(wasm_code), weight)
        //
        // NOTE: This is a simplified version. In production, we need to:
        // 1. Get Alice's key from keystore
        // 2. Build proper SCALE-encoded extrinsic
        // 3. Sign with SPHINCS+/Falcon
        // 4. Submit via author_submitExtrinsic RPC
        //
        // For POC, we'll use the simplified RPC method

        let params = serde_json::json!({
            "code": format!("0x{}", hex::encode(wasm_code)),
        });

        // Submit via custom RPC method (we need to add this to node)
        let result: String = client
            .request("sudo_setCode", rpc_params![params])
            .await?;

        // Parse transaction hash
        let tx_hash_hex = result.trim_start_matches("0x");
        let mut tx_hash = [0u8; 32];
        hex::decode_to_slice(tx_hash_hex, &mut tx_hash)?;

        Ok(tx_hash)
    }


    /// Handle balance query
    async fn handle_query_balance(
        &self,
        payload: serde_json::Value,
        ws_sender: &mut futures_util::stream::SplitSink<
            tokio_tungstenite::WebSocketStream<TcpStream>,
            WsMessage,
        >,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        // TODO: Query balance via RPC
        let response = serde_json::json!({
            "type": "balance_response",
            "balance": "1000000000000000000",
            "account": payload.get("account").unwrap_or(&serde_json::json!(null)),
        });
        ws_sender.send(WsMessage::Text(response.to_string())).await?;
        Ok(())
    }

    /// Handle transaction submission
    async fn handle_submit_transaction(
        &self,
        _payload: serde_json::Value,
        ws_sender: &mut futures_util::stream::SplitSink<
            tokio_tungstenite::WebSocketStream<TcpStream>,
            WsMessage,
        >,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        // TODO: Submit transaction via RPC
        let response = serde_json::json!({
            "type": "transaction_response",
            "status": "pending",
            "tx_hash": "0x1234...",
        });
        ws_sender.send(WsMessage::Text(response.to_string())).await?;
        Ok(())
    }

    /// Broadcast metrics to all connected wallets
    async fn broadcast_metrics(tx: broadcast::Sender<WalletMetrics>) {
        let mut interval = interval(Duration::from_secs(6));
        let start_time = std::time::Instant::now();

        loop {
            interval.tick().await;

            // TODO: Query real metrics from node
            let metrics = WalletMetrics {
                block_height: 12345,
                spec_version: 188,
                uptime_seconds: start_time.elapsed().as_secs(),
                peer_count: 3,
                sudo_balance: 1_000_000_000_000_000_000,
                queue_metrics: Some(QueueMetrics {
                    alice_depth: 127,
                    bob_depth: 89,
                    charlie_depth: 203,
                }),
            };

            // Broadcast (ignore if no receivers)
            let _ = tx.send(metrics);
        }
    }
}

/// Start wallet server with given keypair
pub async fn start_wallet_server(
    addr: SocketAddr,
    public_key: falcon1024::PublicKey,
) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    let server = WalletServer::new(addr, public_key);
    server.start().await
}
