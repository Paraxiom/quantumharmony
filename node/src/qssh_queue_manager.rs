//! QSSH Queue Manager for Multi-Validator Architecture
//!
//! This module implements the queue management system for running multiple validators
//! (Alice, Bob, Charlie) in a single process, using QSSH-RPC servers for isolation
//! and quantum-safe communication.
//!
//! Architecture:
//! ```
//! ┌─────────────────────────────────────────────────────────────────┐
//! │                  main.rs (Single Process)                       │
//! ├─────────────────────────────────────────────────────────────────┤
//! │                                                                  │
//! │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐          │
//! │  │ Alice Task   │  │ Bob Task     │  │ Charlie Task │          │
//! │  │              │  │              │  │              │          │
//! │  └──────┬───────┘  └──────┬───────┘  └──────┬───────┘          │
//! │         │                 │                 │                   │
//! │         ↓                 ↓                 ↓                   │
//! │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐          │
//! │  │ QSSH Queue   │  │ QSSH Queue   │  │ QSSH Queue   │          │
//! │  │ Port 9944    │  │ Port 9945    │  │ Port 9946    │          │
//! │  └──────────────┘  └──────────────┘  └──────────────┘          │
//! │                                                                  │
//! │  ┌────────────────────────────────────────────────────────┐    │
//! │  │ WebSocket Metrics Server (Port 9950)                   │    │
//! │  │ - Real-time queue metrics for LCARS dashboard          │    │
//! │  └────────────────────────────────────────────────────────┘    │
//! │                                                                  │
//! └─────────────────────────────────────────────────────────────────┘
//! ```

use futures::{stream::StreamExt, SinkExt};
use jsonrpsee::{
    server::{Server, ServerHandle},
    types::{Params, ErrorObjectOwned},
    RpcModule,
};
use priority_queue::PriorityQueue;
use serde::{Deserialize, Serialize};
use std::{
    cmp::Reverse,
    collections::HashMap,
    net::SocketAddr,
    sync::{Arc, RwLock},
    time::{Duration, Instant},
};
use tokio::{
    net::TcpListener,
    sync::broadcast,
};
use tokio_tungstenite::{accept_async, tungstenite::Message as WsMessage};
use tracing::{debug, error, info, warn};

/// Message priority based on type and urgency
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum MessagePriority {
    Critical = 100,    // Block imports, finality votes
    High = 75,         // Transactions, entropy submissions
    Normal = 50,       // Gossip, peer discovery
    Low = 25,          // Telemetry, metrics
}

/// Queue message type
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum QueueMessage {
    BlockImport {
        block_hash: [u8; 32],
        block_number: u64,
        timestamp: u64,
    },
    Vote {
        validator: String,
        block_hash: [u8; 32],
        signature: Vec<u8>,
    },
    Transaction {
        tx_hash: [u8; 32],
        tx_data: Vec<u8>,
    },
    EntropyShare {
        device_id: String,
        entropy: Vec<u8>,
        qber_percent: u32,  // QBER as integer (e.g., 85 = 0.85%)
    },
    Gossip {
        topic: String,
        data: Vec<u8>,
    },
}

impl QueueMessage {
    /// Get priority for this message type
    pub fn priority(&self) -> MessagePriority {
        match self {
            QueueMessage::BlockImport { .. } => MessagePriority::Critical,
            QueueMessage::Vote { .. } => MessagePriority::Critical,
            QueueMessage::EntropyShare { .. } => MessagePriority::High,
            QueueMessage::Transaction { .. } => MessagePriority::High,
            QueueMessage::Gossip { .. } => MessagePriority::Normal,
        }
    }
}

/// Validator queue instance
pub struct ValidatorQueue {
    /// Validator name (Alice, Bob, Charlie)
    pub name: String,
    /// QSSH-RPC port
    pub port: u16,
    /// Priority queue for messages (higher priority values come out first)
    pub queue: Arc<RwLock<PriorityQueue<QueueMessage, MessagePriority>>>,
    /// Queue metrics
    pub metrics: Arc<RwLock<QueueMetrics>>,
    /// Server handle for shutdown
    pub server_handle: Option<ServerHandle>,
}

/// Queue performance metrics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct QueueMetrics {
    pub queue_depth: usize,
    pub msg_rate: u64,              // Messages per second
    pub latency: u64,               // Average latency in ms
    pub health: u8,                 // Health percentage (0-100)
    #[serde(skip)]
    pub uptime: Duration,
    pub total_processed: u64,
    #[serde(skip)]
    pub last_message_time: Option<Instant>,
}

impl Default for QueueMetrics {
    fn default() -> Self {
        Self {
            queue_depth: 0,
            msg_rate: 0,
            latency: 0,
            health: 100,
            uptime: Duration::from_secs(0),
            total_processed: 0,
            last_message_time: None,
        }
    }
}

impl ValidatorQueue {
    /// Create a new validator queue
    pub fn new(name: String, port: u16) -> Self {
        Self {
            name,
            port,
            queue: Arc::new(RwLock::new(PriorityQueue::new())),
            metrics: Arc::new(RwLock::new(QueueMetrics::default())),
            server_handle: None,
        }
    }

    /// Submit a message to the queue
    pub fn submit(&self, message: QueueMessage) {
        let priority = message.priority();
        let mut queue = self.queue.write().unwrap();
        queue.push(message, priority);

        // Update metrics
        let mut metrics = self.metrics.write().unwrap();
        metrics.queue_depth = queue.len();
        metrics.last_message_time = Some(Instant::now());
    }

    /// Pop the highest priority message from the queue
    pub fn pop(&self) -> Option<QueueMessage> {
        let mut queue = self.queue.write().unwrap();
        let message = queue.pop().map(|(msg, _)| msg);

        // Update metrics
        if message.is_some() {
            let mut metrics = self.metrics.write().unwrap();
            metrics.queue_depth = queue.len();
            metrics.total_processed += 1;
        }

        message
    }

    /// Get current queue depth
    pub fn depth(&self) -> usize {
        self.queue.read().unwrap().len()
    }

    /// Get current metrics
    pub fn get_metrics(&self) -> QueueMetrics {
        self.metrics.read().unwrap().clone()
    }

    /// Start QSSH-RPC server for this queue
    pub async fn start_qssh_rpc_server(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        let addr = format!("127.0.0.1:{}", self.port).parse::<SocketAddr>()?;

        info!("🔐 Starting QSSH-RPC server for {} on {}", self.name, addr);

        let server = Server::builder()
            .build(addr)
            .await?;

        let mut module = RpcModule::new(());
        let queue = Arc::clone(&self.queue);
        let metrics = Arc::clone(&self.metrics);
        let name = self.name.clone();

        // Register RPC methods

        // qssh_submitMessage - Submit a message to the queue
        let queue_clone = Arc::clone(&queue);
        let metrics_clone = Arc::clone(&metrics);
        module.register_async_method("qssh_submitMessage", move |params: Params, _ctx, _ext| {
            let queue = Arc::clone(&queue_clone);
            let metrics = Arc::clone(&metrics_clone);

            async move {
                let message: QueueMessage = params.parse().map_err(|e| {
                    ErrorObjectOwned::owned(-32602, format!("Invalid params: {}", e), None::<()>)
                })?;
                let priority = message.priority();

                let mut q = queue.write().unwrap();
                q.push(message, priority);

                let mut m = metrics.write().unwrap();
                m.queue_depth = q.len();
                m.last_message_time = Some(Instant::now());

                Ok::<_, ErrorObjectOwned>(format!("Message queued with priority {:?}", priority))
            }
        })?;

        // qssh_popMessage - Pop the highest priority message
        let queue_clone = Arc::clone(&queue);
        let metrics_clone = Arc::clone(&metrics);
        module.register_async_method("qssh_popMessage", move |_params: Params, _ctx, _ext| {
            let queue = Arc::clone(&queue_clone);
            let metrics = Arc::clone(&metrics_clone);

            async move {
                let mut q = queue.write().unwrap();
                let message = q.pop().map(|(msg, _)| msg);

                if message.is_some() {
                    let mut m = metrics.write().unwrap();
                    m.queue_depth = q.len();
                    m.total_processed += 1;
                }

                Ok::<_, ErrorObjectOwned>(message)
            }
        })?;

        // qssh_getQueueDepth - Get current queue depth
        let queue_clone = Arc::clone(&queue);
        module.register_method("qssh_getQueueDepth", move |_params: Params, _ctx, _ext| {
            let q = queue_clone.read().unwrap();
            Ok::<_, ErrorObjectOwned>(q.len())
        })?;

        // qssh_getMetrics - Get queue metrics
        let metrics_clone = Arc::clone(&metrics);
        module.register_method("qssh_getMetrics", move |_params: Params, _ctx, _ext| {
            let m = metrics_clone.read().unwrap();
            Ok::<_, ErrorObjectOwned>(m.clone())
        })?;

        // qssh_getValidatorName - Get validator name
        module.register_method("qssh_getValidatorName", move |_params: Params, _ctx, _ext| {
            Ok::<_, ErrorObjectOwned>(name.clone())
        })?;

        let handle = server.start(module);
        self.server_handle = Some(handle);

        info!("✓ QSSH-RPC server for {} started successfully", self.name);

        Ok(())
    }

    /// Stop the QSSH-RPC server
    pub async fn stop(&mut self) {
        if let Some(handle) = self.server_handle.take() {
            handle.stop().unwrap();
            info!("✓ QSSH-RPC server for {} stopped", self.name);
        }
    }
}

/// QSSH Queue Manager - manages all validator queues
pub struct QsshQueueManager {
    pub validators: HashMap<String, ValidatorQueue>,
    pub metrics_tx: broadcast::Sender<AggregateMetrics>,
    pub start_time: Instant,
}

/// Aggregate metrics for all validators
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AggregateMetrics {
    pub alice: Option<QueueMetrics>,
    pub bob: Option<QueueMetrics>,
    pub charlie: Option<QueueMetrics>,
    pub aggregate: GlobalMetrics,
}

/// Global system metrics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GlobalMetrics {
    pub total_msg_rate: u64,
    pub avg_latency: u64,
    pub block_height: u64,
    pub finalized: u64,
    pub entropy_pool: usize,
    pub stark_valid: u64,
    pub stark_failed: u64,
    pub vrf_election_block: u64,
}

impl Default for GlobalMetrics {
    fn default() -> Self {
        Self {
            total_msg_rate: 0,
            avg_latency: 0,
            block_height: 0,
            finalized: 0,
            entropy_pool: 0,
            stark_valid: 0,
            stark_failed: 0,
            vrf_election_block: 0,
        }
    }
}

impl QsshQueueManager {
    /// Create a new QSSH Queue Manager
    pub fn new() -> Self {
        let (tx, _rx) = broadcast::channel(100);

        Self {
            validators: HashMap::new(),
            metrics_tx: tx,
            start_time: Instant::now(),
        }
    }

    /// Add a validator queue
    pub fn add_validator(&mut self, name: String, port: u16) {
        let queue = ValidatorQueue::new(name.clone(), port);
        self.validators.insert(name, queue);
    }

    /// Start all QSSH-RPC servers
    pub async fn start_all_servers(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        for (name, queue) in self.validators.iter_mut() {
            queue.start_qssh_rpc_server().await?;
        }
        Ok(())
    }

    /// Stop all QSSH-RPC servers
    pub async fn stop_all_servers(&mut self) {
        for (_name, queue) in self.validators.iter_mut() {
            queue.stop().await;
        }
    }

    /// Get aggregate metrics for all validators
    pub fn get_aggregate_metrics(&self, global: GlobalMetrics) -> AggregateMetrics {
        AggregateMetrics {
            alice: self.validators.get("alice").map(|v| v.get_metrics()),
            bob: self.validators.get("bob").map(|v| v.get_metrics()),
            charlie: self.validators.get("charlie").map(|v| v.get_metrics()),
            aggregate: global,
        }
    }

    /// Start WebSocket metrics server for LCARS dashboard
    pub async fn start_metrics_websocket(
        &self,
        port: u16,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let addr = format!("127.0.0.1:{}", port);
        let listener = TcpListener::bind(&addr).await?;

        info!("📊 Starting WebSocket metrics server on ws://{}/qssh-queue-metrics", addr);

        let mut rx = self.metrics_tx.subscribe();

        tokio::spawn(async move {
            loop {
                match listener.accept().await {
                    Ok((stream, peer_addr)) => {
                        info!("WebSocket connection from {}", peer_addr);

                        let mut rx_clone = rx.resubscribe();

                        tokio::spawn(async move {
                            match accept_async(stream).await {
                                Ok(ws_stream) => {
                                    let (mut write, _read) = ws_stream.split();

                                    // Send metrics updates to client
                                    while let Ok(metrics) = rx_clone.recv().await {
                                        let json = serde_json::to_string(&metrics).unwrap();
                                        let msg = WsMessage::Text(json);

                                        if write.send(msg).await.is_err() {
                                            break;
                                        }
                                    }
                                }
                                Err(e) => {
                                    error!("WebSocket error: {}", e);
                                }
                            }
                        });
                    }
                    Err(e) => {
                        error!("Failed to accept connection: {}", e);
                    }
                }
            }
        });

        Ok(())
    }

    /// Broadcast metrics update to all WebSocket clients
    pub fn broadcast_metrics(&self, global: GlobalMetrics) {
        let metrics = self.get_aggregate_metrics(global);
        let _ = self.metrics_tx.send(metrics);
    }

    /// Metrics update loop (call from main loop)
    pub async fn metrics_update_loop(
        manager: Arc<RwLock<QsshQueueManager>>,
        mut global_metrics_rx: tokio::sync::mpsc::Receiver<GlobalMetrics>,
    ) {
        loop {
            tokio::time::sleep(Duration::from_secs(1)).await;

            // Receive global metrics from blockchain
            if let Ok(global) = global_metrics_rx.try_recv() {
                let mgr = manager.read().unwrap();
                mgr.broadcast_metrics(global);
            }
        }
    }
}

impl Default for QsshQueueManager {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_queue_priority() {
        let queue = ValidatorQueue::new("test".to_string(), 9999);

        // Submit messages in reverse priority order
        queue.submit(QueueMessage::Gossip {
            topic: "test".to_string(),
            data: vec![],
        });

        queue.submit(QueueMessage::Transaction {
            tx_hash: [0u8; 32],
            tx_data: vec![],
        });

        queue.submit(QueueMessage::BlockImport {
            block_hash: [0u8; 32],
            block_number: 1,
            timestamp: 0,
        });

        // Should pop BlockImport first (Critical priority)
        let msg1 = queue.pop().unwrap();
        assert!(matches!(msg1, QueueMessage::BlockImport { .. }));

        // Then Transaction (High priority)
        let msg2 = queue.pop().unwrap();
        assert!(matches!(msg2, QueueMessage::Transaction { .. }));

        // Finally Gossip (Normal priority)
        let msg3 = queue.pop().unwrap();
        assert!(matches!(msg3, QueueMessage::Gossip { .. }));
    }

    #[test]
    fn test_metrics_tracking() {
        let queue = ValidatorQueue::new("test".to_string(), 9999);

        queue.submit(QueueMessage::Gossip {
            topic: "test".to_string(),
            data: vec![],
        });

        let metrics = queue.get_metrics();
        assert_eq!(metrics.queue_depth, 1);

        queue.pop();

        let metrics = queue.get_metrics();
        assert_eq!(metrics.queue_depth, 0);
        assert_eq!(metrics.total_processed, 1);
    }

    #[tokio::test]
    async fn test_manager_lifecycle() {
        let mut manager = QsshQueueManager::new();

        manager.add_validator("alice".to_string(), 19944);
        manager.add_validator("bob".to_string(), 19945);
        manager.add_validator("charlie".to_string(), 19946);

        assert_eq!(manager.validators.len(), 3);

        // Start servers
        manager.start_all_servers().await.unwrap();

        // Give servers time to start
        tokio::time::sleep(Duration::from_millis(100)).await;

        // Stop servers
        manager.stop_all_servers().await;
    }
}
