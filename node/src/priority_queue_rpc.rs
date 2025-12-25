//! Priority Queue RPC Server for QuantumHarmony validators
//!
//! Each validator runs its own priority queue RPC server on ports:
//! - Alice: 5555
//! - Bob: 5556
//! - Charlie: 5557
//!
//! This provides custom event submission and priority queue management
//! separate from Substrate's built-in transaction pool.

use jsonrpsee::core::{async_trait, RpcResult};
use jsonrpsee::proc_macros::rpc;
use jsonrpsee::server::Server;
use jsonrpsee::types::ErrorObjectOwned;
use priority_queue::PriorityQueue;
use serde::{Deserialize, Serialize};
use std::cmp::Reverse;
use std::sync::Arc;
use tokio::sync::{Mutex, Semaphore};
use tracing::{error, info, warn};

/// Event structure for the priority queue
#[derive(Serialize, Deserialize, Debug, Clone, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub struct Event {
    /// Unique event identifier
    pub id: u64,
    /// Event data payload
    pub data: String,
    /// Unix timestamp when event was created
    pub timestamp: u64,
    /// Block height when event was submitted
    pub block_height: u64,
}

/// Priority queue wrapper with semaphore for bounded queue management
pub struct QueueWithSemaphore {
    /// The underlying priority queue (higher priority = higher i32 value)
    queue: Mutex<PriorityQueue<Event, i32>>,
    /// Semaphore to limit queue size
    semaphore: Semaphore,
}

impl QueueWithSemaphore {
    /// Create a new queue with maximum capacity
    pub fn new(max_capacity: usize) -> Self {
        Self {
            queue: Mutex::new(PriorityQueue::new()),
            semaphore: Semaphore::new(max_capacity),
        }
    }

    /// Submit an event with given priority
    pub async fn submit(&self, event: Event, priority: i32) -> RpcResult<()> {
        // Try to acquire semaphore permit
        match self.semaphore.try_acquire() {
            Ok(_permit) => {
                let mut queue = self.queue.lock().await;
                queue.push(event.clone(), priority);
                info!("✅ Event {} submitted with priority {}", event.id, priority);
                Ok(())
            }
            Err(_) => {
                warn!("❌ Queue full, cannot submit event {}", event.id);
                Err(ErrorObjectOwned::owned(
                    -32000,
                    "Queue is full".to_string(),
                    None::<String>,
                ))
            }
        }
    }

    /// Pop the highest priority event
    pub async fn pop(&self) -> RpcResult<Option<Event>> {
        let mut queue = self.queue.lock().await;
        if let Some((event, priority)) = queue.pop() {
            info!("📤 Popped event {} with priority {}", event.id, priority);
            Ok(Some(event))
        } else {
            Ok(None)
        }
    }

    /// List all events in the queue
    pub async fn list_all(&self) -> Vec<(Event, i32)> {
        let queue = self.queue.lock().await;
        queue.iter().map(|(e, p)| (e.clone(), *p)).collect()
    }

    /// Clear all events from the queue
    pub async fn clear(&self) {
        let mut queue = self.queue.lock().await;
        let count = queue.len();
        queue.clear();
        info!("🧹 Cleared {} events from queue", count);
    }

    /// Get total event count
    pub async fn count(&self) -> usize {
        let queue = self.queue.lock().await;
        queue.len()
    }

    /// Get event by ID
    pub async fn get_by_id(&self, id: u64) -> Option<(Event, i32)> {
        let queue = self.queue.lock().await;
        queue.iter().find(|(e, _)| e.id == id).map(|(e, p)| (e.clone(), *p))
    }

    /// Update event priority
    pub async fn update_priority(&self, id: u64, new_priority: i32) -> RpcResult<()> {
        let mut queue = self.queue.lock().await;

        // Find and remove the event
        let event = queue
            .iter()
            .find(|(e, _)| e.id == id)
            .map(|(e, _)| e.clone());

        if let Some(event) = event {
            queue.remove(&event);
            queue.push(event.clone(), new_priority);
            info!("🔄 Updated event {} priority to {}", id, new_priority);
            Ok(())
        } else {
            Err(ErrorObjectOwned::owned(
                -32001,
                format!("Event with id {} not found", id),
                None::<String>,
            ))
        }
    }

    /// Get events by timestamp range
    pub async fn get_by_timestamp(&self, min_ts: u64, max_ts: u64) -> Vec<(Event, i32)> {
        let queue = self.queue.lock().await;
        queue
            .iter()
            .filter(|(e, _)| e.timestamp >= min_ts && e.timestamp <= max_ts)
            .map(|(e, p)| (e.clone(), *p))
            .collect()
    }

    /// Remove event by ID
    pub async fn remove_by_id(&self, id: u64) -> RpcResult<()> {
        let mut queue = self.queue.lock().await;

        let event = queue
            .iter()
            .find(|(e, _)| e.id == id)
            .map(|(e, _)| e.clone());

        if let Some(event) = event {
            queue.remove(&event);
            info!("🗑️  Removed event {}", id);
            Ok(())
        } else {
            Err(ErrorObjectOwned::owned(
                -32001,
                format!("Event with id {} not found", id),
                None::<String>,
            ))
        }
    }
}

/// RPC trait defining all priority queue methods
#[rpc(server, client)]
pub trait PriorityQueueRpc {
    /// Submit a new event to the priority queue
    #[method(name = "submit_event")]
    async fn submit_event(&self, event: Event, priority: i32) -> RpcResult<()>;

    /// List all events in the priority queue
    #[method(name = "list_all_events")]
    async fn list_all_events(&self) -> RpcResult<Vec<(Event, i32)>>;

    /// Clear all events from the queue
    #[method(name = "clear_all_events")]
    async fn clear_all_events(&self) -> RpcResult<()>;

    /// Pop the highest priority event
    #[method(name = "pop")]
    async fn pop(&self) -> RpcResult<Option<Event>>;

    /// Get total event count
    #[method(name = "get_event_count")]
    async fn get_event_count(&self) -> RpcResult<usize>;

    /// Get event by ID
    #[method(name = "get_event_by_id")]
    async fn get_event_by_id(&self, id: u64) -> RpcResult<Option<(Event, i32)>>;

    /// Update event priority
    #[method(name = "update_event_priority")]
    async fn update_event_priority(&self, id: u64, new_priority: i32) -> RpcResult<()>;

    /// Get events by timestamp range
    #[method(name = "get_events_by_timestamp")]
    async fn get_events_by_timestamp(
        &self,
        min_timestamp: u64,
        max_timestamp: u64,
    ) -> RpcResult<Vec<(Event, i32)>>;

    /// Remove event by ID
    #[method(name = "remove_event_by_id")]
    async fn remove_event_by_id(&self, id: u64) -> RpcResult<()>;
}

/// Implementation of the RPC trait
#[async_trait]
impl PriorityQueueRpcServer for Arc<QueueWithSemaphore> {
    async fn submit_event(&self, event: Event, priority: i32) -> RpcResult<()> {
        self.submit(event, priority).await
    }

    async fn list_all_events(&self) -> RpcResult<Vec<(Event, i32)>> {
        Ok(self.list_all().await)
    }

    async fn clear_all_events(&self) -> RpcResult<()> {
        self.clear().await;
        Ok(())
    }

    async fn pop(&self) -> RpcResult<Option<Event>> {
        self.pop().await
    }

    async fn get_event_count(&self) -> RpcResult<usize> {
        Ok(self.count().await)
    }

    async fn get_event_by_id(&self, id: u64) -> RpcResult<Option<(Event, i32)>> {
        Ok(self.get_by_id(id).await)
    }

    async fn update_event_priority(&self, id: u64, new_priority: i32) -> RpcResult<()> {
        self.update_priority(id, new_priority).await
    }

    async fn get_events_by_timestamp(
        &self,
        min_timestamp: u64,
        max_timestamp: u64,
    ) -> RpcResult<Vec<(Event, i32)>> {
        Ok(self.get_by_timestamp(min_timestamp, max_timestamp).await)
    }

    async fn remove_event_by_id(&self, id: u64) -> RpcResult<()> {
        self.remove_by_id(id).await
    }
}

/// Run the priority queue RPC server on the specified port
pub async fn run_server(port: u16) -> Result<(), Box<dyn std::error::Error>> {
    info!("🚀 Starting Priority Queue RPC server on port {}", port);

    // Build the server
    let server = Server::builder()
        .build(format!("127.0.0.1:{}", port))
        .await?;

    // Create the priority queue with max capacity of 10,000 events
    let pq = Arc::new(QueueWithSemaphore::new(10_000));

    // Create RPC module
    let module = pq.into_rpc();

    // Start the server
    let handle = server.start(module);

    info!("✅ Priority Queue RPC server listening on 127.0.0.1:{}", port);

    // Keep server running until stopped
    handle.stopped().await;

    Ok(())
}
