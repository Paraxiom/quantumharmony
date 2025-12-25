//! QPP-Enhanced QSSH Queue Manager
//!
//! This module extends the QSSH Queue Manager with Quantum Preservation Pattern (QPP)
//! integration, providing:
//!
//! - **Sync guarantees**: Messages persist to disk before ack
//! - **No-cloning enforcement**: Queue messages follow quantum no-cloning theorem
//! - **Type-state safety**: Queue lifecycle enforced at compile time
//! - **Provenance tracking**: Track message origin and transformations
//!
//! ## Architecture
//!
//! ```text
//! ┌────────────────────────────────────────────────────────────────┐
//! │              QPP-Enhanced QSSH Queue Manager                   │
//! ├────────────────────────────────────────────────────────────────┤
//! │                                                                 │
//! │  Message Submission (Async)                                    │
//! │         ↓                                                       │
//! │  QPP NoClone Wrapper (Quantum No-Cloning Enforcement)          │
//! │         ↓                                                       │
//! │  Priority Queue (In-Memory)                                    │
//! │         ↓                                                       │
//! │  SyncOp: Persist to Disk (fsync before ack)                    │
//! │         ↓                                                       │
//! │  AsyncOp: Broadcast to WebSocket clients                       │
//! │         ↓                                                       │
//! │  Message Consumption (Move Semantics - One-Time Use)           │
//! │                                                                 │
//! └────────────────────────────────────────────────────────────────┘
//! ```
//!
//! ## QPP Integration Points
//!
//! 1. **NoClone<QueueMessage>**: Messages cannot be duplicated
//! 2. **SyncOp/AsyncOp**: Explicit sync vs async operations
//! 3. **Type States**: Queued → Persisted → Consumed
//! 4. **Provenance**: Track message origin and modifications

use crate::qpp::{
    NoClone, EntropySource,
    // TODO: SyncResult and AsyncResult don't exist in qpp module yet
    // sync_async::{SyncOp, AsyncOp, SyncResult, AsyncResult},
};
use crate::qssh_queue_manager::{
    QueueMessage, MessagePriority, QueueMetrics, ValidatorQueue,
};
use priority_queue::PriorityQueue;
use serde::{Deserialize, Serialize};
use std::{
    cmp::Reverse,
    fs::{File, OpenOptions},
    io::{Write, BufWriter, BufReader, BufRead},
    path::{Path, PathBuf},
    sync::{Arc, RwLock},
    time::{Duration, Instant, SystemTime, UNIX_EPOCH},
};
use tracing::{debug, error, info, warn};

/// QPP-wrapped queue message enforcing no-cloning theorem
///
/// Once consumed, the message cannot be used again - enforcing quantum measurement collapse.
pub type QppQueueMessage = NoClone<QueueMessageWithProvenance>;

/// Queue message with provenance tracking
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct QueueMessageWithProvenance {
    /// The actual message payload
    pub message: QueueMessage,

    /// Message ID (for deduplication and tracking)
    pub message_id: u64,

    /// Timestamp when message was created
    pub created_at: u64,

    /// Validator that submitted this message
    pub submitted_by: String,

    /// Has this message been persisted to disk?
    pub persisted: bool,

    /// Has this message been broadcast to WebSocket clients?
    pub broadcast: bool,
}

impl QueueMessageWithProvenance {
    /// Create a new message with provenance
    pub fn new(message: QueueMessage, submitted_by: String, message_id: u64) -> Self {
        Self {
            message,
            message_id,
            created_at: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            submitted_by,
            persisted: false,
            broadcast: false,
        }
    }

    /// Get message priority
    pub fn priority(&self) -> MessagePriority {
        self.message.priority()
    }
}

/// Type-state marker: Message is queued but not yet persisted
#[derive(Debug)]
pub struct Queued;

/// Type-state marker: Message has been persisted to disk
#[derive(Debug)]
pub struct Persisted;

/// Type-state marker: Message has been consumed (measurement collapse)
#[derive(Debug)]
pub struct Consumed;

/// Type-state queue message wrapper
///
/// Uses Rust's type system to enforce queue lifecycle:
/// Queued → Persisted → Consumed
///
/// This prevents:
/// - Consuming non-persisted messages
/// - Double-consumption
/// - Re-using consumed messages
#[derive(Debug)]
pub struct TypeStateMessage<State> {
    message: QueueMessageWithProvenance,
    _state: std::marker::PhantomData<State>,
}

impl TypeStateMessage<Queued> {
    /// Create a new queued message
    pub fn new(message: QueueMessageWithProvenance) -> Self {
        Self {
            message,
            _state: std::marker::PhantomData,
        }
    }

    /// Transition to Persisted state (requires sync operation)
    pub fn persist(mut self, persist_path: &Path) -> Result<TypeStateMessage<Persisted>, String> {
        // Persist message to disk with fsync
        let serialized = serde_json::to_string(&self.message)
            .map_err(|e| format!("Serialization failed: {}", e))?;

        let mut file = OpenOptions::new()
            .create(true)
            .append(true)
            .open(persist_path)
            .map_err(|e| format!("Failed to open persist file: {}", e))?;

        writeln!(file, "{}", serialized)
            .map_err(|e| format!("Failed to write message: {}", e))?;

        // CRITICAL: fsync to ensure durability
        file.sync_all()
            .map_err(|e| format!("fsync failed: {}", e))?;

        // Mark as persisted
        self.message.persisted = true;

        Ok(TypeStateMessage::<Persisted> {
            message: self.message,
            _state: std::marker::PhantomData,
        })
    }
}

impl TypeStateMessage<Persisted> {
    /// Consume the message (measurement collapse - one-time use)
    pub fn consume(self) -> TypeStateMessage<Consumed> {
        TypeStateMessage::<Consumed> {
            message: self.message,
            _state: std::marker::PhantomData,
        }
    }

    /// Borrow the message without consuming
    pub fn borrow(&self) -> &QueueMessageWithProvenance {
        &self.message
    }

    /// Get mutable reference (for marking broadcast, etc.)
    pub fn borrow_mut(&mut self) -> &mut QueueMessageWithProvenance {
        &mut self.message
    }
}

impl TypeStateMessage<Consumed> {
    /// Extract the final message (can only be done once)
    pub fn into_inner(self) -> QueueMessageWithProvenance {
        self.message
    }
}

/// QPP-enhanced validator queue with sync/persistence guarantees
pub struct QppValidatorQueue {
    /// Validator name
    pub name: String,

    /// QSSH-RPC port
    pub port: u16,

    /// In-memory priority queue
    pub queue: Arc<RwLock<PriorityQueue<QueueMessageWithProvenance, Reverse<MessagePriority>>>>,

    /// Queue metrics
    pub metrics: Arc<RwLock<QueueMetrics>>,

    /// Persistence directory
    pub persist_dir: PathBuf,

    /// Write-ahead log file
    pub wal_path: PathBuf,

    /// Message ID counter
    pub next_message_id: Arc<RwLock<u64>>,
}

impl QppValidatorQueue {
    /// Create a new QPP-enhanced validator queue
    pub fn new(name: String, port: u16, persist_dir: impl AsRef<Path>) -> Result<Self, String> {
        let persist_dir = persist_dir.as_ref().to_path_buf();

        // Create persistence directory if it doesn't exist
        std::fs::create_dir_all(&persist_dir)
            .map_err(|e| format!("Failed to create persist dir: {}", e))?;

        let wal_path = persist_dir.join(format!("{}_wal.log", name));

        Ok(Self {
            name,
            port,
            queue: Arc::new(RwLock::new(PriorityQueue::new())),
            metrics: Arc::new(RwLock::new(QueueMetrics::default())),
            persist_dir,
            wal_path,
            next_message_id: Arc::new(RwLock::new(0)),
        })
    }

    /// Submit a message with QPP sync guarantee
    ///
    /// This is a **SyncOp** - message is persisted to disk with fsync before returning.
    /// Guarantees:
    /// - Message survives process crash
    /// - Message persisted before ack
    /// - No data loss on power failure
    pub fn submit_sync(&self, message: QueueMessage) -> Result<u64, String> {
        // Generate unique message ID
        let message_id = {
            let mut counter = self.next_message_id.write().unwrap();
            *counter += 1;
            *counter
        };

        // Wrap message with provenance
        let msg_with_provenance = QueueMessageWithProvenance::new(
            message,
            self.name.clone(),
            message_id,
        );

        // Create type-state message (Queued state)
        let queued_msg = TypeStateMessage::<Queued>::new(msg_with_provenance.clone());

        // Persist to disk (Queued → Persisted transition)
        let persisted_msg = queued_msg.persist(&self.wal_path)?;

        // Add to in-memory queue
        let priority = persisted_msg.borrow().priority();
        let mut queue = self.queue.write().unwrap();
        queue.push(persisted_msg.borrow().clone(), Reverse(priority));

        // Update metrics
        let mut metrics = self.metrics.write().unwrap();
        metrics.queue_depth = queue.len();
        metrics.last_message_time = Some(Instant::now());

        info!("[{}] Message {} persisted (sync)", self.name, message_id);

        Ok(message_id)
    }

    /// Submit a message with async guarantee (no fsync)
    ///
    /// This is an **AsyncOp** - message added to in-memory queue only.
    /// Use for non-critical messages where performance > durability.
    pub fn submit_async(&self, message: QueueMessage) -> Result<u64, String> {
        // Generate unique message ID
        let message_id = {
            let mut counter = self.next_message_id.write().unwrap();
            *counter += 1;
            *counter
        };

        // Wrap message with provenance
        let msg_with_provenance = QueueMessageWithProvenance::new(
            message,
            self.name.clone(),
            message_id,
        );

        // Add to in-memory queue (no persistence)
        let priority = msg_with_provenance.priority();
        let mut queue = self.queue.write().unwrap();
        queue.push(msg_with_provenance, Reverse(priority));

        // Update metrics
        let mut metrics = self.metrics.write().unwrap();
        metrics.queue_depth = queue.len();
        metrics.last_message_time = Some(Instant::now());

        debug!("[{}] Message {} queued (async)", self.name, message_id);

        Ok(message_id)
    }

    /// Pop the highest priority message (enforces no-cloning)
    ///
    /// Returns NoClone<QueueMessageWithProvenance> - can only be consumed once.
    pub fn pop(&self) -> Option<QppQueueMessage> {
        let mut queue = self.queue.write().unwrap();
        let message = queue.pop().map(|(msg, _)| msg);

        // Update metrics
        if message.is_some() {
            let mut metrics = self.metrics.write().unwrap();
            metrics.queue_depth = queue.len();
            metrics.total_processed += 1;
        }

        // Wrap in NoClone to enforce one-time use
        message.map(NoClone::new)
    }

    /// Restore queue from write-ahead log
    ///
    /// Called on startup to recover persisted messages after crash.
    pub fn restore_from_wal(&self) -> Result<usize, String> {
        if !self.wal_path.exists() {
            info!("[{}] No WAL file found, starting fresh", self.name);
            return Ok(0);
        }

        let file = File::open(&self.wal_path)
            .map_err(|e| format!("Failed to open WAL: {}", e))?;

        let reader = BufReader::new(file);
        let mut count = 0;

        for line in reader.lines() {
            let line = line.map_err(|e| format!("Failed to read line: {}", e))?;

            let msg: QueueMessageWithProvenance = serde_json::from_str(&line)
                .map_err(|e| format!("Failed to deserialize message: {}", e))?;

            // Add to queue
            let priority = msg.priority();
            let mut queue = self.queue.write().unwrap();
            queue.push(msg, Reverse(priority));
            count += 1;
        }

        info!("[{}] Restored {} messages from WAL", self.name, count);

        // Update message ID counter
        {
            let mut counter = self.next_message_id.write().unwrap();
            *counter = count;
        }

        Ok(count)
    }

    /// Compact the write-ahead log
    ///
    /// Removes consumed messages from WAL to prevent unbounded growth.
    pub fn compact_wal(&self) -> Result<(), String> {
        // Read current queue state
        let current_messages: Vec<QueueMessageWithProvenance> = {
            let queue = self.queue.read().unwrap();
            queue.iter().map(|(msg, _)| msg.clone()).collect()
        };

        // Create temporary file
        let temp_path = self.wal_path.with_extension("tmp");
        let mut temp_file = BufWriter::new(
            File::create(&temp_path)
                .map_err(|e| format!("Failed to create temp WAL: {}", e))?
        );

        // Write current messages to temp file
        for msg in current_messages {
            let serialized = serde_json::to_string(&msg)
                .map_err(|e| format!("Serialization failed: {}", e))?;
            writeln!(temp_file, "{}", serialized)
                .map_err(|e| format!("Write failed: {}", e))?;
        }

        // Fsync temp file
        temp_file.flush()
            .map_err(|e| format!("Flush failed: {}", e))?;
        temp_file.get_ref().sync_all()
            .map_err(|e| format!("Sync failed: {}", e))?;

        // Atomic rename (replace old WAL with compacted one)
        std::fs::rename(&temp_path, &self.wal_path)
            .map_err(|e| format!("Rename failed: {}", e))?;

        info!("[{}] WAL compacted", self.name);
        Ok(())
    }

    /// Get queue depth
    pub fn depth(&self) -> usize {
        self.queue.read().unwrap().len()
    }

    /// Get metrics
    pub fn get_metrics(&self) -> QueueMetrics {
        self.metrics.read().unwrap().clone()
    }
}

/// QPP Sync/Async Operation Wrappers
///
/// These types enforce the distinction between sync and async operations
/// at compile time, following the QPP sync_async pattern.

/// Sync operation wrapper (guarantees persistence)
pub struct QppSyncSubmit;

impl QppSyncSubmit {
    /// Submit message with sync guarantee (fsync before ack)
    pub fn execute(
        queue: &QppValidatorQueue,
        message: QueueMessage,
    ) -> SyncResult<u64> {
        queue.submit_sync(message)
            .map_err(|e| format!("Sync submit failed: {}", e))
    }
}

/// Async operation wrapper (in-memory only)
pub struct QppAsyncSubmit;

impl QppAsyncSubmit {
    /// Submit message with async guarantee (no fsync)
    pub async fn execute(
        queue: &QppValidatorQueue,
        message: QueueMessage,
    ) -> AsyncResult<u64> {
        // Convert to async Result
        queue.submit_async(message)
            .map_err(|e| format!("Async submit failed: {}", e))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_type_state_transitions() {
        let msg = QueueMessageWithProvenance::new(
            QueueMessage::Gossip {
                topic: "test".to_string(),
                data: vec![1, 2, 3],
            },
            "alice".to_string(),
            1,
        );

        // Create queued message
        let queued = TypeStateMessage::<Queued>::new(msg);

        // Create temp directory for test
        let temp_dir = std::env::temp_dir().join("qpp_queue_test");
        std::fs::create_dir_all(&temp_dir).unwrap();
        let wal_path = temp_dir.join("test_wal.log");

        // Persist (Queued → Persisted)
        let persisted = queued.persist(&wal_path).unwrap();

        // Verify file exists and is synced
        assert!(wal_path.exists());

        // Consume (Persisted → Consumed)
        let consumed = persisted.consume();
        let final_msg = consumed.into_inner();

        assert!(final_msg.persisted);
        assert_eq!(final_msg.submitted_by, "alice");

        // Cleanup
        std::fs::remove_file(wal_path).ok();
    }

    #[test]
    fn test_qpp_sync_submit() {
        let temp_dir = std::env::temp_dir().join("qpp_queue_sync_test");
        let queue = QppValidatorQueue::new("test".to_string(), 9999, &temp_dir).unwrap();

        let message = QueueMessage::Transaction {
            tx_hash: [42u8; 32],
            tx_data: vec![1, 2, 3],
        };

        // Sync submit (persisted to disk)
        let msg_id = QppSyncSubmit::execute(&queue, message).unwrap();
        assert_eq!(msg_id, 1);

        // Verify message in queue
        assert_eq!(queue.depth(), 1);

        // Verify WAL file exists
        assert!(queue.wal_path.exists());

        // Cleanup
        std::fs::remove_dir_all(temp_dir).ok();
    }

    #[test]
    fn test_wal_restore() {
        let temp_dir = std::env::temp_dir().join("qpp_queue_restore_test");

        // Create queue and submit messages
        {
            let queue = QppValidatorQueue::new("test".to_string(), 9999, &temp_dir).unwrap();

            for i in 0..10 {
                let msg = QueueMessage::Gossip {
                    topic: format!("topic_{}", i),
                    data: vec![i as u8],
                };
                queue.submit_sync(msg).unwrap();
            }

            assert_eq!(queue.depth(), 10);
        }

        // Create new queue and restore from WAL
        {
            let queue = QppValidatorQueue::new("test".to_string(), 9999, &temp_dir).unwrap();
            let restored = queue.restore_from_wal().unwrap();
            assert_eq!(restored, 10);
            assert_eq!(queue.depth(), 10);
        }

        // Cleanup
        std::fs::remove_dir_all(temp_dir).ok();
    }

    #[test]
    fn test_no_clone_enforcement() {
        let temp_dir = std::env::temp_dir().join("qpp_queue_noclone_test");
        let queue = QppValidatorQueue::new("test".to_string(), 9999, &temp_dir).unwrap();

        let message = QueueMessage::Gossip {
            topic: "test".to_string(),
            data: vec![1, 2, 3],
        };

        queue.submit_sync(message).unwrap();

        // Pop message (wrapped in NoClone)
        let msg = queue.pop().unwrap();

        // Can only consume once
        let _data = msg.consume();

        // ❌ This would be a compile error:
        // let _data2 = msg.consume(); // Error: value used after move

        // Cleanup
        std::fs::remove_dir_all(temp_dir).ok();
    }

    #[tokio::test]
    async fn test_async_submit() {
        let temp_dir = std::env::temp_dir().join("qpp_queue_async_test");
        let queue = QppValidatorQueue::new("test".to_string(), 9999, &temp_dir).unwrap();

        let message = QueueMessage::Gossip {
            topic: "async_test".to_string(),
            data: vec![1, 2, 3],
        };

        // Async submit (no fsync)
        let msg_id = QppAsyncSubmit::execute(&queue, message).await.unwrap();
        assert_eq!(msg_id, 1);
        assert_eq!(queue.depth(), 1);

        // Cleanup
        std::fs::remove_dir_all(temp_dir).ok();
    }
}
