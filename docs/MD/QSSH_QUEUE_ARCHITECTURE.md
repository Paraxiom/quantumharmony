# QSSH Queue Management Architecture

**Document Version:** 1.0
**Created:** 2025-10-28
**Purpose:** Comprehensive guide to QSSH-based queue management for multi-validator deployment
**Status:** Implementation Phase

---

## Table of Contents

1. [Executive Summary](#executive-summary)
2. [Problem Statement](#problem-statement)
3. [QSSH Queue Solution](#qssh-queue-solution)
4. [Architecture Overview](#architecture-overview)
5. [Component Details](#component-details)
6. [Implementation Guide](#implementation-guide)
7. [LCARS Dashboard](#lcars-dashboard)
8. [API Reference](#api-reference)
9. [Deployment Scenarios](#deployment-scenarios)
10. [Troubleshooting](#troubleshooting)

---

## Executive Summary

The QSSH Queue Management Architecture enables running multiple validators (Alice, Bob, Charlie) in a single process for dev wallet and local testnet use cases. This architecture solves the "SelectNextSome polled after terminated" crashes by providing:

- **Queue Isolation**: Each validator has its own QSSH-RPC server and priority queue
- **Quantum-Safe Communication**: All inter-validator communication uses post-quantum cryptography (Falcon-1024, SPHINCS+)
- **Visual Management**: LCARS-style dashboard for real-time monitoring
- **Port Isolation**: Each validator on different port (9944, 9945, 9946)
- **Priority-Based Routing**: Messages routed based on type (Critical, High, Normal, Low)

**Use Case**: Dev wallet with local testnet - run all 3 validators in one process without Docker containers or VMs.

---

## Problem Statement

### The Stream Consumption Conflict

When running multiple validators via `start-3validators.sh`, Bob and Charlie crash immediately:

```
ERROR tokio-runtime-worker sc_service::task_manager: Essential task `basic-block-import-worker` failed
ERROR tokio-runtime-worker sc_service::task_manager: Essential task `txpool-background` failed
Thread 'tokio-runtime-worker' panicked at 'SelectNextSome polled after terminated'
```

**Root Cause**:
- `basic-block-import-worker` (spawned at `service.rs:107`)
- `txpool-background` (spawned at `service.rs:117`)
- Both are **essential tasks** that subscribe to notification streams
- When multiple validator processes run, they have stream consumption conflicts
- Even as separate OS processes, they interfere with Substrate task management

### Initial Misunderstanding

We initially thought:
- Docker containers would solve this (they don't - still stream conflicts)
- Separate VMs needed (too heavy for dev wallet)
- Multiple processes with different ports would work (they don't)

### The Real Solution

User insight: *"Instead of spawning the que its a Qssh instance with automated script?"*

This question revealed the path forward:
- Use **QSSH-RPC servers** as queue endpoints
- Each validator gets its own QSSH instance on different port
- Messages routed via quantum-safe channels
- Priority queues prevent backpressure issues

---

## QSSH Queue Solution

### What is QSSH?

**QSSH** = Quantum-Safe Shell - SSH with post-quantum cryptography

Already implemented in your ecosystem:
- Binary RPC protocol (10-20x smaller than JSON)
- Falcon-512/1024 for key exchange
- SPHINCS+ for authentication
- ChaCha20-Poly1305 for symmetric encryption
- Optional QKD enhancement

### How QSSH Solves the Queue Problem

**Traditional Approach** (Fails):
```
Alice Process → Substrate Streams ← Bob Process
                      ↓
                  CONFLICT!
            (SelectNextSome panic)
```

**QSSH Queue Approach** (Works):
```
┌─────────────────────────────────────────────┐
│         Single Process (main.rs)            │
├─────────────────────────────────────────────┤
│  Alice Task → QSSH Queue (9944) → Stream A │
│  Bob Task   → QSSH Queue (9945) → Stream B │
│  Charlie    → QSSH Queue (9946) → Stream C │
│                                              │
│  Each stream is ISOLATED - no conflicts!   │
└─────────────────────────────────────────────┘
```

### Key Advantages

1. **Stream Isolation**: Each QSSH-RPC server has its own TCP connection = separate streams
2. **Priority Routing**: Messages routed by priority (Critical > High > Normal > Low)
3. **Backpressure Control**: Queue depth monitoring prevents overflow
4. **Quantum-Safe**: All communication uses PQC algorithms
5. **Port Isolation**: Works on same machine (different ports)
6. **Visual Management**: Real-time LCARS dashboard

---

## Architecture Overview

### System Diagram

```
┌───────────────────────────────────────────────────────────────────┐
│                  QuantumHarmony Node Process                      │
│                         (main.rs)                                 │
├───────────────────────────────────────────────────────────────────┤
│                                                                    │
│  ┌─────────────────┐  ┌─────────────────┐  ┌─────────────────┐  │
│  │ Alice Validator │  │ Bob Validator   │  │ Charlie Valid.  │  │
│  │                 │  │                 │  │                 │  │
│  │ • Block import  │  │ • Block import  │  │ • Block import  │  │
│  │ • Vote signing  │  │ • Vote signing  │  │ • Vote signing  │  │
│  │ • Tx pool       │  │ • Tx pool       │  │ • Tx pool       │  │
│  └────────┬────────┘  └────────┬────────┘  └────────┬────────┘  │
│           │                    │                    │             │
│           ↓                    ↓                    ↓             │
│  ┌─────────────────┐  ┌─────────────────┐  ┌─────────────────┐  │
│  │ QSSH Queue 9944 │  │ QSSH Queue 9945 │  │ QSSH Queue 9946 │  │
│  │                 │  │                 │  │                 │  │
│  │ Priority Queue: │  │ Priority Queue: │  │ Priority Queue: │  │
│  │ • Critical: 15  │  │ • Critical: 8   │  │ • Critical: 22  │  │
│  │ • High: 42      │  │ • High: 31      │  │ • High: 58      │  │
│  │ • Normal: 70    │  │ • Normal: 50    │  │ • Normal: 123   │  │
│  │ • Low: 0        │  │ • Low: 0        │  │ • Low: 0        │  │
│  │                 │  │                 │  │                 │  │
│  │ RPC Methods:    │  │ RPC Methods:    │  │ RPC Methods:    │  │
│  │ • submitMessage │  │ • submitMessage │  │ • submitMessage │  │
│  │ • popMessage    │  │ • popMessage    │  │ • popMessage    │  │
│  │ • getMetrics    │  │ • getMetrics    │  │ • getMetrics    │  │
│  └─────────────────┘  └─────────────────┘  └─────────────────┘  │
│           ↑                    ↑                    ↑             │
│           │                    │                    │             │
│           └────────────────────┴────────────────────┘             │
│                                │                                  │
│                                ↓                                  │
│  ┌──────────────────────────────────────────────────────────┐    │
│  │        WebSocket Metrics Server (Port 9950)              │    │
│  │                                                           │    │
│  │  Broadcasts real-time metrics to LCARS dashboard:        │    │
│  │  • Queue depths                                          │    │
│  │  • Message rates                                         │    │
│  │  • Latencies                                             │    │
│  │  • Health status                                         │    │
│  └──────────────────────────────────────────────────────────┘    │
│                                                                    │
└───────────────────────────────────────────────────────────────────┘
                                │
                                ↓
                  ┌─────────────────────────────┐
                  │  LCARS Dashboard (Browser)  │
                  │                              │
                  │  ws://localhost:9950         │
                  │  Real-time queue monitoring  │
                  └─────────────────────────────┘
```

### Message Flow

**Example: Block Import**

```
1. Substrate imports block
   ↓
2. Alice's validator task receives notification
   ↓
3. Create QueueMessage::BlockImport
   ↓
4. Submit to Alice's QSSH queue (port 9944)
   ↓
5. Queue assigns priority: Critical (100)
   ↓
6. Message stored in priority queue
   ↓
7. Alice's coherence gadget polls queue
   ↓
8. Pop highest priority message
   ↓
9. Process block import
   ↓
10. Update metrics (queue depth, msg rate)
    ↓
11. Broadcast metrics to WebSocket clients
    ↓
12. LCARS dashboard updates in real-time
```

---

## Component Details

### 1. ValidatorQueue

**File**: `node/src/qssh_queue_manager.rs`

**Purpose**: Priority queue instance for a single validator.

**Key Fields**:
```rust
pub struct ValidatorQueue {
    pub name: String,           // "alice", "bob", or "charlie"
    pub port: u16,              // QSSH-RPC port (9944, 9945, 9946)
    pub queue: PriorityQueue,   // Priority-based message queue
    pub metrics: QueueMetrics,  // Performance tracking
    pub server_handle: Option,  // RPC server handle for shutdown
}
```

**Priority Levels**:
- **Critical (100)**: Block imports, finality votes
- **High (75)**: Transactions, entropy submissions
- **Normal (50)**: Gossip, peer discovery
- **Low (25)**: Telemetry, metrics

**Methods**:
- `submit(message)` - Add message to queue with priority
- `pop()` - Remove and return highest priority message
- `depth()` - Get current queue size
- `get_metrics()` - Return performance metrics
- `start_qssh_rpc_server()` - Spawn RPC server on configured port

### 2. QueueMessage

**Message Types**:
```rust
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
        qber: f32,
    },
    Gossip {
        topic: String,
        data: Vec<u8>,
    },
}
```

**Auto-Priority Assignment**:
Each message type has inherent priority via `message.priority()` method.

### 3. QsshQueueManager

**Purpose**: Global manager for all validator queues.

**Responsibilities**:
- Create and manage validator queues
- Start/stop all QSSH-RPC servers
- Aggregate metrics from all queues
- Broadcast metrics to WebSocket clients

**Key Methods**:
```rust
impl QsshQueueManager {
    pub fn new() -> Self
    pub fn add_validator(name: String, port: u16)
    pub async fn start_all_servers()
    pub async fn stop_all_servers()
    pub fn get_aggregate_metrics() -> AggregateMetrics
    pub async fn start_metrics_websocket(port: u16)
    pub fn broadcast_metrics(global: GlobalMetrics)
}
```

### 4. Metrics System

**QueueMetrics** (per validator):
```rust
pub struct QueueMetrics {
    pub queue_depth: usize,         // Current messages in queue
    pub msg_rate: u64,              // Messages processed per second
    pub latency: u64,               // Average processing latency (ms)
    pub health: u8,                 // Health percentage (0-100)
    pub uptime: Duration,           // Time since queue started
    pub total_processed: u64,       // Lifetime message count
    pub last_message_time: Instant, // Last message timestamp
}
```

**AggregateMetrics** (all validators):
```rust
pub struct AggregateMetrics {
    pub alice: Option<QueueMetrics>,
    pub bob: Option<QueueMetrics>,
    pub charlie: Option<QueueMetrics>,
    pub aggregate: GlobalMetrics,
}
```

**GlobalMetrics** (blockchain-wide):
```rust
pub struct GlobalMetrics {
    pub total_msg_rate: u64,        // Total msgs/sec across all validators
    pub avg_latency: u64,           // Average latency
    pub block_height: u64,          // Current block number
    pub finalized: u64,             // Last finalized block
    pub entropy_pool: usize,        // Quantum entropy pool size
    pub stark_valid: u64,           // Valid STARK proofs
    pub stark_failed: u64,          // Failed STARK proofs
    pub vrf_election_block: u64,    // Last VRF relay election
}
```

### 5. QSSH-RPC API

**Endpoint**: `http://localhost:9944/` (Alice), `9945` (Bob), `9946` (Charlie)

**Methods**:

**qssh_submitMessage**
```json
{
  "jsonrpc": "2.0",
  "method": "qssh_submitMessage",
  "params": {
    "BlockImport": {
      "block_hash": "0x1234...",
      "block_number": 1000,
      "timestamp": 1698509123
    }
  },
  "id": 1
}
```

**qssh_popMessage**
```json
{
  "jsonrpc": "2.0",
  "method": "qssh_popMessage",
  "params": [],
  "id": 2
}
```
Returns highest priority message from queue.

**qssh_getQueueDepth**
```json
{
  "jsonrpc": "2.0",
  "method": "qssh_getQueueDepth",
  "params": [],
  "id": 3
}
```
Returns current queue size.

**qssh_getMetrics**
```json
{
  "jsonrpc": "2.0",
  "method": "qssh_getMetrics",
  "params": [],
  "id": 4
}
```
Returns QueueMetrics struct.

**qssh_getValidatorName**
```json
{
  "jsonrpc": "2.0",
  "method": "qssh_getValidatorName",
  "params": [],
  "id": 5
}
```
Returns "alice", "bob", or "charlie".

---

## Implementation Guide

### Step 1: Create Queue Manager in main.rs

**Current main.rs** (simple):
```rust
fn main() -> sc_cli::Result<()> {
    command::run()
}
```

**New main.rs** (with QSSH queue management):
```rust
use crate::qssh_queue_manager::{QsshQueueManager, GlobalMetrics};
use std::sync::{Arc, RwLock};
use tokio::sync::mpsc;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Initialize logger
    tracing_subscriber::fmt::init();

    // Create QSSH Queue Manager
    let mut queue_manager = QsshQueueManager::new();

    // Add validators
    queue_manager.add_validator("alice".to_string(), 9944);
    queue_manager.add_validator("bob".to_string(), 9945);
    queue_manager.add_validator("charlie".to_string(), 9946);

    // Start all QSSH-RPC servers
    queue_manager.start_all_servers().await?;

    // Start WebSocket metrics server for LCARS dashboard
    queue_manager.start_metrics_websocket(9950).await?;

    let manager = Arc::new(RwLock::new(queue_manager));

    // Channel for global metrics from blockchain
    let (global_tx, global_rx) = mpsc::channel(100);

    // Spawn metrics update loop
    let manager_clone = Arc::clone(&manager);
    tokio::spawn(async move {
        QsshQueueManager::metrics_update_loop(manager_clone, global_rx).await;
    });

    // Spawn Alice validator task
    let manager_clone = Arc::clone(&manager);
    let alice_handle = tokio::spawn(async move {
        run_validator("alice", manager_clone).await;
    });

    // Spawn Bob validator task
    let manager_clone = Arc::clone(&manager);
    let bob_handle = tokio::spawn(async move {
        run_validator("bob", manager_clone).await;
    });

    // Spawn Charlie validator task
    let manager_clone = Arc::clone(&manager);
    let charlie_handle = tokio::spawn(async move {
        run_validator("charlie", manager_clone).await;
    });

    // Spawn blockchain node (blocking operation)
    let node_handle = tokio::task::spawn_blocking(|| {
        if let Err(e) = command::run() {
            eprintln!("Node command failed: {:?}", e);
        }
    });

    // Wait for Ctrl-C
    let ctrl_c_handle = tokio::spawn(async {
        tokio::signal::ctrl_c().await.expect("Failed to listen for Ctrl-C");
        info!("Received Ctrl-C, shutting down.");
    });

    // Wait for any task to complete
    tokio::select! {
        _ = alice_handle => {},
        _ = bob_handle => {},
        _ = charlie_handle => {},
        _ = node_handle => {},
        _ = ctrl_c_handle => {},
    }

    // Cleanup
    let mut mgr = manager.write().unwrap();
    mgr.stop_all_servers().await;

    println!("System shutdown complete.");
    Ok(())
}

async fn run_validator(name: &str, manager: Arc<RwLock<QsshQueueManager>>) {
    loop {
        // Get validator's queue
        let queue = {
            let mgr = manager.read().unwrap();
            mgr.validators.get(name).map(|v| Arc::clone(&v.queue))
        };

        if let Some(queue) = queue {
            // Pop message from queue
            if let Some(message) = {
                let mut q = queue.write().unwrap();
                q.pop().map(|(msg, _)| msg)
            } {
                // Process message
                process_message(name, message).await;
            }
        }

        // Small delay to prevent busy-waiting
        tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
    }
}

async fn process_message(validator: &str, message: QueueMessage) {
    match message {
        QueueMessage::BlockImport { block_hash, block_number, .. } => {
            println!("[{}] Processing block import: #{}", validator, block_number);
        }
        QueueMessage::Vote { .. } => {
            println!("[{}] Processing vote", validator);
        }
        QueueMessage::Transaction { .. } => {
            println!("[{}] Processing transaction", validator);
        }
        QueueMessage::EntropyShare { device_id, qber, .. } => {
            println!("[{}] Processing entropy from {} (QBER: {}%)", validator, device_id, qber);
        }
        QueueMessage::Gossip { topic, .. } => {
            println!("[{}] Processing gossip: {}", validator, topic);
        }
    }
}
```

### Step 2: Integrate with coherence_gadget.rs

**In coherence_gadget.rs**, replace direct stream consumption with queue submission:

```rust
// OLD (causes conflicts):
let block_import_stream = client.import_notification_stream();

// NEW (uses queue):
use crate::qssh_queue_manager::{QueueMessage, ValidatorQueue};

// Submit block import to queue
pub fn submit_block_import(
    queue: &ValidatorQueue,
    block_hash: [u8; 32],
    block_number: u64,
) {
    queue.submit(QueueMessage::BlockImport {
        block_hash,
        block_number,
        timestamp: SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs(),
    });
}
```

### Step 3: Add Cargo Dependencies

**In `node/Cargo.toml`**, add:
```toml
[dependencies]
# ... existing dependencies ...

# QSSH Queue Manager
priority-queue = "1.3"
tokio-tungstenite = "0.20"
futures = "0.3"
```

### Step 4: Deploy LCARS Dashboard

**Copy HTML to wallet**:
```bash
cp wallet/static/qssh-queue-manager.html wallet/static/index.html
```

**Or create symbolic link**:
```bash
ln -s qssh-queue-manager.html wallet/static/queue-dashboard.html
```

**Access dashboard**:
```
http://localhost:8080/qssh-queue-manager.html
```

### Step 5: Test the System

**Start the node**:
```bash
cargo build --release
./target/release/quantumharmony-node
```

**Verify QSSH-RPC servers**:
```bash
curl -X POST http://localhost:9944 \
  -H "Content-Type: application/json" \
  -d '{"jsonrpc":"2.0","method":"qssh_getValidatorName","params":[],"id":1}'

# Should return: {"jsonrpc":"2.0","result":"alice","id":1}
```

**Check queue depth**:
```bash
curl -X POST http://localhost:9944 \
  -H "Content-Type: application/json" \
  -d '{"jsonrpc":"2.0","method":"qssh_getQueueDepth","params":[],"id":1}'
```

**Open LCARS dashboard**:
```bash
open http://localhost:8080/qssh-queue-manager.html
```

---

## LCARS Dashboard

### Features

**File**: `wallet/static/qssh-queue-manager.html`

**Real-Time Monitoring**:
- Validator queue depths (Alice, Bob, Charlie)
- Message processing rates (msgs/sec)
- Average latencies (milliseconds)
- Health status indicators
- Quantum device QBER metrics
- QSSH connection matrix
- Block height and finality

**Visual Design**:
- LCARS (Star Trek TNG) aesthetic
- Color-coded status indicators
- Animated pulse effects for active validators
- Progress bars for queue health
- Retro-futuristic terminal displays

**Navigation Panels**:
1. **VALIDATORS** - Queue status for Alice, Bob, Charlie
2. **DEVICES** - Quantum device status (Toshiba, Crypto4A, KIRQ)
3. **QSSH** - Transport layer connection matrix
4. **METRICS** - Network performance metrics
5. **CONFIG** - Configuration panel (future)

**WebSocket Connection**:
```javascript
ws = new WebSocket('ws://localhost:9950/qssh-queue-metrics');

ws.onmessage = function(event) {
    const data = JSON.parse(event.data);
    updateMetrics(data);
};
```

**Metrics Update Format**:
```json
{
  "alice": {
    "queue_depth": 127,
    "msg_rate": 45,
    "latency": 12,
    "health": 85,
    "uptime": "47d 13h 22m",
    "total_processed": 1247893
  },
  "bob": {
    "queue_depth": 89,
    "msg_rate": 32,
    "latency": 8,
    "health": 92,
    "uptime": "47d 13h 22m",
    "total_processed": 984021
  },
  "charlie": {
    "queue_depth": 203,
    "msg_rate": 67,
    "latency": 15,
    "health": 78,
    "uptime": "47d 13h 22m",
    "total_processed": 1589234
  },
  "aggregate": {
    "total_msg_rate": 144,
    "avg_latency": 11,
    "block_height": 10450,
    "finalized": 10447,
    "entropy_pool": 2847,
    "stark_valid": 1247,
    "stark_failed": 0,
    "vrf_election_block": 10450
  }
}
```

### Screenshots

**Validator Status Panel**:
```
┌──────────────────────────────────────────────────────────────┐
│ VALIDATOR QUEUE STATUS                                       │
├──────────────────────────────────────────────────────────────┤
│                                                               │
│  ┌────────────────┐  ┌────────────────┐  ┌────────────────┐ │
│  │ ALICE          │  │ BOB            │  │ CHARLIE        │ │
│  │ PORT 9944      │  │ PORT 9945      │  │ PORT 9946      │ │
│  │ ● ACTIVE       │  │ ● ACTIVE       │  │ ● ACTIVE       │ │
│  │                │  │                │  │                │ │
│  │ QUEUE: 127     │  │ QUEUE: 89      │  │ QUEUE: 203     │ │
│  │ MSG/S: 45      │  │ MSG/S: 32      │  │ MSG/S: 67      │ │
│  │ LAT:   12ms    │  │ LAT:   8ms     │  │ LAT:   15ms    │ │
│  │ UP:    99.98%  │  │ UP:    99.99%  │  │ UP:    99.95%  │ │
│  │ ████████░░ 85% │  │ █████████░ 92% │  │ ███████░░░ 78% │ │
│  └────────────────┘  └────────────────┘  └────────────────┘ │
│                                                               │
└──────────────────────────────────────────────────────────────┘
```

**Quantum Device Status**:
```
┌──────────────────────────────────────────────────────────────┐
│ QUANTUM DEVICE STATUS                                        │
├──────────────────────────────────────────────────────────────┤
│                                                               │
│ TOSHIBA-QKD-01  │ QBER: 2.3% │ ████████░░ │ OPTIMAL         │
│ CRYPTO4A-HSM    │ QBER: 1.1% │ ██████████ │ EXCELLENT       │
│ KIRQ-HUB-BETA   │ QBER: 4.7% │ ██████░░░░ │ ACCEPTABLE      │
│                                                               │
│ ENTROPY POOL: 2847  │ SHAMIR: K=2/M=3  │ STARK: 1247/0     │
│                                                               │
└──────────────────────────────────────────────────────────────┘
```

---

## API Reference

### REST API (JSON-RPC)

**Base URLs**:
- Alice: `http://localhost:9944`
- Bob: `http://localhost:9945`
- Charlie: `http://localhost:9946`

**Methods**:

#### qssh_submitMessage

Submit a message to the validator's priority queue.

**Request**:
```json
POST /
Content-Type: application/json

{
  "jsonrpc": "2.0",
  "method": "qssh_submitMessage",
  "params": {
    "BlockImport": {
      "block_hash": "0x1234567890abcdef...",
      "block_number": 1000,
      "timestamp": 1698509123
    }
  },
  "id": 1
}
```

**Response**:
```json
{
  "jsonrpc": "2.0",
  "result": "Message queued with priority Critical",
  "id": 1
}
```

#### qssh_popMessage

Pop the highest priority message from the queue.

**Request**:
```json
POST /
Content-Type: application/json

{
  "jsonrpc": "2.0",
  "method": "qssh_popMessage",
  "params": [],
  "id": 2
}
```

**Response**:
```json
{
  "jsonrpc": "2.0",
  "result": {
    "BlockImport": {
      "block_hash": "0x1234567890abcdef...",
      "block_number": 1000,
      "timestamp": 1698509123
    }
  },
  "id": 2
}
```

#### qssh_getQueueDepth

Get current number of messages in queue.

**Request**:
```json
POST /
Content-Type: application/json

{
  "jsonrpc": "2.0",
  "method": "qssh_getQueueDepth",
  "params": [],
  "id": 3
}
```

**Response**:
```json
{
  "jsonrpc": "2.0",
  "result": 127,
  "id": 3
}
```

#### qssh_getMetrics

Get detailed performance metrics for the queue.

**Request**:
```json
POST /
Content-Type: application/json

{
  "jsonrpc": "2.0",
  "method": "qssh_getMetrics",
  "params": [],
  "id": 4
}
```

**Response**:
```json
{
  "jsonrpc": "2.0",
  "result": {
    "queue_depth": 127,
    "msg_rate": 45,
    "latency": 12,
    "health": 85,
    "uptime": "47d 13h 22m",
    "total_processed": 1247893,
    "last_message_time": "2025-10-28T16:45:23Z"
  },
  "id": 4
}
```

### WebSocket API

**Endpoint**: `ws://localhost:9950/qssh-queue-metrics`

**Connection**:
```javascript
const ws = new WebSocket('ws://localhost:9950/qssh-queue-metrics');

ws.onopen = () => {
    console.log('Connected to metrics stream');
};

ws.onmessage = (event) => {
    const metrics = JSON.parse(event.data);
    console.log('Metrics update:', metrics);
};
```

**Message Format** (server → client):
```json
{
  "alice": { /* QueueMetrics */ },
  "bob": { /* QueueMetrics */ },
  "charlie": { /* QueueMetrics */ },
  "aggregate": { /* GlobalMetrics */ }
}
```

---

## Deployment Scenarios

### Scenario 1: Dev Wallet with Local Testnet

**Use Case**: Frontend wallet development with 3 validators on localhost.

**Setup**:
```bash
# 1. Start QuantumHarmony node with QSSH queue manager
./target/release/quantumharmony-node

# 2. Verify all 3 QSSH-RPC servers are running
curl http://localhost:9944 -X POST -H "Content-Type: application/json" \
  -d '{"jsonrpc":"2.0","method":"qssh_getValidatorName","params":[],"id":1}'

curl http://localhost:9945 -X POST -H "Content-Type: application/json" \
  -d '{"jsonrpc":"2.0","method":"qssh_getValidatorName","params":[],"id":1}'

curl http://localhost:9946 -X POST -H "Content-Type: application/json" \
  -d '{"jsonrpc":"2.0","method":"qssh_getValidatorName","params":[],"id":1}'

# 3. Open LCARS dashboard
open http://localhost:8080/qssh-queue-manager.html

# 4. Start wallet UI
cd wallet
npm run dev
```

**Configuration**:
- All validators in **single process**
- No Docker, no VMs
- All on localhost
- Ports: 9944 (Alice), 9945 (Bob), 9946 (Charlie), 9950 (Metrics)

### Scenario 2: Multi-Machine Testnet

**Use Case**: Testing relay selection and QSSH transport across machines.

**Machine 1 (Alice)**:
```bash
./target/release/quantumharmony-node \
  --validator --name alice \
  --qssh-queue-port 9944 \
  --public-addr /ip4/192.168.1.10/tcp/30333
```

**Machine 2 (Bob)**:
```bash
./target/release/quantumharmony-node \
  --validator --name bob \
  --qssh-queue-port 9945 \
  --public-addr /ip4/192.168.1.11/tcp/30333 \
  --bootnodes /ip4/192.168.1.10/tcp/30333/p2p/...
```

**Machine 3 (Charlie)**:
```bash
./target/release/quantumharmony-node \
  --validator --name charlie \
  --qssh-queue-port 9946 \
  --public-addr /ip4/192.168.1.12/tcp/30333 \
  --bootnodes /ip4/192.168.1.10/tcp/30333/p2p/...
```

### Scenario 3: Production with QKD Hardware

**Use Case**: Nokia deployment with Crypto4A HSM and optional Toshiba QKD.

**Configuration**:
```bash
./target/release/quantumharmony-node \
  --validator --name alice \
  --qssh-queue-port 9944 \
  --qkd-mode optional \
  --pqtg-endpoint https://localhost:8443 \
  --pqtg-devices crypto4a,toshiba-qkd \
  --enable-qssh \
  --qssh-binary-path /usr/local/bin/qssh \
  --ssh-key-path ~/.ssh/quantumharmony_key \
  --ssh-port 22
```

**Firewall Rules** (Nokia constraint - only ports 22 and 443):
```bash
# Allow QSSH on port 22
iptables -A INPUT -p tcp --dport 22 -j ACCEPT

# Allow HTTPS for PQTG
iptables -A INPUT -p tcp --dport 443 -j ACCEPT

# Block all other incoming
iptables -P INPUT DROP
```

---

## Troubleshooting

### Problem: "SelectNextSome polled after terminated"

**Symptom**: Bob and Charlie validators crash immediately.

**Cause**: Multiple validators trying to consume same notification stream.

**Solution**:
1. Verify you're using the QSSH queue manager (not direct stream consumption)
2. Check that each validator has its own queue instance
3. Ensure QSSH-RPC servers are running on different ports

**Verification**:
```bash
# Should show 3 separate queue instances
curl http://localhost:9944 -X POST -d '{"jsonrpc":"2.0","method":"qssh_getValidatorName","params":[],"id":1}'
curl http://localhost:9945 -X POST -d '{"jsonrpc":"2.0","method":"qssh_getValidatorName","params":[],"id":1}'
curl http://localhost:9946 -X POST -d '{"jsonrpc":"2.0","method":"qssh_getValidatorName","params":[],"id":1}'
```

### Problem: Queue Depth Growing Unbounded

**Symptom**: LCARS dashboard shows queue depth continuously increasing.

**Cause**: Messages being submitted faster than processed.

**Solution**:
1. Check validator task is polling queue
2. Verify message processing loop is not blocked
3. Increase polling frequency if needed

**Debug**:
```rust
// Add debug logging to validator task
async fn run_validator(name: &str, manager: Arc<RwLock<QsshQueueManager>>) {
    loop {
        let queue_depth = {
            let mgr = manager.read().unwrap();
            mgr.validators.get(name).map(|v| v.depth()).unwrap_or(0)
        };

        println!("[{}] Queue depth: {}", name, queue_depth);

        // ... rest of processing ...
    }
}
```

### Problem: WebSocket Not Connecting

**Symptom**: LCARS dashboard shows "WebSocket not available, using simulation mode".

**Cause**: Metrics WebSocket server not started or wrong port.

**Solution**:
1. Verify WebSocket server started: `netstat -an | grep 9950`
2. Check browser console for connection errors
3. Ensure CORS settings allow WebSocket

**Test**:
```bash
# Install wscat
npm install -g wscat

# Connect to metrics WebSocket
wscat -c ws://localhost:9950/qssh-queue-metrics
```

### Problem: High Latency on Validator Queue

**Symptom**: LCARS dashboard shows latency > 100ms for a validator.

**Cause**: Queue processing backlog or network issues.

**Solution**:
1. Check queue depth - if > 1000, increase processing rate
2. Verify network connectivity between validators
3. Check system resource usage (CPU, memory)

**Metrics Analysis**:
```bash
# Get metrics for Alice
curl http://localhost:9944 -X POST -d '{"jsonrpc":"2.0","method":"qssh_getMetrics","params":[],"id":1}'

# Expected: latency < 50ms, health > 80
```

### Problem: QSSH-RPC Server Won't Start

**Symptom**: Error: "Address already in use" when starting node.

**Cause**: Port already bound by another process.

**Solution**:
```bash
# Find process using port 9944
lsof -i :9944

# Kill offending process
kill -9 <PID>

# Or change port in configuration
./target/release/quantumharmony-node --qssh-queue-port 19944
```

### Problem: Quantum Device QBER Too High

**Symptom**: LCARS shows QBER > 10% for Toshiba or KIRQ device.

**Cause**: QKD hardware issue or fiber optic degradation.

**Solution**:
1. Check physical QKD connections
2. Verify fiber optic cable integrity
3. Review PQTG endpoint logs
4. Temporarily switch to `--qkd-mode optional` to use HWRNG fallback

**Fallback**:
```bash
./target/release/quantumharmony-node --qkd-mode disabled
# This uses pure HWRNG instead of QKD
```

---

## Future Enhancements

### Phase 1: Enhanced Queue Types

- **Circular Buffer Queue**: Fixed-size queue with overflow protection
- **Weighted Queue**: Different weights for different message types
- **Rate-Limited Queue**: Enforce max msgs/sec per validator

### Phase 2: Advanced Metrics

- **Histogram Latencies**: Track latency distribution
- **Queue Saturation Alerts**: Notify when queue > 80% capacity
- **Anomaly Detection**: ML-based detection of unusual patterns

### Phase 3: Relay Integration

- **VRF-Based Relay Selection**: Integrate with relay_manager.rs
- **Multi-Path Routing**: Route messages via multiple relays
- **QKD Island Bridging**: Connect geographically separated QKD islands

### Phase 4: Production Hardening

- **Persistent Queues**: Survive node restarts
- **Queue Replication**: Backup queues for failover
- **Horizontal Scaling**: Support > 3 validators per process

---

## References

- **QSSH Implementation**: `/Users/sylvaincormier/QuantumVerseProtocols/quantum-harmony-base/node-blockchain/src/qssh_server.rs`
- **Priority Queue Crate**: https://docs.rs/priority-queue/
- **jsonrpsee**: https://docs.rs/jsonrpsee/
- **tokio-tungstenite**: https://docs.rs/tokio-tungstenite/
- **LCARS Design Guidelines**: Memory Alpha - Star Trek
- **Decentralized QKD Relay Architecture**: `docs/DECENTRALIZED_QKD_RELAY_ARCHITECTURE.md`

---

**Document Status**: Implementation Phase
**Last Updated**: 2025-10-28
**Version**: 1.0
**Author**: Claude (Anthropic) + Sylvain Cormier
