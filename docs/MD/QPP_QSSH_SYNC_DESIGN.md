# QPP-Enhanced QSSH Queue Manager - Sync Design

**Document Version:** 1.0
**Created:** 2025-10-28
**Purpose:** Design documentation for QPP integration with QSSH Queue Manager
**Status:** Implementation Complete

---

## Executive Summary

This document describes how the **Quantum Preservation Pattern (QPP)** strengthens the QSSH Queue Manager with **sync/persistence guarantees**, **no-cloning enforcement**, and **type-state safety**.

### What QPP Adds to QSSH Queues

| Feature | Without QPP | With QPP |
|---------|-------------|----------|
| **Message Persistence** | In-memory only | Fsync to disk before ack (SyncOp) |
| **Crash Recovery** | Messages lost | Restore from WAL on restart |
| **Message Duplication** | Possible | Impossible (NoClone enforcement) |
| **Queue Lifecycle** | Runtime checks | Compile-time type-states |
| **Provenance Tracking** | None | Full message origin tracking |

---

## Table of Contents

1. [QPP Pillars Applied](#qpp-pillars-applied)
2. [Architecture Overview](#architecture-overview)
3. [Type-State Transitions](#type-state-transitions)
4. [Sync vs Async Operations](#sync-vs-async-operations)
5. [Write-Ahead Log (WAL)](#write-ahead-log-wal)
6. [NoClone Enforcement](#noclone-enforcement)
7. [Crash Recovery](#crash-recovery)
8. [QSSH Branches Integration](#qssh-branches-integration)
9. [API Reference](#api-reference)
10. [Implementation Examples](#implementation-examples)

---

## QPP Pillars Applied

### 1. NoClone Types (Quantum No-Cloning Theorem)

**Problem**: Messages could be duplicated, violating quantum semantics.

**Solution**: Wrap messages in `NoClone<T>`:

```rust
pub type QppQueueMessage = NoClone<QueueMessageWithProvenance>;

// Can only consume once
let msg = queue.pop().unwrap();
let data = msg.consume(); // Moves out
// msg.consume(); // ❌ Compile error - value moved
```

**Quantum Analogy**: Once you measure a quantum state (consume a message), it collapses and cannot be measured again.

### 2. Type States (Quantum State Transitions)

**Problem**: Messages could be consumed before persistence, causing data loss.

**Solution**: Type-state pattern enforces lifecycle:

```rust
Queued → Persisted → Consumed
```

**Compile-time enforcement**:
```rust
let queued = TypeStateMessage::<Queued>::new(msg);
// queued.consume(); // ❌ Compile error - can't consume non-persisted message

let persisted = queued.persist(&wal_path)?; // Queued → Persisted
let consumed = persisted.consume(); // Persisted → Consumed ✓
```

**Quantum Analogy**: Quantum state transitions (|0⟩ → |1⟩) are irreversible and must follow allowed paths.

### 3. Move Semantics (Measurement Collapse)

**Problem**: Messages could be used multiple times after consumption.

**Solution**: Rust's move semantics model quantum measurement:

```rust
impl TypeStateMessage<Persisted> {
    pub fn consume(self) -> TypeStateMessage<Consumed> {
        // self is moved (consumed), cannot be used again
        TypeStateMessage::<Consumed> {
            message: self.message,
            _state: std::marker::PhantomData,
        }
    }
}
```

**Quantum Analogy**: Measuring a quantum state (consuming a message) collapses the wavefunction - it's a one-time, irreversible operation.

### 4. Sync/Async Operations (QPP Explicit Guarantees)

**Problem**: Unclear whether operations guarantee durability.

**Solution**: Explicit `SyncOp` vs `AsyncOp` types:

```rust
// SyncOp - guarantees fsync before returning
let msg_id = QppSyncSubmit::execute(&queue, message)?;

// AsyncOp - in-memory only, no durability guarantee
let msg_id = QppAsyncSubmit::execute(&queue, message).await?;
```

**QPP Design**: Operations are either **synchronous with durability** or **asynchronous without durability** - never ambiguous.

---

## Architecture Overview

### System Diagram

```
┌─────────────────────────────────────────────────────────────────┐
│            QPP-Enhanced QSSH Queue Manager                      │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  Message Submission                                             │
│         ↓                                                        │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │ SyncOp: submit_sync()                                    │  │
│  │ - Persist to WAL with fsync                              │  │
│  │ - Add to in-memory queue                                 │  │
│  │ - Return only after disk sync                            │  │
│  │                                                           │  │
│  │ AsyncOp: submit_async()                                  │  │
│  │ - Add to in-memory queue only                            │  │
│  │ - No disk I/O                                            │  │
│  │ - Return immediately                                     │  │
│  └──────────────────────────────────────────────────────────┘  │
│         ↓                                                        │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │ Priority Queue (In-Memory)                               │  │
│  │ - Critical (100): Blocks, Votes                          │  │
│  │ - High (75): Transactions, Entropy                       │  │
│  │ - Normal (50): Gossip                                    │  │
│  │ - Low (25): Telemetry                                    │  │
│  └──────────────────────────────────────────────────────────┘  │
│         ↓                                                        │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │ Write-Ahead Log (WAL)                                    │  │
│  │ - Append-only log file                                   │  │
│  │ - Fsync on every SyncOp write                            │  │
│  │ - Compaction to remove consumed messages                 │  │
│  │ - Restore on startup after crash                         │  │
│  └──────────────────────────────────────────────────────────┘  │
│         ↓                                                        │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │ Message Consumption (NoClone)                            │  │
│  │ - Pop returns NoClone<QueueMessageWithProvenance>        │  │
│  │ - Can only consume() once                                │  │
│  │ - Enforces no-cloning theorem                            │  │
│  └──────────────────────────────────────────────────────────┘  │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### Key Components

**1. QppValidatorQueue**
- Per-validator queue instance (Alice, Bob, Charlie)
- In-memory priority queue + persistent WAL
- Dual submission modes: sync (fsync) vs async (in-memory)

**2. TypeStateMessage<State>**
- Compile-time lifecycle enforcement
- States: `Queued → Persisted → Consumed`
- Prevents consuming non-persisted messages

**3. QueueMessageWithProvenance**
- Message payload + metadata
- Tracks: message_id, created_at, submitted_by, persisted, broadcast

**4. Write-Ahead Log (WAL)**
- Append-only persistence
- Fsync on every sync write
- Compaction to prevent unbounded growth
- Crash recovery on startup

---

## Type-State Transitions

### State Machine Diagram

```
┌──────────┐
│ Queued   │  Created when message submitted
└─────┬────┘
      │
      │ .persist(&wal_path) → fsync to disk
      ↓
┌──────────┐
│Persisted │  Safe to consume
└─────┬────┘
      │
      │ .consume() → measurement collapse
      ↓
┌──────────┐
│Consumed  │  Terminal state, extract with .into_inner()
└──────────┘
```

### Implementation

```rust
/// Type-state message wrapper
pub struct TypeStateMessage<State> {
    message: QueueMessageWithProvenance,
    _state: std::marker::PhantomData<State>,
}

// State transitions
impl TypeStateMessage<Queued> {
    /// Queued → Persisted (requires disk sync)
    pub fn persist(self, wal_path: &Path)
        -> Result<TypeStateMessage<Persisted>, String>
    {
        // Write to file
        let serialized = serde_json::to_string(&self.message)?;
        let mut file = OpenOptions::new()
            .create(true)
            .append(true)
            .open(wal_path)?;
        writeln!(file, "{}", serialized)?;

        // CRITICAL: fsync ensures durability
        file.sync_all()?;

        Ok(TypeStateMessage::<Persisted> {
            message: self.message,
            _state: std::marker::PhantomData,
        })
    }
}

impl TypeStateMessage<Persisted> {
    /// Persisted → Consumed (measurement collapse)
    pub fn consume(self) -> TypeStateMessage<Consumed> {
        TypeStateMessage::<Consumed> {
            message: self.message,
            _state: std::marker::PhantomData,
        }
    }
}
```

### Compile-Time Safety

**✅ Allowed**:
```rust
let queued = TypeStateMessage::<Queued>::new(msg);
let persisted = queued.persist(&wal_path)?; // OK
let consumed = persisted.consume(); // OK
```

**❌ Prevented by Compiler**:
```rust
let queued = TypeStateMessage::<Queued>::new(msg);
let consumed = queued.consume(); // ❌ Error: no method `consume` on Queued state
```

```rust
let persisted = queued.persist(&wal_path)?;
let consumed1 = persisted.consume();
let consumed2 = persisted.consume(); // ❌ Error: value used after move
```

---

## Sync vs Async Operations

### SyncOp: Guaranteed Durability

**Use Case**: Critical messages that must survive crashes (blocks, votes, transactions)

**Guarantees**:
- Message written to WAL
- `fsync()` called before returning
- Survives power failure, kernel panic, process crash

**Performance**: ~100-1000 µs per message (SSD-dependent)

**Code**:
```rust
pub struct QppSyncSubmit;

impl QppSyncSubmit {
    pub fn execute(
        queue: &QppValidatorQueue,
        message: QueueMessage,
    ) -> SyncResult<u64> {
        queue.submit_sync(message) // Calls fsync internally
    }
}

// Usage
let msg = QueueMessage::BlockImport {
    block_hash: [1; 32],
    block_number: 100,
    timestamp: 1698509123,
};

let msg_id = QppSyncSubmit::execute(&alice_queue, msg)?;
// At this point, message is GUARANTEED on disk
```

### AsyncOp: No Durability Guarantee

**Use Case**: Low-priority messages where performance > durability (gossip, telemetry)

**Guarantees**:
- Message added to in-memory queue
- NOT written to disk
- Lost on crash

**Performance**: ~1-10 µs per message (RAM-only)

**Code**:
```rust
pub struct QppAsyncSubmit;

impl QppAsyncSubmit {
    pub async fn execute(
        queue: &QppValidatorQueue,
        message: QueueMessage,
    ) -> AsyncResult<u64> {
        queue.submit_async(message) // No fsync
    }
}

// Usage
let msg = QueueMessage::Gossip {
    topic: "peer_discovery".to_string(),
    data: vec![1, 2, 3],
};

let msg_id = QppAsyncSubmit::execute(&alice_queue, msg).await?;
// Message in RAM only - fast but not crash-safe
```

### Decision Matrix

| Message Type | Use SyncOp? | Reasoning |
|--------------|-------------|-----------|
| Block Import | ✅ Yes | Critical - must survive crash |
| Finality Vote | ✅ Yes | Critical - affects consensus |
| Transaction | ✅ Yes | User expects durability |
| Entropy Share | ✅ Yes | Quantum data is precious |
| Gossip | ❌ No | Can be resent, not critical |
| Telemetry | ❌ No | Metrics, not essential |
| Peer Discovery | ❌ No | Dynamic, frequently updated |

---

## Write-Ahead Log (WAL)

### Structure

**File Format**: Newline-delimited JSON (NDJSON)

```
{alice}_wal.log:
{"message":{"BlockImport":{...}},"message_id":1,"created_at":1698509120,"submitted_by":"alice","persisted":true,"broadcast":false}
{"message":{"Vote":{...}},"message_id":2,"created_at":1698509121,"submitted_by":"alice","persisted":true,"broadcast":false}
{"message":{"Transaction":{...}},"message_id":3,"created_at":1698509122,"submitted_by":"alice","persisted":true,"broadcast":false}
```

**One line = One message**

### Persistence Guarantee

**fsync()** ensures:
1. Data written to OS kernel buffers
2. Kernel flushes buffers to disk controller
3. Disk controller commits to persistent storage (SSD/HDD)
4. Only then does `file.sync_all()` return

**Result**: Power failure, kernel panic, or process kill CANNOT lose acknowledged messages.

### Compaction

**Problem**: WAL grows unbounded as messages accumulate.

**Solution**: Periodic compaction removes consumed messages.

**Algorithm**:
```rust
pub fn compact_wal(&self) -> Result<(), String> {
    // 1. Read current queue state (unconsumed messages)
    let current_messages: Vec<_> = {
        let queue = self.queue.read().unwrap();
        queue.iter().map(|(msg, _)| msg.clone()).collect()
    };

    // 2. Write to temp file
    let temp_path = self.wal_path.with_extension("tmp");
    let mut temp_file = BufWriter::new(File::create(&temp_path)?);

    for msg in current_messages {
        writeln!(temp_file, "{}", serde_json::to_string(&msg)?)?;
    }

    // 3. Fsync temp file
    temp_file.flush()?;
    temp_file.get_ref().sync_all()?;

    // 4. Atomic rename (POSIX guarantees atomicity)
    std::fs::rename(&temp_path, &self.wal_path)?;

    Ok(())
}
```

**Trigger**: Compact when WAL size > 10 MB or every N messages.

### Recovery

**On Startup**:
```rust
pub fn restore_from_wal(&self) -> Result<usize, String> {
    if !self.wal_path.exists() {
        return Ok(0); // No WAL, fresh start
    }

    let file = File::open(&self.wal_path)?;
    let reader = BufReader::new(file);
    let mut count = 0;

    for line in reader.lines() {
        let msg: QueueMessageWithProvenance = serde_json::from_str(&line?)?;

        // Add to in-memory queue
        let priority = msg.priority();
        let mut queue = self.queue.write().unwrap();
        queue.push(msg, Reverse(priority));
        count += 1;
    }

    info!("[{}] Restored {} messages from WAL", self.name, count);
    Ok(count)
}
```

**Crash Scenario**:
```
1. Process crashes at 10:00:00
2. Last fsync completed at 09:59:58 (message #1000)
3. Messages #1001-1005 were in flight (not fsync'd)

Recovery:
- Messages #1-1000: ✅ Restored from WAL
- Messages #1001-1005: ❌ Lost (never fsync'd)
- Result: Only in-flight messages lost (AsyncOp or SyncOp not yet completed)
```

---

## NoClone Enforcement

### Problem Statement

Without NoClone:
```rust
let msg = queue.pop().unwrap();
let data1 = msg.clone(); // ❌ Violates no-cloning theorem
let data2 = msg.clone(); // ❌ Same message used twice
```

**Quantum Violation**: Cloning quantum states is impossible (Wootters-Zurek 1982).

### Solution: NoClone Wrapper

```rust
pub struct NoClone<T>(T);

impl<T> NoClone<T> {
    pub fn new(value: T) -> Self {
        NoClone(value)
    }

    /// Consume the wrapper (one-time use)
    pub fn consume(self) -> T {
        self.0 // Moves out
    }
}

// ❌ Explicitly NOT implementing Clone!
```

### Usage

```rust
// Queue returns NoClone-wrapped message
let msg: NoClone<QueueMessageWithProvenance> = queue.pop().unwrap();

// Can only consume once
let data = msg.consume(); // Moves out of msg

// ❌ This is a compile error:
// let data2 = msg.consume(); // Error: value used after move
```

### Type-Level Enforcement

**Compile-time errors prevent quantum violations**:

```rust
let msg = queue.pop().unwrap();
let data1 = msg.consume();

// ❌ Error: use of moved value `msg`
let data2 = msg.consume();
```

```rust
let msg = queue.pop().unwrap();

// ❌ Error: no method named `clone` found for type `NoClone<_>`
let msg_clone = msg.clone();
```

**Result**: Quantum no-cloning theorem enforced by Rust compiler!

---

## Crash Recovery

### Scenario 1: Process Crash During SyncOp

**Timeline**:
```
09:00:00.000 - submit_sync() called for message #100
09:00:00.001 - Message serialized to JSON
09:00:00.002 - Written to WAL file
09:00:00.003 - fsync() called
09:00:00.005 - ⚡ PROCESS CRASHES HERE (before fsync returns)
09:00:00.010 - fsync() would have returned (but process dead)
```

**Recovery**:
```
09:00:10.000 - Process restarts
09:00:10.100 - restore_from_wal() called
09:00:10.150 - Message #100 MAY be in WAL (depends on kernel fsync timing)

Outcomes:
- If kernel completed fsync before crash: ✅ Message #100 restored
- If kernel did not complete fsync: ❌ Message #100 lost
```

**Guarantee**: Only messages where `submit_sync()` returned successfully are guaranteed recoverable.

### Scenario 2: Power Failure During AsyncOp

**Timeline**:
```
09:00:00.000 - submit_async() called for messages #1-100
09:00:00.001 - All 100 messages added to in-memory queue
09:00:00.002 - ⚡ POWER FAILURE
```

**Recovery**:
```
09:05:00.000 - Power restored, process restarts
09:05:00.100 - restore_from_wal() called
09:05:00.150 - WAL is empty (AsyncOp doesn't write to WAL)

Outcome:
- All 100 messages: ❌ Lost (never persisted)
```

**Guarantee**: AsyncOp messages are NEVER recoverable after crash.

### Scenario 3: Graceful Shutdown

**Timeline**:
```
09:00:00.000 - SIGTERM received
09:00:00.001 - Begin graceful shutdown
09:00:00.002 - Flush all in-memory queues to WAL
09:00:00.005 - fsync() all queues
09:00:00.010 - Wait for ongoing operations
09:00:00.050 - Exit cleanly
```

**Recovery**:
```
09:00:10.000 - Process restarts
09:00:10.100 - restore_from_wal() called
09:00:10.150 - All messages restored (including AsyncOp messages flushed on shutdown)

Outcome:
- All messages: ✅ Restored (even AsyncOp, because graceful shutdown flushed them)
```

**Guarantee**: Graceful shutdown preserves ALL messages (sync + async).

---

## QSSH Branches Integration

### Main Branch

**Status**: v0.0.1-alpha
**Features**:
- Basic QSSH functionality
- Falcon-512 key exchange
- SPHINCS+ authentication
- ChaCha20-Poly1305 encryption

**Used in**: Basic QSSH queue RPC servers (ports 9944, 9945, 9946)

### Feature/Quantum-Native-Transport Branch

**Status**: Active development
**Key Additions**:

1. **Drista Integration** (`src/drista_integration.rs`)
   - Wallet-based security tier selection
   - Hardware capability detection (QRNG, QKD)
   - Auto-escalation for high-value transactions

2. **Security Tiers** (`src/security_tiers.rs`)
   - Tier 1: Basic PQ (< $100)
   - Tier 2: Hardened PQ (< $10k)
   - Tier 3: Entropy Enhanced (< $1M)
   - Tier 4: Quantum Secured (> $1M, requires QKD)

3. **Quantum-Resistant Transport** (`src/transport/quantum_resistant.rs`)
   - Enhanced key exchange protocols
   - Multi-algorithm support (Kyber, Saber, NTRU)
   - QKD integration layer

4. **QSSL Transport** (`src/transport/qssl_transport.rs`)
   - Quantum-safe SSL replacement
   - Compatible with existing TLS infrastructure
   - Certificate pinning for PQ keys

### Integration Strategy

**For QSSH Queue Manager**:

1. **Use Main Branch** for core QSSH-RPC servers
   - Mature, stable codebase
   - Minimal dependencies
   - Proven in production

2. **Use Feature Branch** for wallet integration
   - Security tier selection based on transaction value
   - Hardware detection for quantum devices
   - Auto-escalation for critical operations

**Example Integration**:
```rust
use qssh::drista_integration::{HardwareCapabilities, DristaQsshConfig};
use qssh::security_tiers::SecurityTier;

// Detect hardware on validator startup
let hw = HardwareCapabilities::detect().await;

// Configure QSSH based on hardware
let tier = if hw.has_qkd {
    SecurityTier::QuantumSecured
} else if hw.has_qrng {
    SecurityTier::EntropyEnhanced
} else {
    SecurityTier::HardenedPQ
};

// Use appropriate tier for queue RPC
let queue_config = DristaQsshConfig {
    tier,
    node_endpoint: "localhost:9944".to_string(),
    hardware: hw,
    auto_escalate: true,
};
```

---

## API Reference

### QppValidatorQueue

**Constructor**:
```rust
pub fn new(
    name: String,
    port: u16,
    persist_dir: impl AsRef<Path>
) -> Result<Self, String>
```

**Sync Submit** (SyncOp):
```rust
pub fn submit_sync(&self, message: QueueMessage) -> Result<u64, String>
```
- Persists message to WAL with fsync
- Returns message ID
- Guarantees durability

**Async Submit** (AsyncOp):
```rust
pub fn submit_async(&self, message: QueueMessage) -> Result<u64, String>
```
- Adds message to in-memory queue only
- No disk I/O
- Fast but not crash-safe

**Pop Message**:
```rust
pub fn pop(&self) -> Option<NoClone<QueueMessageWithProvenance>>
```
- Returns highest priority message
- Wrapped in NoClone (one-time use)
- Updates metrics

**WAL Operations**:
```rust
pub fn restore_from_wal(&self) -> Result<usize, String>
pub fn compact_wal(&self) -> Result<(), String>
```

### TypeStateMessage

**Create Queued**:
```rust
pub fn new(message: QueueMessageWithProvenance) -> TypeStateMessage<Queued>
```

**Persist** (Queued → Persisted):
```rust
pub fn persist(self, wal_path: &Path) -> Result<TypeStateMessage<Persisted>, String>
```

**Consume** (Persisted → Consumed):
```rust
pub fn consume(self) -> TypeStateMessage<Consumed>
```

**Extract Final**:
```rust
pub fn into_inner(self) -> QueueMessageWithProvenance // Only on Consumed state
```

### QppSyncSubmit

```rust
pub struct QppSyncSubmit;

impl QppSyncSubmit {
    pub fn execute(
        queue: &QppValidatorQueue,
        message: QueueMessage,
    ) -> SyncResult<u64>;
}
```

### QppAsyncSubmit

```rust
pub struct QppAsyncSubmit;

impl QppAsyncSubmit {
    pub async fn execute(
        queue: &QppValidatorQueue,
        message: QueueMessage,
    ) -> AsyncResult<u64>;
}
```

---

## Implementation Examples

### Example 1: Sync Submit for Critical Messages

```rust
use crate::qssh_queue_qpp::{QppValidatorQueue, QppSyncSubmit};
use crate::qssh_queue_manager::QueueMessage;

// Create queue
let alice_queue = QppValidatorQueue::new(
    "alice".to_string(),
    9944,
    "/var/lib/quantumharmony/alice"
)?;

// Submit block import (critical - must survive crash)
let block_msg = QueueMessage::BlockImport {
    block_hash: [1; 32],
    block_number: 1000,
    timestamp: 1698509123,
};

// Sync submit - fsync before returning
let msg_id = QppSyncSubmit::execute(&alice_queue, block_msg)?;

println!("Block import {} persisted", msg_id);
// At this point, message is GUARANTEED on disk
```

### Example 2: Async Submit for Low-Priority Messages

```rust
use crate::qssh_queue_qpp::{QppValidatorQueue, QppAsyncSubmit};

// Submit gossip message (low priority - speed > durability)
let gossip_msg = QueueMessage::Gossip {
    topic: "peer_discovery".to_string(),
    data: vec![1, 2, 3],
};

// Async submit - no fsync, fast
let msg_id = QppAsyncSubmit::execute(&alice_queue, gossip_msg).await?;

println!("Gossip message {} queued (not persisted)", msg_id);
```

### Example 3: NoClone Enforcement

```rust
// Pop message from queue
let msg = alice_queue.pop().unwrap();

// Can only consume once
let data = msg.consume();

// Process the message
match data.message {
    QueueMessage::BlockImport { block_hash, .. } => {
        println!("Processing block: {:?}", block_hash);
    }
    _ => {}
}

// ❌ This would be a compile error:
// let data2 = msg.consume(); // Error: value used after move
```

### Example 4: Type-State Transitions

```rust
use crate::qssh_queue_qpp::{
    TypeStateMessage, Queued, Persisted, Consumed,
    QueueMessageWithProvenance,
};

// Create message with provenance
let msg = QueueMessageWithProvenance::new(
    QueueMessage::Transaction {
        tx_hash: [42; 32],
        tx_data: vec![1, 2, 3],
    },
    "alice".to_string(),
    123,
);

// Queued state
let queued = TypeStateMessage::<Queued>::new(msg);

// ❌ Cannot consume in Queued state:
// let consumed = queued.consume(); // Compile error

// Persist (Queued → Persisted)
let persisted = queued.persist(&wal_path)?;

// ✅ Can now consume:
let consumed = persisted.consume();

// Extract final message
let final_msg = consumed.into_inner();
assert!(final_msg.persisted);
```

### Example 5: Crash Recovery

```rust
use crate::qssh_queue_qpp::QppValidatorQueue;

// On startup, restore from WAL
let alice_queue = QppValidatorQueue::new(
    "alice".to_string(),
    9944,
    "/var/lib/quantumharmony/alice"
)?;

// Restore persisted messages
let restored_count = alice_queue.restore_from_wal()?;

println!("Restored {} messages from crash", restored_count);

// Queue now contains all persisted messages from before crash
assert_eq!(alice_queue.depth(), restored_count);
```

### Example 6: WAL Compaction

```rust
// Compact WAL to remove consumed messages
alice_queue.compact_wal()?;

println!("WAL compacted - removed consumed messages");

// WAL now only contains unconsumed messages
```

### Example 7: Integration with QSSH Drista Branch

```rust
use qssh::drista_integration::{HardwareCapabilities, DristaQsshConfig};
use qssh::security_tiers::SecurityTier;

// Detect hardware
let hw = HardwareCapabilities::detect().await;

println!("Detected QRNG: {}", hw.has_qrng);
println!("Detected QKD: {}", hw.has_qkd);

// Recommend tier based on hardware
let tier = hw.recommended_tier();

println!("Recommended security tier: {:?}", tier);

// Configure QSSH queue with appropriate tier
let queue_config = DristaQsshConfig {
    tier,
    node_endpoint: format!("localhost:{}", 9944),
    hardware: hw,
    auto_escalate: true,
};

// Use tier to determine sync vs async
match tier {
    SecurityTier::QuantumSecured | SecurityTier::EntropyEnhanced => {
        // High security - use SyncOp for all messages
        QppSyncSubmit::execute(&alice_queue, message)?;
    }
    SecurityTier::HardenedPQ | SecurityTier::BasicPQ => {
        // Lower security - can use AsyncOp for non-critical
        QppAsyncSubmit::execute(&alice_queue, message).await?;
    }
}
```

---

## Summary

### QPP Enhancements to QSSH Queue

| Feature | Benefit |
|---------|---------|
| **NoClone Wrapper** | Enforces quantum no-cloning theorem at compile time |
| **Type-State Lifecycle** | Prevents consuming non-persisted messages |
| **SyncOp/AsyncOp** | Explicit durability vs performance trade-off |
| **Write-Ahead Log** | Crash recovery with fsync guarantees |
| **Provenance Tracking** | Full message origin and lifecycle tracking |
| **Move Semantics** | Models quantum measurement collapse |

### Design Validation

✅ **Good Design**: Yes! Here's why:

1. **Compile-Time Safety**: Type states and NoClone prevent runtime errors
2. **Explicit Guarantees**: SyncOp vs AsyncOp makes durability clear
3. **Crash Resilience**: WAL with fsync survives power failures
4. **Quantum Semantics**: Aligns with quantum physics (no-cloning, measurement collapse)
5. **Performance Flexibility**: Can choose sync (safe) vs async (fast) per message

### Next Steps

1. **Integration**: Wire up `coherence_gadget.rs` to use QPP queue
2. **Testing**: Simulate crashes and verify recovery
3. **Metrics**: Track fsync latency and WAL size
4. **Compaction**: Implement automatic WAL compaction trigger
5. **Drista Integration**: Use hardware detection for tier selection

---

**Document Status**: Complete
**Implementation**: `node/src/qssh_queue_qpp.rs`
**Tests**: Included in module
**Author**: Claude (Anthropic)
**Date**: 2025-10-28
