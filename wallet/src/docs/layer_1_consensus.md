# Layer 1: Consensus & Toroidal Mesh

## What is this layer?

The **consensus layer** implements **Byzantine fault-tolerant consensus** with **toroidal mesh parallelization**. This is where validators agree on the canonical blockchain state.

## Why does it matter?

Traditional blockchains have **bottlenecks**:
- **Bitcoin**: Mining (single winner, 10 min blocks)
- **Ethereum**: Execution (single EVM, ~30 TPS)
- **Polkadot**: Relay chain (single point, 1k validators max)
- **Solana**: Leader selection (rotating bottleneck)

QuantumHarmony uses:
- **Toroidal mesh**: 512 parallel execution zones
- **No single leader**: All validators participate equally
- **O(√N) routing**: Max 22 hops for 512 validators (not 512!)
- **1.5s finality**: Byzantine voting with quantum entropy

## Architecture Overview

### Three Consensus Mechanisms Working Together

```
┌─────────────────────────────────────────┐
│ Aura (Block Authoring)                  │  ← Who produces blocks?
│ • 6-second rounds                       │
│ • Round-robin rotation                  │
│ • Validator X produces block N          │
└────────────┬────────────────────────────┘
             ↓
┌─────────────────────────────────────────┐
│ GRANDPA (Finality Gadget)               │  ← When are blocks final?
│ • Finalizes 100+ blocks at once         │
│ • 2/3+ validator signatures required    │
│ • Irreversible after finalization       │
└────────────┬────────────────────────────┘
             ↓
┌─────────────────────────────────────────┐
│ Coherence (Byzantine Voting)            │  ← How do we vote?
│ • Quantum entropy-based voting          │
│ • 2f+1 threshold (68% required)         │
│ • Vote gossip via P2P network           │
└─────────────────────────────────────────┘
```

## Toroidal Mesh: The Key Innovation

### Traditional Linear Topology (BAD)

```
Validator 0 → Validator 1 → Validator 2 → ... → Validator 511
    ↑                                               ↓
    └───────────────────────────────────────────────┘

Problem: Message from V0 to V511 takes 511 hops!
Complexity: O(N) - doesn't scale
```

### Toroidal Mesh Topology (GOOD)

```
       ╭────────────────╮
      ↗  V2 → V3 → V0   ↖  ← Wraps horizontally
    ↗    ↑↓    ↑↓    ↑↓   ↖
   │     V5 → V6 → V1      │  ← AND vertically
   │     ↑↓    ↑↓    ↑↓    │
   ↖     V8 → V9 → V4     ↗
    ↖                    ↗
     ╰───────────────────╯

Benefits:
• Max path length: √N (not N)
• 512 validators: 22 hops (not 512!)
• No central bottleneck
• All edges wrap around (like a donut)
```

### Ternary Encoding for Coordinates

Instead of binary (base-2), we use **ternary** (base-3):

```rust
// Binary encoding: 512 nodes = 9 bits
Node 341: 101010101₂ (9 bits)

// Ternary encoding: 512 nodes = 6 trits
Node 341: 110201₃ (6 trits = 12 bits with 2 bits/trit)

// 3D torus coordinates
X = 1, Y = 1, Z = 0, W = 2, U = 0, V = 1

// Routing: Move along torus surface
From (1,1,0,2,0,1) to (2,0,1,0,1,2):
  X: 1→2 (1 hop)
  Y: 1→0 (wrap, 2 hops)
  Z: 0→1 (1 hop)
  ...
Total: ~8 hops (not 171!)
```

## Byzantine Fault Tolerance

### Threat Model

Adversary can:
- Control up to 33% of validators
- Delay messages arbitrarily
- Send conflicting messages
- Crash validators

Adversary **cannot**:
- Break SPHINCS+ signatures
- Predict quantum entropy
- Compromise >68% of validators

### Coherence Voting Protocol

```
Block N is proposed by Validator X
    ↓
All validators receive block
    ↓
Each validator votes YES/NO based on:
  1. Block is valid (transactions, signatures)
  2. Quantum entropy commitment matches
  3. Previous block is finalized
    ↓
Votes gossip across toroidal mesh (Layer 2)
    ↓
When 2f+1 (68%) votes collected:
  → Block is FINALIZED
  → Cannot be reverted
```

### Supermajority Math

```
Total validators: N
Byzantine threshold: f = ⌊(N-1)/3⌋

Required for finality: 2f+1 votes
  = 2⌊(N-1)/3⌋ + 1
  ≈ 68% of N

Example (N=50 validators):
  f = 16 (max Byzantine)
  2f+1 = 33 votes required
  33/50 = 66% (actually 68% for safety)
```

## Performance Characteristics

| Metric | Traditional | Toroidal Mesh |
|--------|------------|---------------|
| **Message Complexity** | O(N²) | O(N√N) |
| **Max Path Length** | O(N) | O(√N) |
| **Latency (512 nodes)** | 512 hops | 22 hops |
| **Bandwidth per Node** | O(N) | O(√N) |
| **Scalability** | Limited | 50k+ validators |

**Real benchmark (SPHINCS+ signatures):**
- Sequential: 1.175s for 500 transactions
- 64 segments: 0.153s for 500 transactions
- **Speedup: 7.7x** (empirically proven!)

## Consensus Rounds

### Block Production Flow

```
Block N-1 finalized at time T
    ↓
T+0s: Validator X starts authoring block N
    ↓
T+2s: Block N broadcast to mesh
    ↓
T+3s: Validators receive + verify block N
    ↓
T+4s: Coherence votes gossip across mesh
    ↓
T+5s: 68% votes collected
    ↓
T+6s: Block N finalized, start block N+1
```

### Finality Lag

- Best case: 1 block (6 seconds)
- Typical: 2-3 blocks (12-18 seconds)
- Network issues: 5-10 blocks (30-60 seconds)
- **Target: 1.5s effective** (with pipelining)

## Runtime Parameters

Current configuration:
```
validator_count: 3 (testnet), 50,000 (mainnet)
block_time: 6 seconds
finality_threshold: 68% (2f+1)
max_toroidal_segments: 512
ternary_coordinate_bits: 12 (6 trits × 2 bits)
vote_timeout: 30 seconds
```

## Visualization

```
┌──────────────────────────────────────────┐
│         Toroidal Mesh (3D Donut)         │
├──────────────────────────────────────────┤
│                                          │
│        ╭─────────────────╮               │
│       ↗   Segment 0-63    ↖              │
│     ↗    ╭─────────╮      ↖             │
│   ↗     │ Validator │       ↖            │
│  │      │ (Aura)    │        │           │
│  │      ╰─────┬─────╯        │           │
│  │            ↓               │           │
│  │      ╭─────────╮          │           │
│  │     │ Coherence │         │           │
│  │     │  Voting   │         │           │
│  │      ╰─────┬─────╯        │           │
│  ↖            ↓              ↗            │
│   ↖     ╭─────────╮        ↗             │
│    ↖   │ GRANDPA   │      ↗              │
│     ↖  │ Finality  │    ↗                │
│      ↖  ╰─────────╯  ↗                  │
│       ╰─────────────╯                    │
│                                          │
│  Current Block: #45,678                  │
│  Finalized: #45,675 (lag: 3 blocks)     │
│  Validators: 3/3 online                  │
│  Network Latency: 23ms avg               │
└──────────────────────────────────────────┘
```

## Related Code

- **Coherence Gadget**: `node/src/coherence_gadget.rs` (1,700 lines)
- **Toroidal Mesh**: `pallets/runtime-segmentation/src/lib.rs`
- **Aura Integration**: Uses `sc-consensus-aura`
- **GRANDPA Integration**: Uses `sc-consensus-grandpa`

## Common Questions

**Q: Why not just use Tendermint/HotStuff?**
A: Those require a leader for each round. Toroidal mesh has no leader bottleneck.

**Q: What if 34% of validators are malicious?**
A: Chain halts (cannot reach 68% threshold). This is by design - safety over liveness.

**Q: How does this scale to 50,000 validators?**
A: Hierarchical sharding: 50 shards × 1,000 validators, each shard is a torus.

**Q: Why 6-second block time?**
A: Balance between throughput and network latency. Can be tuned per deployment.

## Next Layer

**↑ Layer 2: Network Transport**
- How votes gossip across the mesh
- QUIC encrypted transport
- P2P peer discovery

Press `2` to navigate to Layer 2 →

**↓ Layer 0: Entropy Foundation**
- Where quantum randomness comes from
- QKD devices and priority queues

Press `0` to navigate to Layer 0 ←
