# PQ-MonadBFT + Karmonic Hybrid Consensus

## Overview

Hybrid architecture combining:
- **MonadBFT's O(n)** linear message complexity
- **Karmonic's** quantum coherence validation
- **Toroidal mesh** for parallel execution

Target: O(n) consensus with post-quantum security and QBER validation.

## The Problem

| Approach | Complexity | Quantum Safe | Coherence |
|----------|------------|--------------|-----------|
| MonadBFT | O(n) | No | No |
| Karmonic | O(N log N) | Yes | Yes |
| **Hybrid** | **O(n)** | **Yes** | **Yes** |

## Key Insight

**Separate concerns:**
- Consensus = O(n) linear leader-based (MonadBFT style)
- Execution = Toroidal mesh parallel (Karmonic style)
- Cryptography = SPHINCS+ for txs, Falcon for votes

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                     NETWORK LAYER                               │
│                                                                 │
│   Hypercube topology for validator P2P                          │
│   - N validators = log₂(N) links per validator                  │
│   - Diameter = log₂(N) hops                                     │
│   - QKD channels for QBER monitoring                            │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                 PQ-MONADBFT CONSENSUS (O(n))                    │
│                                                                 │
│   Phase 1: PROPOSE                                              │
│   ┌─────────────────────────────────────────────────────────┐   │
│   │ Leader (QRNG-selected) proposes block B                 │   │
│   │ - Includes tx ordering (deferred execution)             │   │
│   │ - Broadcasts to all validators: O(n) messages           │   │
│   └─────────────────────────────────────────────────────────┘   │
│                              │                                  │
│                              ▼                                  │
│   Phase 2: VOTE (Linear Aggregation)                            │
│   ┌─────────────────────────────────────────────────────────┐   │
│   │ Each validator:                                         │   │
│   │ 1. Validates block header                               │   │
│   │ 2. Measures QBER on QKD channel                         │   │
│   │ 3. Creates CoherenceVote:                               │   │
│   │    - block_hash                                         │   │
│   │    - qber_measurement                                   │   │
│   │    - falcon_signature (2KB, not SPHINCS+ 49KB)          │   │
│   │ 4. Sends vote to LEADER ONLY: 1 message                 │   │
│   │                                                         │   │
│   │ Total: n validators × 1 message = O(n)                  │   │
│   └─────────────────────────────────────────────────────────┘   │
│                              │                                  │
│                              ▼                                  │
│   Phase 3: AGGREGATE + CERTIFY                                  │
│   ┌─────────────────────────────────────────────────────────┐   │
│   │ Leader:                                                 │   │
│   │ 1. Collects votes until 2/3+ threshold                  │   │
│   │ 2. Aggregates QBER: avg_qber = Σ(qber_i) / n            │   │
│   │ 3. If avg_qber > THRESHOLD: reject block                │   │
│   │ 4. Creates FinalityCertificate:                         │   │
│   │    - block_hash                                         │   │
│   │    - aggregated_qber                                    │   │
│   │    - vote_bitmap (which validators voted)               │   │
│   │    - merkle_root(all_signatures)                        │   │
│   │ 5. Broadcasts certificate: O(n) messages                │   │
│   │                                                         │   │
│   │ Total: 1 broadcast × n recipients = O(n)                │   │
│   └─────────────────────────────────────────────────────────┘   │
│                                                                 │
│   TOTAL CONSENSUS MESSAGES: O(n) + O(n) + O(n) = O(n)           │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│              TOROIDAL EXECUTION LAYER (Parallel)                │
│                                                                 │
│   After consensus on tx ORDER, execute in parallel:             │
│                                                                 │
│   ┌───┬───┬───┬───┬───┬───┬───┬───┐                             │
│   │ 0 │ 1 │ 2 │ 3 │ 4 │ 5 │ 6 │ 7 │  ← X axis (8 segments)      │
│   ├───┼───┼───┼───┼───┼───┼───┼───┤                             │
│   │ 8 │ 9 │...│   │   │   │   │15 │  ← Y axis (8 segments)      │
│   ├───┼───┼───┼───┼───┼───┼───┼───┤                             │
│   │...│   │   │   │   │   │   │...│  ← Z axis (8 segments)      │
│   └───┴───┴───┴───┴───┴───┴───┴───┘                             │
│            8 × 8 × 8 = 512 segments                             │
│                                                                 │
│   Execution Flow:                                               │
│   1. Route txs to segments by sender address hash               │
│   2. Execute optimistically in parallel                         │
│   3. Detect conflicts via read/write sets                       │
│   4. Re-execute conflicts deterministically                     │
│   5. Commit state root                                          │
│                                                                 │
│   Spectral Properties:                                          │
│   - λ₁ = 2 - 2cos(2π/8) ≈ 0.586 (constant gap)                  │
│   - Mixing time = O(log N) for coherence propagation            │
│   - Bounded drift via toroidal wraparound                       │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                   CRYPTOGRAPHIC LAYER                           │
│                                                                 │
│   Transaction Signatures: SPHINCS+-SHAKE-256f                   │
│   - Size: 49,856 bytes                                          │
│   - Security: 256-bit post-quantum                              │
│   - Used for: User transactions (verified in parallel)          │
│                                                                 │
│   Consensus Signatures: Falcon-1024                             │
│   - Size: 1,280 bytes (39x smaller than SPHINCS+)               │
│   - Security: 256-bit post-quantum                              │
│   - Used for: Validator votes (O(n) bandwidth savings)          │
│                                                                 │
│   QBER Monitoring: QKD channels                                 │
│   - Continuous channel integrity verification                   │
│   - Included in consensus votes                                 │
│   - Aggregated for network health                               │
│                                                                 │
│   Entropy: QRNG                                                 │
│   - Leader election (replaces VRF)                              │
│   - Tie-breaking                                                │
│   - Randomness beacon                                           │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

## Message Complexity Analysis

### Current Karmonic: O(N log N)

```
Round 1: Gossip vote to neighbors     = O(N) messages
Round 2: Neighbors relay              = O(N) messages
...
Round log(N): Final propagation       = O(N) messages
─────────────────────────────────────────────────────
Total: O(N) × O(log N) rounds         = O(N log N)
```

### Hybrid PQ-MonadBFT: O(N)

```
Phase 1: Leader broadcasts block      = N messages
Phase 2: Validators vote to leader    = N messages
Phase 3: Leader broadcasts cert       = N messages
─────────────────────────────────────────────────────
Total: 3N                             = O(N)
```

### Improvement Factor

For N = 100 validators:
- Karmonic: 100 × log₂(100) ≈ 100 × 7 = 700 messages
- Hybrid: 3 × 100 = 300 messages
- **Improvement: 2.3x fewer messages**

For N = 1000 validators:
- Karmonic: 1000 × log₂(1000) ≈ 1000 × 10 = 10,000 messages
- Hybrid: 3 × 1000 = 3,000 messages
- **Improvement: 3.3x fewer messages**

## QBER Integration

### Vote Structure

```rust
struct CoherenceVote {
    /// Block being voted on
    block_hash: H256,

    /// Validator's QBER measurement (basis points, 0-10000)
    /// 100 = 1.00% error rate
    qber_measurement: u16,

    /// Timestamp of QBER measurement
    qber_timestamp: u64,

    /// QKD channel ID measured
    qkd_channel_id: u32,

    /// Falcon-1024 signature (1,280 bytes)
    signature: [u8; 1280],
}
```

### Aggregation

```rust
struct FinalityCertificate {
    /// Block finalized
    block_hash: H256,

    /// Aggregated QBER (weighted average)
    aggregated_qber: u16,

    /// Number of validators with QBER < threshold
    healthy_channels: u32,

    /// Bitmap of validators who voted (compressed)
    vote_bitmap: BitVec,

    /// Merkle root of all signatures (for verification)
    signature_merkle_root: H256,

    /// Leader's Falcon signature on certificate
    leader_signature: [u8; 1280],
}
```

### Rejection Criteria

```rust
fn should_reject_block(cert: &FinalityCertificate) -> bool {
    // Reject if average QBER > 11% (theoretical QKD limit)
    if cert.aggregated_qber > 1100 {
        return true;
    }

    // Reject if < 50% of channels healthy
    let total_validators = cert.vote_bitmap.count_ones();
    if cert.healthy_channels < total_validators / 2 {
        return true;
    }

    false
}
```

## Pipelining (MonadBFT Style)

```
Block N:    [PROPOSE]──[VOTE]──[CERTIFY]
Block N+1:         [PROPOSE]──[VOTE]──[CERTIFY]
Block N+2:                [PROPOSE]──[VOTE]──[CERTIFY]

Time ────────────────────────────────────────────────────►

Latency per block: 3 phases
Throughput: 1 block per phase (3x improvement)
```

### Deferred Execution

```
Consensus Phase:     Agree on tx ORDER only (fast)
Execution Phase:     Execute txs in parallel AFTER consensus
State Commitment:    Merkle root committed in NEXT block

Benefits:
- Consensus not blocked by slow SPHINCS+ verification
- Parallel execution across 512 toroidal segments
- State disputes resolved by fraud proofs
```

## Tail-Fork Resistance

MonadBFT's tail-fork protection adapted for PQ:

```rust
struct BlockProposal {
    /// Previous block hash
    parent_hash: H256,

    /// Previous block's finality certificate (REQUIRED)
    parent_certificate: FinalityCertificate,

    /// New transactions
    transactions: Vec<Transaction>,

    /// Leader's Falcon signature
    signature: [u8; 1280],
}

fn validate_proposal(proposal: &BlockProposal) -> bool {
    // TAIL-FORK PROTECTION: Must include parent's certificate
    // This prevents leader from forking away predecessor's block
    verify_certificate(&proposal.parent_certificate)
}
```

## Implementation Status

### Phase 1: Linear Voting ✅ COMPLETE (2026-01-24)
- [x] `send_vote_linear()` - Validators send votes to leader only
- [x] `handle_vote_from_validator()` - Leader aggregates incoming votes
- [x] `VoteToLeader` gossip message type
- [x] Environment toggle `USE_LINEAR_VOTING` (default: true)

### Phase 2: Certificate Structure ✅ COMPLETE (2026-01-24)
- [x] `broadcast_finality_certificate()` - Leader broadcasts to all validators
- [x] `FinalityCertificateBroadcast` message with QBER aggregation
- [x] `check_leader_supermajority()` - Leader threshold check with QBER
- [x] Certificate includes: aggregated_qber, healthy_channels, validator_count

### Phase 3: Pipelining ✅ COMPLETE (2026-01-24)
- [x] `PipelinePhase` enum - Tracks block state (Propose → Vote → Certify → ConsensusComplete → Executed)
- [x] `DeferredBlock` struct - Queues blocks for deferred execution
- [x] `validate_tail_fork_protection()` - Verifies parent certificate before accepting proposal
- [x] `queue_for_deferred_execution()` - Queues certified blocks for parallel execution
- [x] `process_deferred_executions()` - Processes execution queue after consensus
- [x] Pipeline phase tracking integrated into `process_block()` flow
- [x] Certificate caching for tail-fork protection
- [x] Periodic pipeline cleanup (every 10 blocks)

### Phase 4: QRNG Leader Election ✅ COMPLETE (2026-01-24)
- [x] `get_qrng_entropy_for_election()` - Tries QRNG first, falls back to VRF
- [x] `reconstruct_qrng_entropy()` - Shamir reconstruction from K shares
- [x] Integration with `round_coordinator.rs` share pool
- [x] Automatic fallback when QRNG unavailable

### Phase 5: Testing
- [ ] Benchmark message complexity
- [ ] Test with 10, 50, 100 validators
- [ ] Verify QBER aggregation accuracy

## Comparison Summary

| Feature | MonadBFT | Karmonic (before) | Karmonic+Hybrid (now) |
|---------|----------|-------------------|----------------------|
| Message Complexity | O(n) | O(N log N) | **O(n)** |
| Post-Quantum Sigs | No | SPHINCS+ | **Falcon + SPHINCS+** |
| QBER Validation | No | Yes | **Yes** |
| Parallel Execution | Optimistic | Toroidal | **Toroidal** |
| Deferred Execution | Yes | No | **Yes** |
| Pipelining | Yes | No | **Yes** |
| Tail-Fork Resistant | Yes | No | **Yes** |
| Coherence Scoring | No | Yes | **Yes** |
| QRNG Arbitrage | No | Yes | **Yes** |

## Key Achievement

**Karmonic Mesh now achieves O(n) message complexity** while retaining:
- Post-quantum signatures (SPHINCS+ for transactions, Falcon for votes)
- QBER-based coherence validation
- Toroidal parallel execution (512 segments)
- Spectral consensus properties (λ₁ = constant gap)

## References

- MonadBFT: https://docs.monad.xyz/monad-arch/consensus/monad-bft
- Karmonic Mesh: DOI 10.5281/zenodo.17928991
- SPHINCS+: NIST PQC Standard
- Falcon: NIST PQC Standard
- QKD QBER: https://en.wikipedia.org/wiki/Quantum_bit_error_rate
