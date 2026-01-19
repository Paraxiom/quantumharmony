# QuantumHarmony FAQ

Frequently asked questions about QuantumHarmony's architecture, cryptography, and design decisions.

---

## Torus Topology & SPHINCS+ Signatures

### Q: How does the torus (donut) mesh topology help with SPHINCS+ signature propagation and sub-quadratic scaling?

**Short Answer:** The torus bounds fanout to 4 neighbors regardless of network size, reduces propagation diameter to O(√n), and enables directional flooding that prevents signature "backwash" - all critical for handling SPHINCS+ signatures that are ~250x larger than Ed25519.

**Detailed Explanation:**

#### The SPHINCS+ Problem

SPHINCS+ signatures are **~8-17KB** (vs 64 bytes for Ed25519). In naive gossip:
- Each node forwards to `log(n)` or more peers
- Total bandwidth per signature: `O(n × log(n) × 17KB)`
- This becomes **quadratic** in practice as n grows

#### How the Torus Helps

##### 1. Bounded Degree = Bounded Fanout

In a 2D torus, each node has exactly 4 neighbors:

```
        [North]
           |
[West] -- Node -- [East]
           |
        [South]
```

Fanout is CONSTANT regardless of network size. 100 validators or 10,000 - still only 4 peers.

##### 2. Sub-linear Propagation Diameter

For `n` validators arranged in a `√n × √n` torus:
- **Max hops** = `√n` (diameter)
- **Propagation time** = `O(√n)` not `O(n)` or `O(log n × n)`

With 10,000 validators: ~100 hops max vs potentially thousands in random gossip.

##### 3. Directional Flooding (No Backwash)

```rust
// Signature enters from North
// Forward to South, East, West - NOT back North
fn propagate(&self, sig: &Signature, from: Direction) {
    for neighbor in self.neighbors() {
        if neighbor.direction != from.opposite() {
            neighbor.send(sig);
        }
    }
}
```

This cuts redundant transmissions by ~25%.

##### 4. Verification Load Distribution

The geometric boundaries create natural "verification wavefronts":

```
Time 0:    [V][ ][ ][ ][ ]     V = verified
Time 1:    [V][V][ ][ ][ ]
Time 2:    [V][V][V][ ][ ]     Wave spreads evenly
Time 3:    [V][V][V][V][ ]     No node overwhelmed
Time 4:    [V][V][V][V][V]
```

Each node verifies at most 4 signatures per round (one from each neighbor), not a flood of `n` signatures.

##### 5. Locality-Aware Chunking

For 17KB SPHINCS+ signatures, we can chunk:

```
[Header: 256B] → Verify structure, allocate buffer
[Chunk 1: 4KB] → Forward while verifying
[Chunk 2: 4KB] → Pipeline continues
[Chunk 3: 4KB] →
[Chunk 4: 4KB] →
[Final: 1KB]   → Complete verification
```

The predictable torus paths allow **pipelined verification** - node verifies chunk 1 while receiving chunk 2.

#### Performance Comparison

| Metric | Random Gossip | Torus Gossip |
|--------|---------------|--------------|
| Fanout | O(log n) | **4 (constant)** |
| Diameter | O(log n) | **O(√n)** |
| Messages/sig | O(n × log n) | **O(n)** |
| Bandwidth/node | O(log n × sig_size) | **O(4 × sig_size)** |

For 1,000 validators with 17KB signatures:
- Random: ~170MB total network traffic per signature
- Torus: ~68MB total network traffic per signature

#### Implementation

This is implemented in `entropy_gossip.rs`:

```rust
pub struct TorusGossip {
    position: (u16, u16),      // Our (x,y) coordinate
    neighbors: [PeerId; 4],    // N, S, E, W
    seen_bloom: BloomFilter,   // Deduplication
}
```

The gossip protocol uses the torus coordinates to:
1. Calculate optimal routing paths
2. Prevent signature backwash
3. Distribute verification load evenly
4. Enable predictable chunk pipelining

**Conclusion:** The donut shape directly enables sub-quadratic scaling with large post-quantum signatures. The geometric constraints become an advantage, not a limitation.

---

## More Questions?

Submit questions via GitHub Issues or contact the team.
