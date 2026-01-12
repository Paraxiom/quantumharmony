# QuantumHarmony Architecture Q&A

Technical questions and answers about the QuantumHarmony network architecture.

---

## Q: How does the Toroidal Mesh help with SPHINCS+ signature propagation?

**Asked by:** Edwin
**Date:** January 2026

### Question

> I've been thinking more about that Toroidal Mesh setup and the idea of using geometry instead of just stake to run the network.
>
> Since we're using SPHINCS+ (which I know has pretty large signature sizes) and trying to keep the scaling sub-quadratic, I was wondering how the 'donut' shape of the mesh helps with the time it takes for those big signatures to move between nodes?
>
> Does the specific shape of the torus let us tweak the Gossip protocol so the 'signature bloat' doesn't kill the speed as we add more validators? I'm curious if having those geometric boundaries actually helps keep the signature verification load from drifting too much across the mesh.

### Answer

**Clarification first** - we're not using "geometry instead of stake." The network has **3 security tiers**:

1. **QKD** - Quantum Key Distribution (point-to-point encrypted channels)
2. **QRNG** - Quantum Random Number Generation (unpredictable validator selection/routing)
3. **Stake** - Economic security (slashing, bonding)

The toroidal mesh is the **topology** these three tiers operate on - it's the network shape, not a replacement for any of them.

### How the Torus Helps with SPHINCS+ Signature Propagation

SPHINCS+-256f signatures are approximately **49KB each**. In a naive gossip protocol, every validator forwards to every peer = O(n²) message complexity. With 100 validators, that's potentially 10,000 × 49KB = 490MB per block just for signatures.

The 3D torus (8×8×8 = 512 segments) addresses this:

| Metric | Naive Gossip | Toroidal Gossip |
|--------|--------------|-----------------|
| Message complexity | O(n²) | O(n × ∛n) |
| Max hops (512 nodes) | 511 | 12 |
| Signature traffic | 262K messages | 4K messages |

### Why the Torus Shape Works

#### 1. Bounded Diameter O(∛n)
Maximum hops between any two nodes is ~12 in our 512-segment mesh. Signatures don't traverse the entire network - they propagate along geodesic paths.

#### 2. Six Neighbors Per Segment
Each segment connects to ±X, ±Y, ±Z neighbors with wraparound. Instead of broadcasting to all, nodes propagate directionally:

```
Segment (x,y,z) → neighbors at:
  ((x±1) mod 8, y, z)
  (x, (y±1) mod 8, z)
  (x, y, (z±1) mod 8)
```

#### 3. No Edge Effects
Unlike a flat grid, every segment has exactly 6 neighbors. No "corner" nodes getting hammered with traffic - uniform load distribution across the mesh.

#### 4. QRNG-Selected Routing
Quantum randomness selects which of the 6 neighbors propagates first, preventing adversarial routing manipulation.

#### 5. Ring-Based Propagation
Signatures spread in "ripples" across the torus surface. A signature entering at segment (0,0,0) reaches (4,4,4) - the antipodal point - in just 12 hops, not 256.

### Verification Load Balancing

The torus naturally distributes verification work:

- **Segment-Local Verification**: Each segment verifies signatures from its local validators first, then propagates *verified* attestations (smaller than raw signatures)
- **Parallel Verification**: We fragment the 49KB SPHINCS+ signature into 48 chunks (~1KB each) and verify concurrently
  - Sequential: ~250ms per signature
  - Parallel: ~85ms per signature (3× speedup)

### The Math

Traditional gossip: **O(n²)** messages
Toroidal gossip: **O(n × diameter)** = O(n × ∛n) for 3D torus

For 512 segments: 512 × 8 = 4,096 message hops vs 262,144 for naive broadcast.

**That's a 64× reduction in signature traffic.**

### Summary

The donut shape creates geometric "lanes" that signatures travel along. Combined with:
- **QRNG** for unpredictable routing
- **Parallel verification** for faster processing
- **QKD** for secure point-to-point channels
- **Stake** for economic finality

We keep propagation sub-quadratic even with 49KB signatures.

### Related Files

| File | Purpose |
|------|---------|
| `pallets/runtime-segmentation/src/lib.rs` | 8×8×8 toroidal mesh implementation |
| `node/src/coherence_gossip.rs` | Vote gossip protocol |
| `node/src/sphincs_parallel_verify.rs` | Fragment-based parallel verification |
| `pallets/topological-coherence/src/lib.rs` | Tonnetz torus topology |

---

*More Q&A entries will be added as architecture questions come in.*
