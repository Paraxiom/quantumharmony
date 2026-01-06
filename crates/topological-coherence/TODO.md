# Topological Coherence - Implementation TODO

**Status**: Local development (not committed to main repo)

**Paper**: [Topological Constraints for Coherent Language Models](https://github.com/Paraxiom/topological-coherence)

---

## Phase 1: Core Topology - COMPLETE

- [x] `Tonnetz<N>` struct with const generic grid size
- [x] Toroidal distance calculation (L1 with wraparound)
- [x] Linear index ↔ 2D coordinate conversion
- [x] Spectral gap computation (λ₁ = 2 - 2cos(2π/N))
- [x] Decay rate for non-resonant modes
- [x] Property tests: symmetry, identity, triangle inequality
- [x] Max distance bounded test
- [x] Coordinate roundtrip test

## Phase 2: Mask Variants - COMPLETE

- [x] `MaskType` enum: HardCutoff, SoftExponential, Hybrid
- [x] Hard cutoff mask: `M(i,j) = 1 if d ≤ r, else 0`
- [x] Soft exponential: `M(i,j) = exp(-α * d)`
- [x] Hybrid mask (default): `1 if d ≤ r, else exp(-α*(d-r))`
- [x] `ToroidalMask` with configurable type
- [x] `sinkhorn_knopp()` for doubly-stochastic projection
- [x] `is_doubly_stochastic()` verification
- [x] Tests for all mask variants
- [x] Sinkhorn-Knopp convergence test

## Phase 3: Substrate Integration - COMPLETE

- [x] SCALE codec support (`parity-scale-codec`, `scale-info`)
- [x] `ToroidalPosition` - storage-optimized position type
- [x] `CoherenceConfig` - on-chain configuration storage
- [x] `CoherenceResult` - validation result type
- [x] `substrate` feature flag for optional dependencies
- [x] Tests for all integration types
- [ ] Add to workspace `Cargo.toml` (when ready to commit)
- [ ] Off-chain worker trait implementation (future)
- [ ] Benchmarks for on-chain verification cost (future)

## Phase 4: Advanced Features - PENDING

- [ ] Learned projection: `φ_θ(e) = (σ(W₁e) mod 1, σ(W₂e) mod 1)`
- [ ] Adjacency loss: `L_topo = E[d_T(φ(a), φ(b))] - λ·E[d_T(φ(a), φ(c))]`
- [ ] Multi-scale Tonnetz (6x6, 12x12, 24x24)
- [ ] Higher-dimensional tori (T^3, T^4)
- [ ] Sparse mask representation (CSR format)

## Phase 5: Pallet Development - PENDING

- [ ] `pallet-topological-coherence`
- [ ] Store topological embeddings on-chain
- [ ] Verify coherence bounds in extrinsics
- [ ] Oracle integration for off-chain ML validation
- [ ] Governance for parameter updates (radius, alpha)

---

## Test Summary

```
27 tests passed:
- 4 basic distance tests
- 5 property tests (metric space axioms)
- 2 spectral gap tests
- 5 mask type tests
- 2 Sinkhorn-Knopp tests
- 2 drift meter tests
- 1 coordinate conversion test
- 6 Substrate integration type tests
```

---

## Feature Flags

| Feature | Dependencies | Use Case |
|---------|--------------|----------|
| `std` (default) | - | Standard library support |
| `substrate` | parity-scale-codec, scale-info | Substrate/Polkadot integration |

---

## API Summary

```rust
// Core topology
let dist = Tonnetz::<12>::distance((0,0), (5,7));
let gap = Tonnetz::<12>::spectral_gap();

// Mask generation
let mask = ToroidalMask::new(64, 2.0, 1.0);
let m = mask.generate();
let ds = mask.generate_doubly_stochastic(50);

// Substrate types (with `substrate` feature)
let pos = ToroidalPosition::new(5, 7);
let config = CoherenceConfig::default();
let result = CoherenceResult::from_meter(&meter, 0.1);
```

---

## References

- Cormier (2026): Topological Constraints for Coherent Language Models
- ERLHS: DOI 10.5281/zenodo.17928909
- Karmonic Mesh: DOI 10.5281/zenodo.17928991
- mHC (DeepSeek): arXiv:2512.24880
