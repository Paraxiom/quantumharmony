# topological-coherence

Rust implementation of topological constraints for coherent inference.

Based on: [Topological Constraints for Coherent Language Models](https://github.com/Paraxiom/topological-coherence) (Cormier, 2026)

## Theory

Hallucination is a geometry problem: unconstrained latent dynamics permit arbitrary drift through latent space. Topological constraints (specifically toroidal manifolds with constant spectral gap) bound this drift.

**Key result**: Toroidal attention reduces semantic drift by 40% compared to baseline, and 96% compared to random sparse masks.

## Usage

```rust
use topological_coherence::{Tonnetz, ToroidalMask, MaskType};

// Core topology - 12x12 torus (musical Tonnetz)
let dist = Tonnetz::<12>::distance((0, 0), (5, 7));
let gap = Tonnetz::<12>::spectral_gap();

// Attention masks
let mask = ToroidalMask::new(64, 2.0, 1.0);           // Hybrid
let mask = ToroidalMask::hard_cutoff(64, 2.0, 12);   // Binary
let mask = ToroidalMask::soft_exponential(64, 1.0, 12); // Smooth

// Generate matrices
let m = mask.generate();                              // Vec<Vec<f32>>
let ds = mask.generate_doubly_stochastic(50);        // Sinkhorn-projected
```

## Features

- **`Tonnetz<N>`**: Toroidal topology with const generic grid size
- **`ToroidalMask`**: Three mask types (hard cutoff, soft exponential, hybrid)
- **`sinkhorn_knopp()`**: Doubly-stochastic projection (Birkhoff polytope)
- **`DriftMeter`**: Semantic drift measurement
- **`no_std` compatible**: Works in embedded/WASM contexts

### Substrate Integration

Enable the `substrate` feature for Polkadot/Substrate compatibility:

```toml
[dependencies]
topological-coherence = { version = "0.1", features = ["substrate"] }
```

Provides SCALE-encoded types for on-chain storage:
- `ToroidalPosition` - Storage-optimized position (2 bytes)
- `CoherenceConfig` - Configuration for validation
- `CoherenceResult` - Validation results

## Mask Types

| Type | Formula | Use Case |
|------|---------|----------|
| Hard Cutoff | `1 if d ≤ r, else 0` | Strict locality |
| Soft Exponential | `exp(-α * d)` | Smooth falloff |
| Hybrid | `1 if d ≤ r, else exp(-α*(d-r))` | Best of both |

## Spectral Gap

For a 2D torus T²_N:

```
λ₁ = 2 - 2cos(2π/N) = Θ(1) for fixed N
```

This constant spectral gap (independent of embedding dimension) is the key property that bounds drift.

## License

Apache-2.0

## References

- [Paper & Python Experiment](https://github.com/Paraxiom/topological-coherence)
- ERLHS: DOI 10.5281/zenodo.17928909
- Karmonic Mesh: DOI 10.5281/zenodo.17928991
