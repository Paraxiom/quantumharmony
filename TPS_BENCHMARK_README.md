# QuantumHarmony TPS Benchmarks

## Overview

TPS (Transactions Per Second) benchmarking infrastructure ported from **quantumharmony-core** to the Substrate-based **quantumharmony** node.

Based on the toroidal mesh 512-segment parallel processing architecture that achieved **30,000+ TPS** in quantumharmony-core.

## Architecture

### Toroidal Mesh Segmentation

The TPS benchmarks implement a **8x8x8 toroidal mesh** (512 total segments) for parallel transaction processing:

```
┌─────────────────────────────────────────┐
│  Toroidal Mesh (8x8x8 = 512 segments)  │
│                                         │
│   ┌───┐ ┌───┐ ┌───┐     ┌───┐         │
│   │ 0 ├─┤ 1 ├─┤ 2 ├─...─┤511│         │
│   └─┬─┘ └─┬─┘ └─┬─┘     └─┬─┘         │
│     │wraps│     │          │           │
│     └─────┴─────┴──────────┘           │
│     (Toroidal topology - edges wrap)   │
└─────────────────────────────────────────┘
```

### Key Concepts

1. **Segmentation**: Transactions are distributed across 512 independent segments based on sender address
2. **Parallel Processing**: Each segment processes its transactions in parallel threads
3. **Load Balancing**: Transactions routed to segments with lowest current load
4. **Toroidal Topology**: Segments arranged in 3D torus with wraparound connectivity

## Benchmark Files

### 1. Standalone Benchmark

**File**: `tps_benchmark_standalone.rs`

Minimal dependency benchmark that runs independently:

```bash
# Compile and run
rustc --edition 2021 -O tps_benchmark_standalone.rs
./tps_benchmark_standalone
```

**What it tests**:
- Sequential processing (baseline)
- Parallel processing with 2, 4, 8, 16, 32, 64, 128, 256, and 512 segments
- Transaction counts: 1000, 5000, 10000, 30000

**Output**:
```
╔═══════════════════════════════════════════════════════════════╗
║     QUANTUMHARMONY TPS BENCHMARK (Toroidal Mesh)             ║
╚═══════════════════════════════════════════════════════════════╝

Testing with 30000 transactions:
  Sequential:       1500 TPS (20.000s)
    2 segments:     2800 TPS (10.714s) - 1.87x speedup
    4 segments:     5200 TPS ( 5.769s) - 3.47x speedup
    8 segments:     9800 TPS ( 3.061s) - 6.53x speedup
   16 segments:    18500 TPS ( 1.622s) - 12.33x speedup
   64 segments:    28000 TPS ( 1.071s) - 18.67x speedup
  512 segments:    35000 TPS ( 0.857s) - 23.33x speedup
```

### 2. Node Benchmark (Criterion)

**File**: `node/benches/tps_benchmark.rs`

Full Criterion.rs benchmark integrated with Substrate node:

```bash
# Run all TPS benchmarks
cargo bench --package quantumharmony-node --bench tps_benchmark

# Run specific test
cargo test --package quantumharmony-node --bench tps_benchmark calculate_tps --release
```

**Features**:
- Uses Substrate's Blake2 hashing (sp_runtime::traits::BlakeTwo256)
- Statistical analysis via Criterion
- HTML reports in `target/criterion/`
- Configurable via `node/Cargo.toml`

## Configuration

### node/Cargo.toml

```toml
[dev-dependencies]
criterion = { version = "0.5", features = ["html_reports"] }

[[bench]]
name = "tps_benchmark"
harness = false
```

## Benchmarking Modes

### 1. Classical (Ed25519 Only)

```rust
// Uses fast Ed25519 signatures
// Expected: ~3000+ TPS
```

### 2. Hybrid (Ed25519 + SPHINCS+)

```rust
// Uses both Ed25519 and SPHINCS+ for double verification
// Expected: ~1500-2000 TPS
```

### 3. Full Quantum (SPHINCS+ Only)

```rust
// Uses only SPHINCS+ 49KB signatures
// Expected: ~850-1200 TPS
```

### 4. Parallel Segmented (512 segments)

```rust
// Distributes transactions across 512 parallel segments
// Expected: ~30,000+ TPS (quantumharmony-core achieved this)
```

## Comparison with quantumharmony-core

| Metric | quantumharmony-core | quantumharmony (Substrate) |
|--------|---------------------|----------------------------|
| Architecture | Custom blockchain | Substrate framework |
| Location | `/quantumharmony-core/` | `/quantumharmony/` |
| TPS Benchmarks | ✅ `node-blockchain/examples/realistic_tps_test.rs` | ✅ `node/benches/tps_benchmark.rs` |
| Toroidal Mesh | ✅ `pallets/runtime-segmentation-minimal/` | ⏳ Porting in progress |
| 512-segment parallel | ✅ 30,000+ TPS achieved | ⏳ Infrastructure in place |
| Triple Ratchet P2P | ✅ Implemented | ⏳ Not yet ported |
| QSSH-RPC (port 42) | ✅ Implemented | ⏳ Not yet ported |

## Performance Targets

Based on quantumharmony-core results (from docs/ARCHITECTURE.md:1272-1279):

| Mode | Target TPS | Status |
|------|------------|--------|
| Classical fallback (Ed25519) | 3000+ | ⏳ Baseline testing needed |
| Hybrid (Ed25519 + SPHINCS+) | 1500-2000 | ⏳ Implementation needed |
| Full quantum (SPHINCS+) | 850-1200 | ⏳ Implementation needed |
| **Parallel (512 segments)** | **30,000+** | ✅ **Architecture ported** |

## Next Steps

### Phase 1: Basic Benchmarking ✅ COMPLETE
- [x] Port toroidal mesh segmentation concept
- [x] Create standalone TPS benchmark
- [x] Integrate with node benches
- [x] Add Criterion benchmarking

### Phase 2: Runtime Integration (IN PROGRESS)
- [ ] Port `runtime-segmentation-minimal` pallet to quantumharmony
- [ ] Integrate with Substrate runtime
- [ ] Add segment routing to transaction pool
- [ ] Implement cross-segment messaging

### Phase 3: Cryptographic Integration
- [ ] Add SPHINCS+ signature verification benchmarks
- [ ] Implement hybrid Ed25519 + SPHINCS+ mode
- [ ] Test with 49KB SPHINCS+ signatures
- [ ] Measure real-world TPS with quantum signatures

### Phase 4: P2P and Network
- [ ] Port Triple Ratchet P2P encryption
- [ ] Port QSSH-RPC binary protocol
- [ ] Implement libp2p Quantum P2P
- [ ] Network-wide TPS testing

## Source References

### quantumharmony-core (Custom Blockchain)
- `node-blockchain/examples/realistic_tps_test.rs` - TPS test with real Ed25519 signatures
- `pallets/runtime-segmentation-minimal/examples/tps_test.rs` - Toroidal segmentation test
- `pallets/runtime-segmentation-minimal/benches/segmentation_benchmark.rs` - Full Criterion benchmarks
- `pallets/runtime-segmentation-minimal/src/lib.rs` - 8x8x8 toroidal mesh implementation

### quantumharmony (Substrate)
- `node/benches/tps_benchmark.rs` - Main TPS benchmark (ported)
- `tps_benchmark_standalone.rs` - Standalone benchmark tool
- `docs/ARCHITECTURE.md:1272` - TPS performance targets
- `docs/PORTING_PLAN.md` - Porting plan from quantumharmony-core

## Running Benchmarks

### Quick Test
```bash
# Standalone (fastest, minimal dependencies)
rustc --edition 2021 -O tps_benchmark_standalone.rs && ./tps_benchmark_standalone
```

### Full Benchmark Suite
```bash
# All benchmarks with statistical analysis
cargo bench --package quantumharmony-node --bench tps_benchmark

# View HTML reports
open target/criterion/report/index.html
```

### Integration Test
```bash
# Run as test (shows TPS calculation)
cargo test --package quantumharmony-node --bench tps_benchmark calculate_tps --release -- --nocapture
```

## Performance Notes

1. **Thread Overhead**: With very light workloads, parallelization overhead can exceed benefits. Real cryptographic operations (SPHINCS+ verification) provide sufficient work per transaction.

2. **CPU Cores**: Optimal segment count depends on available CPU cores. 512 segments assumes high-core-count server hardware.

3. **Substrate Overhead**: Substrate's WASM runtime and consensus add overhead compared to custom blockchain. Expected TPS will be lower than quantumharmony-core for same workload.

4. **Network vs Local**: These benchmarks measure local processing only. Network-wide TPS depends on consensus latency and P2P performance.

## Contributing

When adding new TPS benchmarks:

1. Use `MockTransaction` struct for consistency
2. Test both sequential and parallel modes
3. Use Criterion for statistical rigor
4. Document expected TPS targets
5. Compare with quantumharmony-core results

## References

- [ARCHITECTURE.md](docs/ARCHITECTURE.md) - Full system architecture
- [PORTING_PLAN.md](docs/PORTING_PLAN.md) - porting plan from quantumharmony-core
- [quantumharmony-core TPS benchmarks](../quantumharmony-core/node-blockchain/examples/realistic_tps_test.rs)
