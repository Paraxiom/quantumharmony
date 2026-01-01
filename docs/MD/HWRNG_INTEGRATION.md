# HWRNG Integration Architecture

## Overview

This document outlines the integration of Hardware Random Number Generator (HWRNG/QRNG) entropy into all cryptographic operations in QuantumHarmony, fulfilling the requirement that "all seeds and hashes must have the possibility to come from HWRNG".

## Architecture

### 1. Centralized Entropy Provider (`node/src/quantum_entropy.rs`)

The `QuantumEntropyProvider` module provides a unified interface for accessing quantum entropy from HWRNG devices with automatic fallback to deterministic entropy when quantum devices are unavailable.

**Key Features:**
- **Threshold QRNG Integration** - Uses K-of-M Shamir Secret Sharing from multiple QRNG devices
- **Automatic Fallback** - Falls back to Keccak-256 deterministic entropy when QRNG unavailable
- **Entropy Quality Tracking** - Monitors and reports entropy source quality
- **Three Operating Modes:**
  - `PreferQuantum` - Try quantum, fall back to deterministic
  - `RequireQuantum` - Fail if quantum unavailable (for production validators)
  - `AlwaysDeterministic` - Always use deterministic (for testing/reproducibility)

### 2. Integration Points

#### A. SPHINCS+ Key Generation

**Location:** `node/src/service.rs:181`

**Current:** Uses hardcoded seeds from `test_accounts.rs`

**Enhancement:**
```rust
// Example integration pattern (pseudocode)
let entropy_provider = QuantumEntropyProvider::new(
    pqtg_client,
    threshold_config,
    EntropyMode::PreferQuantum,
);

// Generate 48-byte seed from HWRNG
let (seed_bytes, quality) = entropy_provider.get_entropy_with_quality(48).await?;
let seed_hex = format!("0x{}", hex::encode(seed_bytes));

// Use quantum-generated seed for SPHINCS+ keypair
keystore.sphincs_generate_new(aura_keytype, Some(&seed_hex))?;

// Log entropy quality
if quality.is_quantum() {
    info!("✅ Generated SPHINCS+ key from quantum entropy (quality: {})", quality.quality_score());
} else {
    warn!("⚠️  Generated SPHINCS+ key from deterministic fallback");
}
```

**Impact:** All validator SPHINCS+ keys can now be generated from true quantum entropy, significantly enhancing security.

#### B. VRF Randomness

**Location:** `runtime/src/quantum_config.rs:20-26`

**Current:** Stub implementation returning `H256::zero()`

**Enhancement Strategy:**

Since the runtime cannot have async dependencies or direct access to node infrastructure, we use a hybrid approach:

1. **Runtime Host Function** - Add a custom host function that the runtime can call to request quantum entropy
2. **Node-Side Implementation** - The host function is implemented in the node, accessing `QuantumEntropyProvider`
3. **Runtime Randomness** - The `QuantumRandomness` trait implementation calls the host function

**Implementation:**

```rust
// In runtime/src/quantum_config.rs
pub struct QuantumRandomness;
impl frame_support::traits::Randomness<sp_core::H256, u32> for QuantumRandomness {
    fn random(subject: &[u8]) -> (sp_core::H256, u32) {
        // Call host function to get quantum entropy
        let entropy = sp_io::crypto::quantum_entropy(subject.len() as u32);

        // Convert to H256
        let mut hash = [0u8; 32];
        hash.copy_from_slice(&entropy[..32]);

        (sp_core::H256(hash), frame_system::Pallet::<Runtime>::block_number())
    }
}
```

```rust
// In node/src/service.rs - register host function
let extensions = sc_executor::ExecutorBuilder::default()
    .with_execution_method(sc_cli::ExecutionStrategy::Native)
    .with_heap_pages(Some(64))
    .with_max_runtime_instances(8)
    .with_runtime_cache_size(2)
    .with_offchain_heap_pages(Some(64))
    // Register quantum entropy host function
    .with_host_functions(vec![
        Box::new(quantum_entropy_host_functions::QuantumEntropyHostFunctions::new(
            entropy_provider.clone()
        ))
    ])
    .build();
```

**Impact:** All on-chain randomness (VRF, lottery, nonce generation) can now use quantum entropy.

#### C. Block Hash Generation

**Location:** `runtime/src/lib.rs` - Hashing trait

**Current:** Uses standard Keccak-256 (Blake2) hashing

**Enhancement Strategy:**

Block hashes must remain deterministic and verifiable across all nodes. However, we can inject quantum entropy into the **nonce** or **extra data** fields that feed into the hash:

```rust
// In block authoring (Aura consensus)
// Add quantum entropy to block extra data
let quantum_nonce = entropy_provider.get_entropy(32).await?;
block.header.digest.push(DigestItem::PreRuntime(
    AURA_ENGINE_ID,
    quantum_nonce.encode()
));
```

**Impact:** While the hash function remains deterministic, the input includes quantum entropy, making blocks unpredictable and enhancing security against pre-computation attacks.

#### D. Transaction Signatures

**Location:** `node/src/rpc/transaction_gateway.rs:124`

**Current:** Uses `SphincsPair::from_seed()` with fixed seeds

**Enhancement:**
```rust
// Generate ephemeral signing key from quantum entropy
let (seed_bytes, quality) = entropy_provider.get_entropy_with_quality(48).await?;
let signing_pair = SphincsPair::from_seed_slice(&seed_bytes)?;

info!("Generated transaction signing key from {} entropy",
      if quality.is_quantum() { "quantum" } else { "deterministic" });
```

**Impact:** RPC transaction signing can use quantum-generated ephemeral keys.

### 3. Configuration

**Environment Variables:**
```bash
# Enable quantum entropy mode
QUANTUM_ENTROPY_MODE=prefer  # or "require" or "deterministic"

# PQTG endpoints for QRNG devices
PQTG_DEVICE_1=https://qrng1.example.com
PQTG_DEVICE_2=https://qrng2.example.com
PQTG_DEVICE_3=https://qrng3.example.com

# Threshold configuration
QUANTUM_THRESHOLD_K=2  # Need 2 shares to reconstruct
QUANTUM_THRESHOLD_M=3  # Out of 3 total devices
```

**CLI Arguments:**
```bash
./quantumharmony-node \
  --validator \
  --quantum-entropy prefer \
  --pqtg-endpoint https://qrng1.example.com \
  --pqtg-endpoint https://qrng2.example.com \
  --quantum-threshold 2/3
```

### 4. Testing Strategy

#### Unit Tests
- Test deterministic mode produces reproducible output
- Test fallback mechanism when quantum unavailable
- Test quality scoring and tracking

#### Integration Tests
- Test SPHINCS+ key generation with quantum entropy
- Test randomness generation in runtime
- Test threshold reconstruction with multiple devices

#### Network Tests
- Run testnet with quantum entropy enabled
- Verify block production with quantum nonces
- Measure performance impact

### 5. Migration Path

**Phase 1: Development (Current)**
- Implement `QuantumEntropyProvider` ✅
- Add configuration options
- Implement fallback mechanisms
- Default to `AlwaysDeterministic` mode for compatibility

**Phase 2: Testing**
- Enable `PreferQuantum` mode on testnet
- Monitor quality metrics
- Identify and fix issues
- Performance benchmarking

**Phase 3: Production**
- Validators can opt-in to `PreferQuantum` mode
- Document QRNG device setup
- Provide monitoring dashboards
- Eventually migrate to `RequireQuantum` for critical operations

### 6. Security Considerations

**Entropy Quality:**
- Quality scores track QBER and device count
- Warn operators when quality degrades
- Support governance-controlled quality thresholds

**Device Compromise:**
- Threshold scheme (K-of-M) prevents single device compromise
- STARK proofs verify quantum measurement authenticity
- Devices can be added/removed via governance

**Fallback Security:**
- Deterministic mode uses Keccak-256 (quantum-resistant)
- Nonce counter prevents replay attacks
- Clearly logged when fallback is used

### 7. Performance Impact

**Expected Overhead:**
- QRNG device communication: ~50-200ms per request
- Threshold reconstruction: <1ms
- Total: <250ms for quantum entropy generation

**Mitigation:**
- Cache quantum entropy in pool
- Pre-generate entropy asynchronously
- Only use for critical operations (keys, VRF)
- Block hashes remain fast (deterministic)

### 8. Monitoring and Metrics

**Key Metrics:**
- Entropy quality score over time
- Quantum vs deterministic usage ratio
- Device availability and QBER
- Entropy generation latency
- Threshold reconstruction success rate

**Prometheus Metrics:**
```
quantum_entropy_quality{type="quantum|deterministic"}
quantum_entropy_requests_total{source="sphincs|vrf|hash"}
quantum_device_qber{device_id}
quantum_entropy_latency_seconds
```

## Implementation Status

- [x] Design HWRNG integration architecture
- [ ] Integrate HWRNG into SPHINCS+ key generation
- [ ] Enhance VRF randomness with HWRNG
- [ ] Add HWRNG to hash generation (block nonces)
- [ ] Test HWRNG integration
- [ ] Document HWRNG implementation

## References

- `node/src/quantum_entropy.rs` - Centralized entropy provider
- `node/src/threshold_qrng.rs` - K-of-M threshold QRNG implementation
- `node/src/pqtg_client.rs` - PQTG device client
- `runtime/src/quantum_config.rs` - Runtime randomness configuration
