# Layer 0: Quantum Entropy Foundation

## What is this layer?

The **entropy foundation** provides **true quantum randomness** from physical quantum devices, not pseudo-random computer algorithms. This is the bedrock of QuantumHarmony's security.

## Why does it matter?

Traditional blockchains use:
- **Deterministic hashing** (SHA-256, Blake2) - mathematically predictable
- **Block timestamps** - can be manipulated by validators
- **VRF (Verifiable Random Functions)** - still pseudo-random

QuantumHarmony uses:
- **Quantum Key Distribution (QKD)** devices - true randomness from quantum physics
- **Hardware Security Modules (HSM)** - tamper-resistant secure storage
- **Priority queues** - sorted by quality (QBER threshold)

## How does it work?

### 1. Quantum Entropy Generation

```
QKD Device (e.g., Toshiba, IdQuantique)
    ↓
Photon emission + polarization measurement
    ↓
Quantum superposition collapse → True random bits
    ↓
QBER (Quantum Bit Error Rate) < 5% threshold
    ↓
Store in priority queue (best quality first)
```

### 2. Local Shamir Secret Sharing (K=2, M=2)

Each validator runs **2 QKD devices** for redundancy:

```
Device A: Generates entropy_A
Device B: Generates entropy_B
    ↓
Shamir split: entropy = f(share_A, share_B)
    ↓
Requires BOTH devices to reconstruct
    ↓
Byzantine tolerance: 1 device can fail
```

### 3. Priority Queue Selection

```rust
// Pseudo-code
let mut queue = PriorityQueue::new();

for device in [device_a, device_b] {
    let sample = device.get_entropy();
    if sample.qber < 5.0 {  // Quality threshold
        queue.push(sample, sample.qber);  // Lower QBER = higher priority
    }
}

let best_entropy = queue.pop();  // Get highest quality
```

## Security Properties

| Property | Traditional (Pseudo-Random) | QuantumHarmony (QKD) |
|----------|----------------------------|----------------------|
| **Deterministic** | ✅ Yes (same seed → same output) | ❌ No (quantum physics) |
| **Predictable** | ⚠️ With enough compute power | ❌ Impossible (Heisenberg) |
| **MEV Resistant** | ❌ Validators can front-run | ✅ Entropy hidden until reveal |
| **Quantum Safe** | ❌ Shor's algorithm breaks it | ✅ Information-theoretic security |

## Key Concepts

### QBER (Quantum Bit Error Rate)
- Measures **noise** in quantum channel
- <1%: Excellent quality (fiber optic, short distance)
- 1-5%: Good quality (acceptable for consensus)
- >5%: Poor quality (reject, possible eavesdropping)

### Shamir Secret Sharing
- **K-of-M threshold**: Need K shares to reconstruct
- **Local**: K=2, M=2 (both devices required)
- **Network**: K=34, M=50 (68% of validators required)
- Byzantine fault tolerance: Up to 33% can be compromised

### HSM (Hardware Security Module)
- Tamper-resistant chip (e.g., Crypto4A QxEDGE)
- Stores entropy encrypted at rest
- Cannot be extracted without authentication
- Physical destruction if tampered

## Runtime Parameters

Current configuration:
```
qkd_device_count_per_validator: 2
priority_queue_size: 1000 samples
qber_threshold: 5.0% (reject worse)
entropy_refresh_rate: Every block (6 seconds)
local_shamir_threshold: K=2, M=2
```

## Visualization

```
        ╭─────────────────╮
        │  QKD Device A   │  ← Photon source
        ╰────────┬────────╯
                 ↓ entropy_A
        ╭────────────────────╮
        │  Priority Queue    │  ← QBER-sorted
        │  [Sample 1: 0.8%]  │
        │  [Sample 2: 1.2%]  │
        │  [Sample 3: 2.5%]  │
        ╰────────┬───────────╯
                 ↓ best_sample
        ╭────────────────────╮
        │  Shamir Combiner   │  ← Reconstruct
        ╰────────┬───────────╯
                 ↓ final_entropy
        ╭────────────────────╮
        │  HSM Storage       │  ← Secure vault
        ╰────────────────────╯
                 ↓ to Layer 1 (Consensus)
```

## Related Code

- **Implementation**: `node/src/threshold_qrng.rs`
- **QKD Client**: `pallets/qkd-client/src/lib.rs`
- **Entropy Pallet**: `pallets/validator-entropy/src/lib.rs`

## Common Questions

**Q: What if a validator doesn't have QKD devices?**
A: Software fallback uses secure HWRNG (hardware random number generator) with lower trust guarantees.

**Q: Can quantum computers break this?**
A: No! QKD is **information-theoretically secure** - even infinite compute power cannot break it.

**Q: Why not just use /dev/urandom?**
A: /dev/urandom is pseudo-random (deterministic algorithm). QKD is true randomness from quantum physics.

**Q: What's the cost of QKD devices?**
A: ~$50,000 per device. For testnet/small deployments, software fallback is acceptable.

## Next Layer

**↑ Layer 1: Consensus & Toroidal Mesh**
- How this entropy is used in Byzantine consensus
- Toroidal mesh parallelization for 50k validators
- Aura + GRANDPA + Coherence finality gadget

Press `1` to navigate to Layer 1 →
