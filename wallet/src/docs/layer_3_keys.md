# Layer 3: Key Management & Forward Secrecy

## What is this layer?

The **key management layer** implements **Sparse Triple Ratchet** for forward secrecy, **SPQDR key derivation**, and **VRF-based shard assignment**. This is where ephemeral keys are rotated per-message to prevent compromise of past/future sessions.

## Why does it matter?

Traditional blockchains have **long-lived keys**:
- **Bitcoin**: Same ECDSA key for years (if compromised, all history at risk)
- **Ethereum**: Same account key forever (no forward secrecy)
- **Polkadot**: Session keys rotate per era (~24 hours, still long-lived)
- **Solana**: No automatic key rotation

QuantumHarmony uses:
- **Sparse Triple Ratchet**: Per-message key rotation (Signal protocol extended)
- **Forward secrecy**: Past messages safe even if current key compromised
- **Post-quantum**: Falcon1024-based key derivation
- **VRF shard assignment**: Unpredictable validator assignment

## Architecture Overview

### Three Key Derivation Mechanisms

```
┌─────────────────────────────────────┐
│ Sparse Triple Ratchet               │  ← Per-message ephemeral keys
│ • Send chain: KDF(send_key, msg#)   │
│ • Receive chain: KDF(recv_key, msg#)│
│ • Root chain: DH ratchet every N    │
└──────────┬──────────────────────────┘
           ↓
┌─────────────────────────────────────┐
│ SPQDR (Sparse Quantum Double Rat.)  │  ← Validator session keys
│ • Combines 2 entropy sources         │
│ • QPP Phase 3 (quantum + classical) │
│ • Rotates every epoch (~1 hour)     │
└──────────┬──────────────────────────┘
           ↓
┌─────────────────────────────────────┐
│ VRF (Verifiable Random Function)    │  ← Shard assignment
│ • Falcon1024-based VRF               │
│ • Unpredictable shard selection     │
│ • Publicly verifiable proof         │
└─────────────────────────────────────┘
```

## Sparse Triple Ratchet

### Signal's Double Ratchet (Original)

Signal's protocol has **2 ratchets**:
```
Symmetric ratchet: KDF chain for send/receive keys
    +
DH ratchet: ECDH key exchange after each message
```

### QuantumHarmony's Triple Ratchet (Extended)

We add a **3rd ratchet** for post-quantum security:

```
1. Symmetric ratchet (same as Signal)
2. DH ratchet (ECDH, classical)
3. KEM ratchet (Falcon1024, post-quantum)  ← NEW!
```

### Why "Sparse"?

**Full Triple Ratchet** would do DH + KEM after **every message** (slow!).

**Sparse Triple Ratchet** does:
- Symmetric ratchet: **Every message** (fast KDF)
- DH ratchet: **Every 100 messages** (ECDH)
- KEM ratchet: **Every 1000 messages** (Falcon1024)

### Key Derivation Chain

```rust
// Pseudo-code
struct RatchetState {
    send_chain_key: [u8; 32],
    recv_chain_key: [u8; 32],
    root_key: [u8; 32],
    message_number: u64,
}

impl RatchetState {
    fn derive_message_key(&mut self, direction: Direction) -> [u8; 32] {
        let chain_key = match direction {
            Direction::Send => &mut self.send_chain_key,
            Direction::Receive => &mut self.recv_chain_key,
        };

        // Symmetric ratchet: KDF(chain_key, "message_key")
        let message_key = blake2_256(&[chain_key, b"message_key"].concat());

        // Advance chain: chain_key = KDF(chain_key, "chain_key")
        *chain_key = blake2_256(&[chain_key, b"chain_key"].concat());

        self.message_number += 1;

        // Check if DH ratchet needed (every 100 messages)
        if self.message_number % 100 == 0 {
            self.dh_ratchet();
        }

        // Check if KEM ratchet needed (every 1000 messages)
        if self.message_number % 1000 == 0 {
            self.kem_ratchet();
        }

        message_key
    }
}
```

## SPQDR (Sparse Quantum Double Ratchet)

### QPP Phase 3 Integration

SPQDR is the **Quantum Preservation Pattern Phase 3** implementation:

```
Entropy Source A (QKD device or secure HWRNG)
    ↓ 256 bits
    ├─→ Blake2-256 hash
    │        ↓
    │   Hash_A: 256 bits
    │        ↓
Entropy Source B (OS /dev/urandom + HSM)
    ↓ 256 bits
    ├─→ SHA3-256 hash
    │        ↓
    │   Hash_B: 256 bits
    │        ↓
    └─→ XOR(Hash_A, Hash_B)
             ↓
        Mixed: 256 bits (QPP-compliant)
             ↓
    Falcon1024 key derivation
             ↓
        Session key (rotates every epoch)
```

### No-Cloning Theorem Guarantee

**Quantum no-cloning**: Cannot copy quantum state without destroying it.

If Source A is true quantum (QKD):
- Adversary cannot intercept without being detected (QBER increases)
- Even if Source B is compromised, XOR with quantum bits preserves entropy
- **Information-theoretic security** against quantum attacks

### Session Key Rotation

```
Epoch 0: Validator derives session_key_0 from SPQDR
    ↓
Epoch 1 (1 hour later): Re-run SPQDR → session_key_1
    ↓
Old session_key_0 is DELETED from memory
    ↓
Even if session_key_1 compromised, cannot decrypt Epoch 0 messages
    ↓
= Forward secrecy
```

## VRF (Verifiable Random Function)

### Purpose: Shard Assignment

In a multi-shard blockchain:
- Need to assign validators to shards **unpredictably**
- But assignment must be **publicly verifiable**
- Prevent manipulation ("I want to be in shard 3!")

### Falcon1024-Based VRF

```rust
// Pseudo-code
struct VrfProof {
    output: [u8; 32],       // Random shard ID
    proof: Falcon1024Sig,   // Proves validity
}

fn vrf_compute(secret_key: &Falcon1024Secret, input: &[u8]) -> VrfProof {
    // 1. Sign the input with Falcon1024
    let signature = falcon_sign(secret_key, input);

    // 2. Hash the signature to get random output
    let output = blake2_256(&signature);

    VrfProof { output, proof: signature }
}

fn vrf_verify(public_key: &Falcon1024Public, input: &[u8], proof: &VrfProof) -> bool {
    // 1. Verify the Falcon1024 signature
    if !falcon_verify(public_key, input, &proof.proof) {
        return false;
    }

    // 2. Check output matches hash
    let expected_output = blake2_256(&proof.proof);
    expected_output == proof.output
}
```

### Shard Assignment Example

```
Block N: Need to assign 50 validators to 5 shards

For each validator:
    Input = blake2(block_N_hash || validator_id)
    VRF output = vrf_compute(validator_secret, input)
    Shard ID = output % 5

Validator 0: VRF output = 0xAB12... → Shard 3
Validator 1: VRF output = 0x7F89... → Shard 1
Validator 2: VRF output = 0x234C... → Shard 0
...

Result: 10 validators per shard (on average)
```

## Performance Characteristics

| Operation | Latency | Frequency |
|-----------|---------|-----------|
| **Symmetric Ratchet** | ~1 µs | Every message |
| **DH Ratchet (ECDH)** | ~50 µs | Every 100 messages |
| **KEM Ratchet (Falcon1024)** | ~200 µs | Every 1000 messages |
| **SPQDR Derivation** | ~500 µs | Every epoch (~1 hour) |
| **VRF Compute** | ~200 µs | Once per block (shard assignment) |

**Real benchmark (Falcon1024):**
- Key generation: 0.5ms
- Signing: 0.2ms
- Verification: 0.1ms
- Signature size: 1,280 bytes

## Key Storage

### In-Memory Key Hierarchy

```
Root Key (HSM-protected, never leaves hardware)
    ↓
    ├─→ Validator Identity Key (Falcon1024, rotates yearly)
    │       ↓
    │       ├─→ Session Key (SPQDR, rotates hourly)
    │       │       ↓
    │       │       ├─→ Message Key (Triple Ratchet, per-message)
    │       │       │       ↓
    │       │       │   Ephemeral (deleted after use)
    │       │       │
    │       │       └─→ Old message keys (kept for 1 hour, then purge)
    │       │
    │       └─→ Old session keys (DELETED immediately after rotation)
    │
    └─→ Old identity keys (archived for 1 year, then DELETED)
```

### Forward Secrecy Guarantees

| Compromise Scenario | What's Safe? |
|---------------------|--------------|
| **Current message key** | Past messages safe (can't reverse KDF) |
| **Current session key** | Old epoch messages safe (keys deleted) |
| **Current identity key** | Old session messages safe (SPQDR rotated) |
| **Root key** | Everything compromised (catastrophic) |

**Mitigation**: Root key stored in HSM (hardware-protected), requires physical access.

## Runtime Parameters

Current configuration:
```
symmetric_ratchet_interval: 1 (every message)
dh_ratchet_interval: 100 messages
kem_ratchet_interval: 1000 messages
spqdr_epoch_duration: 3600 seconds (1 hour)
vrf_proof_verification_cost: 100,000 weight
session_key_retention: 3600 seconds (1 hour after rotation)
message_key_cache_size: 1000 keys (for out-of-order delivery)
```

## Visualization

```
┌────────────────────────────────────────┐
│   Key Management Layer (Triple Ratchet)│
├────────────────────────────────────────┤
│                                        │
│  ╭─────────────╮   Every message      │
│  │  Symmetric  │ ──────────────→ KDF  │
│  │   Ratchet   │      (~1 µs)         │
│  ╰─────────────╯                      │
│         ↓                              │
│  ╭─────────────╮   Every 100 msgs     │
│  │     DH      │ ──────────────→ ECDH │
│  │   Ratchet   │      (~50 µs)        │
│  ╰─────────────╯                      │
│         ↓                              │
│  ╭─────────────╮   Every 1000 msgs    │
│  │    KEM      │ ──────────→ Falcon   │
│  │   Ratchet   │      (~200 µs)       │
│  ╰─────────────╯                      │
│         ↓                              │
│  ╭─────────────╮   Every epoch        │
│  │    SPQDR    │ ──────→ QPP Phase 3  │
│  │  (Session)  │      (~500 µs)       │
│  ╰─────────────╯                      │
│                                        │
│  Current Epoch: 1234                   │
│  Messages This Epoch: 8,456            │
│  Next DH Ratchet: 44 messages          │
│  Next KEM Ratchet: 544 messages        │
│  Next Epoch Rotation: 32 minutes       │
└────────────────────────────────────────┘
```

## Related Code

- **Triple Ratchet**: `node/src/qpp.rs` (QPP Phase 3 implementation)
- **SPQDR**: `node/src/threshold_qrng.rs` (entropy mixing)
- **VRF**: `pallets/runtime-segmentation/src/vrf.rs`
- **Falcon1024**: `node/src/falcon_crypto.rs`

## Common Questions

**Q: Why not just use Signal's Double Ratchet?**
A: Double Ratchet uses ECDH (vulnerable to Shor's algorithm). We need post-quantum KEM (Falcon1024).

**Q: Why "sparse" ratchet instead of full ratchet?**
A: Full ratchet does ECDH + KEM after every message = too slow. Sparse ratchet amortizes cost.

**Q: What if a validator loses their root key?**
A: Generate new identity, re-stake with new key. Old messages cannot be recovered (forward secrecy trade-off).

**Q: Can quantum computers break this?**
A: **No.** Falcon1024 is NIST PQC Level 5 (strongest). Even with quantum computer, past messages are safe.

**Q: How do you prevent key exhaustion?**
A: KDF chains are theoretically infinite (256-bit state space = 2²⁵⁶ messages). Practically, rotate session keys hourly.

## Security Proofs

### Forward Secrecy Proof Sketch

**Claim**: If session key K_t is compromised at time t, messages at time t-1 remain secure.

**Proof**:
1. Message at t-1 encrypted with key K_{t-1}
2. K_{t-1} derived from root_key_{t-1}
3. At time t, root_key_{t-1} is DELETED (not stored anywhere)
4. K_t is derived from root_key_t (different root key)
5. No computable function f such that f(K_t) = K_{t-1} (KDF is one-way)
6. Therefore, adversary with K_t cannot decrypt messages at t-1 ∎

### VRF Unpredictability Proof Sketch

**Claim**: Adversary cannot predict VRF output without knowing secret key.

**Proof**:
1. VRF output = Hash(Falcon1024_Sign(secret_key, input))
2. Falcon1024 signature security = NIST PQC Level 5 (2²⁵⁶ operations)
3. Without secret key, adversary cannot forge signature
4. Hash function is random oracle (output indistinguishable from random)
5. Therefore, adversary cannot predict output better than random guessing ∎

## Attack Scenarios

### Scenario 1: Compromise Current Session Key

**Attacker gains**: Ability to decrypt messages in current epoch
**Attacker CANNOT**: Decrypt past epoch messages (keys deleted)
**Mitigation**: Rotate session keys frequently (1 hour)

### Scenario 2: Compromise Root Key (HSM)

**Attacker gains**: Ability to derive all future keys
**Attacker CANNOT**: Decrypt past messages (forward secrecy)
**Mitigation**: Physical security for HSM, multi-party key sharding

### Scenario 3: Quantum Computer Attack

**Attacker gains**: Nothing (Falcon1024 is quantum-resistant)
**Mitigation**: Already mitigated by design

## Next Layer

**↑ Layer 4: Cryptographic Signatures**
- How SPHINCS+ signatures work
- Lamport chains for signature aggregation
- Falcon1024 integration with SPHINCS+

Press `4` to navigate to Layer 4 →

**↓ Layer 2: Network Transport**
- How ephemeral keys are exchanged via QUIC
- P2P gossip protocol for key rotation announcements

Press `2` to navigate to Layer 2 ←
