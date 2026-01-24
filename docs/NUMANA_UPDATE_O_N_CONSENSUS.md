# Karmonic Mesh: O(n) Consensus Update

**Date:** 2026-01-24
**Status:** Implemented
**Document:** Update for Numana partnership materials

---

## Executive Summary

The Karmonic Mesh consensus has been upgraded from **O(N log N)** to **O(n)** message complexity through integration of MonadBFT-style linear voting, while retaining all quantum security features.

---

## Before vs After

| Metric | Before | After | Improvement |
|--------|--------|-------|-------------|
| **Message Complexity** | O(N log N) | **O(n)** | 3.3x fewer messages at N=1000 |
| **100 Validators** | ~700 msgs | ~300 msgs | 2.3x reduction |
| **1000 Validators** | ~10,000 msgs | ~3,000 msgs | 3.3x reduction |

---

## What Changed

### Old: Gossip-Based Voting
```
V1 → V2, V3     (gossip)
V2 → V1, V3     (gossip)
V3 → V1, V2     (gossip)
...relay through network...
Total: N × log(N) messages
```

### New: Leader-Based Linear Voting
```
V1 → Leader     (1 message)
V2 → Leader     (1 message)
V3 → Leader     (1 message)
Leader → All    (certificate broadcast)
Total: 2N messages = O(n)
```

---

## What Stayed the Same

All quantum security features are preserved:

| Feature | Status |
|---------|--------|
| SPHINCS+ transaction signatures | Preserved |
| Falcon-1024 vote signatures | Preserved |
| QBER validation (<11% threshold) | Preserved |
| Coherence scoring | Preserved |
| Toroidal parallel execution | Preserved |
| QRNG arbitrage | Preserved |
| Post-quantum security | Preserved |

---

## Updated Comparison Table (for Numana docs)

Replace the old comparison table with:

```
Aspect              BFT Classique    Karmonic Mesh (Updated)
─────────────────────────────────────────────────────────────
Messages            O(N²)            O(n)
Convergence         O(N)             O(log N)
Bruit               Seuils fixes     Filtrage spectral
Hypothèses          Game-théorétiques Géométriques
Scalabilité         ~100 nœuds       ~50,000 nœuds
Post-Quantique      Non              Oui (SPHINCS+/Falcon)
Validation QBER     Non              Oui (<11%)
```

---

## Technical Implementation

### New Message Types

```rust
// Validator sends vote directly to leader
VoteToLeader {
    vote: CoherenceVote,
    qber_measurement: u16,  // basis points (0-10000)
    qkd_channel_id: u32,
}

// Leader broadcasts finality certificate
FinalityCertificateBroadcast {
    block_hash: H256,
    block_number: u64,
    aggregated_qber: u16,
    healthy_channels: u32,
    validator_count: u32,
    encoded_certificate: Vec<u8>,
}
```

### QBER Aggregation

Leader aggregates QBER from all votes:
- `aggregated_qber = Σ(qber_i) / n`
- `healthy_channels = count(qber < 1100)` (11% threshold)
- Block rejected if `aggregated_qber > 1100` OR `healthy_channels < 50%`

---

## Files Modified

```
node/src/coherence_gadget.rs   - Linear voting logic
node/src/coherence_gossip.rs   - New message types
```

---

## Environment Configuration

```bash
# Enable linear voting (default: true)
USE_LINEAR_VOTING=true

# Disable to fall back to O(N log N) gossip
USE_LINEAR_VOTING=false
```

---

---

## QRNG Leader Election (Phase 4)

Leader election now uses **threshold QRNG** from Crypto4A/KIRQ devices:

```
┌─────────────────────────────────────────────────────────┐
│           QRNG Leader Election Flow                     │
├─────────────────────────────────────────────────────────┤
│                                                         │
│   1. Collect K shares from QRNG devices                 │
│      (Crypto4A HSM, KIRQ, quantum_vault)                │
│                                                         │
│   2. Reconstruct entropy via Shamir                     │
│      entropy = reconstruct(share_1, share_2, ...)       │
│                                                         │
│   3. Compute election output for each validator         │
│      output_i = Hash(validator_i || block || entropy)   │
│                                                         │
│   4. Lowest output wins (provably fair)                 │
│      leader = argmin(output_i)                          │
│                                                         │
│   FALLBACK: If QRNG unavailable → deterministic VRF    │
│                                                         │
└─────────────────────────────────────────────────────────┘
```

**Key Property**: QRNG provides **true randomness** that cannot be predicted or manipulated by any participant, ensuring fair leader selection.

---

## References

- Implementation: `docs/HYBRID_CONSENSUS_SPEC.md`
- MonadBFT: https://docs.monad.xyz/monad-arch/consensus/monad-bft
- Karmonic Mesh: DOI 10.5281/zenodo.17928991

---

**Contact:** sylvain@paraxiom.org
