# Coherence & Compliance Adversarial Evaluation (CCAE)

## Overview

QuantumHarmony's next phase: stateful, coverage-guided exploration of consensus + runtime + compliance pipeline under adversarial conditions, with Proof of Coherence (PoC) as the invariant oracle.

**Core differentiator:** *"Not a static code audit — a stateful adversarial evaluation of consensus trajectories under compliance constraints."*

---

## 1. PoC Fuzz Harness Architecture

### Goal

Stateful, coverage-guided exploration of:
- Consensus mechanisms
- Runtime execution
- Compliance pipeline (STARK verification)

Under adversarial:
- Ordering perturbations
- Timing attacks
- Entropy manipulation
- Network partitions

### High-Level Components

#### A. Scenario Schema (Structured Inputs)

Typed schema (protobuf/serde) describing multi-epoch test cases:

```rust
struct FuzzScenario {
    // Network topology
    validators: Vec<ValidatorConfig>,      // N validators, roles, latencies
    partitions: Vec<NetworkPartition>,     // Network splits

    // Message schedule
    events: Vec<ScheduledEvent>,           // Ordered: gossip, votes, equivocations, delays

    // Block contents
    extrinsics: Vec<ExtrinsicMix>,         // Weights, fee patterns

    // Entropy events
    qrng_injections: Vec<QrngEvent>,       // Replay/withhold variants

    // Fault model
    faults: Vec<FaultBehavior>,            // Crash/Byzantine, key rotations, clock skew

    // Compliance toggles
    stark_gate: bool,                      // On/off
    malformed_proofs: Vec<ProofMalformation>,
    boundary_sizes: Vec<u32>,
}
```

Think "transaction sequences" → but for **consensus trajectories**.

#### B. Executor / Deterministic Sandbox

Run chain in deterministic harness:

| Component | Implementation |
|-----------|---------------|
| Randomness | Seedable PRNG (reproducible) |
| Time | Virtual clock (controllable) |
| Network | Partition/delay/reorder hooks |
| State | Snapshots for fast rollback |

#### C. Feedback / Coverage Layers

```
┌─────────────────────────────────────────────────────────┐
│                    COVERAGE LAYERS                       │
├─────────────────────────────────────────────────────────┤
│ 1. Runtime Coverage    │ WASM basic-block/edge coverage │
│ 2. Consensus Coverage  │ State-machine transition edges │
│ 3. Compliance Coverage │ STARK verifier branches        │
│ 4. Economic Coverage   │ Slashing, equivocation paths   │
│ 5. PoC Coverage        │ Coherence constraint activation│
└─────────────────────────────────────────────────────────┘
```

#### D. Invariant Oracles

| Category | Invariants |
|----------|-----------|
| **Safety** | No invalid finality, no double-finalize, no invalid state transitions |
| **Liveness** | Within bounded conditions, progress must occur |
| **Compliance** | STARK verification accepts only valid witness, rejects malleations |
| **PoC** | Coherence score bounds, drift limits, forbidden phase transitions |

#### E. Reducer

When failure occurs:
1. Minimize scenario (delta-debugging on event list)
2. Output "repro bundle":
   - Seed
   - Event trace
   - State snapshots
   - Proof artifacts

### Harness Loop

```
┌──────────────────────────────────────────────────────────┐
│                    FUZZ HARNESS LOOP                      │
├──────────────────────────────────────────────────────────┤
│  1. Pick scenario from corpus                             │
│  2. Mutate (structure-aware, semantically valid)          │
│  3. Execute for K blocks/epochs with injected faults      │
│  4. Collect coverage + check invariants                   │
│  5. If new "interesting" coverage → add to corpus         │
│  6. If invariant violated → minimize + emit report        │
└──────────────────────────────────────────────────────────┘
```

---

## 2. STARK Compliance → Coverage Signals

### Why This Matters

Stop thinking "STARK verified or not" — explore:
- **How** it fails
- **Where** it fails
- **What consensus does** around failure modes

*That's where real exploits live.*

### Signal Class 1: Verifier Branch Coverage

Instrument verifier to emit edge IDs for:

```rust
// Coverage points in STARK verifier
coverage_point!("parsing/domain_check");
coverage_point!("merkle/commitment_verify");
coverage_point!("constraint/polynomial_check");
coverage_point!("fiat_shamir/transcript_check");
coverage_point!("boundary/max_size_hit");
coverage_point!("boundary/empty_witness");
coverage_point!("boundary/near_field_overflow");
```

### Signal Class 2: Constraint-Family Hits

Tag constraints by family, track activation:

```
Coverage Bitmap:
├── C_transition:        [HIT]
├── C_boundary:          [HIT]
├── C_permutation:       [   ]
├── C_lookup:            [   ]
├── C_degree_max:        [HIT]
├── C_air_composition:   [   ]
├── C_blowup_factor:     [HIT]
└── C_transcript_edge:   [HIT]
```

### Signal Class 3: Proof-Object Morphology

Treat proof as structured input; track novelty in:

| Metric | Buckets |
|--------|---------|
| Proof size | small/medium/large/huge |
| Query count | 1-10/11-50/51-100/100+ |
| FRI layers reached | depth buckets |
| Transcript length | short/medium/long |
| Commitment tree depth | shallow/deep |
| Field element distribution | coarse statistical buckets |

Guides fuzzer toward "weird but valid" proofs without brute-forcing secrets.

### Signal Class 4: End-to-End Compliance Gating

```
Consensus Pipeline Gates:
┌─────────────┐     ┌─────────────┐     ┌─────────────┐
│ precheck    │ --> │ verifier    │ --> │ finality    │
│ pass/fail   │     │ pass/fail   │     │ commit/abort│
└─────────────┘     └─────────────┘     └─────────────┘
                                              │
                                              v
                                    ┌─────────────────┐
                                    │ slashing_trigger│
                                    └─────────────────┘
```

Coverage edges to track:
- "Proof fails late but triggers soft-fail path"
- "Timeout causes fallback behavior"
- "Partial availability causes dangerous acceptance"

---

## 3. Commercial Offering: CCAE

### Deliverables

| # | Deliverable | Description |
|---|-------------|-------------|
| 1 | **Threat Model** | Tailored: stateful + economic + compliance |
| 2 | **Harness + Corpus** | Reproducible for their chain/module |
| 3 | **Coverage Report** | Consensus transitions, runtime paths, verifier branches |
| 4 | **Findings** | Minimal repro traces, severity, exploit narrative, patch guidance |
| 5 | **Regression Suite** | Minimized failing cases as tests |
| 6 | **Optional** | Proof-market hardening (if applicable) |

### Scope Tiers

| Tier | Duration | Scope |
|------|----------|-------|
| **A** | 2 weeks | Verifier + runtime + basic stateful sequences |
| **B** | 4-6 weeks | Full network fault model + multi-epoch consensus fuzzing |
| **C** | 8-12 weeks | Concolic assist for plateaus + formalized invariants + CI integration |

### Key Differentiator

> "Not a static code audit — a stateful adversarial evaluation of consensus trajectories under compliance constraints."

---

## 4. Integration Points (QuantumHarmony)

### Current STARK Gate Location

```
pallets/consensus-voting/
├── src/
│   ├── lib.rs              # Vote collection + finality
│   └── stark_gate.rs       # STARK verification hooks [TODO]
│
node/src/
├── service.rs              # Consensus service
└── quantum_p2p.rs          # P2P vote propagation
```

### Coverage Hook Insertion Points

1. **Vote Reception** (`quantum_p2p.rs`)
   - Vote signature verification
   - QRNG entropy validation

2. **Block Finalization** (`consensus-voting/lib.rs`)
   - Supermajority check
   - STARK proof verification gate

3. **Runtime Execution** (`runtime/src/lib.rs`)
   - Extrinsic dispatch
   - State transition validation

### First 10 Invariants to Encode

```rust
// Safety
invariant!(no_double_finalize);
invariant!(no_invalid_state_transition);
invariant!(no_unauthorized_authority_change);

// Liveness
invariant!(progress_within_bounds);
invariant!(vote_propagation_completes);

// Compliance
invariant!(stark_rejects_malformed_proof);
invariant!(stark_accepts_valid_proof);

// PoC
invariant!(coherence_score_bounded);
invariant!(no_forbidden_phase_transition);
invariant!(entropy_drift_limited);
```

---

## 5. Next Steps

1. [ ] Implement `stark_gate.rs` with coverage instrumentation
2. [ ] Create scenario schema (protobuf definitions)
3. [ ] Build deterministic sandbox executor
4. [ ] Integrate coverage collection (WASM + consensus state machine)
5. [ ] Define first 10 invariant oracles
6. [ ] Create minimizer for failure reproduction
7. [ ] Package as CCAE offering

---

## References

- Inversive Labs Solaris (Solana fuzzing)
- Structure-aware fuzzing literature
- STARK verification implementation patterns
- QuantumHarmony Proof of Coherence specification
