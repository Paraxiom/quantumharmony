# ISO/TC 307 Blockchain & DLT Standards Compliance

## Overview

This document maps QuantumHarmony components to ISO/TC 307 standards and identifies required modifications for compliance.

**ISO/TC 307** - Technologies des chaînes de blocs et technologies de registre distribué
- Secretariat: Standards Australia (SA)
- Chair: Dr Scott Farrell (until 2026)
- Established: 2016
- Published standards: 12
- Standards in development: 22

### Participation

Join the mirror committee (Canada): [SCC MC ISO/TC 307](https://www.scc.ca/en/standards/participate/mirror-committee/MCISOTC307)

---

## Working Group Mapping

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    ISO/TC 307 ←→ QUANTUMHARMONY MAPPING                      │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  ISO/TC 307/WG 1 (Foundations)                                              │
│  └─► runtime/, node/src/                                                     │
│      • Block structure, consensus, state machine                            │
│                                                                              │
│  ISO/TC 307/WG 3 (Smart Contracts)                                          │
│  └─► pallets/oracle/, pallets/validator-governance/                         │
│      • Oracle pallet, governance logic                                      │
│                                                                              │
│  ISO/TC 307/WG 5 (Governance)                                               │
│  └─► pallets/validator-governance/, pallets/substrate-validator-set/        │
│      • Validator approval, voting mechanisms                                │
│                                                                              │
│  ISO/TC 307/WG 6 (Use Cases)                                                │
│  └─► QRNG signals, carbon markets (AHG 4)                                   │
│      • Entropy distribution, environmental assets                           │
│                                                                              │
│  ISO/TC 307/WG 7 (Interoperability)                                         │
│  └─► node/src/entropy_gossip.rs, priority_queue_rpc.rs                      │
│      • Cross-node communication, signal propagation                         │
│                                                                              │
│  ISO/TC 307/WG 8 (Asset Tokenization)                                       │
│  └─► Future: carbon credits, QRNG tokens                                    │
│      • Digital asset representation                                         │
│                                                                              │
│  ISO/TC 307/JWG 4 (Security, Privacy, Identity)                             │
│  └─► Falcon1024, threshold signatures, QRNG                                 │
│      • Post-quantum cryptography, secure randomness                         │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Relevant ISO Standards

### Published Standards

| Standard | Title | QH Relevance |
|----------|-------|--------------|
| ISO 22739:2024 | Blockchain and DLT - Vocabulary | Terminology alignment |
| ISO 23257:2022 | Reference architecture | Architecture validation |
| ISO/TR 23244:2020 | Privacy and PII protection | Reporter identity, validator keys |
| ISO/TR 23576:2020 | Security management | QRNG security, Falcon signatures |
| ISO 23631:2024 | DLT systems interaction | Node interoperability |
| ISO 24643:2023 | Overview of smart contracts | Oracle/governance pallets |

### Standards in Development (Relevant)

| Standard | Title | QH Impact |
|----------|-------|-----------|
| ISO/AWI 24641 | Smart contract interactions | Oracle signal acceptance |
| ISO/CD 24642 | Guidelines for smart contract security | Pallet audit requirements |
| ISO/AWI TS 23259 | Legal/regulatory considerations | Validator liability |
| ISO/AWI TR 6039 | DLT identity management | Reporter approval system |

---

## Required QuantumHarmony Modifications

### Phase 1: Terminology Alignment (ISO 22739)

**File: All documentation**

Update terminology to match ISO 22739:2024:

| Current Term | ISO Term |
|--------------|----------|
| "Node" | "DLT node" or "Peer" |
| "Block" | "Block" (confirmed) |
| "Validator" | "Validating node" |
| "Oracle" | "Oracle" (confirmed) |
| "Smart contract" | "Smart contract" or "Distributed application" |
| "Token" | "Digital token" or "Crypto-asset" |

### Phase 2: Reference Architecture Compliance (ISO 23257)

**Files to modify:**
- `docs/MD/SYSTEM_ARCHITECTURE.md`
- `docs/MD/UNIFIED_ARCHITECTURE_DIAGRAM.md`

ISO 23257 defines these layers:

```
┌─────────────────────────────────────────────────────────────┐
│                    ISO 23257 LAYERS                          │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  Layer 5: User Layer                                         │
│  └─► node-operator-dashboard/                                │
│      REQUIRED: User interface standards                      │
│                                                              │
│  Layer 4: API Layer                                          │
│  └─► node/src/rpc/                                           │
│      REQUIRED: Standardized RPC interface documentation      │
│                                                              │
│  Layer 3: Smart Contract Layer                               │
│  └─► pallets/oracle/, pallets/validator-governance/          │
│      REQUIRED: Contract interface specification              │
│                                                              │
│  Layer 2: Ledger Services Layer                              │
│  └─► runtime/                                                │
│      REQUIRED: State transition documentation                │
│                                                              │
│  Layer 1: Infrastructure Layer                               │
│  └─► node/src/                                               │
│      REQUIRED: Network protocol specification                │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

**Action items:**
1. Create `docs/ISO/LAYER_MAPPING.md` documenting each layer
2. Add API documentation following ISO layer 4 guidelines
3. Document state transitions for ISO layer 2 compliance

### Phase 3: Security Compliance (ISO/TR 23576 + JWG 4)

**Files to modify:**
- `pallets/oracle/src/lib.rs`
- `node/src/threshold_qrng.rs`
- `crates/falcon-ffi/`

**Required additions:**

```rust
// pallets/oracle/src/lib.rs

/// ISO/TR 23576 Security Classification
///
/// Security Level: HIGH
/// - Post-quantum signatures: Falcon-1024 (NIST Level V)
/// - Entropy source: Threshold QRNG (K-of-M)
/// - Key management: Per-validator isolated keys
///
/// Threat model documented in: docs/ISO/THREAT_MODEL.md
```

**New documentation required:**
- `docs/ISO/THREAT_MODEL.md` - Formal threat analysis
- `docs/ISO/SECURITY_CONTROLS.md` - Control mapping to ISO 23576
- `docs/ISO/KEY_MANAGEMENT.md` - Lifecycle of validator keys

### Phase 4: Smart Contract Guidelines (ISO 24643 + ISO/CD 24642)

**Files to modify:**
- `pallets/oracle/src/lib.rs`
- `pallets/validator-governance/src/lib.rs`

**Required:**

1. **Formal specification** of each extrinsic:
```rust
/// # ISO 24643 Smart Contract Specification
///
/// ## Function: propose_reporter
///
/// ### Preconditions
/// - Caller is existing validator
/// - Candidate not already a reporter
/// - Stake >= MinReporterStake
///
/// ### Postconditions
/// - ReporterProposal created
/// - ProposalCreated event emitted
/// - Voting period begins
///
/// ### Invariants
/// - Total reporters <= MaxReporters
/// - No duplicate proposals for same candidate
#[pallet::call_index(X)]
pub fn propose_reporter(...) -> DispatchResult
```

2. **Audit trail** for all state changes
3. **Upgrade mechanism** documentation

### Phase 5: Interoperability (ISO 23631)

**Files to modify:**
- `node/src/entropy_gossip.rs`
- `node/src/rpc/oracle_rpc.rs`

**Required interface documentation:**

```
┌─────────────────────────────────────────────────────────────┐
│              ISO 23631 INTEROPERABILITY SPEC                 │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  External System Interface:                                  │
│  ┌───────────────────────────────────────────────────────┐  │
│  │ Protocol: JSON-RPC 2.0 over WebSocket                 │  │
│  │ Encoding: SCALE (Substrate standard)                  │  │
│  │ Auth: Falcon-1024 signatures                          │  │
│  └───────────────────────────────────────────────────────┘  │
│                                                              │
│  Signal Format (ISO-compliant):                             │
│  ┌───────────────────────────────────────────────────────┐  │
│  │ {                                                      │  │
│  │   "version": "1.0",                                   │  │
│  │   "schema": "iso:tc307:signal:v1",                    │  │
│  │   "source": {                                         │  │
│  │     "node_id": "0x...",                               │  │
│  │     "timestamp": 1234567890,                          │  │
│  │     "signature": "falcon1024:0x..."                   │  │
│  │   },                                                  │  │
│  │   "payload": {                                        │  │
│  │     "type": "qrng_entropy | oracle_price | custom",   │  │
│  │     "data": "0x...",                                  │  │
│  │     "metadata": {}                                    │  │
│  │   }                                                   │  │
│  │ }                                                      │  │
│  └───────────────────────────────────────────────────────┘  │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

### Phase 6: Carbon Markets (ISO/TC 307/AHG 4)

**New pallet required:** `pallets/carbon-credits/`

QuantumHarmony can participate in DLT carbon market standardization:

```rust
// pallets/carbon-credits/src/lib.rs (future)

/// Carbon Credit Token (ISO/TC 307/AHG 4 compliant)
///
/// Represents verified emission reductions with:
/// - Immutable origin (project ID, vintage year)
/// - QRNG-backed randomness for selection fairness
/// - Post-quantum transfer signatures
#[pallet::storage]
pub type CarbonCredits<T> = StorageMap<_, _, CreditId, CarbonCredit<T>>;
```

---

## UN Sustainable Development Goals Alignment

ISO/TC 307 contributes to these SDGs - QuantumHarmony alignment:

| SDG | ISO Contribution | QH Feature |
|-----|------------------|------------|
| 7 - Clean Energy | Energy-efficient DLT | Ternary weights (SMDR) - 10-20x less compute |
| 8 - Economic Growth | Digital economy infrastructure | Validator rewards, oracle fees |
| 9 - Innovation | DLT innovation | Post-quantum crypto, QRNG |
| 12 - Responsible Consumption | Supply chain tracking | Signal provenance |
| 13 - Climate Action | Carbon market standards | AHG 4 participation ready |
| 16 - Strong Institutions | Governance mechanisms | Validator governance pallet |

**See detailed analysis:** [CARBON_EFFICIENCY.md](./CARBON_EFFICIENCY.md)

---

## Implementation Checklist

```
Phase 1: Terminology (Q1)
[ ] Audit all docs for ISO 22739 compliance
[ ] Update README.md terminology
[ ] Create glossary.md with ISO terms

Phase 2: Architecture (Q1-Q2)
[ ] Create docs/ISO/LAYER_MAPPING.md
[ ] Document all RPC endpoints
[ ] Map runtime to ISO 23257 layers

Phase 3: Security (Q2)
[ ] Create docs/ISO/THREAT_MODEL.md
[ ] Document Falcon-1024 compliance
[ ] Create key management documentation

Phase 4: Smart Contracts (Q2-Q3)
[ ] Add formal specs to oracle pallet
[ ] Add formal specs to governance pallet
[ ] Document upgrade mechanisms

Phase 5: Interoperability (Q3)
[ ] Define ISO-compliant signal format
[ ] Document external system interface
[ ] Test cross-implementation compatibility

Phase 6: Carbon Markets (Q4)
[ ] Evaluate AHG 4 participation
[ ] Design carbon credit pallet
[ ] Implement if standards finalized
```

---

## Contact

**ISO/TC 307 Secretariat:**
Standards Australia
Level 10, The Exchange Centre
20 Bridge Street, Sydney 2000 NSW, Australia
Email: intsect@standards.org.au

**Canadian Mirror Committee:**
Standards Council of Canada (SCC)
[Join MCISOTC307](https://www.scc.ca/en/standards/participate/mirror-committee/MCISOTC307)

---

## References

- [ISO/TC 307 Home](https://www.iso.org/committee/6266604.html)
- [ISO 22739:2024 Vocabulary](https://www.iso.org/standard/73771.html)
- [ISO 23257:2022 Reference Architecture](https://www.iso.org/standard/75093.html)
- [ISO/TR 23576:2020 Security Management](https://www.iso.org/standard/76072.html)
