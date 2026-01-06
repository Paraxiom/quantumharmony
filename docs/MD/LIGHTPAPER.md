# QuantumHarmony Light Paper

**Version 2.0 - January 2026**

**Repository**: https://github.com/Paraxiom/quantumharmony

> **Changelog v2.0**: Added VOTE SYNC encrypted validator messaging. Added Node Operator one-command deployment.
>
> **v1.9**: Added Section 8 "Sovereignty and System-Level Auditability" — policy framing for vendor-agnostic, auditable quantum infrastructure.
>
> **v1.8**: Updated to Public Beta status. 600+ tests passing. 3 production validators live.
>
> **v1.7**: Clarified PQC costs—we avoid migration overhead but still have raw PQC signature size, mitigated via toroidal parallelization.
>
> **v1.6**: Added "Why Greenfield?" section citing Campbell (2025) on PQC migration governance impossibility.
>
> **v1.5**: Added Web Interface section. Added Research Publications with DOIs (6 papers on Zenodo). Expanded references.
>
> **v1.4**: Added Quantum P2P networking section (ML-KEM-1024, Falcon-1024, QKD hardware interface). Expanded Proof of Coherence with P2P integration details.
>
> **v1.3**: Added Use Cases section (QCAD, Fideicommis, Pedersen). Expanded governance documentation. Added Triple Ratchet encryption and 512-segment toroidal mesh documentation.
>
> **v1.2**: Added MEV protection documentation. Corrected finality description—QuantumHarmony provides deterministic BFT finality via the Coherence Gadget, not probabilistic finality.

## Abstract

QuantumHarmony is a Layer 1 blockchain built on Substrate that replaces quantum-vulnerable cryptographic components with post-quantum alternatives. This document describes what the system does, how it works, and its current state.

## 1. Problem Statement

### Quantum Computing Threat
Current blockchains rely on cryptographic primitives that quantum computers can break:

| Primitive | Algorithm | Quantum Attack | Time to Break |
|-----------|-----------|----------------|---------------|
| Signatures | ECDSA, Ed25519 | Shor's Algorithm | Polynomial time |
| Finality | BLS (GRANDPA) | Shor's Algorithm | Polynomial time |
| Hashing | Blake2b | Grover's Algorithm | Quadratic speedup (still secure with 256-bit) |

**Fact**: NIST estimates cryptographically relevant quantum computers could exist within 10-15 years. Blockchain addresses and signed transactions recorded today become vulnerable when such computers exist.

### Why Greenfield?

**Why not migrate existing chains?** Campbell (2025) demonstrates that post-quantum migration for Bitcoin and Ethereum faces what he terms "governance impossibility":

| Impact | Bitcoin | Ethereum |
|--------|---------|----------|
| Capacity loss | 50% | 50% |
| Fee increase | 3× | 3× |
| State bloat | 59× | 59× |
| Immediate user benefit | Zero | Zero |

No rational validator/miner coalition will vote for changes that halve their revenue with no offsetting benefit. The required migration timeline (10-15 years for full ecosystem transition) may exceed the quantum threat timeline itself.

**QuantumHarmony's approach**: Build post-quantum from genesis. No migration governance, no backwards compatibility debt, no hybrid transition period.

**What we avoid vs. what we address differently**:

| Cost | Migration Approach | QuantumHarmony |
|------|-------------------|----------------|
| Hybrid signature overhead | Required during transition | None (PQC-only from genesis) |
| Legacy state bloat | 59× for backwards compatibility | None |
| Governance deadlock | Unsolvable | Not applicable |
| Raw PQC signature size | ~29KB SPHINCS+ | Same (~29KB) |
| **Mitigation** | None proposed | 512-segment toroidal parallelization |

PQC signatures are inherently larger than classical signatures. Campbell's state bloat comes from maintaining *both* formats during migration. QuantumHarmony still has larger signatures, but compensates through parallel verification across the toroidal mesh (see Section 2.4), achieving 10K TPS with SPHINCS+ signatures.

### What QuantumHarmony Changes

| Component | Standard Substrate | QuantumHarmony |
|-----------|-------------------|----------------|
| Signatures | Ed25519/ECDSA | SPHINCS+ (NIST PQC standard) |
| Block Hashing | Blake2b | Keccak-256 (SHA-3) |
| Finality Gadget | GRANDPA (BLS) | Coherence Gadget (Falcon1024) |
| Randomness | VRF | Quantum-enhanced VRF (QKD optional) |

## 2. Technical Implementation

### 2.1 SPHINCS+ Signatures

**What it is**: A stateless hash-based signature scheme standardized by NIST in 2024.

**Security basis**: Security relies only on hash function properties, not mathematical problems like discrete logarithms (which quantum computers solve efficiently).

**Trade-offs**:
- Signature size: ~8-50 KB (vs 64 bytes for Ed25519)
- Signing time: Slower than Ed25519
- Verification: Comparable to Ed25519

**Implementation**: `pallet-sphincs-keystore` provides key generation, signing, and verification.

### 2.2 Keccak-256 Hashing

**What it is**: SHA-3 family hash function with sponge construction.

**Why used**:
- 256-bit output provides 128-bit security against Grover's algorithm
- 1600-bit internal state resistant to quantum attacks
- Widely audited and standardized

**Implementation**: Custom `QuantumHasher` in `runtime/src/quantum_hasher.rs` replaces Blake2 throughout the runtime.

### 2.3 Triple Ratchet Encryption

Validator-to-validator communication uses a **Triple Ratchet** protocol combining three key rotation mechanisms:

1. **Falcon Ratchet**: Long-term post-quantum signatures (slow rotation)
2. **Merkle Ratchet**: Hierarchical key derivation (periodic rotation)
3. **Symmetric Ratchet**: Ephemeral session keys (per-message rotation)

This provides forward secrecy: compromise of current keys does not reveal past messages.

Implementation: `node/src/qpp.rs`

### 2.4 512-Segment Toroidal Mesh

Runtime execution is parallelized across an 8×8×8 toroidal mesh (512 segments):

- Each segment handles a subset of accounts
- Parallel transaction execution within segments
- Cross-segment communication via 6 neighbors (3D torus)
- Load balancing with automatic rebalancing
- Maximum 3 hops between any two segments

Implementation: `pallet-runtime-segmentation`

### 2.5 Quantum-Secured P2P Networking

Validator-to-validator communication uses a fully post-quantum secured P2P layer (`node/src/quantum_p2p/`):

**Identity & Key Exchange:**
- **Falcon-1024**: Node identity and message signing (NIST PQC)
- **ML-KEM-1024** (Kyber): Key encapsulation for session establishment (NIST PQC)
- **AES-256-GCM**: Authenticated encryption for message confidentiality

**Protocol Flow:**
1. Node generates Falcon-1024 signing keypair + ML-KEM-1024 KEM keypair
2. Session initiation: ML-KEM encapsulation creates shared secret
3. Shared secret derives AES-256 session key
4. All messages signed with Falcon-1024, encrypted with AES-256-GCM
5. Automatic key rotation (default: 1 hour)

**QKD Hardware Integration:**
When QKD hardware is available, session keys can be derived from QKD-generated entropy instead of ML-KEM:

| Vendor | Interface | Status |
|--------|-----------|--------|
| Toshiba QKD | ETSI GS QKD 014 | Stub ready |
| ID Quantique (Cerberis) | ETSI GS QKD 014 | Stub ready |
| QuantumCTek | Vendor API | Stub ready |
| SK Telecom IDQ | ETSI GS QKD 014 | Stub ready |
| NTT QKD | ETSI GS QKD 014 | Stub ready |

**VRF Peer Selection:**
Peer connections use verifiable random selection to prevent eclipse attacks.

### 2.6 Consensus & Finality

**Block Production**: Aura (Authority Round) - validators take turns producing blocks.

**Finality**: Deterministic BFT finality via the **Coherence Gadget** - a post-quantum replacement for GRANDPA.

**Why not GRANDPA**: GRANDPA uses BLS aggregate signatures, which rely on elliptic curve pairings vulnerable to quantum attacks.

#### Coherence Gadget

The Coherence Gadget provides GRANDPA-equivalent deterministic finality using post-quantum cryptography:

| GRANDPA | Coherence Gadget |
|---------|------------------|
| BLS signatures | Falcon1024 signatures |
| Voter set | ValidatorSet with PQ keys |
| Prevote/Precommit | STARK proof verification + coherence scoring |
| 2/3 supermajority | 2/3 supermajority (same BFT guarantee) |
| Finality proof | FinalityCertificate |

**Protocol flow**:
1. Wait for new block from Aura
2. Collect STARK proofs from reporters (quantum entropy measurements)
3. Verify proofs, calculate coherence score based on QBER
4. Sign vote with Falcon1024
5. Broadcast vote to validators (encrypted with Triple Ratchet)
6. Collect votes, check for 2/3+ supermajority
7. Generate finality certificate
8. Block is **final** (irreversible)

### 2.7 Proof of Coherence (PoC)

PoC is the consensus mechanism that combines quantum entropy with BFT finality.

**With QKD/QRNG hardware**:
- Real quantum entropy from devices (Toshiba QKD, Crypto4A QRNG, IdQuantique)
- STARK proofs verified with Winterfell
- QBER (Quantum Bit Error Rate) measurements for coherence scoring (threshold: 11%)
- Information-theoretic security from quantum physics
- QKD-derived session keys for validator P2P (via `quantum_p2p/qkd_interface.rs`)

**Without quantum hardware (fallback)**:
- Mock entropy sources for testing
- ML-KEM-1024 session keys for validator P2P
- BFT consensus still runs with 2/3 supermajority
- Falcon1024 signatures provide post-quantum security
- Deterministic finality still guaranteed

**Integration with P2P Layer:**
- Coherence votes broadcast via quantum-secured P2P channels
- Vote encryption uses QKD-derived keys when available, ML-KEM otherwise
- Triple Ratchet provides forward secrecy for vote messages

**Key insight**: Quantum hardware is an optimization, not a requirement. The BFT layer always provides deterministic finality. QKD/QRNG adds additional entropy quality guarantees when available.

### 2.8 MEV Protection

QuantumHarmony implements native Maximal Extractable Value (MEV) protection through a leader-based mempool validation mechanism.

#### The MEV Problem

In traditional blockchains, validators can:
- Reorder transactions for profit (frontrunning)
- Insert their own transactions (sandwich attacks)
- Censor specific transactions

#### QuantumHarmony's Solution

The elected leader maintains a qVRF-ordered priority queue that serves as the canonical transaction ordering:

1. **Leader Election**: `substrate-validator-set` elects a leader using quantum-seeded randomness
2. **Queue Comparison**: Leader compares their priority queue against the public mempool
3. **Discrepancy Detection**: Any transaction in wrong position or that shouldn't exist is flagged
4. **Deletion**: Discrepant transactions are removed from the mempool

```rust
// Leader validates mempool integrity
for tx in mempool {
    if tx.position != priority_queue.position(tx) {
        mempool.delete(tx);  // Discrepancy detected
    }
}
```

#### Reporter Random Numbers

Every report submitted to the network must include a randomly generated number:

```
tx_hash = Hash(payload || random_nonce)
```

This ensures:
- **Unique transaction hashes**: No two reports can have the same hash
- **Replay protection**: Cannot resubmit old reports
- **Ordering integrity**: Position in queue is deterministic based on qVRF

#### Security Guarantees

| Attack | Mitigation |
|--------|------------|
| Frontrunning | qVRF ordering is unpredictable |
| Sandwich attacks | Discrepancy detection removes injected txs |
| Transaction censorship | Multiple leaders, rotation |
| Replay attacks | Random nonce in each report |

### 2.9 VOTE SYNC - Encrypted Validator Messaging

Real-time encrypted messaging between validators using the Triple Ratchet protocol (Section 2.3):

**Cryptographic Stack:**
- **ML-KEM-768**: Key encapsulation for session establishment
- **SPHINCS+**: Message signatures
- **Triple Ratchet**: Forward secrecy (Falcon + Merkle + Symmetric ratchets)

**Features:**
- End-to-end encrypted validator coordination
- Message history with read receipts
- Peer discovery via blockchain identity
- Accessible via Node Operator Dashboard

**Implementation**: `node-operator/src/messaging.rs`, `crates/pq-triple-ratchet/`

## 3. Use Cases

### 3.1 QCAD Stablecoin

Canadian dollar stablecoin (`pallet-stablecoin`):
- 1:1 CAD peg via oracle price feeds
- Collateralized vaults (150% minimum ratio)
- Liquidation engine for undercollateralized positions
- Stability fees paid in native token

### 3.2 Fideicommis Trusts

Quebec Civil Code compatible trust administration (`pallet-fideicommis`):
- Trust creation with grantor, trustee, beneficiaries
- Asset registration (on-chain and off-chain references)
- Distribution rules: time-locked, conditional, discretionary
- Trustee succession with multi-sig handoff

### 3.3 Pedersen Commitments

Zero-knowledge proofs on BLS12-381 (`pallet-pedersen-commitment`):
- Commit-reveal for MEV protection
- Range proofs for private amounts
- Binding + hiding properties

## 4. Governance System

### 4.1 Standard Substrate Governance
QuantumHarmony includes standard Substrate governance pallets:
- Democracy (referenda voting)
- Collective (council/committee management)
- Treasury (on-chain funds management)
- Scheduler (timed governance actions)

### 4.2 Academic Vouching (`pallet-academic-vouch`)

**Purpose**: Allow verified academics to vouch for applicants to specialized programs.

**How it works**:
1. Academic submits registration with credentials
2. Existing academics vote on registration
3. Registered academics can vouch for program applicants
4. Applicants accepted when vouch threshold met

**Use case**: Architecture Program applicant needs vouches from registered architects/academics.

### 4.3 Ricardian Contracts (`pallet-ricardian-contracts`)

**What it is**: On-chain storage and management of human-readable legal contracts with machine-executable terms.

**Features**:
- Contract creation with hash of legal text
- Multi-party signing workflow
- Amendment system
- State transitions: Draft -> Active -> Executed/Terminated

**Contract types supported**: Academic Program, Partnership, Service Agreement, Employment, Licensing, Custom.

### 4.4 Notarial Services (`pallet-notarial`)

**What it is**: Document timestamping and attestation system.

**Features**:
- Store document hash with timestamp
- Witness signatures for certification
- Certificate generation
- Revocation capability

**What it proves**: A document with a specific hash existed at a specific block/time.

## 5. Current State

### Network Status
- **Phase**: Public Beta Testnet
- **Validators**: 3 production validators (Montreal, Beauharnois, Frankfurt)
- **Block time**: 6 seconds
- **Consensus**: Proof of Coherence (PQ-BFT)
- **Test Coverage**: 600+ unit and integration tests passing

### What's Implemented
- SPHINCS+ signature verification across all pallets
- Falcon-1024/ML-KEM-1024 quantum P2P networking
- Coherence Gadget for deterministic BFT finality
- All governance pallets (Democracy, Treasury, Collective)
- Financial pallets (QCAD stablecoin, Fideicommis trusts)
- Legal pallets (Ricardian contracts, Notarial attestation)
- 512-segment toroidal mesh parallelization
- Docker deployment for node operators
- Forkless runtime upgrades

### Node Operator Deployment

One-command deployment for validators and node operators:

```bash
./start.sh              # Full node + messaging + dashboard
./start.sh fresh        # Update and restart (pulls latest)
./start.sh ui           # Dashboard only (no Docker)
```

**Services:**
| Port | Service |
|------|---------|
| 8080 | Dashboard (web UI) |
| 9944 | RPC/WebSocket |
| 9955 | VOTE SYNC messaging |
| 30333 | P2P |

Pre-configured bootnodes enable automatic peer discovery.

### Seeking
- Security audit (pre-mainnet)
- QKD hardware production testing
- Additional validator operators

## 6. Token Economics

**Token**: QHY
**Decimals**: 18
**Initial distribution**: Genesis validators

**Reward mechanism**: `pallet-validator-rewards` distributes block rewards to active validators.

**Transaction fees**: Standard Substrate weight-based fees.

## 7. Limitations and Honest Assessment

### What This Is
- A post-quantum secure blockchain framework
- A working testnet demonstrating the concepts
- An integration of NIST-standardized post-quantum cryptography into Substrate

### What This Is Not
- A production-ready mainnet (yet)
- A guarantee against all quantum attacks
- A replacement for proper security audits

### Known Trade-offs
1. **Larger signatures**: SPHINCS+ signatures are 8-50KB vs 64 bytes for Ed25519; Falcon1024 ~1.3KB
2. **Finality vote size**: Coherence Gadget uses Falcon1024 (~1.3KB per vote vs BLS aggregation)
3. **Compatibility**: Not compatible with standard Substrate tooling that expects Ed25519/Sr25519

### Open Questions
- Optimal SPHINCS+ parameter selection for blockchain use
- Performance at scale with larger signatures
- Bridge compatibility with other chains

## 8. Sovereignty and System-Level Auditability

### The Distinction Between Component and System Validation

Quantum security primitives can be validated at two levels:

| Level | What's Validated | What's Not |
|-------|------------------|------------|
| **Component** | Individual QRNG/QKD device output | Integration, dependency chains, system behavior |
| **System** | End-to-end protocol, all code paths | Nothing hidden; full auditability |

Component-level validation certifies that a device produces quality entropy. It does not certify how that entropy is integrated, transported, or consumed by downstream systems.

### Why This Matters for Public Infrastructure

Public funding for quantum security R&D—whether from federal, provincial, or innovation programs—carries an implicit expectation: that the resulting capabilities strengthen domestic infrastructure and remain inspectable by the funding jurisdiction.

When a publicly funded quantum primitive is validated exclusively through foreign, closed, or non-auditable systems, several issues arise:

1. **Dependency chains**: The validated component becomes dependent on external trust anchors
2. **Inspection gaps**: Domestic regulators cannot verify system-level behavior
3. **Sovereignty erosion**: Critical security primitives become policy liabilities

This is not a criticism of international collaboration, which is normal and often necessary. It is a structural observation about where validation authority resides.

### QuantumHarmony's Position

QuantumHarmony is designed as **vendor-agnostic infrastructure**:

| Property | Implementation |
|----------|----------------|
| Entropy abstraction | QRNG/QKD are optional inputs, not dependencies |
| Hardware interfaces | ETSI GS QKD 014 standard; vendor stubs for Toshiba, ID Quantique, QuantumCTek, etc. |
| Fallback mode | Full BFT consensus operates without quantum hardware |
| Code visibility | 100% open source, all paths inspectable |

**Key point**: QuantumHarmony does not compete with QRNG/QKD vendors. It provides the neutral substrate into which such components can be integrated—with full system-level auditability.

### Policy Implication

A question for funders, regulators, and procurement officials:

> *How should publicly funded quantum security primitives be integrated into open, auditable, sovereignty-preserving infrastructure?*

QuantumHarmony offers one answer: build the substrate first, validate at the system level, and let component vendors plug in without creating closed dependency chains.

## 9. Comparison with Alternatives

| Feature | QuantumHarmony | Standard Substrate | QRL |
|---------|----------------|-------------------|-----|
| Signature Scheme | SPHINCS+ / Falcon1024 | Ed25519/Sr25519 | XMSS |
| Hash Function | Keccak-256 | Blake2b | SHA-256 |
| Finality | Deterministic (Coherence Gadget) | GRANDPA (BFT) | PoW |
| Stateless Signatures | Yes | N/A | No (stateful) |
| Substrate-based | Yes | Yes | No |
| Quantum Hardware Support | Yes (Toshiba QKD, QRNG) | No | No |

## 10. Web Interface

A web-based notarial interface is available for end users:

**Features:**
- Document attestation with SPHINCS+ signatures
- Contract creation and multi-party signing
- QCAD stablecoin transactions
- Fideicommis trust management
- Account creation with local key storage

**Technical Stack:**
- SHA-256 document hashing
- SPHINCS+-256s post-quantum signatures
- Real-time blockchain connection

## 11. Research Publications

Theoretical foundations published on Zenodo with DOIs:

| Paper | Topic | DOI |
|-------|-------|-----|
| ERLHS | Hamiltonian framework for coherence-preserving ML | 10.5281/zenodo.17928909 |
| Karmonic Mesh | O(N log N) spectral consensus on toroidal manifolds | 10.5281/zenodo.17928991 |
| Proof of Coherence | QKD-based distributed consensus mechanism | 10.5281/zenodo.17929054 |
| Toroidal Mesh | 10K TPS with SPHINCS+ via parallel verification | 10.5281/zenodo.17931222 |
| Toroidal Governance | Tonnetz manifold governance (defensive publication) | 10.5281/zenodo.17929091 |
| Augmented Democracy | Coherence-constrained democratic infrastructure | Preprint |

## 12. References

1. NIST Post-Quantum Cryptography Standardization (2024)
2. SPHINCS+ Specification (NIST FIPS 205)
3. Falcon Specification (NIST FIPS 206)
4. ML-KEM Specification (NIST FIPS 203)
5. Substrate Developer Documentation
6. ETSI GS QKD 014 - QKD Key Delivery API
7. Grover's Algorithm - Quantum Search (1996)
8. Shor's Algorithm - Quantum Factoring (1994)
9. Campbell, R. "Hybrid Post-Quantum Signatures for Bitcoin and Ethereum: A Protocol-Level Integration Strategy." JBBA 9(1), 2025. DOI: 10.31585/jbba-9-1-(2)2026

## 13. Contact

**Project**: QuantumHarmony by QuantumVerse Protocols
**Repository**: https://github.com/Paraxiom/quantumharmony
**Security**: security@quantumverseprotocols.com

---

*This document describes the system as implemented. Version 2.0, January 2026.*
