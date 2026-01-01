# QuantumHarmony Light Paper

**Version 1.5 - January 2025**

**DOI**: [Pending Zenodo Publication]

**Repository**: https://github.com/Paraxiom/quantumharmony

> **Changelog v1.5**: Added Web Interface section. Added Research Publications with DOIs (6 papers on Zenodo). Expanded references.
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
- **Testnet**: Operational with 3 validators
- **Block time**: 6 seconds
- **Consensus**: Aura (proof of authority)

### What Works
- Block production with Aura
- SPHINCS+ signature verification in pallets
- All governance pallets
- Academic vouch, Ricardian contracts, Notarial pallets
- Docker deployment

### What's In Progress
- WASM runtime upgrade mechanism
- Full SPHINCS+ integration in transaction signing
- QKD hardware integration testing

### What's Not Done
- Production mainnet launch
- Full security audit
- Hardware QKD production deployment

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

## 8. Comparison with Alternatives

| Feature | QuantumHarmony | Standard Substrate | QRL |
|---------|----------------|-------------------|-----|
| Signature Scheme | SPHINCS+ / Falcon1024 | Ed25519/Sr25519 | XMSS |
| Hash Function | Keccak-256 | Blake2b | SHA-256 |
| Finality | Deterministic (Coherence Gadget) | GRANDPA (BFT) | PoW |
| Stateless Signatures | Yes | N/A | No (stateful) |
| Substrate-based | Yes | Yes | No |
| Quantum Hardware Support | Yes (Toshiba QKD, QRNG) | No | No |

## 9. Web Interface

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

## 10. Research Publications

Theoretical foundations published on Zenodo with DOIs:

| Paper | Topic | DOI |
|-------|-------|-----|
| ERLHS | Hamiltonian framework for coherence-preserving ML | 10.5281/zenodo.17928909 |
| Karmonic Mesh | O(N log N) spectral consensus on toroidal manifolds | 10.5281/zenodo.17928991 |
| Proof of Coherence | QKD-based distributed consensus mechanism | 10.5281/zenodo.17929054 |
| Toroidal Mesh | 10K TPS with SPHINCS+ via parallel verification | 10.5281/zenodo.17931222 |
| Toroidal Governance | Tonnetz manifold governance (defensive publication) | 10.5281/zenodo.17929091 |
| Augmented Democracy | Coherence-constrained democratic infrastructure | Preprint |

## 11. References

1. NIST Post-Quantum Cryptography Standardization (2024)
2. SPHINCS+ Specification (NIST FIPS 205)
3. Falcon Specification (NIST FIPS 206)
4. ML-KEM Specification (NIST FIPS 203)
5. Substrate Developer Documentation
6. ETSI GS QKD 014 - QKD Key Delivery API
7. Grover's Algorithm - Quantum Search (1996)
8. Shor's Algorithm - Quantum Factoring (1994)

## 12. Contact

**Project**: QuantumHarmony by QuantumVerse Protocols
**Technical Lead**: Sylvain Cormier (Paraxiom)
**Repository**: https://github.com/QuantumVerseProtocols/quantumharmony

---

*This document describes the system as implemented. No forward-looking statements or projections are made.*
