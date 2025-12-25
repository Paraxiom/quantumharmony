# QuantumHarmony Light Paper

**Version 1.0 - December 2024**

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
| Finality Gadget | GRANDPA (BLS) | Removed (Aura-only consensus) |
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

### 2.3 Consensus

**Current model**: Aura (Authority Round) block production without GRANDPA finality.

**Finality**: Probabilistic finality through block depth (similar to Bitcoin). A block is considered final after sufficient confirmations.

**Why no GRANDPA**: GRANDPA uses BLS aggregate signatures, which rely on elliptic curve pairings vulnerable to quantum attacks.

### 2.4 QKD Integration (Optional)

**What it is**: Interface for Quantum Key Distribution hardware to provide true quantum randomness.

**Current state**: Pallet exists (`pallet-qkd-client`); hardware integration requires physical QKD devices.

**Use case**: When connected to QKD hardware (e.g., Nokia QKD systems), provides entropy for validator selection that is theoretically unpredictable.

## 3. Governance System

### 3.1 Standard Substrate Governance
QuantumHarmony includes standard Substrate governance pallets:
- Democracy (referenda voting)
- Collective (council/committee management)
- Treasury (on-chain funds management)
- Scheduler (timed governance actions)

### 3.2 Academic Vouching (`pallet-academic-vouch`)

**Purpose**: Allow verified academics to vouch for applicants to specialized programs.

**How it works**:
1. Academic submits registration with credentials
2. Existing academics vote on registration
3. Registered academics can vouch for program applicants
4. Applicants accepted when vouch threshold met

**Use case**: Architecture Program applicant needs vouches from registered architects/academics.

### 3.3 Ricardian Contracts (`pallet-ricardian-contracts`)

**What it is**: On-chain storage and management of human-readable legal contracts with machine-executable terms.

**Features**:
- Contract creation with hash of legal text
- Multi-party signing workflow
- Amendment system
- State transitions: Draft -> Active -> Executed/Terminated

**Contract types supported**: Academic Program, Partnership, Service Agreement, Employment, Licensing, Custom.

### 3.4 Notarial Services (`pallet-notarial`)

**What it is**: Document timestamping and attestation system.

**Features**:
- Store document hash with timestamp
- Witness signatures for certification
- Certificate generation
- Revocation capability

**What it proves**: A document with a specific hash existed at a specific block/time.

## 4. Current State

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

## 5. Token Economics

**Token**: QHY
**Decimals**: 18
**Initial distribution**: Genesis validators

**Reward mechanism**: `pallet-validator-rewards` distributes block rewards to active validators.

**Transaction fees**: Standard Substrate weight-based fees.

## 6. Limitations and Honest Assessment

### What This Is
- A post-quantum secure blockchain framework
- A working testnet demonstrating the concepts
- An integration of NIST-standardized post-quantum cryptography into Substrate

### What This Is Not
- A production-ready mainnet (yet)
- A guarantee against all quantum attacks
- A replacement for proper security audits

### Known Trade-offs
1. **Larger signatures**: SPHINCS+ signatures are 8-50KB vs 64 bytes for Ed25519
2. **No instant finality**: Without GRANDPA, finality is probabilistic
3. **Compatibility**: Not compatible with standard Substrate tooling that expects Ed25519/Sr25519

### Open Questions
- Optimal SPHINCS+ parameter selection for blockchain use
- Performance at scale with larger signatures
- Bridge compatibility with other chains

## 7. Comparison with Alternatives

| Feature | QuantumHarmony | Standard Substrate | QRL |
|---------|----------------|-------------------|-----|
| Signature Scheme | SPHINCS+ | Ed25519/Sr25519 | XMSS |
| Hash Function | Keccak-256 | Blake2b | SHA-256 |
| Finality | Probabilistic | GRANDPA (instant) | PoW |
| Stateless Signatures | Yes | N/A | No (stateful) |
| Substrate-based | Yes | Yes | No |

## 8. References

1. NIST Post-Quantum Cryptography Standardization (2024)
2. SPHINCS+ Specification (NIST FIPS 205)
3. Substrate Developer Documentation
4. Grover's Algorithm - Quantum Search (1996)
5. Shor's Algorithm - Quantum Factoring (1994)

## 9. Contact

**Project**: QuantumHarmony by QuantumVerse Protocols
**Technical Lead**: Sylvain Cormier (Paraxiom)
**Repository**: https://github.com/QuantumVerseProtocols/quantumharmony

---

*This document describes the system as implemented. No forward-looking statements or projections are made.*
