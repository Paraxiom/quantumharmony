# QuantumHarmony

**The first post-quantum Layer 1 blockchain built from genesis.**

[![Tests](https://img.shields.io/badge/tests-950%20passing-brightgreen)](https://github.com/Paraxiom/quantumharmony)
[![Validators](https://img.shields.io/badge/validators-3%20live-blue)](https://github.com/Paraxiom/quantumharmony)
[![License](https://img.shields.io/badge/license-Apache%202.0-blue.svg)](LICENSE)

---

## Public Beta Testnet

**Live Network**: 3 production validators across Montreal, Beauharnois, and Frankfurt

| Metric | Value |
|--------|-------|
| Test Coverage | 950 unit & integration tests |
| Pallets | 23 custom runtime modules |
| Block Time | 6 seconds |
| Consensus | Proof of Coherence (PQ-BFT) |
| Signatures | SPHINCS+ (NIST PQC Standard) |
| Status | Pre-audit, seeking security review |

---

## Why QuantumHarmony?

Existing blockchains face an impossible migration problem. Campbell (2025) demonstrates that post-quantum migration for Bitcoin/Ethereum requires:
- **50% capacity loss** during transition
- **3x fee increase** for hybrid signatures
- **59x state bloat** for backwards compatibility
- **Zero immediate user benefit**

No rational validator coalition will vote for this.

**QuantumHarmony's approach**: Post-quantum from genesis. No migration governance, no backwards compatibility debt, no hybrid transition period.

---

## Technical Stack

### Cryptography
| Layer | Algorithm | Security Level |
|-------|-----------|----------------|
| Signatures | SPHINCS+-SHAKE-256s | 256-bit post-quantum |
| P2P Identity | Falcon-1024 | 256-bit post-quantum |
| Key Exchange | ML-KEM-1024 (Kyber) | 256-bit post-quantum |
| Hashing | Keccak-256 (SHA-3) | 128-bit post-quantum |
| Encryption | AES-256-GCM | 128-bit post-quantum |

### Consensus
- **Proof of Coherence**: BFT finality with Falcon-1024 signatures
- **Leader Rotation**: VRF-based quantum entropy selection
- **Finality**: Deterministic 2/3 supermajority (no GRANDPA/BLS)

### Scalability
- **512-segment toroidal mesh**: 8x8x8 parallel transaction processing
- **Target**: 10,000+ TPS with SPHINCS+ signatures

---

## Runtime Modules (Pallets)

### Quantum / Consensus
| Pallet | Description |
|--------|-------------|
| `pallet-quantum-crypto` | PQC key management (Falcon-1024, SPHINCS+, ML-KEM-1024) |
| `pallet-proof-of-coherence` | Proof-of-Coherence consensus mechanism |
| `pallet-topological-coherence` | Toroidal coherence scoring |
| `pallet-axiom-attestation` | On-chain AI task attestations with rate limiting |
| `pallet-sphincs-keystore` | SPHINCS+ key storage for runtime upgrades |
| `pallet-validator-entropy` | Quantum entropy contribution (QRNG) |
| `pallet-runtime-segmentation` | 8x8x8 toroidal mesh parallelization |

### Financial Infrastructure
| Pallet | Description |
|--------|-------------|
| `pallet-stablecoin` | QCAD collateralized stablecoin with liquidation |
| `pallet-fideicommis` | Quebec-style trusts (constituant/fiduciary/beneficiary) |
| `pallet-validator-rewards` | Staking, slashing, reward distribution |
| `pallet-pedersen-commitment` | Cryptographic commitments for privacy |
| `pallet-devonomics` | Developer economics and incentive alignment |

### Governance
| Pallet | Description |
|--------|-------------|
| `pallet-mesh-forum` | On-chain governance discussion forum |
| `pallet-dev-governance` | Developer governance proposals and voting |
| `pallet-validator-governance` | Validator-level governance |
| `pallet-substrate-validator-set` | Dynamic validator set management |
| `pallet-consensus-level` | Consensus level tracking |

### Legal / Notarial
| Pallet | Description |
|--------|-------------|
| `pallet-ricardian-contracts` | Human+machine readable legal contracts |
| `pallet-notarial` | Document attestation and certification |
| `pallet-academic-vouch` | Academic credential verification |

### Network
| Pallet | Description |
|--------|-------------|
| `pallet-relay-coordination` | QKD relay network management |
| `pallet-oracle` | External data oracle |
| `pallet-oracle-feeds` | Oracle data feed aggregation |
| `pallet-qkd-client` | QKD key distribution client |

### Node Components
| Component | Tests | Description |
|-----------|-------|-------------|
| Coherence Gadget | 25+ | PQ-BFT finality engine |
| Quantum P2P | 50+ | Falcon/Kyber secured networking |
| Triple Ratchet | 15+ | Forward-secret key rotation |
| Threshold QRNG | 10+ | Distributed quantum randomness |

---

## Quick Start

### Run a Node (Docker)
```bash
docker pull sylvaincormier/quantumharmony-node:v28.2-bgfl
docker-compose up -d
```

### Build from Source
```bash
git clone https://github.com/Paraxiom/quantumharmony.git
cd quantumharmony
cargo build --release
./target/release/quantumharmony-node --chain=production --name="MyNode"
```

### Run Tests
```bash
cargo test --workspace
# 950 tests across all pallets and node components
```

---

## Dependencies

QuantumHarmony requires forked Substrate dependencies with PQC modifications:

| Repository | Purpose |
|------------|---------|
| [Paraxiom/polkadot-sdk](https://github.com/Paraxiom/polkadot-sdk) | SPHINCS+ signatures, Falcon consensus, quantum entropy |
| [Paraxiom/parity-scale-codec](https://github.com/Paraxiom/parity-scale-codec) | Increased preallocation for PQC signature sizes |

---

## Documentation

- [LIGHTPAPER](docs/MD/LIGHTPAPER.md) - Technical overview and architecture
- [SECURITY.md](SECURITY.md) - Security policy and vulnerability reporting
- [TESTNET_ONBOARDING](docs/MD/TESTNET_ONBOARDING.md) - Join the testnet
- [RUNTIME_UPGRADE_GUIDE](RUNTIME_UPGRADE_GUIDE.md) - Forkless upgrades

---

## Formal Verification

Lean 4 + Mathlib v4.27.0 mathematical proofs — zero sorries.

| File | Scope | Theorems |
|------|-------|----------|
| `Consensus.lean` | BFT quorum intersection, finality uniqueness, supermajority implies majority | 8 |
| `Crypto.lean` | Keccak-256, SPHINCS+, Falcon parameters, block capacity (68+ txns/block) | 16 |
| `Toroidal.lean` | 8x8x8 torus (512 segments), diameter 12, spectral gap positivity | 9 |
| `QBER.lean` | 11% threshold < 14.6% BB84 max, average bounds, acceptance criteria | 14 |
| `STARK.lean` | STARK proof system parameters and bounds | 10 |
| `AxiomAttestation.lean` | BoundedVec bounds, rate limiting, storage footprint | 19 |

```bash
cd lean && lake build  # 0 errors, 0 sorries, 76 theorems
```

**Paper**: [810 Lean 4 Theorems for Post-Quantum Infrastructure](https://doi.org/10.5281/zenodo.18663125) (Zenodo, Mar 2026) — 76 theorems for QuantumHarmony, 810 total across 10 systems

---

## Research Publications

| Paper | Topic | DOI |
|-------|-------|-----|
| 810 Lean 4 Theorems | Formal verification across 10 PQ systems | [10.5281/zenodo.18663125](https://doi.org/10.5281/zenodo.18663125) |
| Defensive Technical Disclosure | Toroidal coherence methods — 4 embodiments | [10.5281/zenodo.18595753](https://doi.org/10.5281/zenodo.18595753) |
| Toroidal Logit Bias | Geometric constraints for LLM truthfulness | [10.5281/zenodo.18516477](https://doi.org/10.5281/zenodo.18516477) |
| PQ Transport Gateway | Replacing classical TLS on QKD control channels | [10.5281/zenodo.18786526](https://doi.org/10.5281/zenodo.18786526) |
| Proof of Coherence | QKD-based distributed consensus | [10.5281/zenodo.17929054](https://doi.org/10.5281/zenodo.17929054) |
| Toroidal Mesh | 10K TPS with SPHINCS+ | [10.5281/zenodo.17931222](https://doi.org/10.5281/zenodo.17931222) |
| ERLHS | Hamiltonian coherence framework | [10.5281/zenodo.17928909](https://doi.org/10.5281/zenodo.17928909) |
| Karmonic Mesh | O(N log N) spectral consensus | [10.5281/zenodo.17928991](https://doi.org/10.5281/zenodo.17928991) |

---

## Status

**Current Phase**: Public Beta Testnet

- [x] Core runtime with SPHINCS+ signatures
- [x] 3 production validators (geographically distributed)
- [x] 950 passing tests
- [x] 3-tier formal verification (Kani + Verus + Lean 4)
- [x] Docker deployment for node operators
- [x] Quantum P2P with Falcon-1024/ML-KEM-1024
- [ ] Security audit (seeking auditors)
- [ ] Mainnet launch

---

## License

Apache-2.0

## Contact

**QuantumVerse Protocols**
- GitHub: [Paraxiom/quantumharmony](https://github.com/Paraxiom/quantumharmony)
- Security: security@quantumverseprotocols.com
