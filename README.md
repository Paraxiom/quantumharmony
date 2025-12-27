# QuantumHarmony Blockchain

> **Technical Preview v0.30.0** - Research Testnet
>
> This is an **experimental post-quantum blockchain** for research and development purposes.
>
> **NOT FOR PRODUCTION USE** - No economic security guarantees. APIs may change. Not audited.

---

A post-quantum secure Layer 1 blockchain built on Substrate, featuring SPHINCS+ signatures, quantum-resistant consensus, and innovative governance mechanisms including academic vouching and on-chain Ricardian contracts.

## Status

| Component | Status |
|-----------|--------|
| Post-Quantum Crypto (SPHINCS+) | Tested |
| Consensus (Aura) | Operational |
| Validator Rewards | Tested |
| Governance Pallets | Experimental |
| QKD Integration | Interface Ready |
| Security Audit | Pending |
| Fuzzing/Adversarial Tests | Partial |

**Current Deployment**: Technical preview testnet with 3 validators.

## Overview

QuantumHarmony is a research blockchain that replaces quantum-vulnerable cryptographic primitives (ECDSA, Ed25519, GRANDPA) with post-quantum alternatives. The chain uses SPHINCS+ hash-based signatures (NIST-standardized, stateless) and Keccak-256 hashing throughout.

## Core Security Features

### Post-Quantum Cryptography
- **SPHINCS+**: Stateless hash-based signatures (NIST PQC winner) - replaces Ed25519/ECDSA
- **Keccak-256**: SHA-3 family hasher with 128-bit quantum security (Grover resistance)
- **No GRANDPA**: Removed quantum-vulnerable BLS-based finality gadget
- **Aura Consensus**: Block production without quantum-vulnerable components

### Quantum Key Distribution Integration
- Hardware QKD client support for true quantum randomness
- Quantum-enhanced VRF for validator selection
- Integration path for Nokia QKD hardware

## Pallets (Runtime Modules)

### Core Pallets
| Pallet | Description |
|--------|-------------|
| `pallet-sphincs-keystore` | SPHINCS+ key management and signature verification |
| `pallet-quantum-crypto` | Quantum cryptographic primitives and utilities |
| `pallet-proof-of-coherence` | Quantum coherence proof mechanisms |
| `pallet-consensus-level` | Adaptive 5-level consensus tracking (BFT → PQ-BFT → Coherence → QRNG → Full PoC) |
| `pallet-validator-entropy` | Entropy distribution for validator selection |
| `pallet-relay-coordination` | QKD relay network coordination |
| `pallet-runtime-segmentation` | Runtime security segmentation |

### Governance Pallets
| Pallet | Description |
|--------|-------------|
| `pallet-validator-governance` | Validator set management and voting |
| `pallet-dev-governance` | Development governance for upgrades |
| `pallet-democracy` | On-chain democratic voting |
| `pallet-collective` | Council and committee management |
| `pallet-treasury` | On-chain treasury management |
| `pallet-scheduler` | Scheduled governance actions |

### Legal/Academic Pallets
| Pallet | Description |
|--------|-------------|
| `pallet-academic-vouch` | Academic credential registration and vouching for programs |
| `pallet-ricardian-contracts` | Human+machine readable legal contracts on-chain |
| `pallet-notarial` | Document timestamping, attestation, and certification |

### Utility Pallets
| Pallet | Description |
|--------|-------------|
| `pallet-validator-rewards` | Block reward distribution |
| `pallet-identity` | On-chain identity management |
| `pallet-proxy` | Account proxy and delegation |
| `pallet-preimage` | Preimage storage for governance |

## Quick Start

### Prerequisites
- Rust 1.75+ with nightly toolchain
- Docker (optional, for containerized deployment)

### Build from Source
```bash
git clone https://github.com/QuantumVerseProtocols/quantumharmony.git
cd quantumharmony
cargo build --release
```

### Run a Node
```bash
./target/release/quantumharmony-node \
    --chain=production \
    --name="MyNode" \
    --rpc-external \
    --rpc-cors=all \
    --rpc-methods=Safe
```

### Docker Deployment
```bash
# Pull the latest image
docker pull sylvaincormier/quantumharmony-node:latest

# Run with docker-compose
docker-compose up -d
```

See `docs/DOCKER.md` for detailed Docker deployment instructions.

## Network Information

### Production Testnet
- **Chain Spec**: `production`
- **RPC Endpoints**: Contact team for access
- **Block Time**: 6 seconds
- **Token**: QHY (18 decimals)

### Bootnodes
Configured in chain specification for automatic peer discovery.

## Architecture

```
quantumharmony/
├── node/                    # Node implementation
├── runtime/                 # Chain runtime (WASM)
│   └── src/
│       ├── lib.rs          # Runtime configuration
│       └── quantum_hasher.rs # Keccak-256 hasher
├── pallets/                 # Custom pallets
│   ├── academic-vouch/      # Academic vouching system
│   ├── ricardian-contracts/ # Legal contracts
│   ├── notarial/           # Document attestation
│   ├── sphincs-keystore/   # PQ signatures
│   └── ...                 # Other pallets
├── docs/                    # Documentation
└── docker/                  # Docker configurations
```

## Documentation

- `docs/ARCHITECTURE.md` - Full system architecture
- `docs/CRYPTOGRAPHIC_STACK_INTEGRATION.md` - Crypto details
- `docs/RUNTIME_UPGRADE_GUIDE.md` - Runtime upgrade process
- `docs/TESTNET_ONBOARDING.md` - Joining the testnet
- `docs/DOCKER.md` - Docker deployment

## Governance Features

### Academic Vouching
Registered academics can vouch for applicants to specialized programs (e.g., Architecture Program). Requires:
- Academic registration with credential verification
- Minimum vouch threshold for acceptance
- On-chain voting for academic registration

### Ricardian Contracts
Human-readable legal contracts with machine-executable terms:
- Multi-party signing workflow
- Amendment system
- Contract types: Academic, Partnership, Service, Employment, Licensing

### Notarial Services
On-chain document attestation:
- Timestamped hash attestation
- Witness certification system
- Certificate generation
- Permanent, immutable records

## Development

### Running Tests
```bash
cargo test --workspace
```

### Building WASM Runtime
```bash
SKIP_WASM_BUILD=0 cargo build --release -p quantumharmony-runtime
```

### Runtime Upgrade
See `docs/RUNTIME_UPGRADE_GUIDE.md` for forkless upgrade instructions.

## Security Considerations

- All signatures use SPHINCS+ (post-quantum secure)
- No BLS signatures (quantum vulnerable)
- No GRANDPA finality (replaced with probabilistic finality)
- Keccak-256 provides 128-bit quantum security
- QKD integration for hardware entropy (optional)

## Research Publications

The theoretical foundations of QuantumHarmony are documented in peer-archived publications:

| Paper | Topic | DOI |
|-------|-------|-----|
| ERLHS | Hamiltonian coherence framework | [10.5281/zenodo.17928909](https://doi.org/10.5281/zenodo.17928909) |
| Karmonic Mesh | O(N log N) spectral consensus | [10.5281/zenodo.17928991](https://doi.org/10.5281/zenodo.17928991) |
| Proof of Coherence | QKD-based distributed consensus | [10.5281/zenodo.17929054](https://doi.org/10.5281/zenodo.17929054) |
| Toroidal Mesh | 10K TPS with SPHINCS+ | [10.5281/zenodo.17931222](https://doi.org/10.5281/zenodo.17931222) |

## License

Apache-2.0

## Contact

QuantumVerse Protocols
- Technical: Sylvain Cormier (Paraxiom)
- Repository: https://github.com/QuantumVerseProtocols/quantumharmony
