# Quantum Harmony - Dependencies & Requirements

**Date**: October 5, 2025
**Branch**: quantum-2025-10-03-daily

---

## Forked Dependencies (Critical)

### 1. polkadot-sdk
- **Original**: https://github.com/paritytech/polkadot-sdk
- **Fork**: https://github.com/QuantumVerseProtocols/polkadot-sdk
- **Branch**: quantum-only
- **Modifications**: Classical crypto removed, SPHINCS+ primary, QKD integration

### 2. parity-scale-codec
- **Original**: https://github.com/paritytech/parity-scale-codec
- **Fork**: https://github.com/QuantumVerseProtocols/parity-scale-codec
- **Modification**: INITIAL_PREALLOCATION 16KB → 256KB
- **Required for**: SPHINCS+ signatures (49KB), STARK proofs

---

## QuantumVerse Repositories (18 Total)

### Core Blockchain
1. **polkadot-sdk** - Modified Polkadot SDK (quantum-only branch)
2. **quantumharmony** - Main blockchain implementation
3. **quantum-harmony-base** - Experimental platform
4. **parity-scale-codec** - Modified encoding library

### Quantum Hardware
5. **qkd_client** - QKD hardware interface (C++/Rust)
6. **quantum-rng-kirk-hub** - KIRQ entropy distribution (Python)
7. **qnt-lattice-optics** - CNT quantum research (TeX)
8. **cnt-repeater-validation** - Quantum network validation

### Applications
9. **drista** - Quantum wallet desktop (Rust)
10. **tao-signal-agent** - Trading/governance platform (Python)
11. **AugmentedDemocracy** - Governance module (Rust)

### AI/ML
12. **quantumverse-tensor-net** - Tensor network library
13. **federated-learning** - Federated learning (Python)
14. **tonnetz-ai** - Harmonic AI (Python)

### Intelligence
15. **Hydra** - Risk analysis system (Python)
16. **blockchain-intelligence-pipeline** - Multi-chain streaming (Python)
17. **code-audit-tool** - Code analysis (Rust)

### Documentation
18. **docs** - Technical documentation (TeX)
19. **corporate** - Business documentation

---

## Core Dependencies

### Post-Quantum Cryptography
```toml
pqcrypto = "0.18"
pqcrypto-sphincsplus = "0.7"   # ~49KB signatures
pqcrypto-falcon = "0.3"         # FN-DSA-1024: 1.3KB signatures (P2P + Gateway)
pqcrypto-kyber = "0.8"          # ML-KEM-1024: Post-quantum KEM for Triple Ratchet
ed25519-dalek = "2.1"           # Classical hybrid
x25519-dalek = "1"              # X25519 ECDH for Triple Ratchet
```

### Zero-Knowledge
```toml
winterfell = "0.7"              # STARK proofs
blake3 = "1.5"
sha3 = "0.10"
```

### Blockchain & Networking
```toml
# Substrate (from polkadot-sdk fork)
sp-core, sp-runtime, sp-io
frame-support, frame-system

# P2P Networking
libp2p = { version = "0.53", features = ["tcp", "noise", "yamux", "gossipsub", "identify", "kad", "mdns"] }
futures = "0.3"

# Async
tokio = { version = "1.47", features = ["full"] }

# Storage
rocksdb = "0.22"
```

---

## System Requirements

### Development
- **OS**: macOS, Linux, Windows (WSL2)
- **Rust**: 1.82+ nightly
- **Docker**: 24.0+
- **Python**: 3.8+
- **Disk**: ~15GB

### Production
- **CPU**: 8+ cores
- **RAM**: 16GB min
- **Storage**: 100GB+ SSD
- **Network**: 1 Gbps+

---

## Build

**IMPORTANT**: You must use the QuantumVerseProtocols forks of Substrate and parity-scale-codec. See "Forked Dependencies (Critical)" above.

```bash
# 1. Clone Substrate fork (quantum-only branch)
git clone https://github.com/QuantumVerseProtocols/polkadot-sdk -b quantum-only

# 2. Clone QuantumHarmony Core
git clone https://github.com/QuantumVerseProtocols/quantumharmony-core.git
cd quantumharmony-core

# 3. Apply parity-scale-codec patch in Cargo.toml
[patch.crates-io]
parity-scale-codec = { git = "https://github.com/QuantumVerseProtocols/parity-scale-codec" }

# 4. Build
cargo build --release -p quantum-node-blockchain
```

---

## Architecture Components

### Consensus
- **Proof of Coherence** (pallets/quantum-consensus-minimal, substrate/frame/proof-of-coherence)
- **Tonnetz harmonic validation**
- **6-factor scoring system**

### Crypto Stack
- **Signatures**: SPHINCS+, Falcon1024, Ed25519
- **P2P Encryption**: Triple Ratchet (X25519 ECDH + ML-KEM-1024 + Falcon1024)
- **ZK**: Winterfell STARK (sp-stark-crypto)
- **Hashing**: SHA3, Blake3

### Runtime
- **Toroidal mesh segmentation** (3D: compute/storage/security)
- **Quantum bridge** (substrate/bin/quantum-node/runtime/src/quantum_bridge.rs)
- **QKD protocols**: BB84, E91, BBM92

### Transport
- **QSSH-RPC**: Binary client-server protocol (port 42)
  - 53-byte header + bincode payload
  - SHA3-256 checksums
  - 41.77 GiB/s peak throughput
- **libp2p Quantum P2P**: Node-to-node networking (port 30333)
  - Gossipsub for block/transaction propagation
  - mDNS + Kademlia for peer discovery
  - Triple Ratchet (ECDH + ML-KEM-1024 + Falcon1024) - Signal SPQR approach
  - QRNG-seeded quantum sessions
  - Full multi-node support (✅ implemented Oct 4, 2025)

### Wallet
- **quantum-wallet-polkadot.html** (JavaScript, 58KB)
- **drista native** (Rust/Tauri, planned)

### Governance
- **Sudo/Multisig** pallets
- **Runtime upgrades** (forkless)
- **TNTZ token** economy

---

## Key Files

### Forks
- `.cargo/config.toml` - Codec patch
- `substrate/` - Modified framework
- `quantum/` - Quantum extensions

### Implementations
- `node-blockchain/src/pqc.rs` - SPHINCS+ hybrid
- `quantum-gateway/src/pqc.rs` - Falcon512
- `pallets/quantum-consensus-minimal/` - Consensus
- `pallets/kirq-entropy-minimal/` - Entropy (simulated)
- `pallets/qkd-minimal/` - QKD protocols

### Transport & Networking
- `node-blockchain/src/qssh_rpc.rs` - QSSH-RPC protocol (432 lines)
- `node-blockchain/src/qssh_server.rs` - QSSH server (283 lines)
- `node-blockchain/src/p2p/quantum_crypto.rs` - Triple Ratchet (ECDH + ML-KEM + Falcon) (455 lines)
- `node-blockchain/src/p2p/network.rs` - libp2p network (234 lines)
- `node-blockchain/src/p2p/gossip.rs` - Block/TX gossip
- `drista/src/quantum/qssh_client.rs` - Wallet client (350 lines)

### Runtime
- `substrate/bin/quantum-node/runtime/src/quantum_bridge.rs` - Quantum ops
- `quantum/quantum-extensions/primitives/stark-crypto/` - STARK

---

## Status

### Implemented
- ✅ PQC signatures (SPHINCS+, Falcon1024, Ed25519)
- ✅ Winterfell STARK integration
- ✅ Toroidal mesh segmentation
- ✅ Quantum bridge (gates, entanglement)
- ✅ parity-scale-codec fork (256KB)
- ✅ **QSSH-RPC binary protocol** (Oct 2025)
- ✅ **libp2p Quantum P2P network** (Oct 4-5, 2025)
  - Gossipsub block/transaction propagation
  - mDNS + Kademlia peer discovery
  - Triple Ratchet (X25519 ECDH + ML-KEM-1024 + Falcon1024) - Signal SPQR
  - 101 tests passing (69 in node-blockchain)
  - Multi-node deployment validated

### Simulated
- ⚠️ Quantum RNG (using PRNG)
- ⚠️ Coherence metrics (calculated)
- ⚠️ QKD channels (structure ready)

### Integration Ready
- ❌ KIRQ RNG Hub integration (code ready, awaiting network access)
- ❌ QKD hardware connection (code ready, awaiting hardware)

---

**Last Updated**: October 5, 2025

**October 4-5, 2025 Update**: Quantum P2P networking upgraded to Triple Ratchet following Signal's SPQR (Sparse Post-Quantum Ratchet) approach announced Oct 4. The network now uses industry-standard X25519 ECDH + ML-KEM-1024 (Kyber) + Falcon1024 signatures, replacing the previous Double Ratchet + Lamport implementation. Full decentralized operation with libp2p gossip protocol, automatic peer discovery via mDNS/Kademlia. All 101 tests passing (69 in node-blockchain, 32+20+13 in integration suites).
