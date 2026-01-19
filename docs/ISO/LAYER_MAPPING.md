# ISO 23257 Reference Architecture Layer Mapping

## Overview

This document maps QuantumHarmony components to the ISO 23257:2022 DLT Reference Architecture layers.

**Standard:** ISO 23257:2022 - Blockchain and distributed ledger technologies — Reference architecture

---

## Layer Architecture

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    QUANTUMHARMONY ISO 23257 LAYER MAPPING                    │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │ LAYER 5: USER LAYER                                                   │  │
│  │ ISO: End-user applications and interfaces                             │  │
│  ├───────────────────────────────────────────────────────────────────────┤  │
│  │ QH Component: node-operator-dashboard/                                │  │
│  │                                                                       │  │
│  │ Files:                                                                │  │
│  │   • dashboard/index.html - Main operator interface                    │  │
│  │   • index.html - Landing page                                         │  │
│  │                                                                       │  │
│  │ Functions:                                                            │  │
│  │   • Validator management (approve/remove validators)                  │  │
│  │   • QRNG signal monitoring and fetching                               │  │
│  │   • Oracle reporter management                                        │  │
│  │   • Network health visualization                                      │  │
│  │   • Transaction submission                                            │  │
│  └───────────────────────────────────────────────────────────────────────┘  │
│                                    │                                         │
│                                    ▼                                         │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │ LAYER 4: API LAYER                                                    │  │
│  │ ISO: Interfaces for external system communication                     │  │
│  ├───────────────────────────────────────────────────────────────────────┤  │
│  │ QH Component: node/src/rpc/                                           │  │
│  │                                                                       │  │
│  │ Files:                                                                │  │
│  │   • oracle_rpc.rs - Oracle signal submission                          │  │
│  │   • threshold_qrng_rpc.rs - QRNG entropy retrieval                    │  │
│  │   • priority_queue_rpc.rs - Signal queue management                   │  │
│  │   • gateway_rpc.rs - Transaction gateway                              │  │
│  │   • notarial_rpc.rs - Document attestation                            │  │
│  │                                                                       │  │
│  │ Protocol: JSON-RPC 2.0 over HTTP/WebSocket                            │  │
│  │ Port: 9944 (default)                                                  │  │
│  └───────────────────────────────────────────────────────────────────────┘  │
│                                    │                                         │
│                                    ▼                                         │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │ LAYER 3: SMART CONTRACT LAYER                                         │  │
│  │ ISO: Business logic and automated agreements                          │  │
│  ├───────────────────────────────────────────────────────────────────────┤  │
│  │ QH Component: pallets/                                                │  │
│  │                                                                       │  │
│  │ Core Pallets:                                                         │  │
│  │   • pallets/oracle/ - External data feeds, reporter management        │  │
│  │   • pallets/validator-governance/ - Validator voting system           │  │
│  │   • pallets/substrate-validator-set/ - Validator set management       │  │
│  │   • pallets/notarial/ - Document attestation                          │  │
│  │                                                                       │  │
│  │ Additional Pallets:                                                   │  │
│  │   • pallets/stablecoin/ - Stable value token                          │  │
│  │   • pallets/mesh-forum/ - On-chain communication                      │  │
│  │   • pallets/ricardian-contracts/ - Legal contract binding             │  │
│  │   • pallets/fideicommis/ - Trust arrangements                         │  │
│  │   • pallets/academic-vouch/ - Credential verification                 │  │
│  └───────────────────────────────────────────────────────────────────────┘  │
│                                    │                                         │
│                                    ▼                                         │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │ LAYER 2: LEDGER SERVICES LAYER                                        │  │
│  │ ISO: Consensus, state management, transaction processing              │  │
│  ├───────────────────────────────────────────────────────────────────────┤  │
│  │ QH Component: runtime/                                                │  │
│  │                                                                       │  │
│  │ Files:                                                                │  │
│  │   • runtime/src/lib.rs - Runtime configuration                        │  │
│  │   • runtime/src/weights.rs - Transaction weights                      │  │
│  │                                                                       │  │
│  │ Services:                                                             │  │
│  │   • BABE consensus (block production)                                 │  │
│  │   • GRANDPA finality                                                  │  │
│  │   • State trie management                                             │  │
│  │   • Transaction pool                                                  │  │
│  │   • Block import queue                                                │  │
│  └───────────────────────────────────────────────────────────────────────┘  │
│                                    │                                         │
│                                    ▼                                         │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │ LAYER 1: INFRASTRUCTURE LAYER                                         │  │
│  │ ISO: Network, storage, compute resources                              │  │
│  ├───────────────────────────────────────────────────────────────────────┤  │
│  │ QH Component: node/src/                                               │  │
│  │                                                                       │  │
│  │ Network:                                                              │  │
│  │   • entropy_gossip.rs - P2P signal propagation                        │  │
│  │   • libp2p networking (port 30333)                                    │  │
│  │   • Kademlia DHT for peer discovery                                   │  │
│  │                                                                       │  │
│  │ Cryptography:                                                         │  │
│  │   • crates/falcon-ffi/ - Falcon-1024 post-quantum signatures          │  │
│  │   • threshold_qrng.rs - K-of-M entropy combination                    │  │
│  │   • SPHINCS+ keystore                                                 │  │
│  │                                                                       │  │
│  │ Storage:                                                              │  │
│  │   • RocksDB backend                                                   │  │
│  │   • Chain data in /data volume                                        │  │
│  └───────────────────────────────────────────────────────────────────────┘  │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## RPC Endpoint Documentation (Layer 4)

### Oracle RPC

| Method | Parameters | Returns | Description |
|--------|------------|---------|-------------|
| `oracle_submitSignal` | `{type, data, signature}` | `{hash, status}` | Submit oracle data |
| `oracle_getAvailableSignals` | `{filter?}` | `[Signal]` | List available signals |
| `oracle_acceptExternalSignal` | `{signal_id, reporter_id}` | `{success}` | Accept signal from reporter |
| `oracle_getReporters` | `{}` | `[Reporter]` | List approved reporters |

### QRNG RPC

| Method | Parameters | Returns | Description |
|--------|------------|---------|-------------|
| `qrng_getEntropy` | `{bytes}` | `{entropy, qber, source}` | Get quantum random bytes |
| `qrng_fetchFromCrypto4a` | `{}` | `{entropy, timestamp}` | Fetch from Crypto4A simulator |
| `qrng_getPoolStatus` | `{}` | `{size, sources, last_update}` | Pool health status |
| `qrng_pushToQueue` | `{signal}` | `{queued}` | Add signal to priority queue |

### Gateway RPC

| Method | Parameters | Returns | Description |
|--------|------------|---------|-------------|
| `gateway_submit` | `{from, to, amount, nonce, secretKey, genesisHash}` | `{hash, segment, status}` | Submit signed transaction |
| `gateway_getNonce` | `{address}` | `{nonce}` | Get account nonce |

### Notarial RPC

| Method | Parameters | Returns | Description |
|--------|------------|---------|-------------|
| `notarial_attest` | `{document_hash, metadata}` | `{attestation_id}` | Attest document |
| `notarial_verify` | `{attestation_id}` | `{valid, timestamp, attester}` | Verify attestation |

---

## State Transitions (Layer 2)

### Block Production Flow

```
1. Transaction Pool
   │
   ├─► Validate transaction signatures (Falcon-1024)
   ├─► Check nonce and balance
   └─► Queue for block inclusion
   │
2. BABE Block Authoring
   │
   ├─► Select transactions by priority
   ├─► Execute runtime calls
   └─► Produce block with VRF proof
   │
3. GRANDPA Finality
   │
   ├─► Validators vote on block
   ├─► 2/3+ agreement = finalized
   └─► Finalized blocks are immutable
```

### State Storage Structure

```
Storage Root
├── System
│   ├── Account (nonces, balances)
│   ├── BlockHash (history)
│   └── Events (per-block)
├── ValidatorSet
│   ├── Validators (current set)
│   ├── Proposals (pending)
│   └── Votes (per-proposal)
├── Oracle
│   ├── Reporters (approved)
│   ├── ReporterProposals (pending)
│   ├── Feeds (data feeds)
│   └── Signals (received)
└── Notarial
    ├── Attestations (documents)
    └── Metadata (per-attestation)
```

---

## Cross-Layer Communication

```
┌─────────────────────────────────────────────────────────────────┐
│                    CROSS-LAYER DATA FLOW                         │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  User Action (Layer 5)                                          │
│       │                                                         │
│       ▼                                                         │
│  Dashboard: "Fetch from Crypto4A"                               │
│       │                                                         │
│       ▼                                                         │
│  RPC Call (Layer 4)                                             │
│  POST /rpc { method: "qrng_fetchFromCrypto4a" }                 │
│       │                                                         │
│       ▼                                                         │
│  HTTP Fetch → crypto4a-simulator:8001                           │
│       │                                                         │
│       ▼                                                         │
│  Entropy Processing (Layer 1)                                   │
│  threshold_qrng.rs: combine K-of-M sources                      │
│       │                                                         │
│       ▼                                                         │
│  Signal Creation (Layer 3)                                      │
│  Oracle pallet: create Signal struct                            │
│       │                                                         │
│       ▼                                                         │
│  P2P Gossip (Layer 1)                                           │
│  entropy_gossip.rs: propagate to peers                          │
│       │                                                         │
│       ▼                                                         │
│  State Update (Layer 2)                                         │
│  Runtime: update Signals storage                                │
│       │                                                         │
│       ▼                                                         │
│  Event Emission                                                 │
│  SignalReceived { source, type, hash }                          │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

---

## Compliance Notes

### ISO 23257 Requirements Met

- [x] Clear layer separation
- [x] Documented interfaces between layers
- [x] Standardized API protocols (JSON-RPC 2.0)
- [x] State management documentation
- [x] Network protocol specification

### Deviations

| ISO Recommendation | QH Implementation | Rationale |
|--------------------|-------------------|-----------|
| RESTful API option | JSON-RPC only | Substrate ecosystem standard |
| SQL database option | RocksDB | Optimized for blockchain workloads |
| Traditional PKI | Post-quantum (Falcon-1024) | Future-proof security |

---

## References

- [ISO 23257:2022](https://www.iso.org/standard/75093.html)
- [Substrate Architecture](https://docs.substrate.io/learn/architecture/)
- [JSON-RPC 2.0 Specification](https://www.jsonrpc.org/specification)
