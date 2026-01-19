# ISO/TR 23576 Security Controls

## Overview

This document maps QuantumHarmony security controls to ISO/TR 23576:2020 requirements.

**Standard:** ISO/TR 23576:2020 - Blockchain and distributed ledger technologies — Security management of digital asset custodians

---

## Control Categories

### 1. Cryptographic Controls

| Control ID | ISO Requirement | QH Implementation | Status |
|------------|-----------------|-------------------|--------|
| CRYPTO-001 | Quantum-resistant signatures | Falcon-1024 (NIST Level V) | Implemented |
| CRYPTO-002 | Secure key generation | Hardware QRNG + threshold | Implemented |
| CRYPTO-003 | Key storage protection | HSM support, encrypted keystore | Implemented |
| CRYPTO-004 | Signature verification | All transactions verified | Implemented |
| CRYPTO-005 | Hash algorithm security | BLAKE2b-256 | Implemented |

#### CRYPTO-001: Post-Quantum Signatures

```rust
// crates/falcon-ffi/src/lib.rs

/// Falcon-1024 provides NIST PQC Level V security
/// - 256-bit classical security
/// - Resistant to Shor's algorithm (quantum)
/// - Signature size: ~1280 bytes
/// - Verification: O(n log n)

pub fn falcon_sign(message: &[u8], secret_key: &[u8]) -> Result<Vec<u8>, Error>;
pub fn falcon_verify(message: &[u8], signature: &[u8], public_key: &[u8]) -> bool;
```

#### CRYPTO-002: Threshold QRNG

```rust
// node/src/threshold_qrng.rs

/// K-of-M threshold combination ensures:
/// - Tolerance of M-K source failures
/// - No single source can bias output
/// - QBER validation per source

pub struct ThresholdQrng {
    sources: Vec<QrngSource>,
    k: usize,  // Minimum required
    m: usize,  // Total sources
}

impl ThresholdQrng {
    pub fn combine(&self) -> Result<[u8; 32], Error> {
        // XOR combination of K successful sources
        // Validate QBER < 0.01 for each
    }
}
```

---

### 2. Access Controls

| Control ID | ISO Requirement | QH Implementation | Status |
|------------|-----------------|-------------------|--------|
| ACCESS-001 | Role-based access | Validator/Reporter/User roles | Implemented |
| ACCESS-002 | Authentication | Falcon signatures for all calls | Implemented |
| ACCESS-003 | Authorization | On-chain permission checks | Implemented |
| ACCESS-004 | Privileged operations | Multi-sig governance | Implemented |
| ACCESS-005 | Session management | Nonce-based replay protection | Implemented |

#### ACCESS-001: Role Hierarchy

```
┌─────────────────────────────────────────────────────────────────┐
│                     ROLE HIERARCHY                               │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  Validator (Highest Privilege)                                  │
│  ├── Can: Produce blocks, vote on governance, approve reporters │
│  ├── Requires: Governance approval (2/3+ validators)            │
│  └── Keys: Falcon-1024 stored in HSM                            │
│       │                                                         │
│       ▼                                                         │
│  Reporter (Medium Privilege)                                    │
│  ├── Can: Submit oracle data, earn fees                         │
│  ├── Requires: Validator approval + stake                       │
│  └── Keys: Falcon-1024 in secure keystore                       │
│       │                                                         │
│       ▼                                                         │
│  User (Basic Privilege)                                         │
│  ├── Can: Send transactions, query state                        │
│  ├── Requires: Valid account with balance                       │
│  └── Keys: User-managed                                         │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

#### ACCESS-003: On-Chain Authorization

```rust
// pallets/oracle/src/lib.rs

#[pallet::call]
impl<T: Config> Pallet<T> {
    /// Only approved reporters can submit signals
    #[pallet::call_index(0)]
    pub fn submit_signal(
        origin: OriginFor<T>,
        signal: Signal,
    ) -> DispatchResult {
        let who = ensure_signed(origin)?;

        // Authorization check
        ensure!(
            Reporters::<T>::contains_key(&who),
            Error::<T>::NotApprovedReporter
        );

        // ... process signal
    }
}
```

---

### 3. Network Controls

| Control ID | ISO Requirement | QH Implementation | Status |
|------------|-----------------|-------------------|--------|
| NET-001 | Encrypted communication | Noise protocol (P2P), TLS 1.3 (RPC) | Implemented |
| NET-002 | Peer authentication | Node identity signatures | Implemented |
| NET-003 | Rate limiting | 100 req/s per IP default | Implemented |
| NET-004 | DDoS protection | Connection limits, request size limits | Implemented |
| NET-005 | Network segmentation | Separate P2P and RPC ports | Implemented |

#### NET-001: Transport Security

```
P2P Layer (port 30333):
┌─────────────────────────────────────────┐
│ Noise Protocol Framework                │
│ ├── XX handshake pattern               │
│ ├── ChaCha20-Poly1305 encryption       │
│ └── Curve25519 key exchange            │
└─────────────────────────────────────────┘

RPC Layer (port 9944):
┌─────────────────────────────────────────┐
│ TLS 1.3                                 │
│ ├── ECDHE key exchange                 │
│ ├── AES-256-GCM encryption             │
│ └── Certificate validation             │
└─────────────────────────────────────────┘
```

#### NET-003: Rate Limiting Configuration

```rust
// node/src/rpc/mod.rs

pub struct RpcConfig {
    /// Maximum requests per second per IP
    pub rate_limit: u32,  // default: 100

    /// Maximum request body size
    pub max_request_size: usize,  // default: 10MB

    /// Maximum concurrent connections
    pub max_connections: u32,  // default: 500

    /// Burst allowance
    pub burst_size: u32,  // default: 50
}
```

---

### 4. Operational Controls

| Control ID | ISO Requirement | QH Implementation | Status |
|------------|-----------------|-------------------|--------|
| OPS-001 | Logging | Structured JSON logs | Implemented |
| OPS-002 | Monitoring | Prometheus metrics | Implemented |
| OPS-003 | Alerting | Configurable thresholds | Implemented |
| OPS-004 | Backup | Chain data + keystore backup | Documented |
| OPS-005 | Disaster recovery | Multi-node redundancy | Documented |

#### OPS-001: Audit Logging

```rust
// Events emitted for audit trail

// Governance events
ValidatorApproved { who: AccountId, approved_by: Vec<AccountId> }
ValidatorRemoved { who: AccountId, reason: Vec<u8> }

// Oracle events
ReporterApproved { who: AccountId, stake: Balance }
SignalSubmitted { reporter: AccountId, signal_type: SignalType, hash: H256 }

// Transaction events
TransactionSubmitted { from: AccountId, to: AccountId, amount: Balance, nonce: u64 }
TransactionFinalized { hash: H256, block: BlockNumber }
```

#### OPS-002: Prometheus Metrics

```
# Exposed at :9615/metrics

# Consensus metrics
substrate_block_height{status="best"} 12345
substrate_block_height{status="finalized"} 12340
substrate_number_peers 8

# QRNG metrics
quantumharmony_qrng_pool_size 1024
quantumharmony_qrng_sources_healthy 4
quantumharmony_qrng_last_fetch_seconds 30

# Oracle metrics
quantumharmony_oracle_reporters_count 5
quantumharmony_oracle_signals_pending 12
quantumharmony_oracle_last_signal_age_seconds 15

# Transaction metrics
quantumharmony_tx_pool_size 42
quantumharmony_tx_throughput_per_second 150
```

---

### 5. Governance Controls

| Control ID | ISO Requirement | QH Implementation | Status |
|------------|-----------------|-------------------|--------|
| GOV-001 | Change management | On-chain governance voting | Implemented |
| GOV-002 | Validator approval | 2/3+ majority required | Implemented |
| GOV-003 | Emergency procedures | Sudo for emergencies (removable) | Implemented |
| GOV-004 | Upgrade mechanism | Forkless runtime upgrades | Implemented |
| GOV-005 | Audit trail | All votes recorded on-chain | Implemented |

#### GOV-001: Governance Flow

```
┌─────────────────────────────────────────────────────────────────┐
│                    GOVERNANCE FLOW                               │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  1. Proposal Submission                                         │
│     └── Any validator can propose                               │
│         └── Proposal stored on-chain with deadline              │
│                                                                  │
│  2. Voting Period                                               │
│     └── Duration: 100 blocks (configurable)                     │
│         └── Each validator: 1 vote (approve/reject)             │
│                                                                  │
│  3. Finalization                                                │
│     └── After voting period ends:                               │
│         ├── 2/3+ approve → Execute proposal                     │
│         └── Otherwise → Reject proposal                         │
│                                                                  │
│  4. Execution                                                   │
│     └── Automatic execution of approved proposals               │
│         └── Events emitted for audit                            │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

---

### 6. Data Protection Controls

| Control ID | ISO Requirement | QH Implementation | Status |
|------------|-----------------|-------------------|--------|
| DATA-001 | Data integrity | Merkle tree state root | Implemented |
| DATA-002 | Data availability | Block propagation gossip | Implemented |
| DATA-003 | Data confidentiality | Encrypted P2P, optional tx encryption | Partial |
| DATA-004 | Data retention | Configurable pruning | Implemented |
| DATA-005 | Data backup | RocksDB snapshot support | Implemented |

#### DATA-001: State Integrity

```
Block Header:
┌─────────────────────────────────────────┐
│ parent_hash: H256                       │
│ number: u32                             │
│ state_root: H256  ◄── Merkle root       │
│ extrinsics_root: H256                   │
│ digest: Vec<DigestItem>                 │
└─────────────────────────────────────────┘

State Trie:
         [state_root]
              │
    ┌─────────┼─────────┐
    │         │         │
 [System]  [Oracle]  [Balances]
    │         │         │
   ...       ...       ...

Any modification changes state_root
└── Validators verify state_root in blocks
```

---

## Compliance Matrix

| ISO/TR 23576 Section | Control IDs | Compliance |
|----------------------|-------------|------------|
| 5.2 Cryptographic security | CRYPTO-001 to CRYPTO-005 | Full |
| 5.3 Access control | ACCESS-001 to ACCESS-005 | Full |
| 5.4 Network security | NET-001 to NET-005 | Full |
| 5.5 Operational security | OPS-001 to OPS-005 | Full |
| 5.6 Governance | GOV-001 to GOV-005 | Full |
| 5.7 Data protection | DATA-001 to DATA-005 | Partial |

---

## References

- [ISO/TR 23576:2020](https://www.iso.org/standard/76072.html)
- [NIST Cybersecurity Framework](https://www.nist.gov/cyberframework)
- [CIS Controls](https://www.cisecurity.org/controls)
