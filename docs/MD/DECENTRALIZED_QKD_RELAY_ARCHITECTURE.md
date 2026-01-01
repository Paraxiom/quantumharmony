# Decentralized QKD Relay Architecture

**Document Version:** 1.1
**Created:** 2025-01-23
**Last Updated:** 2025-01-23
**Status:** Design Phase
**Authors:** Sylvain Cormier, Claude (Anthropic)

---

## Table of Contents

1. [Executive Summary](#executive-summary)
2. [Permissionless QKD Support](#permissionless-qkd-support)
3. [Problem Statement](#problem-statement)
4. [Decentralization Principles](#decentralization-principles)
5. [Architecture Overview](#architecture-overview)
6. [Component Stack](#component-stack)
7. [QKD Island Topology](#qkd-island-topology)
8. [Relay Selection Protocol](#relay-selection-protocol)
9. [QSSH Transport Layer](#qssh-transport-layer)
10. [STUN Decentralization](#stun-decentralization)
11. [Security Analysis](#security-analysis)
12. [Implementation Roadmap](#implementation-roadmap)

---

## Executive Summary

This document describes the fully decentralized architecture for connecting quantum key distribution (QKD) islands using validator-operated relays. The design eliminates centralization points while enabling validators behind corporate firewalls (Nokia requirement: ports 22/443 only) to participate in the network.

**Key Principles:**
- ✅ **No central KIRQ Hub** - Each validator runs their own PQTG client
- ✅ **No fixed relay infrastructure** - Validators volunteer and are elected via VRF
- ✅ **No centralized STUN** - Validators run their own or use public servers
- ✅ **No fixed bootnodes** - DHT-based peer discovery
- ✅ **QKD islands bridge** - Relays connect geographically isolated QKD deployments
- ✅ **Permissionless QKD** - Runtime supports ALL entropy types from genesis
- ✅ **QKD is optional** - Chain works with or without QKD validators

---

## Permissionless QKD Support

### Core Design Principle

**The QuantumHarmony chain MUST support all entropy source types from genesis block.**

This means:
- ✅ QKD validators can join at ANY time (no hard fork required)
- ✅ Non-QKD validators can participate from day one
- ✅ Mixed validator sets work seamlessly
- ✅ Chain never "upgrades" to support QKD - it's always supported

### Why This Matters

Traditional blockchains require hard forks to add new validator types. QuantumHarmony is **permissionless** - any validator with any entropy source type can join without network-wide coordination.

```
┌─────────────────────────────────────────────────────────────────┐
│                 Permissionless Evolution                         │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  Year 1 (2025): Launch with pure PQC validators                 │
│  ├─ Nokia validator: Crypto4A HSM (--qkd-mode disabled)         │
│  ├─ Telco validator: Hardware RNG (--qkd-mode optional)         │
│  └─ Community validator: Stake-only (--qkd-mode disabled)       │
│      ↓ Chain works fine with pure NIST PQC                      │
│                                                                  │
│  Year 2 (2026): NTT Docomo joins with QKD                       │
│  └─ NTT validator: Toshiba QKD (--qkd-mode required)            │
│      ↓ NO HARD FORK NEEDED                                      │
│      ↓ Runtime already supports QKD entropy                     │
│      ↓ Consensus accepts mixed validator set                    │
│                                                                  │
│  Year 3 (2027): SingTel joins with QKD                          │
│  └─ SingTel validator: IdQuantique (--qkd-mode required)        │
│      ↓ NO HARD FORK NEEDED                                      │
│      ↓ Now: 2 QKD validators + 3 non-QKD validators             │
│      ↓ All coexist in same consensus rounds                     │
│                                                                  │
│  Year 5 (2029): 50% validators use QKD                          │
│      ↓ NO CHANGES TO PROTOCOL                                   │
│      ↓ Organic adoption, no forced upgrades                     │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### Runtime Support

```rust
// Runtime ALWAYS supports ALL entropy source types (from block 0)

#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo)]
pub enum EntropySourceType {
    HardwareRNG,    // Crypto4A, EntropyKey, /dev/hwrng
    QKD,            // Toshiba, IdQuantique (optional hardware)
    Hybrid,         // Mix of HWRNG + QKD
    StakeOnly,      // No quantum hardware
}

// Validators register their entropy sources on-chain
#[pallet::storage]
pub type ValidatorEntropyConfigs<T: Config> =
    StorageMap<_, Blake2_128Concat, T::AccountId, ValidatorEntropyConfig>;

// Consensus validates entropy from ANY source type
impl<T: Config> Pallet<T> {
    fn validate_entropy_submission(
        validator: &T::AccountId,
        entropy: &[u8],
        device_shares: &Vec<DeviceShare>,
    ) -> Result<bool, Error<T>> {
        // Works with HardwareRNG, QKD, Hybrid, or StakeOnly
        // No special cases needed
    }
}
```

### CLI Flag Behavior

**IMPORTANT:** `--qkd-mode` is a **validator-local preference**, NOT a chain mode.

```bash
# Nokia validator (pure PQC):
./quantumharmony-node --validator \
  --qkd-mode disabled \
  --pqtg-devices crypto4a,hwrng

# NTT validator (requires QKD):
./quantumharmony-node --validator \
  --qkd-mode required \
  --pqtg-devices toshiba-qkd,crypto4a

# Default (auto-detect):
./quantumharmony-node --validator \
  --qkd-mode optional \
  --pqtg-endpoint https://localhost:8443
```

**Both validators participate in the SAME chain, SAME consensus, SAME blocks.**

No coordination needed. No hard fork. Permissionless.

---

## Problem Statement

### QKD Physical Limitations

Quantum Key Distribution (QKD) is limited by fiber optic attenuation:
- **Maximum distance:** ~100km over standard fiber
- **Signal loss:** Quantum states cannot be amplified without measurement
- **Result:** QKD deployments form isolated "islands"

### Example Scenario

```
Tokyo QKD Island          Singapore QKD Island
(Validators A, B, C)      (Validators D, E, F)
   Connected via          Connected via
   QKD fiber <100km       QKD fiber <100km
        ↓                      ↓
     Need relay to connect islands
     (No QKD over 100km)
```

### Corporate Firewall Constraints

**Nokia Requirement:**
- Only ports **22 (SSH)** and **443 (HTTPS)** allowed outbound
- Cannot open arbitrary ports for P2P (e.g., 30333 for libp2p)
- Must tunnel all traffic through quantum-safe SSH (QSSH)

### Centralization Risks to Avoid

❌ **Avoid:**
- Central "KIRQ Hub" service that all validators query
- Fixed relay infrastructure (single points of failure)
- Project-operated STUN servers (`stun-1.qh.io`)
- Single bootnode DNS (`boot.quantumharmony.io`)

---

## Decentralization Principles

### 1. Validator Autonomy

Each validator operator is fully autonomous:
- **Owns their QKD hardware** (Toshiba, Crypto4A, IdQuantique)
- **Runs PQTG locally** (localhost:8443) to translate device APIs
- **Runs validator node** (quantumharmony-node) with local entropy collection
- **Chooses to volunteer** as relay or not

### 2. No Required Central Services

The network must function without any central operators:
- **Peer discovery:** DHT-based (like BitTorrent)
- **Relay selection:** On-chain VRF election
- **STUN servers:** Validator-operated or public (Google, Cloudflare)
- **Bootnodes:** Multiple, operated by different entities

### 3. Geographic Distribution

Validators are geographically distributed:
- **QKD islands:** Regions with <100km fiber connectivity
- **Relay validators:** Between islands, using classical internet + QSSH
- **No single region dominance:** Global validator set

### 4. Economic Incentives

Validators are economically incentivized to cooperate:
- **Relay rewards:** Validators who relay earn fees
- **Slashing:** Relays that censor or provide poor service are slashed
- **Stake-weighted:** Higher stake = higher probability of relay election

---

## Architecture Overview

### Full Stack Diagram

```
┌───────────────────────────────────────────────────────────────┐
│                    Validator Node (Local)                     │
├───────────────────────────────────────────────────────────────┤
│  ┌─────────────────────────────────────────────────────────┐  │
│  │ coherence_gadget.rs                                     │  │
│  │ • Entropy collection & consensus                        │  │
│  │ • Calls pqtg_client for device entropy                  │  │
│  └─────────────────────────────────────────────────────────┘  │
│                                                                │
│  ┌─────────────────────────────────────────────────────────┐  │
│  │ pqtg_client.rs (renamed from kirq_client.rs)           │  │
│  │ • Direct PQTG queries (localhost:8443)                  │  │
│  │ • Device aggregation (K=2, M=3 threshold)               │  │
│  │ • QBER validation                                       │  │
│  └─────────────────────────────────────────────────────────┘  │
│                                                                │
│  ┌─────────────────────────────────────────────────────────┐  │
│  │ qssh_transport.rs                                       │  │
│  │ • Wraps libp2p in QSSH tunnels                          │  │
│  │ • Port 22 (SSH) for corporate firewalls                 │  │
│  │ • NIST PQC (Kyber-1024, Dilithium3, Falcon-1024)       │  │
│  └─────────────────────────────────────────────────────────┘  │
│                                                                │
│  ┌─────────────────────────────────────────────────────────┐  │
│  │ relay_manager.rs                                        │  │
│  │ • Volunteer to be relay                                 │  │
│  │ • Monitor relay performance                             │  │
│  │ • VRF-based relay election                              │  │
│  └─────────────────────────────────────────────────────────┘  │
└───────────────────────────────────────────────────────────────┘
                              ↓
          ┌───────────────────┴───────────────────┐
          ↓                                       ↓
┌─────────────────────────┐        ┌──────────────────────────┐
│ PQTG (localhost:8443)   │        │ QSSH (Existing Repo)     │
│ • KIRQ's software       │        │ • Quantum-safe SSH       │
│ • Falcon/SPHINCS+ auth  │        │ • Port 22 transport      │
│ • Vendor TLS translation│        │ • NIST PQC KEX           │
└─────────────────────────┘        └──────────────────────────┘
          ↓
┌─────────────────────────┐
│ QKD Hardware (USB/Net)  │
│ • Toshiba QKD           │
│ • Crypto4A HSM          │
│ • IdQuantique           │
└─────────────────────────┘
```

---

## Component Stack

### 1. PQTG Client (Validator-Local)

**File:** `node/src/pqtg_client.rs` (renamed from `kirq_client.rs`)

**Purpose:** Direct interface to PQTG for quantum device entropy collection.

**Key Changes:**
- ❌ Remove "KIRQ Hub" terminology (implies central service)
- ✅ Rename to `pqtg_client` (direct device interface)
- ✅ Each validator runs their own PQTG instance
- ✅ PQTG is KIRQ's proprietary device abstraction software

**Architecture:**
```rust
pub struct PqtgClient {
    config: PqtgConfig,
    http_client: reqwest::Client,
}

impl PqtgClient {
    /// Query PQTG for entropy from a specific device
    async fn query_device_via_pqtg(
        &self,
        device: &DeviceConfig,
        entropy_size: usize,
    ) -> Result<DeviceEntropyResponse, String> {
        // POST https://localhost:8443/devices/{type}/entropy
        // PQTG translates to vendor's classical TLS
        // Returns: entropy bytes + QBER + timestamp
    }
}
```

**Device Ownership:**
- **Current:** KIRQ owns QKD machines, provides PQTG software
- **Future:** Paraxiom acquires their own devices, runs PQTG
- **Decentralized:** Each validator operator owns their devices

### 2. QSSH Transport Layer

**File:** `node/src/qssh_transport.rs` (new)

**Purpose:** Wrap libp2p connections in quantum-safe SSH tunnels for port 22 compatibility.

**Integration:**
- Uses existing QSSH implementation (from user's QSSH repo)
- Provides libp2p `Transport` trait implementation
- All P2P traffic tunnels through port 22 (Nokia firewall requirement)

**NIST PQC Algorithms:**
- **KEX:** CRYSTALS-Kyber-1024 (post-quantum key exchange)
- **Signatures:** Dilithium3 or Falcon-1024 (post-quantum signatures)
- **Symmetric:** AES-256-GCM (session encryption)

**Connection Flow:**
```
Validator A                          Validator B
   ↓                                    ↓
libp2p wants to connect           libp2p listening
   ↓                                    ↓
qssh_transport wraps connection   qssh_transport unwraps
   ↓                                    ↓
QSSH tunnel over port 22 ─────────→ QSSH accepts port 22
   ↓                                    ↓
Corporate firewall allows         Corporate firewall allows
   ↓                                    ↓
Encrypted P2P data flows          Encrypted P2P data flows
```

### 3. Relay Manager

**File:** `node/src/relay_manager.rs` (new)

**Purpose:** Decentralized relay selection and management for bridging QKD islands.

**Responsibilities:**
1. **Volunteer Phase:** Validators signal willingness to relay
2. **Election Phase:** VRF selects relays from validator set
3. **Monitoring:** Track relay performance (latency, uptime, censorship)
4. **Slashing:** Penalize bad relays
5. **Rotation:** Re-elect relays every N blocks

**On-Chain Integration:**
- New extrinsic: `volunteer_as_relay(stake_amount)`
- New storage: `RelayValidators: Vec<AccountId>`
- New pallet: `pallet-relay-coordination`

---

## QKD Island Topology

### Geographic Distribution

```
┌─────────────────────────────────────────────────────────────────┐
│                         GLOBAL NETWORK                          │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  QKD Island 1: Tokyo Region (<100km fiber)                     │
│  ┌────────────────────────────────────────┐                    │
│  │ Validator-A ←──QKD──→ Validator-B      │                    │
│  │      ↓                     ↓            │                    │
│  │      └─────QKD─────────────┘            │                    │
│  │  (Fully connected QKD mesh)             │                    │
│  └────────────────────────────────────────┘                    │
│         ↓                         ↓                              │
│         │  Relay-1 (Seoul)        │  Relay-2 (Taipei)           │
│         │  No QKD, Internet+QSSH  │  No QKD, Internet+QSSH      │
│         ↓                         ↓                              │
│  ┌────────────────────────────────────────┐                    │
│  │ QKD Island 2: Singapore Region          │                    │
│  │ Validator-D ←──QKD──→ Validator-E      │                    │
│  │      ↓                     ↓            │                    │
│  │      └─────QKD─────────────┘            │                    │
│  └────────────────────────────────────────┘                    │
│         ↓                         ↓                              │
│         │  Relay-3 (Mumbai)       │  Relay-4 (Perth)            │
│         ↓                         ↓                              │
│  ┌────────────────────────────────────────┐                    │
│  │ QKD Island 3: Europe Region             │                    │
│  │ Validator-G ←──QKD──→ Validator-H      │                    │
│  └────────────────────────────────────────┘                    │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### Connection Types

**Type 1: QKD Direct Connection** (Within Island)
```
Validator-A ←───QKD fiber <100km───→ Validator-B
• Post-quantum encryption: QKD + PQC hybrid
• Full entropy distribution
• Low latency (<10ms)
```

**Type 2: QSSH Relay Connection** (Between Islands)
```
Validator-A ──QSSH/Internet──→ Relay-1 ──QSSH/Internet──→ Validator-D
• Post-quantum encryption: NIST PQC only (no QKD)
• Relay forwards P2P messages
• Higher latency (~50-200ms)
```

**Type 3: Direct QSSH** (Public IP validators)
```
Validator-A ─────QSSH direct over Internet─────→ Validator-Z
• Post-quantum encryption: NIST PQC
• No relay needed (both have public IPs)
• Medium latency (~30-100ms)
```

---

## Relay Selection Protocol

### Phase 1: Volunteer Registration

Validators signal their willingness to be relays via on-chain extrinsic:

```rust
// In pallet-relay-coordination
#[pallet::call]
impl<T: Config> Pallet<T> {
    #[pallet::weight(10_000)]
    pub fn volunteer_as_relay(
        origin: OriginFor<T>,
        min_stake: BalanceOf<T>,
        geographic_region: Vec<u8>, // e.g., "asia", "europe", "americas"
        max_bandwidth: u64,          // bytes/sec
    ) -> DispatchResult {
        let who = ensure_signed(origin)?;

        // Ensure validator has minimum stake
        ensure!(
            Self::validator_stake(&who) >= min_stake,
            Error::<T>::InsufficientStake
        );

        // Register as relay candidate
        RelayVolunteers::<T>::insert(&who, RelayInfo {
            stake: Self::validator_stake(&who),
            region: geographic_region,
            bandwidth: max_bandwidth,
            uptime: Self::calculate_uptime(&who),
            performance_score: 100, // Initial score
        });

        Self::deposit_event(Event::RelayVolunteered { validator: who });
        Ok(())
    }
}
```

### Phase 2: VRF-Based Election

Every N blocks (e.g., N=1000, ~3.3 hours with 12s blocks), elect relays using VRF:

```rust
impl<T: Config> Pallet<T> {
    fn elect_relays(block_number: BlockNumber) {
        let volunteers = RelayVolunteers::<T>::iter().collect::<Vec<_>>();

        // Calculate number of relays needed (e.g., 10% of validators)
        let target_relay_count = (validators_count / 10).max(5);

        let mut selected_relays = Vec::new();

        for _ in 0..target_relay_count {
            // VRF selection weighted by stake + performance
            let relay = Self::vrf_select_relay(&volunteers, block_number);
            selected_relays.push(relay);
        }

        // Update on-chain relay set
        ActiveRelays::<T>::put(selected_relays);

        Self::deposit_event(Event::RelaysElected {
            count: target_relay_count,
            block: block_number,
        });
    }

    fn vrf_select_relay(
        volunteers: &[(AccountId, RelayInfo)],
        block_number: BlockNumber,
    ) -> AccountId {
        // VRF: Hash(block_randomness || volunteer_id) weighted by stake + performance
        let block_randomness = Self::block_randomness(block_number);

        let mut weighted_volunteers = volunteers
            .iter()
            .map(|(id, info)| {
                let weight = info.stake * info.performance_score / 100;
                let vrf_output = blake2_256(&[block_randomness, id.encode()].concat());
                (id, weight, vrf_output)
            })
            .collect::<Vec<_>>();

        // Sort by VRF output, weighted by stake
        weighted_volunteers.sort_by_key(|(_, weight, vrf)| {
            // Higher weight and lower VRF = higher priority
            (*vrf as u128) / (*weight as u128)
        });

        weighted_volunteers[0].0.clone()
    }
}
```

### Phase 3: Performance Monitoring

Validators monitor relay performance and report:

```rust
#[pallet::call]
impl<T: Config> Pallet<T> {
    #[pallet::weight(5_000)]
    pub fn report_relay_performance(
        origin: OriginFor<T>,
        relay: T::AccountId,
        metrics: RelayMetrics,
    ) -> DispatchResult {
        let reporter = ensure_signed(origin)?;

        // Aggregate metrics from multiple reporters
        RelayPerformanceReports::<T>::mutate(&relay, |reports| {
            reports.push((reporter, metrics));
        });

        // If majority reports poor performance, slash relay
        if Self::calculate_consensus_score(&relay) < 50 {
            Self::slash_relay(&relay)?;
        }

        Ok(())
    }
}

pub struct RelayMetrics {
    pub latency_ms: u32,
    pub packet_loss: u8,      // Percentage
    pub uptime: u8,           // Percentage
    pub censorship_detected: bool,
}
```

### Phase 4: Slashing Mechanism

Bad relays are penalized:

```rust
impl<T: Config> Pallet<T> {
    fn slash_relay(relay: &T::AccountId) -> DispatchResult {
        let slash_amount = Self::relay_stake(relay) / 10; // 10% slash

        // Slash stake
        T::Currency::slash(relay, slash_amount);

        // Remove from active relay set
        ActiveRelays::<T>::mutate(|relays| {
            relays.retain(|r| r != relay);
        });

        // Ban from volunteering for N blocks
        RelayBanList::<T>::insert(relay, Self::current_block() + 1000);

        Self::deposit_event(Event::RelaySlashed {
            relay: relay.clone(),
            amount: slash_amount,
        });

        Ok(())
    }
}
```

### Phase 5: Rotation

Relays rotate every N blocks to prevent centralization:

```rust
impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
    fn on_initialize(n: BlockNumberFor<T>) -> Weight {
        if n % T::RelayRotationInterval::get() == 0 {
            Self::elect_relays(n);
        }
        Weight::zero()
    }
}
```

---

## QSSH Transport Layer

### Integration with Existing QSSH

The user has an existing QSSH implementation (from separate repo). We need to wrap it for libp2p:

**File:** `node/src/qssh_transport.rs`

```rust
//! QSSH Transport for libp2p
//!
//! Wraps libp2p connections in quantum-safe SSH tunnels to enable P2P over port 22.
//! This allows validators behind corporate firewalls (Nokia requirement) to participate.

use futures::prelude::*;
use libp2p::core::{
    transport::{Transport, TransportError},
    multiaddr::Multiaddr,
};
use std::io;
use tokio::process::{Command, Child};

/// QSSH transport configuration
pub struct QsshConfig {
    /// Path to QSSH binary (from user's QSSH repo)
    pub qssh_binary: String,

    /// SSH key path for authentication
    pub ssh_key_path: String,

    /// Port to use (default: 22)
    pub ssh_port: u16,

    /// NIST PQC algorithms
    pub kex_algorithm: String,      // e.g., "kyber1024"
    pub signature_algorithm: String, // e.g., "dilithium3" or "falcon1024"
}

impl Default for QsshConfig {
    fn default() -> Self {
        Self {
            qssh_binary: "qssh".to_string(),
            ssh_key_path: "~/.ssh/quantumharmony_key".to_string(),
            ssh_port: 22,
            kex_algorithm: "kyber1024".to_string(),
            signature_algorithm: "falcon1024".to_string(),
        }
    }
}

/// QSSH transport that wraps TCP connections in quantum-safe SSH
pub struct QsshTransport {
    config: QsshConfig,
    inner_transport: libp2p_tcp::tokio::Transport,
}

impl QsshTransport {
    pub fn new(config: QsshConfig) -> Self {
        Self {
            config,
            inner_transport: libp2p_tcp::tokio::Transport::default(),
        }
    }

    /// Establish QSSH connection to remote peer
    async fn establish_qssh_connection(
        &self,
        remote_addr: &Multiaddr,
    ) -> io::Result<QsshConnection> {
        // Parse multiaddr to extract IP and port
        let (ip, port) = self.parse_multiaddr(remote_addr)?;

        // Spawn QSSH client process
        let mut child = Command::new(&self.config.qssh_binary)
            .arg("-i").arg(&self.config.ssh_key_path)
            .arg("-p").arg(self.config.ssh_port.to_string())
            .arg("-o").arg(format!("KexAlgorithms={}", self.config.kex_algorithm))
            .arg("-o").arg(format!("PubkeyAcceptedKeyTypes={}", self.config.signature_algorithm))
            .arg("-N") // No command, just tunnel
            .arg("-L").arg(format!("127.0.0.1:0:{}", port)) // Dynamic local port forwarding
            .arg(format!("validator@{}", ip))
            .spawn()?;

        // Wait for SSH tunnel to establish
        tokio::time::sleep(tokio::time::Duration::from_millis(500)).await;

        // Get local port that SSH forwarded
        let local_port = self.get_forwarded_port(&child)?;

        Ok(QsshConnection {
            child,
            local_port,
            remote_addr: remote_addr.clone(),
        })
    }

    fn parse_multiaddr(&self, addr: &Multiaddr) -> io::Result<(String, u16)> {
        // Extract IP and port from /ip4/1.2.3.4/tcp/30333 format
        // TODO: Full implementation
        Ok(("127.0.0.1".to_string(), 30333))
    }

    fn get_forwarded_port(&self, child: &Child) -> io::Result<u16> {
        // Parse SSH output to find dynamically assigned local port
        // TODO: Full implementation
        Ok(12345)
    }
}

/// QSSH connection handle
pub struct QsshConnection {
    child: Child,
    local_port: u16,
    remote_addr: Multiaddr,
}

impl QsshConnection {
    /// Get the local port that tunnels to remote peer
    pub fn local_port(&self) -> u16 {
        self.local_port
    }
}

impl Drop for QsshConnection {
    fn drop(&mut self) {
        // Kill SSH process when connection is dropped
        let _ = self.child.kill();
    }
}

// TODO: Implement libp2p::Transport trait for QsshTransport
```

### Usage in Service

```rust
// In node/src/service.rs
use crate::qssh_transport::{QsshTransport, QsshConfig};

pub fn new_full(config: Configuration) -> Result<TaskManager, ServiceError> {
    // ...

    // Create QSSH transport if enabled
    let transport = if config.network.enable_qssh {
        let qssh_config = QsshConfig {
            qssh_binary: config.network.qssh_binary_path.clone(),
            ssh_key_path: config.network.ssh_key_path.clone(),
            ssh_port: 22,
            kex_algorithm: "kyber1024".to_string(),
            signature_algorithm: "falcon1024".to_string(),
        };

        QsshTransport::new(qssh_config)
    } else {
        // Fallback to regular TCP
        libp2p_tcp::tokio::Transport::default()
    };

    // Build libp2p network with QSSH transport
    // ...
}
```

---

## STUN Decentralization

### Problem

STUN servers help validators behind NAT discover their public IP addresses. If we operate `stun-1.qh.io`, that's a centralization point.

### Solution 1: Validator-Operated STUN

Validators can optionally run their own STUN servers:

```bash
# Install coturn (open-source STUN/TURN server)
sudo apt-get install coturn

# Configure /etc/turnserver.conf
listening-port=3478
fingerprint
lt-cred-mech
user=validator:password
realm=quantumharmony.network

# Start STUN server
sudo systemctl start coturn
```

**Announce STUN server to network:**

```rust
#[pallet::call]
impl<T: Config> Pallet<T> {
    #[pallet::weight(5_000)]
    pub fn announce_stun_server(
        origin: OriginFor<T>,
        stun_addr: Vec<u8>, // e.g., "stun:192.0.2.1:3478"
    ) -> DispatchResult {
        let who = ensure_signed(origin)?;

        // Store STUN server in on-chain registry
        StunServers::<T>::insert(&who, stun_addr.clone());

        Self::deposit_event(Event::StunServerAnnounced {
            validator: who,
            addr: stun_addr,
        });

        Ok(())
    }
}
```

### Solution 2: Public STUN Servers

Use existing public STUN servers (no centralization):

```rust
// In node/src/service.rs
let default_stun_servers = vec![
    "stun:stun.l.google.com:19302",       // Google
    "stun:stun1.l.google.com:19302",      // Google
    "stun:stun.cloudflare.com:3478",      // Cloudflare
    "stun:stun.stunprotocol.org:3478",    // Open source
];
```

### Solution 3: DHT-Based STUN Discovery

Validators discover STUN servers via DHT (like BitTorrent):

```rust
// Query on-chain STUN registry + DHT
async fn discover_stun_servers(&self) -> Vec<String> {
    let mut stun_servers = Vec::new();

    // 1. Query on-chain STUN registry
    let onchain_stun = self.client
        .runtime_api()
        .get_stun_servers(self.client.info().best_hash)
        .unwrap_or_default();
    stun_servers.extend(onchain_stun);

    // 2. Query DHT for peer-advertised STUN servers
    let dht_stun = self.network.dht_query("stun_servers").await;
    stun_servers.extend(dht_stun);

    // 3. Fallback to public STUN servers
    stun_servers.extend(DEFAULT_PUBLIC_STUN_SERVERS);

    stun_servers
}
```

---

## Security Analysis

### Attack Vectors and Mitigations

#### 1. Malicious Relay Attack

**Attack:** Relay validator censors or delays messages between islands.

**Mitigation:**
- **Multi-relay paths:** Each island connects via multiple relays
- **Performance monitoring:** Validators report relay latency
- **Automatic failover:** Switch to backup relay if primary is slow
- **Slashing:** Penalize relays with poor performance scores

#### 2. Sybil Attack on Relay Election

**Attack:** Attacker creates many low-stake validators to dominate relay set.

**Mitigation:**
- **Stake-weighted VRF:** Higher stake = higher election probability
- **Minimum stake requirement:** e.g., 10,000 QH tokens to volunteer
- **Performance scoring:** New relays start with low score, earn reputation over time
- **Geographic diversity:** Limit relays per region to prevent single-region dominance

#### 3. QSSH Downgrade Attack

**Attack:** Attacker forces validators to use weak crypto by intercepting KEX.

**Mitigation:**
- **Hardcoded NIST PQC algorithms:** No negotiation, always use Kyber-1024 + Falcon-1024
- **Certificate pinning:** Validators pin each other's Falcon public keys
- **On-chain key registry:** Public keys stored on-chain, verified during connection

#### 4. Relay Eclipse Attack

**Attack:** Attacker controls all relays between two islands, censoring messages.

**Mitigation:**
- **Multiple relay paths:** Require 2+ relays between islands (different operators)
- **Direct QSSH fallback:** If all relays fail, try direct connection
- **Alert system:** Validators detect censorship and alert network

#### 5. PQTG Compromise

**Attack:** Attacker compromises PQTG software to leak entropy.

**Mitigation:**
- **Open-source PQTG:** Validators can audit code (requires KIRQ to open-source)
- **Reproducible builds:** Verify PQTG binary matches source
- **Device diversity:** Use multiple device vendors (Toshiba, Crypto4A, IdQuantique)
- **Threshold entropy:** K-of-M requires attacker to compromise multiple devices

---

## Implementation Roadmap

### Phase 1: Renaming and Refactoring (Week 1)

**Tasks:**
1. ✅ Rename `kirq_client.rs` → `pqtg_client.rs`
2. ✅ Update documentation to remove "KIRQ Hub" terminology
3. ✅ Update `coherence_gadget.rs` to use `pqtg_client`
4. ✅ Commit changes with proper documentation

**Status:** Ready to start

### Phase 2: Relay Manager (Week 2-3)

**Tasks:**
1. Create `pallet-relay-coordination` (on-chain logic)
   - Volunteer extrinsic
   - VRF election algorithm
   - Performance monitoring storage
   - Slashing mechanism
2. Create `node/src/relay_manager.rs` (off-chain worker)
   - Monitor relay performance
   - Report metrics on-chain
   - Automatic relay discovery
3. Integration tests for relay election

**Status:** Design complete, ready to implement

### Phase 3: QSSH Transport (Week 4-5)

**Tasks:**
1. Study existing QSSH implementation (user's repo)
2. Create `node/src/qssh_transport.rs`
   - libp2p Transport trait implementation
   - QSSH process spawning and management
   - Port forwarding logic
3. Add CLI flags:
   - `--enable-qssh`
   - `--qssh-binary-path`
   - `--ssh-key-path`
4. Test with Nokia firewall constraints (port 22 only)

**Status:** Design complete, pending QSSH repo analysis

### Phase 4: STUN Decentralization (Week 6)

**Tasks:**
1. Create `pallet-stun-registry` for on-chain STUN server list
2. Implement DHT-based STUN discovery
3. Add default public STUN servers (Google, Cloudflare)
4. Integration with NAT traversal logic

**Status:** Design complete

### Phase 5: End-to-End Testing (Week 7-8)

**Tasks:**
1. Multi-region testnet deployment
   - QKD island 1: Tokyo (3 validators)
   - QKD island 2: Singapore (3 validators)
   - Relay validators: Seoul, Taipei, Mumbai (3 relays)
2. Simulate Nokia firewall (port 22/443 only)
3. Test relay rotation and slashing
4. Performance benchmarks

**Status:** Pending previous phases

### Phase 6: Documentation and Audit (Week 9-10)

**Tasks:**
1. Complete operator documentation
2. Security audit of relay election
3. Performance tuning
4. Mainnet deployment guide

**Status:** Pending

---

## Appendix A: CLI Flag Reference

### QKD Mode Flag

The `--qkd-mode` flag controls whether the validator uses QKD hardware when available:

- `disabled`: Never use QKD hardware (pure PQC/HWRNG)
- `optional`: Use QKD if hardware is detected (default)
- `required`: Fail to start if QKD hardware unavailable

### Example 1: Nokia Validator (Pure PQC - No QKD Hardware)

```bash
quantumharmony-node \
  --validator \
  --name "Nokia-Helsinki-Validator" \
  --base-path /data/validator \
  --chain mainnet \
  \
  # QKD Configuration: Disabled (pure HWRNG/PQC)
  --qkd-mode disabled \
  --pqtg-endpoint https://localhost:8443 \
  --pqtg-devices crypto4a,hwrng \
  \
  # QSSH Configuration
  --enable-qssh \
  --qssh-binary-path /usr/local/bin/qssh \
  --ssh-key-path ~/.ssh/quantumharmony_key \
  --ssh-port 22 \
  \
  # Relay Configuration
  --volunteer-as-relay \
  --relay-stake 50000 \
  --relay-region europe \
  --relay-max-bandwidth 1000000000 \
  \
  # Bootnode Configuration
  --bootnodes /ip4/192.0.2.1/tcp/30333/p2p/12D3KooW... \
  --bootnodes /ip4/198.51.100.1/tcp/30333/p2p/12D3KooW...
```

### Example 2: NTT Validator (QKD Required)

```bash
quantumharmony-node \
  --validator \
  --name "NTT-Tokyo-Validator" \
  --base-path /data/validator \
  --chain mainnet \
  \
  # QKD Configuration: Required (must have QKD hardware)
  --qkd-mode required \
  --pqtg-endpoint https://localhost:8443 \
  --pqtg-devices toshiba-qkd,crypto4a \
  \
  # QSSH Configuration
  --enable-qssh \
  --qssh-binary-path /usr/local/bin/qssh \
  --ssh-key-path ~/.ssh/quantumharmony_key \
  --ssh-port 22 \
  \
  # Relay Configuration
  --volunteer-as-relay \
  --relay-stake 50000 \
  --relay-region asia \
  --relay-max-bandwidth 1000000000 \
  \
  # Bootnode Configuration
  --bootnodes /ip4/192.0.2.1/tcp/30333/p2p/12D3KooW... \
  --bootnodes /ip4/198.51.100.1/tcp/30333/p2p/12D3KooW...
```

### Example 3: Default Validator (Auto-Detect QKD)

```bash
quantumharmony-node \
  --validator \
  --name "Generic-Validator" \
  --base-path /data/validator \
  --chain mainnet \
  \
  # QKD Configuration: Optional (auto-detect, default)
  --qkd-mode optional \
  --pqtg-endpoint https://localhost:8443 \
  # No --pqtg-devices: auto-discovery from PQTG
  \
  # QSSH Configuration
  --enable-qssh \
  --qssh-binary-path /usr/local/bin/qssh \
  --ssh-key-path ~/.ssh/quantumharmony_key \
  --ssh-port 22 \
  \
  # Relay Configuration
  --volunteer-as-relay \
  --relay-stake 50000 \
  --relay-region global \
  --relay-max-bandwidth 1000000000 \
  \
  # Bootnode Configuration
  --bootnodes /ip4/192.0.2.1/tcp/30333/p2p/12D3KooW... \
  --bootnodes /ip4/198.51.100.1/tcp/30333/p2p/12D3KooW...
```

### Flag Descriptions

| Flag | Type | Default | Description |
|------|------|---------|-------------|
| `--qkd-mode` | `disabled\|optional\|required` | `optional` | QKD hardware usage policy |
| `--pqtg-endpoint` | URL | `https://localhost:8443` | PQTG API endpoint |
| `--pqtg-devices` | Comma-separated list | Auto-detect | Specific devices to use |
| `--enable-qssh` | Boolean | `false` | Enable QSSH transport |
| `--qssh-binary-path` | Path | `/usr/local/bin/qssh` | Path to QSSH binary |
| `--ssh-key-path` | Path | `~/.ssh/quantumharmony_key` | SSH private key path |
| `--ssh-port` | Integer | `22` | SSH port for QSSH |
| `--volunteer-as-relay` | Boolean | `false` | Volunteer as QSSH relay |
| `--relay-stake` | Integer | `0` | Stake amount for relay election |
| `--relay-region` | String | `global` | Geographic region identifier |
| `--relay-max-bandwidth` | Integer | `1000000000` | Max bandwidth (bytes/sec) |

---

## Appendix B: Hardware Requirements

### QKD Device Requirements

**Toshiba QKD:**
- Fiber optic connection (<100km)
- USB or network interface
- QBER < 11%

**Crypto4A HSM:**
- PCIe or USB connection
- Hardware RNG (not QKD, but quantum-resistant)
- QBER < 5% (best quality)

**IdQuantique:**
- Fiber optic connection (<100km)
- Network interface (192.168.x.x)
- QBER < 8%

### Validator Hardware Requirements

**Minimum:**
- CPU: 4 cores (Intel/AMD x86_64)
- RAM: 8 GB
- Storage: 500 GB SSD
- Network: 100 Mbps symmetric
- PQTG software installed

**Recommended:**
- CPU: 8 cores
- RAM: 16 GB
- Storage: 1 TB NVMe SSD
- Network: 1 Gbps symmetric
- UPS for power backup

---

## Appendix C: Network Topology Examples

### Example 1: Asia-Pacific Region

```
Tokyo Island (3 validators)
  ├─ NTT Docomo (Toshiba QKD)
  ├─ SoftBank (Crypto4A HSM)
  └─ Rakuten (IdQuantique)
       ↓
  Seoul Relay (SK Telecom)
       ↓
Singapore Island (3 validators)
  ├─ SingTel (Toshiba QKD)
  ├─ StarHub (IdQuantique)
  └─ M1 (Crypto4A HSM)
```

### Example 2: Europe Region

```
London Island (3 validators)
  ├─ BT (Toshiba QKD)
  ├─ Vodafone (IdQuantique)
  └─ O2 (Crypto4A HSM)
       ↓
  Frankfurt Relay (Deutsche Telekom)
       ↓
Zurich Island (2 validators)
  ├─ Swisscom (Toshiba QKD)
  └─ Sunrise (IdQuantique)
```

---

## Document History

| Version | Date       | Author           | Changes                                    |
|---------|------------|------------------|--------------------------------------------|
| 1.0     | 2025-01-23 | Sylvain Cormier  | Initial design document                    |
|         |            | Claude (Anthropic)| Architecture and implementation details   |

---

## References

1. **QKD Technology:**
   - Toshiba QKD: https://www.toshiba.eu/quantum/
   - ID Quantique: https://www.idquantique.com/
   - Crypto4A: https://www.crypto4a.com/

2. **NIST PQC Standards:**
   - CRYSTALS-Kyber: https://pq-crystals.org/kyber/
   - CRYSTALS-Dilithium: https://pq-crystals.org/dilithium/
   - Falcon: https://falcon-sign.info/

3. **Substrate/Polkadot:**
   - libp2p: https://libp2p.io/
   - Substrate Networking: https://docs.substrate.io/

4. **STUN/NAT Traversal:**
   - RFC 5389 (STUN): https://tools.ietf.org/html/rfc5389
   - coturn (STUN/TURN): https://github.com/coturn/coturn

---

**END OF DOCUMENT**
