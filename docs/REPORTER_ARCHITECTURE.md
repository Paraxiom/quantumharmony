# REPORTER System Architecture

## Overview

The REPORTER tab provides three interconnected quantum-safe data services:

1. **Decentralized QRNG** - Aggregated quantum randomness from multiple validators
2. **QKD Routing** - Quantum key distribution to consensus/messaging/custom
3. **Decentralized Oracle Network** - Multi-validator data feeds with SLA rewards

---

## 1. Decentralized QRNG

### Purpose
Combine quantum random number outputs from multiple validators to create verifiable, Byzantine-fault-tolerant randomness that no single validator can manipulate.

### Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                    VALIDATOR NETWORK                         │
├─────────────────┬─────────────────┬─────────────────────────┤
│   Alice Node    │    Bob Node     │    Charlie Node         │
│   ┌─────────┐   │   ┌─────────┐   │   ┌─────────┐          │
│   │ Local   │   │   │ Local   │   │   │ Local   │          │
│   │ QRNG    │   │   │ QRNG    │   │   │ QRNG    │          │
│   └────┬────┘   │   └────┬────┘   │   └────┬────┘          │
│        │        │        │        │        │                │
│   ┌────▼────┐   │   ┌────▼────┐   │   ┌────▼────┐          │
│   │ Shamir  │   │   │ Shamir  │   │   │ Shamir  │          │
│   │ Share   │   │   │ Share   │   │   │ Share   │          │
│   └────┬────┘   │   └────┬────┘   │   └────┬────┘          │
└────────┼────────┴────────┼────────┴────────┼────────────────┘
         │                 │                 │
         └────────────┬────┴─────────────────┘
                      │ entropy_gossip.rs
                      ▼
         ┌────────────────────────┐
         │   Threshold QRNG       │
         │   K-of-M Combination   │
         │   (threshold_qrng.rs)  │
         └───────────┬────────────┘
                     │
                     ▼
         ┌────────────────────────┐
         │   Combined Entropy     │
         │   + STARK Proof        │
         │   + Reconstruction     │
         └────────────────────────┘
```

### Data Flow
1. Each validator generates local quantum entropy (or simulated)
2. Entropy is split into Shamir shares
3. Shares are gossiped via `entropy_gossip.rs`
4. Leader collects K-of-M shares
5. Reconstruction produces combined entropy + proof
6. Proof is validated by 2/3+ validators

### Existing Components to Use
- `node/src/threshold_qrng.rs` - Shamir implementation
- `node/src/quantum_entropy.rs` - Local entropy provider
- `node/src/entropy_gossip.rs` - P2P share distribution
- `pallets/qkd-client/` - Randomness trait

### UI Requirements
```
┌─────────────────────────────────────────┐
│ QRNG POOL                               │
├─────────────────────────────────────────┤
│ Local Entropy:    ████████████ ACTIVE   │
│ Source: simulated (no HWRNG)            │
│                                         │
│ Network Shares Received:                │
│   Alice:   ✓ 32 bytes (QBER: 0.8%)     │
│   Bob:     ✓ 32 bytes (QBER: 1.1%)     │
│   Charlie: ✓ 32 bytes (QBER: 0.9%)     │
│                                         │
│ Threshold: 2-of-3                       │
│ Combined: 0x7f3a...9b2c (valid proof)   │
│ Last Update: 2 blocks ago               │
│                                         │
│ [GENERATE NEW] [EXPORT] [CONFIGURE]     │
└─────────────────────────────────────────┘
```

---

## 2. QKD Routing

### Purpose
Route quantum-derived keys to different subsystems based on security requirements.

### Architecture

```
┌─────────────────────────────────────────┐
│           QKD KEY POOL                  │
│  (from threshold QRNG or real QKD)      │
└─────────────────┬───────────────────────┘
                  │
    ┌─────────────┼─────────────┐
    │             │             │
    ▼             ▼             ▼
┌────────┐  ┌──────────┐  ┌──────────┐
│CONSENSUS│ │MESSAGING │  │ CUSTOM   │
│         │ │          │  │          │
│ Leader  │ │ pq-triple│  │ User-    │
│ VRF     │ │ -ratchet │  │ defined  │
│ Nonces  │ │ sessions │  │ apps     │
└────────┘  └──────────┘  └──────────┘
```

### Routing Rules
| Destination | Key Size | Refresh Rate | Priority |
|-------------|----------|--------------|----------|
| Consensus   | 32 bytes | Per block    | Critical |
| Messaging   | 32 bytes | Per session  | High     |
| Custom      | Variable | On demand    | Normal   |

### Existing Components to Use
- `pallets/qkd-client/` - Key material generation
- `node-operator/src/messaging.rs` - Messaging integration
- `node/src/coherence_gadget.rs` - Consensus integration

### UI Requirements
```
┌─────────────────────────────────────────┐
│ QKD KEY ROUTING                         │
├─────────────────────────────────────────┤
│ Keys Available: 48                      │
│ Source: Threshold QRNG (simulated)      │
│                                         │
│ ROUTING STATUS:                         │
│ ┌─────────────────────────────────────┐ │
│ │ Consensus    │ ✓ Active │ 12 used  │ │
│ │ Messaging    │ ✓ Active │ 8 used   │ │
│ │ Custom Pool  │ ○ Idle   │ 0 used   │ │
│ └─────────────────────────────────────┘ │
│                                         │
│ Last Key Exchange: Block #71,234        │
│ Next Refresh: ~6 blocks                 │
│                                         │
│ [ROUTE TO...] [REFRESH NOW] [SETTINGS]  │
└─────────────────────────────────────────┘
```

---

## 3. Decentralized Oracle Network

### Purpose
Enable validators to request, provide, and verify external data feeds with economic incentives.

### Architecture

```
┌────────────────────────────────────────────────────────────────┐
│                      ORACLE FEED LIFECYCLE                      │
└────────────────────────────────────────────────────────────────┘

1. REQUEST PHASE
   ┌──────────────┐
   │ Validator A  │──────► Creates OracleFeedRequest
   │ (Requester)  │        - data_type: "weather"
   └──────────────┘        - source_url: "api.weather.com/..."
                           - reward: 10 QMHY
                           - sla: 99% uptime, <5s latency
                           - duration: 1000 blocks

2. ACCEPTANCE PHASE
   ┌──────────────┐  ┌──────────────┐  ┌──────────────┐
   │ Validator B  │  │ Validator C  │  │ Validator D  │
   │   ACCEPT ✓   │  │   ACCEPT ✓   │  │   DECLINE    │
   └──────────────┘  └──────────────┘  └──────────────┘

   Minimum acceptances required: 2 (configurable)

3. REPORTING PHASE
   Every N blocks, reporters submit:
   ┌─────────────────────────────────────────────┐
   │ OracleReport {                              │
   │   feed_id: 1,                               │
   │   data: "temperature: 22.5C",               │
   │   timestamp: 1704393600,                    │
   │   signature: SPHINCS+(data),                │
   │   source_proof: hash(api_response)          │
   │ }                                           │
   └─────────────────────────────────────────────┘

4. AGGREGATION PHASE
   ┌─────────────────────────────────────────────┐
   │ Consensus on data:                          │
   │ - Validator B reported: 22.5C              │
   │ - Validator C reported: 22.6C              │
   │ - Median/Mode: 22.55C                       │
   │ - Agreement: 100% (within tolerance)        │
   └─────────────────────────────────────────────┘

5. CONSUMPTION PHASE
   ┌─────────────────────────────────────────────┐
   │ Smart Contract / Runtime Module             │
   │ calls: OracleFeeds::get_feed(feed_id)       │
   │ returns: AggregatedData { value, proof }    │
   └─────────────────────────────────────────────┘

6. REWARD PHASE
   If data used in transaction:
   - Reporters split reward based on SLA compliance
   - Slashing for incorrect/late data
```

### Pallet Design: `pallet-oracle-feeds`

```rust
// Storage
#[pallet::storage]
pub type FeedRequests<T> = StorageMap<_, Blake2_128Concat, FeedId, FeedRequest<T>>;

#[pallet::storage]
pub type FeedReporters<T> = StorageMap<_, Blake2_128Concat, FeedId, Vec<T::AccountId>>;

#[pallet::storage]
pub type FeedReports<T> = StorageDoubleMap<
    _, Blake2_128Concat, FeedId,
    Blake2_128Concat, T::AccountId,
    OracleReport<T>
>;

#[pallet::storage]
pub type AggregatedFeeds<T> = StorageMap<_, Blake2_128Concat, FeedId, AggregatedData>;

// Types
pub struct FeedRequest<T: Config> {
    pub requester: T::AccountId,
    pub data_type: DataType,           // Weather, Price, Custom
    pub source_url: BoundedVec<u8, MaxUrlLength>,
    pub reward_per_report: BalanceOf<T>,
    pub sla_uptime: Percent,           // e.g., 99%
    pub sla_latency_ms: u32,           // e.g., 5000ms
    pub min_reporters: u8,             // e.g., 2
    pub report_interval: BlockNumber,  // e.g., every 10 blocks
    pub duration: BlockNumber,         // e.g., 1000 blocks
    pub created_at: BlockNumber,
    pub status: FeedStatus,
}

pub enum FeedStatus {
    Pending,        // Waiting for min_reporters
    Active,         // Reporting in progress
    Completed,      // Duration ended
    Cancelled,      // Requester cancelled
}

pub struct OracleReport<T: Config> {
    pub reporter: T::AccountId,
    pub feed_id: FeedId,
    pub data: BoundedVec<u8, MaxDataLength>,
    pub timestamp: u64,
    pub block_number: BlockNumber,
    pub latency_ms: u32,
}

pub struct AggregatedData {
    pub value: BoundedVec<u8, MaxDataLength>,
    pub reporters_count: u8,
    pub agreement_percent: Percent,
    pub last_updated: BlockNumber,
}

// Extrinsics
#[pallet::call]
impl<T: Config> Pallet<T> {
    pub fn request_feed(origin, request: FeedRequest<T>) -> DispatchResult;
    pub fn accept_feed(origin, feed_id: FeedId) -> DispatchResult;
    pub fn submit_report(origin, report: OracleReport<T>) -> DispatchResult;
    pub fn cancel_feed(origin, feed_id: FeedId) -> DispatchResult;
}

// Runtime API for consumption
pub trait OracleFeedsApi<Block> {
    fn get_feed(feed_id: FeedId) -> Option<AggregatedData>;
    fn get_active_feeds() -> Vec<FeedId>;
}
```

### SLA & Rewards

| Metric | Threshold | Reward Impact |
|--------|-----------|---------------|
| Uptime | 99%+ | Full reward |
| Uptime | 95-99% | 80% reward |
| Uptime | <95% | No reward + slash |
| Latency | <5s | Full reward |
| Latency | 5-10s | 90% reward |
| Latency | >10s | No reward |
| Accuracy | Within tolerance | Full reward |
| Accuracy | Outside tolerance | Slash |

### UI Requirements
```
┌─────────────────────────────────────────────────────────────┐
│ ORACLE FEEDS                                                │
├─────────────────────────────────────────────────────────────┤
│ [+ REQUEST NEW FEED]                                        │
│                                                             │
│ ACTIVE REQUESTS (from network):                             │
│ ┌─────────────────────────────────────────────────────────┐ │
│ │ #1 Weather API                                          │ │
│ │    URL: api.openweather.com/data/2.5/weather?q=...     │ │
│ │    Reward: 10 QMHY/report | SLA: 99% / 5s              │ │
│ │    Reporters: 2/3 | Status: ACTIVE                      │ │
│ │    [ACCEPT] [DETAILS]                                   │ │
│ └─────────────────────────────────────────────────────────┘ │
│ ┌─────────────────────────────────────────────────────────┐ │
│ │ #2 BTC/USD Price                                        │ │
│ │    URL: api.coingecko.com/api/v3/simple/price?...      │ │
│ │    Reward: 5 QMHY/report | SLA: 99.5% / 2s             │ │
│ │    Reporters: 1/2 | Status: PENDING                     │ │
│ │    [ACCEPT] [DETAILS]                                   │ │
│ └─────────────────────────────────────────────────────────┘ │
│                                                             │
│ MY FEEDS (providing):                                       │
│ ┌─────────────────────────────────────────────────────────┐ │
│ │ #1 Weather API                                          │ │
│ │    Reports: 142 | Earned: 1,420 QMHY                   │ │
│ │    SLA: 99.3% uptime | Avg latency: 2.1s               │ │
│ │    Next report in: 3 blocks                             │ │
│ └─────────────────────────────────────────────────────────┘ │
│                                                             │
│ FEED HISTORY:                                               │
│ Block #71,230 | Weather: 22.5C | 3/3 agree | Used: Yes    │
│ Block #71,220 | Weather: 22.4C | 3/3 agree | Used: No     │
│ Block #71,210 | Weather: 22.6C | 2/3 agree | Used: Yes    │
└─────────────────────────────────────────────────────────────┘
```

---

## Integration Points

### REPORTER Tab Integration Map

```
┌─────────────────────────────────────────────────────────────────┐
│                        REPORTER TAB                              │
├──────────────────┬──────────────────┬───────────────────────────┤
│    QRNG POOL     │   QKD ROUTING    │     ORACLE FEEDS          │
├──────────────────┼──────────────────┼───────────────────────────┤
│ threshold_qrng   │ qkd-client       │ pallet-oracle-feeds (NEW) │
│ quantum_entropy  │ messaging.rs     │                           │
│ entropy_gossip   │ coherence_gadget │                           │
├──────────────────┴──────────────────┴───────────────────────────┤
│                     SHARED INFRASTRUCTURE                        │
├─────────────────────────────────────────────────────────────────┤
│ • SPHINCS+ signatures for all reports                           │
│ • P2P gossip for data distribution                              │
│ • On-chain storage for aggregated results                       │
│ • RPC endpoints for UI queries                                  │
└─────────────────────────────────────────────────────────────────┘
```

---

## Implementation Phases

### Phase 1: UI Stub (Week 1)
- [ ] Create REPORTER tab UI skeleton
- [ ] Mock data for all three sections
- [ ] Remove MESSAGES tab (redundant with VOTE SYNC)

### Phase 2: QRNG Display (Week 2)
- [ ] Connect UI to existing `threshold_qrng` endpoints
- [ ] Display local entropy status
- [ ] Show network share collection

### Phase 3: QKD Routing Display (Week 2-3)
- [ ] Connect UI to `qkd-client`
- [ ] Show key pool status
- [ ] Display routing destinations

### Phase 4: Oracle Pallet MVP (Week 3-4)
- [ ] Create `pallet-oracle-feeds` skeleton
- [ ] Implement request/accept extrinsics
- [ ] Basic report submission

### Phase 5: Oracle Integration (Week 4-5)
- [ ] Report aggregation logic
- [ ] SLA tracking
- [ ] Reward distribution

### Phase 6: Full Integration (Week 5-6)
- [ ] End-to-end testing
- [ ] Documentation
- [ ] Mainnet preparation

---

## Open Questions for Discussion

1. **QRNG Hardware**: Are you planning to connect real QRNG devices, or is simulation sufficient for testnet?

2. **Oracle Data Types**: What types of data feeds are priority?
   - Price feeds (crypto, forex)
   - Weather/environmental
   - Sports/events
   - Custom APIs

3. **Minimum Reporters**: What's the minimum number of validators needed to accept a feed? (suggested: 2)

4. **Report Interval**: How often should reporters submit data? (suggested: every 10-50 blocks)

5. **Reward Source**: Where do oracle rewards come from?
   - Requester deposits upfront
   - Network inflation
   - Transaction fees from consumers

6. **Slashing**: How aggressive should slashing be for bad data?
