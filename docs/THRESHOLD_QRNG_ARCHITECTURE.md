# Threshold QRNG Architecture with Shamir Secret Sharing

**Date**: October 21, 2025
**Version**: 1.0
**Status**: Implementation Design

## Executive Summary

QuantumHarmony implements a **K-of-M threshold scheme** using Shamir Secret Sharing to combine multiple quantum random number generators (QRNGs) into a single, Byzantine-fault-tolerant entropy source. This architecture ensures that:

1. No single device can compromise the system
2. The combined entropy is quantum-secure
3. STARK proofs validate each device's contribution
4. Mempool grooming enforces cryptographic integrity

---

## 1. Architecture Overview

### Components

```
┌─────────────────────────────────────────────────────────────────┐
│                     QRNG Device Layer                           │
├─────────────────────────────────────────────────────────────────┤
│  Device 1          Device 2          Device 3                   │
│  (Toshiba QRNG)    (Crypto4A HSM)    (KIRQ Hub)                 │
│      ↓                 ↓                 ↓                       │
│  STARK Proof₁      STARK Proof₂      STARK Proof₃               │
│  + Share₁          + Share₂          + Share₃                   │
│  (QBER: 0.8%)      (QBER: 1.2%)      (QBER: 0.5%)               │
└─────────────────────────────────────────────────────────────────┘
                           ↓
┌─────────────────────────────────────────────────────────────────┐
│              Per-Device Priority Queues (Node)                  │
├─────────────────────────────────────────────────────────────────┤
│  Queue[Device1]    Queue[Device2]    Queue[Device3]             │
│  Priority: QBER    Priority: QBER    Priority: QBER             │
│  ↓ Lower is better ↓ Lower is better ↓ Lower is better          │
└─────────────────────────────────────────────────────────────────┘
                           ↓
┌─────────────────────────────────────────────────────────────────┐
│            VRF Leader Election (Block N)                        │
├─────────────────────────────────────────────────────────────────┤
│  Leader = Hash(validator_id || block || quantum_seed)           │
│  Lowest VRF output wins                                          │
└─────────────────────────────────────────────────────────────────┘
                           ↓
┌─────────────────────────────────────────────────────────────────┐
│         Leader Collects Top K Shares (coherence_gadget.rs)     │
├─────────────────────────────────────────────────────────────────┤
│  1. Pop top share from each device queue                        │
│  2. Validate STARK proof for each share                         │
│  3. Sort by QBER (ascending)                                    │
│  4. Select best K shares (lowest QBER)                          │
└─────────────────────────────────────────────────────────────────┘
                           ↓
┌─────────────────────────────────────────────────────────────────┐
│            SHAMIR SECRET SHARING RECONSTRUCTION                 │
├─────────────────────────────────────────────────────────────────┤
│  Input:  K shares from M devices (K ≤ M)                        │
│  Output: Combined quantum entropy (32-256 bytes)                │
│  Algorithm: Lagrange interpolation in GF(2^256)                 │
└─────────────────────────────────────────────────────────────────┘
                           ↓
┌─────────────────────────────────────────────────────────────────┐
│        Create Unsigned Transaction                              │
├─────────────────────────────────────────────────────────────────┤
│  Tx Data:                                                        │
│    - combined_entropy: Vec<u8>                                  │
│    - device_shares: Vec<(DeviceId, Share, QBER, STARKProof)>   │
│    - threshold_k: u32                                           │
│    - timestamp: Moment                                          │
└─────────────────────────────────────────────────────────────────┘
                           ↓
┌─────────────────────────────────────────────────────────────────┐
│                    MEMPOOL                                      │
├─────────────────────────────────────────────────────────────────┤
│  Transaction Pool (Ready Transactions)                          │
│  Max: 8192 transactions                                         │
│  Grooming Threshold: 6144 (75%)                                 │
└─────────────────────────────────────────────────────────────────┘
                           ↓
┌─────────────────────────────────────────────────────────────────┐
│          OFFCHAIN WORKER: Mempool Grooming                      │
├─────────────────────────────────────────────────────────────────┤
│  For each transaction in mempool:                               │
│    1. Extract (combined_entropy, device_shares)                 │
│    2. Validate: K shares exist in THIS validator's queues       │
│    3. Validate: Shamir reconstruction matches combined_entropy  │
│    4. Validate: All STARK proofs verify                         │
│    5. If ANY validation fails → ZAP! Remove from mempool        │
└─────────────────────────────────────────────────────────────────┘
                           ↓
┌─────────────────────────────────────────────────────────────────┐
│                   BLOCK PRODUCTION                              │
├─────────────────────────────────────────────────────────────────┤
│  Include valid transactions in block                            │
│  Byzantine consensus: 2/3 validators agree                      │
└─────────────────────────────────────────────────────────────────┘
                           ↓
┌─────────────────────────────────────────────────────────────────┐
│              FINALIZED COMBINED ENTROPY                         │
├─────────────────────────────────────────────────────────────────┤
│  Available for consumption via:                                 │
│    - Runtime API: quantum_getLatestEntropy()                    │
│    - RPC Endpoint: GET /quantum/entropy                         │
│    - Event Subscription: CombinedEntropyReady                   │
│    - Local Storage: sp_io::offchain::local_storage              │
└─────────────────────────────────────────────────────────────────┘
```

---

## 2. Data Structures

### Device Share
```rust
#[derive(Clone, Debug, Encode, Decode)]
pub struct DeviceShare {
    pub device_id: DeviceId,           // "toshiba-qrng-1"
    pub share: Vec<u8>,                // Shamir share bytes
    pub qber: u32,                     // QBER * 10000 (0.8% = 80)
    pub stark_proof: Vec<u8>,          // STARK proof of quantum measurement
    pub timestamp: Moment,
}

#[derive(Clone, Debug, Encode, Decode, PartialEq, Eq, Hash)]
pub struct DeviceId(pub Vec<u8>);
```

### Combined Entropy Transaction
```rust
#[derive(Clone, Debug, Encode, Decode)]
pub struct CombinedEntropyTx {
    pub combined_entropy: Vec<u8>,     // Result of Shamir reconstruction
    pub device_shares: Vec<DeviceShare>, // K shares used for reconstruction
    pub threshold_k: u32,              // Minimum shares required
    pub total_devices_m: u32,          // Total devices available
    pub reconstruction_timestamp: Moment,
}
```

### Per-Device Priority Queue
```rust
pub struct DeviceQueues {
    queues: HashMap<DeviceId, PriorityQueue<DeviceShare, Reverse<u32>>>,
    // Key: DeviceId
    // Value: Priority queue ordered by QBER (lower = higher priority)
}
```

---

## 3. Shamir Secret Sharing Implementation

### Encoding (Device Side)

Each QRNG device generates entropy and splits it into M shares:

```rust
use sharks::{Share, Sharks};

fn generate_shares(
    entropy: &[u8],       // 32 bytes of quantum entropy
    threshold_k: u8,      // Minimum shares to reconstruct (e.g., 2)
    total_m: u8,          // Total shares to create (e.g., 3)
) -> Vec<Vec<u8>> {
    let sharks = Sharks(threshold_k);
    let dealer = sharks.dealer(entropy);

    // Generate M shares
    let shares: Vec<Share> = dealer.take(total_m as usize).collect();

    // Convert to bytes
    shares.iter().map(|s| Vec::from(&s)).collect()
}
```

**Example**:
```
Original Entropy: 0x1a2b3c4d... (32 bytes)
K=2, M=3

Share 1: 0x7f8e9d... → Sent to Device 1 queue
Share 2: 0x3c4b5a... → Sent to Device 2 queue
Share 3: 0x9e8f7d... → Sent to Device 3 queue
```

### Reconstruction (Leader Node)

The VRF-elected leader collects K best shares and reconstructs:

```rust
use sharks::{Share, Sharks};

fn reconstruct_entropy(
    device_shares: &[DeviceShare],
    threshold_k: u8,
) -> Result<Vec<u8>, String> {
    // Sort by QBER (ascending)
    let mut sorted_shares = device_shares.to_vec();
    sorted_shares.sort_by_key(|s| s.qber);

    // Take best K shares
    let best_shares = &sorted_shares[0..(threshold_k as usize)];

    // Convert to Sharks shares
    let sharks_shares: Vec<Share> = best_shares
        .iter()
        .map(|ds| Share::try_from(ds.share.as_slice()).unwrap())
        .collect();

    // Reconstruct
    let sharks = Sharks(threshold_k);
    let entropy = sharks.recover(&sharks_shares)
        .map_err(|_| "Shamir reconstruction failed")?;

    Ok(entropy)
}
```

---

## 4. STARK Proof Validation

Each device share includes a STARK proof that certifies:
1. The entropy was generated from a quantum source
2. The measurement process was valid
3. The QBER is within acceptable bounds

### Validation Flow

```rust
fn validate_device_share(share: &DeviceShare) -> Result<(), String> {
    // 1. Verify STARK proof
    verify_stark_proof(&share.stark_proof, &share.share)?;

    // 2. Check QBER threshold
    if share.qber > 1100 {  // 11% QBER threshold
        return Err("QBER too high");
    }

    // 3. Verify timestamp is recent
    let now = current_timestamp();
    if now - share.timestamp > MAX_SHARE_AGE {
        return Err("Share too old");
    }

    Ok(())
}
```

---

## 5. Mempool Grooming Algorithm

### Objective
Ensure mempool only contains transactions with **valid** K-of-M share sets that can be verified against local priority queues.

### Implementation

```rust
async fn groom_mempool_if_needed(&self) -> Result<(), String> {
    let ready_txs = self.transaction_pool.ready();
    let device_queues = self.device_queues.lock().await;

    for tx in ready_txs {
        // Parse transaction data
        let entropy_tx: CombinedEntropyTx = parse_tx_data(&tx)?;

        // VALIDATION 1: Check if K shares exist in our queues
        let mut valid_shares = 0;
        for device_share in &entropy_tx.device_shares {
            if let Some(queue) = device_queues.get(&device_share.device_id) {
                // Check if this exact share exists in the queue
                if queue.contains(&device_share.share) {
                    valid_shares += 1;
                }
            }
        }

        if valid_shares < entropy_tx.threshold_k {
            warn!("🧹 ZAP! Tx {} - only {}/{} shares found in local queues",
                  tx.hash(), valid_shares, entropy_tx.threshold_k);
            self.transaction_pool.remove_invalid(&[tx.hash()]);
            continue;
        }

        // VALIDATION 2: Shamir reconstruction matches
        let reconstructed = reconstruct_entropy(
            &entropy_tx.device_shares,
            entropy_tx.threshold_k as u8,
        )?;

        if reconstructed != entropy_tx.combined_entropy {
            warn!("🧹 ZAP! Tx {} - Shamir reconstruction mismatch", tx.hash());
            self.transaction_pool.remove_invalid(&[tx.hash()]);
            continue;
        }

        // VALIDATION 3: All STARK proofs verify
        for device_share in &entropy_tx.device_shares {
            if let Err(e) = validate_device_share(device_share) {
                warn!("🧹 ZAP! Tx {} - STARK proof invalid: {}", tx.hash(), e);
                self.transaction_pool.remove_invalid(&[tx.hash()]);
                break;
            }
        }
    }

    Ok(())
}
```

### Byzantine Consensus Property

**Key Invariant**: Each validator independently validates based on **their own** device queues.

- If a validator is missing share data → They delete the transaction
- If 2/3+ validators have the shares → Transaction proceeds to block
- Byzantine fault tolerance: Up to 1/3 validators can be malicious or offline

---

## 6. Reporter Interface (Dev Wallet UI)

### QRNGReporters.tsx Component

The UI provides control and monitoring for QRNG devices:

#### Device Configuration
```typescript
interface QRNGSource {
  id: string;              // "toshiba-qrng-1"
  name: string;            // "Toshiba QRNG #1"
  type: 'toshiba' | 'crypto4a' | 'kirq';
  status: 'stopped' | 'running' | 'error';
  endpoint: string;        // "http://localhost:5555"
  dataRate: number;        // bytes/sec
  qberRate: number;        // Current QBER %
  lastUpdate: Date;
  bytesGenerated: number;
  proofsSubmitted: number;
  sharesCreated: number;   // NEW: Shamir shares created
  sharesUsed: number;      // NEW: Shares used in reconstruction
}
```

#### Start/Stop Control
```typescript
const handleToggleSource = async (sourceId: string) => {
  const source = sources.find(s => s.id === sourceId);

  if (source.status === 'stopped') {
    // Start device reporting
    await invoke('start_qrng_device', {
      deviceId: sourceId,
      endpoint: source.endpoint,
      threshold: thresholdConfig.k,  // Use global K threshold
      totalDevices: thresholdConfig.m
    });
  } else {
    // Stop device reporting
    await invoke('stop_qrng_device', { deviceId: sourceId });
  }
};
```

#### Threshold Configuration Panel
```typescript
interface ThresholdConfig {
  k: number;  // Minimum shares required (e.g., 2)
  m: number;  // Total devices (e.g., 3)
}

// UI allows configuring K-of-M
<TextField
  label="Threshold K (minimum shares)"
  type="number"
  value={thresholdConfig.k}
  onChange={(e) => setThresholdConfig({
    ...thresholdConfig,
    k: parseInt(e.target.value)
  })}
  inputProps={{ min: 1, max: thresholdConfig.m }}
/>

<TextField
  label="Total Devices M"
  type="number"
  value={thresholdConfig.m}
  onChange={(e) => setThresholdConfig({
    ...thresholdConfig,
    m: parseInt(e.target.value)
  })}
  inputProps={{ min: thresholdConfig.k }}
/>
```

#### Real-Time Monitoring
```typescript
// Display Shamir share statistics per device
{sources.map((source) => (
  <Card key={source.id}>
    <CardContent>
      <Typography variant="h6">{source.name}</Typography>
      <Chip
        label={source.status}
        color={source.status === 'running' ? 'success' : 'default'}
      />

      {/* QBER indicator */}
      <LinearProgress
        variant="determinate"
        value={source.qberRate * 10}  // 1% = 10 on scale
        color={source.qberRate < 2 ? 'success' : 'warning'}
      />

      {/* NEW: Shamir statistics */}
      <Typography variant="body2">
        Shares Created: {source.sharesCreated}
      </Typography>
      <Typography variant="body2">
        Shares Used: {source.sharesUsed}
      </Typography>
      <Typography variant="body2">
        Utilization: {((source.sharesUsed / source.sharesCreated) * 100).toFixed(1)}%
      </Typography>
    </CardContent>
  </Card>
))}
```

---

## 7. Node Operator Consumption

### Option 1: Runtime API (On-Chain)

```rust
// In runtime/src/lib.rs
sp_api::decl_runtime_apis! {
    pub trait QuantumEntropyApi {
        /// Get the latest combined entropy
        fn get_latest_entropy() -> Option<Vec<u8>>;

        /// Get entropy with minimum device threshold
        fn get_entropy_with_threshold(min_devices: u32) -> Option<Vec<u8>>;

        /// Get entropy metadata
        fn get_entropy_metadata() -> Option<EntropyMetadata>;
    }
}

#[derive(Encode, Decode, Clone)]
pub struct EntropyMetadata {
    pub combined_entropy_hash: H256,
    pub device_count: u32,
    pub threshold_k: u32,
    pub average_qber: u32,
    pub timestamp: Moment,
}
```

**Usage**:
```bash
# Via RPC
curl -H "Content-Type: application/json" -d '{
  "id": 1,
  "jsonrpc": "2.0",
  "method": "quantum_getLatestEntropy",
  "params": []
}' http://localhost:9944

# Response
{
  "jsonrpc": "2.0",
  "result": {
    "entropy": "0x1a2b3c4d...",
    "metadata": {
      "device_count": 3,
      "threshold_k": 2,
      "average_qber": 95,  // 0.95%
      "timestamp": 1729526400
    }
  },
  "id": 1
}
```

### Option 2: Offchain Worker Export

```rust
impl<T: Config> Pallet<T> {
    pub fn offchain_worker(block_number: T::BlockNumber) {
        // After finalizing combined entropy
        if let Some(entropy) = Self::get_latest_finalized_entropy() {
            // Write to persistent local storage
            sp_io::offchain::local_storage_set(
                StorageKind::PERSISTENT,
                b"quantum_entropy_latest",
                &entropy.encode()
            );

            // Also expose via HTTP (optional)
            Self::serve_entropy_http(&entropy);
        }
    }
}
```

**Usage**:
```bash
# Read from node's local storage
cat ~/.local/share/quantumharmony/offchain-worker/quantum_entropy_latest

# Or via HTTP endpoint
curl http://localhost:9615/quantum/entropy
```

### Option 3: Event Subscription

```rust
#[pallet::event]
#[pallet::generate_deposit(pub(super) fn deposit_event)]
pub enum Event<T: Config> {
    /// New combined entropy is ready
    CombinedEntropyReady {
        entropy_hash: T::Hash,
        device_count: u32,
        threshold_k: u32,
        average_qber: u32,
        timestamp: T::Moment,
    },
}
```

**Usage**:
```javascript
// WebSocket subscription
import { ApiPromise, WsProvider } from '@polkadot/api';

const wsProvider = new WsProvider('ws://localhost:9945');
const api = await ApiPromise.create({ provider: wsProvider });

api.query.system.events((events) => {
  events.forEach((record) => {
    const { event } = record;

    if (event.section === 'quantumCrypto' &&
        event.method === 'CombinedEntropyReady') {
      console.log('New entropy available:', event.data);

      // Fetch the actual entropy
      const entropy = await api.rpc.quantum.getLatestEntropy();
      processEntropy(entropy);
    }
  });
});
```

---

## 8. Configuration Example

### Node Config (`config.toml`)
```toml
[quantum]
# Shamir threshold configuration
threshold_k = 2        # Require 2 shares minimum
total_devices_m = 3    # Out of 3 total devices

# Device registry
[[quantum.devices]]
id = "toshiba-qrng-1"
type = "qrng"
endpoint = "http://localhost:5555"
qber_threshold = 1100  # 11% maximum QBER

[[quantum.devices]]
id = "crypto4a-hsm-1"
type = "rng"
endpoint = "http://localhost:5556"
qber_threshold = 500   # 5% maximum QBER

[[quantum.devices]]
id = "kirq-hub-1"
type = "qrng"
endpoint = "http://localhost:8001"
qber_threshold = 1000  # 10% maximum QBER

[mempool]
ready_limit = 8192
grooming_threshold = 6144  # 75%
grooming_interval_blocks = 3
```

---

## 9. Security Properties

### Byzantine Fault Tolerance
- **Threshold**: K-of-M shares required
- **Maximum Malicious Devices**: M - K devices can be compromised without affecting security
- **Example**: With K=2, M=3 → 1 device can be malicious

### Quantum Security
- STARK proofs ensure quantum origin of entropy
- QBER validation prevents classical entropy injection
- Per-device isolation in priority queues

### Mempool Integrity
- Cross-validation against priority queues
- Shamir reconstruction verification
- Byzantine consensus via independent validator checks
- **ZAP deletion**: Only when validator lacks the exact share data

---

## 10. Implementation Checklist

### Phase 1: Core Infrastructure ✅
- [x] Priority queues per device
- [x] VRF leader election
- [x] STARK proof validation
- [x] Mempool grooming skeleton

### Phase 2: Shamir Integration (In Progress)
- [ ] Add Shamir Secret Sharing library (sharks crate)
- [ ] Implement share generation at device level
- [ ] Implement reconstruction in leader collection
- [ ] Update transaction structure for shares
- [ ] Enhance mempool grooming with share validation

### Phase 3: Reporter Interface (Partial)
- [x] QRNGReporters UI component
- [ ] Add Shamir threshold configuration UI
- [ ] Add share statistics display
- [ ] Implement Tauri backend for device control

### Phase 4: Consumption APIs
- [ ] Runtime API implementation
- [ ] Offchain worker HTTP export
- [ ] Event emission and subscription
- [ ] Documentation for node operators

### Phase 5: Testing & Validation
- [ ] Unit tests for Shamir reconstruction
- [ ] Integration tests with 3 devices
- [ ] Mempool grooming stress tests
- [ ] Byzantine fault injection tests

---

## 11. Performance Considerations

### Shamir Overhead
- **Share Generation**: ~100μs for 3 shares (galois field operations)
- **Reconstruction**: ~50μs for K=2 shares
- **Minimal impact**: < 0.1% of block time

### Mempool Grooming Cost
- **Per Transaction**: 3 validations
  1. Queue lookup: O(K) where K is small (2-3)
  2. Shamir reconstruction: O(K²) polynomial interpolation
  3. STARK verification: ~5ms per proof
- **Total**: ~15ms for K=2, 3 proofs per transaction
- **Acceptable**: Can validate 100+ transactions per block

### Priority Queue Size
- **Per Device**: ~1000 shares max
- **Total Memory**: 3 devices × 1000 shares × 512 bytes = ~1.5 MB
- **Negligible**: Compared to full node storage

---

## 12. Cryptographic Proof Hierarchy

### Three-Layer Proof Architecture

QuantumHarmony implements a **multi-level proof system** to ensure end-to-end cryptographic integrity from device to finalized block:

```
┌─────────────────────────────────────────────────────────────────┐
│            LEVEL 1: Device Authenticity (STARK)                 │
├─────────────────────────────────────────────────────────────────┤
│  Proves: Entropy came from quantum measurement                  │
│  Generated by: Each QRNG device                                 │
│  Verified by: All validators                                    │
│  Properties: Zero-knowledge, quantum-secure                     │
└─────────────────────────────────────────────────────────────────┘
                           ↓
┌─────────────────────────────────────────────────────────────────┐
│         LEVEL 2: Reconstruction Correctness (Hybrid)            │
├─────────────────────────────────────────────────────────────────┤
│  Proves: Shamir reconstruction was done correctly               │
│  Generated by: VRF-elected leader                               │
│  Verified by: Independent validator reconstruction              │
│                                                                  │
│  Components:                                                     │
│   - Commitment: Hash(shares || entropy || leader_id)            │
│   - Signature: Leader signs commitment                          │
│   - Optional STARK: Full polynomial evaluation proof            │
└─────────────────────────────────────────────────────────────────┘
                           ↓
┌─────────────────────────────────────────────────────────────────┐
│           LEVEL 3: Byzantine Consensus (2/3 Validators)         │
├─────────────────────────────────────────────────────────────────┤
│  Proves: Majority of network agrees on validity                 │
│  Mechanism: Transaction only finalizes with 2/3+ agreement      │
│  Protection: Up to 1/3 validators can be malicious              │
└─────────────────────────────────────────────────────────────────┘
```

### Level 1: STARK Proof of Quantum Origin

**Purpose**: Each device must prove its entropy share came from a genuine quantum measurement.

```rust
#[derive(Clone, Debug, Encode, Decode)]
pub struct DeviceSTARKProof {
    /// STARK proof that entropy was generated from quantum source
    pub proof: Vec<u8>,

    /// Public inputs to the STARK circuit
    pub public_inputs: STARKPublicInputs,

    /// Timestamp of measurement
    pub measurement_timestamp: Moment,
}

#[derive(Clone, Debug, Encode, Decode)]
pub struct STARKPublicInputs {
    /// Hash of the entropy share
    pub share_hash: H256,

    /// QBER measurement (scaled by 10000)
    pub qber: u32,

    /// Device ID
    pub device_id: DeviceId,

    /// Quantum measurement parameters
    pub basis: QuantumBasis,
    pub detector_efficiency: u32,
}
```

**Validation**:
```rust
fn verify_device_stark_proof(proof: &DeviceSTARKProof) -> Result<(), String> {
    // Verify STARK proof structure
    stark::verify_proof(&proof.proof, &proof.public_inputs)
        .map_err(|_| "STARK proof verification failed")?;

    // Check QBER threshold
    if proof.public_inputs.qber > MAX_QBER_THRESHOLD {
        return Err(format!("QBER {} exceeds threshold", proof.public_inputs.qber));
    }

    // Check timestamp freshness
    let age = current_timestamp() - proof.measurement_timestamp;
    if age > MAX_SHARE_AGE {
        return Err("STARK proof too old");
    }

    Ok(())
}
```

### Level 2: Shamir Reconstruction Proof

**Purpose**: The leader must prove they correctly reconstructed entropy from the claimed K shares.

#### Option A: Cryptographic Commitment (Default)

```rust
#[derive(Clone, Debug, Encode, Decode)]
pub struct ShamirReconstructionProof {
    /// Commitment to the reconstruction process
    /// Commitment = Hash(sorted_share_hashes || combined_entropy || leader_id || timestamp)
    pub reconstruction_commitment: H256,

    /// Leader's signature over the commitment
    pub leader_signature: Signature,

    /// Merkle root of device shares used
    pub shares_merkle_root: H256,
}
```

**Generation by Leader**:
```rust
fn create_reconstruction_proof(
    device_shares: &[DeviceShare],
    combined_entropy: &[u8],
    leader_keypair: &Keypair,
) -> ShamirReconstructionProof {
    // Sort shares by device ID for determinism
    let mut sorted_shares = device_shares.to_vec();
    sorted_shares.sort_by_key(|s| s.device_id.clone());

    // Compute share hashes
    let share_hashes: Vec<H256> = sorted_shares
        .iter()
        .map(|s| sp_core::blake2_256(&s.share).into())
        .collect();

    // Build Merkle tree
    let shares_merkle_root = compute_merkle_root(&share_hashes);

    // Create commitment
    let commitment_data = (
        &share_hashes,
        combined_entropy,
        &leader_keypair.public,
        current_timestamp(),
    );
    let reconstruction_commitment: H256 =
        sp_core::blake2_256(&commitment_data.encode()).into();

    // Sign commitment
    let leader_signature = leader_keypair.sign(&reconstruction_commitment.as_ref());

    ShamirReconstructionProof {
        reconstruction_commitment,
        leader_signature,
        shares_merkle_root,
    }
}
```

**Validation by Validators**:
```rust
fn verify_reconstruction_proof(
    entropy_tx: &CombinedEntropyTx,
    leader_public_key: &Public,
) -> Result<(), String> {
    // STEP 1: Independently reconstruct Shamir
    let reconstructed = shamir_reconstruct(
        &entropy_tx.device_shares,
        entropy_tx.threshold_k as u8,
    )?;

    // STEP 2: Verify reconstruction matches leader's claim
    if reconstructed != entropy_tx.combined_entropy {
        return Err("Shamir reconstruction mismatch - leader cheated!");
    }

    // STEP 3: Re-compute commitment with same inputs
    let mut sorted_shares = entropy_tx.device_shares.clone();
    sorted_shares.sort_by_key(|s| s.device_id.clone());

    let share_hashes: Vec<H256> = sorted_shares
        .iter()
        .map(|s| sp_core::blake2_256(&s.share).into())
        .collect();

    let expected_commitment_data = (
        &share_hashes,
        &entropy_tx.combined_entropy,
        leader_public_key,
        entropy_tx.reconstruction_timestamp,
    );
    let expected_commitment: H256 =
        sp_core::blake2_256(&expected_commitment_data.encode()).into();

    // STEP 4: Verify commitment matches
    if expected_commitment != entropy_tx.reconstruction_proof.reconstruction_commitment {
        return Err("Reconstruction commitment mismatch");
    }

    // STEP 5: Verify leader signature
    if !sp_core::sr25519::Signature::verify(
        &entropy_tx.reconstruction_proof.leader_signature,
        &expected_commitment,
        leader_public_key,
    ) {
        return Err("Invalid leader signature");
    }

    // STEP 6: Verify Merkle root
    let computed_merkle = compute_merkle_root(&share_hashes);
    if computed_merkle != entropy_tx.reconstruction_proof.shares_merkle_root {
        return Err("Shares Merkle root mismatch");
    }

    Ok(())
}
```

#### Option B: Full STARK Proof (Optional, High-Security Mode)

For critical entropy generation, the leader can optionally generate a full STARK proof of the Shamir polynomial evaluation:

```rust
#[derive(Clone, Debug, Encode, Decode)]
pub struct ShamirSTARKProof {
    /// STARK proof of correct polynomial interpolation
    pub polynomial_proof: Vec<u8>,

    /// Public inputs to STARK circuit
    pub public_inputs: ShamirSTARKPublicInputs,
}

#[derive(Clone, Debug, Encode, Decode)]
pub struct ShamirSTARKPublicInputs {
    /// Hashes of K shares used as input
    pub share_hashes: Vec<H256>,

    /// Hash of reconstructed entropy
    pub entropy_hash: H256,

    /// Threshold K
    pub threshold: u8,

    /// Lagrange coefficients (for verification)
    pub lagrange_coefficients: Vec<[u8; 32]>,
}
```

**STARK Circuit** (pseudocode):
```
Circuit ShamirReconstruction:
  Private inputs:
    - shares: [Share1, Share2, ..., ShareK]
    - polynomial_coefficients: [c0, c1, ..., c_{K-1}]

  Public inputs:
    - share_hashes: [Hash(Share1), Hash(Share2), ..., Hash(ShareK)]
    - entropy_hash: Hash(reconstructed_entropy)

  Constraints:
    1. For each share_i:
         Hash(share_i) == share_hashes[i]

    2. Polynomial interpolation in GF(2^256):
         P(x) = Σ(i=0 to K-1) c_i * x^i
         where shares define K points: (x_i, y_i)

    3. Lagrange interpolation:
         For each i: P(x_i) == y_i

    4. Reconstruction at x=0:
         reconstructed_entropy = P(0) = c_0

    5. Hash check:
         Hash(reconstructed_entropy) == entropy_hash
```

### Level 3: Byzantine Consensus

**Purpose**: Ensure network-wide agreement on transaction validity despite malicious validators.

```rust
/// Mempool grooming with Byzantine fault tolerance
async fn groom_mempool_byzantine(&self) -> Result<(), String> {
    let ready_txs = self.transaction_pool.ready();
    let my_validator_id = self.get_validator_id();

    for tx in ready_txs {
        let entropy_tx: CombinedEntropyTx = parse_tx_data(&tx)?;

        // Perform independent verification
        let verification_result = self.verify_combined_entropy_tx(&entropy_tx).await;

        match verification_result {
            Ok(()) => {
                // Valid - gossip approval
                self.gossip_tx_approval(tx.hash(), my_validator_id);
            },
            Err(e) => {
                // Invalid - check if others agree
                let approvals = self.get_tx_approvals(tx.hash()).await;
                let total_validators = self.validator_set.len();

                // Byzantine threshold: 2/3+ validators
                let byzantine_threshold = ((total_validators * 2) + 2) / 3;

                if approvals.len() < byzantine_threshold {
                    // Not enough approvals - ZAP!
                    warn!("🧹 ZAP! Tx {} - Byzantine consensus failed ({}/{} approvals)",
                          tx.hash(), approvals.len(), byzantine_threshold);
                    self.transaction_pool.remove_invalid(&[tx.hash()]);
                } else {
                    // Majority approves - I might be wrong or have stale data
                    warn!("⚠️  Tx {} - I failed verification but Byzantine consensus passed",
                          tx.hash());
                    // Keep transaction, sync state
                    self.request_missing_shares(tx.hash()).await;
                }
            }
        }
    }

    Ok(())
}
```

### Complete Verification Flow

```rust
/// Full verification with all 3 proof levels
async fn verify_combined_entropy_tx(
    &self,
    entropy_tx: &CombinedEntropyTx,
) -> Result<(), String> {
    // LEVEL 1: Verify all device STARK proofs
    info!("🔍 Level 1: Verifying {} device STARK proofs",
          entropy_tx.device_shares.len());
    for device_share in &entropy_tx.device_shares {
        verify_device_stark_proof(&device_share.stark_proof)
            .map_err(|e| format!("Device {} STARK failed: {}",
                                 device_share.device_id.0, e))?;
    }

    // LEVEL 2: Verify Shamir reconstruction proof
    info!("🔍 Level 2: Verifying Shamir reconstruction proof");
    let leader_public_key = self.get_leader_public_key().await?;
    verify_reconstruction_proof(entropy_tx, &leader_public_key)?;

    // LEVEL 2b: Verify shares exist in local priority queues
    info!("🔍 Level 2b: Cross-checking shares against local priority queues");
    let device_queues = self.device_queues.lock().await;
    let mut valid_shares = 0;

    for device_share in &entropy_tx.device_shares {
        if let Some(queue) = device_queues.get(&device_share.device_id) {
            if queue.contains_share(&device_share.share) {
                valid_shares += 1;
            }
        }
    }

    if valid_shares < entropy_tx.threshold_k {
        return Err(format!(
            "Only {}/{} shares found in local queues - possible Byzantine attack",
            valid_shares, entropy_tx.threshold_k
        ));
    }

    // LEVEL 3: Byzantine consensus handled separately by gossip protocol

    info!("✅ All verification levels passed for tx");
    Ok(())
}
```

### Security Analysis

| Attack Vector | Proof Level | Defense Mechanism |
|--------------|-------------|-------------------|
| **Fake quantum entropy** | Level 1 (STARK) | STARK proof verification fails |
| **Incorrect Shamir reconstruction** | Level 2 (Commitment) | Independent reconstruction + signature check |
| **Share substitution** | Level 2 (Merkle root) | Merkle tree verification detects tampering |
| **Leader cheating** | Level 2 + 3 | Commitment mismatch + Byzantine consensus |
| **Malicious validator** | Level 3 (Byzantine) | 2/3 threshold requires supermajority |
| **Replay attack** | All levels | Timestamp checks + nonce in commitment |

### Performance Impact

- **Level 1 verification**: ~5ms per device STARK proof (K devices = 15ms total for K=3)
- **Level 2 commitment**: ~1ms (hash + signature verification)
- **Level 2 STARK** (optional): ~100ms (only for high-security mode)
- **Level 3 consensus**: ~50ms (gossip protocol + approval collection)

**Total overhead**: ~65ms per transaction (acceptable for block time >> 1 second)

---

## 13. Future Enhancements

1. **Dynamic Threshold Adjustment**
   - Adjust K based on network conditions
   - Lower K during low traffic, higher K for critical entropy

2. **Device Reputation Scoring**
   - Track QBER history per device
   - Prioritize reliable devices for share selection

3. **Multi-Source Entropy Mixing**
   - Combine Shamir entropy with other sources (VRF, RANDAO)
   - XOR mixing for additional security layer

4. **Zero-Knowledge Share Proofs**
   - Prove possession of valid share without revealing it
   - Enable privacy-preserving validation

---

## References

- Shamir Secret Sharing: [Original Paper](https://web.mit.edu/6.857/OldStuff/Fall03/ref/Shamir-HowToShareASecret.pdf)
- STARK Proofs: [StarkWare Documentation](https://docs.starkware.co/starkex/stark-core/)
- Substrate Offchain Workers: [Substrate Docs](https://docs.substrate.io/reference/how-to-guides/offchain-workers/)
- sharks crate: [Rust Implementation](https://docs.rs/sharks/)

---

**End of Document**
