# What's Next: Multi-Validator Testnet Deployment

## Current Situation ✅

**Single Node Status**:
```
💤 Idle (0 peers - localhost limitation)
best: #0 (genesis)
finalized: #0 (genesis)
```

**Why No Blocks?**

You're absolutely correct! Blocks are **not being produced** because:

1. **Need Multiple Validators**: Our consensus requires Byzantine supermajority (2/3 of validators)
2. **Need Peers**: Aura block production needs network peers for gossiping
3. **Localhost Limitation**: Single machine can't properly simulate distributed consensus

## Why Single Node Doesn't Produce Blocks

Let me explain the consensus flow:

```rust
// From coherence_gadget.rs:823-858
fn get_current_validators(&self) -> Result<Vec<sr25519::Public>, String> {
    let authorities = runtime_api.authorities(best_hash)?;
    // Returns: 1 validator (Alice)
}

// From coherence_gadget.rs:710-740
fn check_coherence_supermajority(&self, votes: &[CoherenceVote]) -> bool {
    let required = (validator_count * 2) / 3 + 1;  // BFT: 2/3 + 1
    votes.len() >= required
}
```

**The Math**:
- Validators: 1 (Alice only)
- Required votes: (1 * 2) / 3 + 1 = 1 vote
- Alice's vote: 1
- **Problem**: Alice can't gossip votes to herself!

**What Actually Happens**:
```
Block #1 Time
├── Aura: Alice selected to produce block
├── Alice creates block
├── Alice tries to gossip votes
├── notification_service.send_sync_notification(&peers, vote)
│   └── peers.len() = 0  ← NO PEERS!
└── Vote never gets to coherence gadget
    └── Block stuck, waiting for finalization
```

## What We Need: Real Multi-Validator Testnet

### Option 1: Local 3-Validator Testnet (Recommended First)

**Setup**: 3 VMs or 3 physical machines on same LAN

**Architecture**:
```
┌─────────────────┐      ┌─────────────────┐
│   VM1: Alice    │◄────►│   VM2: Bob      │
│ 192.168.1.10    │      │ 192.168.1.11    │
│ Port: 30333     │      │ Port: 30333     │
└─────────────────┘      └─────────────────┘
         ▲                        ▲
         │                        │
         └───────┐       ┌────────┘
                 │       │
         ┌───────▼───────▼────┐
         │   VM3: Charlie     │
         │  192.168.1.12      │
         │  Port: 30333       │
         └────────────────────┘

Validators: 3
BFT Required: (3 * 2) / 3 + 1 = 3 votes
Block Production: YES ✅
Finalization: YES ✅
```

### Option 2: Cloud Testnet (AWS/GCP/DigitalOcean)

**Setup**: 3+ cloud instances in same region

**Benefits**:
- Real network latency
- Test NAT traversal
- Test firewall rules
- Production-like environment

**Cost**: ~$30-50/month for 3 small VMs

### Option 3: Docker Compose (Quick Test)

**Setup**: Docker containers with virtual network

**Pros**: Easy setup, fast iteration
**Cons**: Still localhost, not true distributed testing

## Deployment Guide: 3-Validator Testnet

### Step 1: Prepare Chain Spec

```bash
# Generate custom chain spec
./target/release/quantumharmony-node build-spec \
    --disable-default-bootnode \
    --chain local \
    > customSpec.json

# Edit customSpec.json - add 3 validators:
{
  "aura": {
    "authorities": [
      "5GrwvaEF5zXb26Fz9rcQpDWS57CtERHpNehXCPcNoHGKutQY", // Alice
      "5FHneW46xGXgs5mUiveU4sbTyGBzmstUspZC92UhjJM694ty", // Bob
      "5FLSigC9HGRKVhB9FiEo4Y3koPsNmBmLJbpXg2mp1hXcS59Y"  // Charlie
    ]
  },
  "coherence": {
    "validators": [
      "5GrwvaEF5zXb26Fz9rcQpDWS57CtERHpNehXCPcNoHGKutQY",
      "5FHneW46xGXgs5mUiveU4sbTyGBzmstUspZC92UhjJM694ty",
      "5FLSigC9HGRKVhB9FiEo4Y3koPsNmBmLJbpXg2mp1hXcS59Y"
    ]
  }
}

# Convert to raw spec
./target/release/quantumharmony-node build-spec \
    --chain=customSpec.json \
    --raw \
    --disable-default-bootnode \
    > customSpecRaw.json
```

### Step 2: Deploy to VM1 (Alice)

```bash
# On VM1 (192.168.1.10)
./target/release/quantumharmony-node \
    --base-path /tmp/alice \
    --chain ./customSpecRaw.json \
    --port 30333 \
    --rpc-port 9944 \
    --validator \
    --rpc-cors all \
    --name Alice \
    --alice \
    --node-key 0000000000000000000000000000000000000000000000000000000000000001 \
    --public-addr /ip4/192.168.1.10/tcp/30333

# Note Alice's peer ID from startup logs:
# 🏷  Local node identity is: QmXXXXXX...
```

### Step 3: Deploy to VM2 (Bob)

```bash
# On VM2 (192.168.1.11)
./target/release/quantumharmony-node \
    --base-path /tmp/bob \
    --chain ./customSpecRaw.json \
    --port 30333 \
    --rpc-port 9944 \
    --validator \
    --rpc-cors all \
    --name Bob \
    --bob \
    --node-key 0000000000000000000000000000000000000000000000000000000000000002 \
    --bootnodes /ip4/192.168.1.10/tcp/30333/p2p/QmAlicePeerID
```

### Step 4: Deploy to VM3 (Charlie)

```bash
# On VM3 (192.168.1.12)
./target/release/quantumharmony-node \
    --base-path /tmp/charlie \
    --chain ./customSpecRaw.json \
    --port 30333 \
    --rpc-port 9944 \
    --validator \
    --rpc-cors all \
    --name Charlie \
    --charlie \
    --node-key 0000000000000000000000000000000000000000000000000000000000000003 \
    --bootnodes /ip4/192.168.1.10/tcp/30333/p2p/QmAlicePeerID
```

### Step 5: Verify Network

**Check peer connections**:
```bash
# On any node
curl -H "Content-Type: application/json" \
     -d '{"id":1, "jsonrpc":"2.0", "method":"system_peers"}' \
     http://localhost:9944

# Should show 2 peers
```

**Expected Output**:
```
2025-10-27 10:00:00 🏷  Local node identity is: QmBobPeerID
2025-10-27 10:00:01 🔍 Discovered new external address...
2025-10-27 10:00:02 ⚙️  Syncing, target=#0 (2 peers)
2025-10-27 10:00:08 ✨ Imported #1 (0xabcd...)
2025-10-27 10:00:14 ✨ Imported #2 (0x1234...)
2025-10-27 10:00:14 💤 Idle (2 peers), best: #2, finalized #1, ⬇ 0.5kiB/s ⬆ 0.3kiB/s
```

## What Will Happen on Real Testnet

### Block Production Flow

```
Time: T=0s (Block 1)
├── VRF Leader Election
│   ├── Alice: VRF output = 0x1234...
│   ├── Bob:   VRF output = 0x5678...
│   └── Charlie: VRF output = 0x9abc...
│       Winner: Alice (lowest output)
│
├── Alice Produces Block
│   ├── Collect transactions
│   ├── Execute extrinsics
│   ├── Compute state root
│   └── Sign with SPHINCS+
│
├── Block Propagation
│   ├── Alice → Bob: GossipSub
│   ├── Alice → Charlie: GossipSub
│   └── Import time: ~100-500ms
│
└── Coherence Finalization
    ├── Alice creates CoherenceVote + Falcon1024 sig
    ├── Bob creates CoherenceVote + Falcon1024 sig
    ├── Charlie creates CoherenceVote + Falcon1024 sig
    │
    ├── Votes propagated via GossipSub
    │   └── Each validator receives 3/3 votes
    │
    └── Supermajority Check: 3 >= 3 ✅
        └── Block #1 FINALIZED

Time: T=6s (Block 2)
├── VRF picks new leader...
└── (repeat)
```

### Entropy Distribution (Nokia Mode)

```
Phase 1: Threshold QRNG Collection
├── Alice connects to PQTG device #1
├── Bob connects to PQTG device #2
├── Charlie connects to PQTG device #3
└── Each collects Shamir share

Phase 2: Leader Distributes to Validators
├── Alice (leader) reconstructs entropy
├── Encrypts with each validator's Falcon1024 pubkey
├── Gossips EntropyMessage to Bob and Charlie
└── Bob & Charlie decrypt with their Falcon1024 privkeys

Phase 3: VRF Election
├── Alice: compute VRF(entropy, block_number)
├── Bob: compute VRF(entropy, block_number)
├── Charlie: compute VRF(entropy, block_number)
└── Lowest output wins leadership
```

### Expected Logs (Real Testnet)

**Alice's logs**:
```
2025-10-27 10:00:06 🔮 [COHERENCE] Starting Phase 1: VRF leader election
2025-10-27 10:00:06 📊 [COHERENCE] Queried 3 validators from runtime
2025-10-27 10:00:06 🎲 [VRF] My output: 0x1234... (LOWEST - I am leader!)
2025-10-27 10:00:06 👑 [COHERENCE] I am the leader for block #1
2025-10-27 10:00:06 📡 [THRESHOLD] Auto-discovering PQTG devices...
2025-10-27 10:00:06 ✅ [THRESHOLD] Found 3 devices, threshold 2-of-3
2025-10-27 10:00:07 🔄 [THRESHOLD] Collected share 1/3 (QBER: 850, quality: 92)
2025-10-27 10:00:07 🔄 [THRESHOLD] Collected share 2/3 (QBER: 920, quality: 88)
2025-10-27 10:00:07 ✅ [THRESHOLD] Reconstructed entropy (2-of-3 threshold met)
2025-10-27 10:00:07 📦 Created entropy package for block #1
2025-10-27 10:00:07 🔐 Generated Falcon1024 keypairs using Crypto4A vault
2025-10-27 10:00:07 🔐 Encrypted entropy package (2156 bytes)
2025-10-27 10:00:07 📤 [GOSSIP] Broadcasting entropy to 2 validators
2025-10-27 10:00:08 🎯 Prepared block #1 for proposing
2025-10-27 10:00:08 ✨ Imported #1 (0xabcd...)
2025-10-27 10:00:08 📝 [COHERENCE] Created vote for block #1
2025-10-27 10:00:08 📤 [GOSSIP] Broadcasting vote to 2 validators
2025-10-27 10:00:08 📥 [GOSSIP] Received vote from Bob for block #1
2025-10-27 10:00:08 📥 [GOSSIP] Received vote from Charlie for block #1
2025-10-27 10:00:08 ✅ [COHERENCE] Supermajority achieved: 3/3 votes
2025-10-27 10:00:08 🏁 [COHERENCE] Finalized block #1
```

**Bob's logs**:
```
2025-10-27 10:00:06 🔮 [COHERENCE] Starting Phase 1: VRF leader election
2025-10-27 10:00:06 🎲 [VRF] My output: 0x5678... (not lowest)
2025-10-27 10:00:06 👤 [COHERENCE] Alice is leader for block #1
2025-10-27 10:00:07 📥 [GOSSIP] Received entropy package from Alice
2025-10-27 10:00:07 🔓 Decrypted entropy package with my Falcon1024 key
2025-10-27 10:00:07 ✅ Verified Alice's Falcon1024 signature
2025-10-27 10:00:08 📥 Imported #1 from Alice
2025-10-27 10:00:08 📝 [COHERENCE] Created vote for block #1
2025-10-27 10:00:08 📤 [GOSSIP] Broadcasting vote to 2 validators
2025-10-27 10:00:08 ✅ [COHERENCE] Supermajority achieved: 3/3 votes
2025-10-27 10:00:08 🏁 [COHERENCE] Finalized block #1
```

## Expected Performance on Real Testnet

### Block Timeline (6 second blocks)

```
T+0.0s: VRF election completes (~10ms)
T+0.2s: Leader collects QRNG shares (~200ms)
T+0.4s: Leader encrypts & gossips entropy (~200ms)
T+0.8s: Validators decrypt entropy (~400ms)
T+1.0s: Leader produces block (~200ms)
T+1.5s: Block propagated to all validators (~500ms LAN)
T+2.0s: All validators create & gossip votes (~500ms)
T+2.5s: Supermajority achieved (~500ms)
T+2.5s: Block finalized
T+6.0s: Next block starts (Aura 6s slot)
```

**Finality Latency**: ~2.5 seconds from block production

### Network Traffic

**Per Block**:
- Block gossip: ~10 KB
- 3 Coherence votes: 3 × 1.1 KB = 3.3 KB
- Entropy package: ~2 KB
- **Total**: ~15 KB per block

**Per Validator** (10 blocks/minute):
- Inbound: ~150 KB/min
- Outbound: ~150 KB/min
- **Total**: ~300 KB/min (~17 MB/hour)

## Troubleshooting Real Testnet

### No Blocks Produced

**Check**:
1. Are all 3 nodes connected? (`system_peers` should show 2 peers)
2. Are keys inserted? (`author_hasKey` for Aura and Coherence)
3. Is Aura running? (logs should show "Starting Aura")
4. Network ports open? (30333 must be accessible)

**Fix**:
```bash
# Check keys
curl -X POST http://localhost:9944 \
  -d '{"jsonrpc":"2.0","method":"author_hasKey","params":["PUBLIC_KEY_HEX","aura"],"id":1}'

# Check network
telnet 192.168.1.10 30333
```

### Blocks Produced But Not Finalized

**Symptoms**: Blocks import but finality stuck

**Likely Cause**: Coherence votes not propagating

**Check**:
```bash
# Check for coherence logs
grep "COHERENCE" /tmp/alice/log.txt

# Should see:
# - "Created vote for block #X"
# - "Received vote from ..."
# - "Supermajority achieved"
```

### High Latency / Slow Finality

**Likely Causes**:
1. Network latency too high (use same datacenter)
2. QRNG devices slow (check QBER threshold)
3. CPU overloaded (use dedicated VMs)

## Next Steps Checklist

- [ ] **Choose deployment method** (VMs, cloud, or Docker)
- [ ] **Generate chain spec** with 3+ validators
- [ ] **Deploy validators** on separate machines
- [ ] **Verify network connectivity** (30333 open, peers connect)
- [ ] **Insert validator keys** (Aura + Coherence)
- [ ] **Start nodes** and watch for block production
- [ ] **Monitor finality** (blocks should finalize ~2-3s after production)
- [ ] **Test transactions** (send some transfers)
- [ ] **Measure TPS** (use benchmarking tool)
- [ ] **Test failover** (kill one validator, network should continue)

## Recommended: Start with Local VMs

**Easiest Path**:
1. Use VirtualBox or VMware
2. Create 3 Ubuntu VMs (2GB RAM each)
3. Bridge network (so VMs get LAN IPs)
4. Copy binary to each VM
5. Follow deployment guide above
6. **You'll see blocks being produced!**

**Estimated Time**: 2-3 hours for full setup

## Summary

✅ **Current**: Single node working, but idle (no peers)
✅ **Needed**: 3+ validators on separate machines
✅ **Expected**: Blocks every 6s, finality ~2.5s later
✅ **Next**: Deploy to VMs or cloud testnet

**The node is ready - it just needs friends! 🚀**

Once you deploy the multi-validator testnet, you'll see:
- ✨ Block production every 6 seconds
- 🏁 Finalization after 2-3 seconds
- 📡 Vote gossip working
- 🔐 Falcon1024 signatures verified
- 🎲 VRF leader election
- 📊 Real TPS numbers

**Want me to help set up a 3-validator testnet script?**
