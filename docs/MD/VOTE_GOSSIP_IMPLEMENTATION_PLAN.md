# Vote Gossip Protocol: Implementation Plan

**Date:** October 27, 2025
**Priority:** 🔴 Critical (Blocks Multi-Validator)
**Estimated Effort:** 2 weeks (1 senior developer)
**Status:** Ready to implement

---

## Executive Summary

The vote gossip protocol is **90% architected** but the critical message passing functions are stubbed out with TODOs. This document provides a step-by-step implementation plan to complete the remaining 10% and unblock multi-validator testnet deployment.

**Current State:**
- ✅ Protocol registered (`/quantumharmony/coherence/1`)
- ✅ NotificationService integrated
- ✅ GossipMessage types defined
- ✅ Vote storage (in-memory HashMap)
- ✅ Vote receiver task spawned
- ❌ Actual message send/receive **NOT IMPLEMENTED**

**What's Blocking:**
```rust
// coherence_gadget.rs:369
// TODO: Implement actual notification reception once NotificationService trait
// provides async methods for receiving messages

// coherence_gadget.rs:829
// TODO: Broadcast to all connected peers once NotificationService trait provides
// the appropriate methods
```

---

## Architecture Review

### Current Vote Flow (Implemented)

```
Validator A:
1. process_block() → create_vote() ✅
2. store_vote(vote) → HashMap ✅
3. broadcast_vote(vote) → [STUB] ❌

Network:
   [No actual gossip happening]

Validator B:
1. run_vote_receiver_static() → [STUB] ❌
2. Would decode and validate vote
3. Would store in HashMap
```

### Target Vote Flow (To Implement)

```
Validator A (Block Producer):
1. Creates vote for block N
2. Signs with Falcon1024
3. Encode vote → SCALE bytes
4. notification_service.send_sync_notification(peers, encoded_vote)
   ↓
libp2p P2P Network:
   GossipSub protocol: /quantumharmony/coherence/1
   TCP port 30333
   Message size: ~1-2 KB per vote
   ↓
Validator B (Receiver):
5. notification_service.next_notification() → encoded_vote
6. Decode SCALE bytes → CoherenceVote
7. Validate:
   - Signature correctness (Falcon1024)
   - Validator is in active set
   - Vote is for known block
   - No duplicate votes from same validator
8. Store in votes HashMap
9. Check for supermajority (>2/3)
10. If supermajority → generate finality certificate
```

---

## Implementation Steps

### Step 1: Understand NotificationService API ✅

The `NotificationService` trait is defined in `sc-network` and provides these key methods:

```rust
pub trait NotificationService: Debug + Send + Sync {
    /// Send synchronous notification to peers
    fn send_sync_notification(&self, peers: &[PeerId], notification: Vec<u8>);

    /// Get next notification (blocking/async)
    async fn next_notification(&mut self) -> Option<(PeerId, Vec<u8>)>;

    /// Get list of connected peers
    fn connected_peers(&self) -> Vec<PeerId>;
}
```

**Status:** API exists in sc-network v0.35+. Need to verify exact method signatures in our Substrate version.

### Step 2: Implement Vote Broadcasting (2-3 days)

**File:** `node/src/coherence_gadget.rs`
**Function:** `broadcast_vote()` (line 810)

**Current Code:**
```rust
fn broadcast_vote(
    &self,
    vote: &CoherenceVote<sp_core::sr25519::Public, NumberFor<Block>, Block::Hash>,
) -> Result<(), String> {
    use crate::coherence_gossip::GossipMessage;
    let message = GossipMessage::<Block>::Vote(vote.clone());
    let encoded = message.encode();

    let service = self._notification_service.lock()
        .map_err(|e| format!("Failed to lock notification service: {}", e))?;

    // TODO: Broadcast to all connected peers
    Ok(())
}
```

**Target Implementation:**
```rust
fn broadcast_vote(
    &self,
    vote: &CoherenceVote<sp_core::sr25519::Public, NumberFor<Block>, Block::Hash>,
) -> Result<(), String> {
    use crate::coherence_gossip::GossipMessage;

    // Encode vote as GossipMessage
    let message = GossipMessage::<Block>::Vote(vote.clone());
    let encoded = message.encode();

    info!(
        "📡 Broadcasting vote for block #{} (size: {} bytes)",
        vote.block_number,
        encoded.len()
    );

    // Lock notification service
    let service = self._notification_service.lock()
        .map_err(|e| format!("Failed to lock notification service: {}", e))?;

    // Get all connected peers
    let peers: Vec<_> = service.connected_peers().into_iter().collect();

    if peers.is_empty() {
        debug!("No peers connected, vote not broadcasted");
        return Ok(());
    }

    info!("📡 Broadcasting to {} peers", peers.len());

    // Broadcast to all peers synchronously
    service.send_sync_notification(&peers, encoded);

    info!("✅ Vote broadcasted to {} validators", peers.len());

    Ok(())
}
```

**Testing:**
```rust
#[test]
fn test_vote_broadcast_encoding() {
    let vote = CoherenceVote {
        validator: sp_core::sr25519::Public::from_raw([1; 64]),
        block_hash: H256::random(),
        block_number: 42,
        coherence_score: 95,
        quantum_state: QuantumState::default(),
        signature: vec![0; 1024], // Falcon1024 signature
        vote_type: VoteType::Prevote,
    };

    let message = GossipMessage::<Block>::Vote(vote);
    let encoded = message.encode();

    assert!(encoded.len() > 0);
    assert!(encoded.len() < 4096); // Should fit in typical MTU

    // Test round-trip
    let decoded: GossipMessage<Block> = Decode::decode(&mut &encoded[..]).unwrap();
    match decoded {
        GossipMessage::Vote(v) => assert_eq!(v.block_number, 42),
        _ => panic!("Wrong message type"),
    }
}
```

### Step 3: Implement Vote Reception (3-4 days)

**File:** `node/src/coherence_gadget.rs`
**Function:** `run_vote_receiver_static()` (line 350)

**Current Code:**
```rust
async fn run_vote_receiver_static(
    notification_service: Arc<std::sync::Mutex<Box<dyn NotificationService>>>,
    votes: Arc<std::sync::Mutex<HashMap<Block::Hash, Vec<CoherenceVote<...>>>>>,
) -> Result<(), String> {
    info!("📡 Vote receiver task starting...");

    loop {
        // Lock and immediately release (placeholder)
        let mut service = notification_service.lock()...;
        drop(service);
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;

        // TODO: Implement actual notification reception
    }
}
```

**Target Implementation:**
```rust
async fn run_vote_receiver_static(
    notification_service: Arc<std::sync::Mutex<Box<dyn NotificationService>>>,
    votes: Arc<std::sync::Mutex<HashMap<Block::Hash, Vec<CoherenceVote<sp_core::sr25519::Public, NumberFor<Block>, Block::Hash>>>>>,
) -> Result<(), String> {
    info!("📡 Vote receiver task starting...");

    loop {
        // Receive next notification from any peer
        let (peer_id, encoded_message) = {
            let mut service = notification_service.lock()
                .map_err(|e| format!("Failed to lock notification service: {}", e))?;

            // This may block until a message arrives
            match service.next_notification().await {
                Some(notification) => notification,
                None => {
                    warn!("📡 Notification stream ended, reconnecting...");
                    tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
                    continue;
                }
            }
        };

        // Decode the gossip message
        let message = match GossipMessage::<Block>::decode(&mut &encoded_message[..]) {
            Ok(msg) => msg,
            Err(e) => {
                warn!("❌ Failed to decode gossip message from {:?}: {}", peer_id, e);
                continue;
            }
        };

        // Handle the message
        match message {
            GossipMessage::Vote(vote) => {
                info!(
                    "📨 Received vote from peer {:?} for block #{} (validator: {:?})",
                    peer_id, vote.block_number, vote.validator
                );

                // Validate the vote
                if let Err(e) = Self::validate_vote_static(&vote) {
                    warn!("❌ Invalid vote from {:?}: {}", peer_id, e);
                    continue;
                }

                // Store the vote
                let mut votes_map = votes.lock()
                    .map_err(|e| format!("Failed to lock votes: {}", e))?;

                let block_votes = votes_map.entry(vote.block_hash)
                    .or_insert_with(Vec::new);

                // Check for duplicate
                if block_votes.iter().any(|v| v.validator == vote.validator) {
                    debug!("⚠️  Duplicate vote from validator {:?}, ignoring", vote.validator);
                    continue;
                }

                // Add vote
                block_votes.push(vote.clone());

                info!(
                    "✅ Vote stored: {} total votes for block {:?}",
                    block_votes.len(),
                    vote.block_hash
                );
            }

            GossipMessage::VoteRequest(block_hash) => {
                debug!("📬 Vote request received for block {:?} from {:?}", block_hash, peer_id);
                // Future: Send our votes for this block back to requester
            }
        }
    }
}
```

**Add Static Validation Function:**
```rust
/// Validate vote without &self (for static context)
fn validate_vote_static(
    vote: &CoherenceVote<sp_core::sr25519::Public, NumberFor<Block>, Block::Hash>,
) -> Result<(), String> {
    // 1. Check coherence score is reasonable
    if vote.coherence_score > 100 {
        return Err(format!("Coherence score {} exceeds maximum", vote.coherence_score));
    }

    // 2. Check QBER is reasonable
    if vote.quantum_state.average_qber > 1100 {
        return Err(format!("QBER {} exceeds 11% threshold", vote.quantum_state.average_qber));
    }

    // 3. Check signature exists
    if vote.signature.len() == 0 {
        return Err("Vote has no signature".to_string());
    }

    // 4. TODO: Verify Falcon1024 signature (Phase 2)
    // verify_falcon_signature(&vote.signature, &vote.validator, ...)?;

    // 5. TODO: Check validator is in active set (Phase 2)
    // if !is_valid_validator(&vote.validator) {
    //     return Err("Validator not in active set".to_string());
    // }

    Ok(())
}
```

### Step 4: Test with 2-Node Setup (2-3 days)

**Goal:** Verify votes propagate between Alice and Bob

**Setup:**
```bash
# Terminal 1: Alice (validator, port 30333)
./target/release/quantumharmony-node \
  --alice \
  --validator \
  --base-path /tmp/alice \
  --chain local \
  --port 30333 \
  --rpc-port 9944

# Terminal 2: Bob (validator, port 30334)
./target/release/quantumharmony-node \
  --bob \
  --validator \
  --base-path /tmp/bob \
  --chain local \
  --port 30334 \
  --rpc-port 9945 \
  --bootnodes /ip4/127.0.0.1/tcp/30333/p2p/<ALICE_PEER_ID>
```

**Expected Logs:**
```
Alice:
🔮 New block imported: #1
👑 Leader elected, collecting proofs...
📊 Creating vote: score=95, QBER=0.5%
📡 Broadcasting vote to 1 peers
✅ Vote broadcasted to 1 validators

Bob:
📨 Received vote from peer <Alice> for block #1
✅ Vote stored: 1 total votes for block 0x...
```

**Success Criteria:**
- ✅ Both nodes discover each other (libp2p)
- ✅ Alice broadcasts votes
- ✅ Bob receives and stores votes
- ✅ Supermajority detected (2/3 = 2 of 2 in dev)
- ✅ Finality achieved on both nodes

### Step 5: Add 3rd Validator (Charlie) (1 day)

**Goal:** Test Byzantine fault tolerance with 3 validators

**Setup:**
```bash
# Terminal 3: Charlie (validator, port 30335)
./target/release/quantumharmony-node \
  --charlie \
  --validator \
  --base-path /tmp/charlie \
  --chain local \
  --port 30335 \
  --rpc-port 9946 \
  --bootnodes /ip4/127.0.0.1/tcp/30333/p2p/<ALICE_PEER_ID>
```

**Test Scenarios:**
1. **Normal operation:** All 3 vote, finality at 2/3 (2 votes)
2. **One offline:** 2 nodes vote, still reach 2/3
3. **Byzantine node:** 1 node sends invalid votes, other 2 finalize
4. **Network partition:** Temporarily disconnect Charlie, verify recovery

**Success Criteria:**
- ✅ Finality with 2/3 votes (even if 1 validator offline)
- ✅ Invalid votes rejected
- ✅ Network heals after partition

---

## Code Changes Summary

### Files to Modify:

**1. `node/src/coherence_gadget.rs`** (Primary changes)
- Line 810: Implement `broadcast_vote()` - add peer discovery and send
- Line 350: Implement `run_vote_receiver_static()` - add message reception loop
- Add `validate_vote_static()` helper function
- Update error handling and logging

**2. `node/src/coherence_gossip.rs`** (Minor updates)
- Verify `GossipMessage` encoding/decoding works
- Add serialization tests
- Document message format

**3. `node/src/service.rs`** (Integration)
- Verify NotificationService is properly passed to gadget
- Ensure coherence protocol is registered

**4. `docs/TRANSPORT_AND_PERFORMANCE.md`** (Documentation)
- Update vote propagation section with actual implementation
- Add bandwidth measurements

### Estimated Lines of Code:

```
broadcast_vote():              ~30 lines
run_vote_receiver_static():    ~80 lines
validate_vote_static():        ~40 lines
Tests:                         ~150 lines
Documentation updates:         ~50 lines
------------------------------------------
Total:                         ~350 lines
```

---

## Testing Strategy

### Unit Tests

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vote_encoding_roundtrip() {
        // Test SCALE encoding/decoding
    }

    #[test]
    fn test_vote_validation() {
        // Test validation logic
    }

    #[test]
    fn test_duplicate_vote_rejection() {
        // Test duplicate detection
    }

    #[test]
    fn test_invalid_signature_rejection() {
        // Test signature validation
    }
}
```

### Integration Tests

**File:** `node/tests/vote_gossip_integration.rs`

```rust
#[tokio::test]
async fn test_two_node_vote_propagation() {
    // Spawn Alice and Bob
    // Wait for connection
    // Trigger block production on Alice
    // Verify Bob receives vote
    // Check both reach finality
}

#[tokio::test]
async fn test_byzantine_vote_rejection() {
    // Spawn 3 nodes
    // Send invalid vote from one node
    // Verify other 2 still reach finality
}
```

### Performance Tests

**Metrics to Measure:**
- Vote propagation latency (target: <50ms LAN)
- Bandwidth per validator (target: <10 KB/s per validator)
- CPU overhead (target: <1% additional)
- Memory usage (target: <10 MB for vote storage)

---

## Risk Mitigation

### Risk 1: NotificationService API Incompatibility 🟡

**Scenario:** sc-network API changed since architecture was designed

**Mitigation:**
1. Check Substrate version: `cargo tree | grep sc-network`
2. Read sc-network docs: https://paritytech.github.io/substrate/master/sc_network/
3. If API changed, adapt implementation to new API
4. Worst case: Use sc-network-gossip crate directly

**Fallback:** Implement custom gossip protocol using libp2p directly

### Risk 2: Vote Spam / DoS 🟡

**Scenario:** Malicious node floods network with invalid votes

**Mitigation:**
1. Rate limiting: Max 1 vote per validator per block
2. Signature verification before storage
3. Ban peers sending invalid votes
4. Connection limits (25 in + 25 out per shard)

**Implementation:** Add rate limiter in `run_vote_receiver_static()`

### Risk 3: Network Partition 🟡

**Scenario:** Nodes can't discover each other

**Mitigation:**
1. Proper bootnode configuration
2. mDNS for local network discovery
3. Kademlia DHT for wide-area
4. Manual peer addition via `--reserved-nodes`

**Testing:** Simulate partitions with iptables rules

### Risk 4: Consensus Deadlock 🔴

**Scenario:** Nodes don't reach supermajority

**Mitigation:**
1. Timeout mechanism: Re-vote after 30 seconds
2. Vote request messages for missing votes
3. Detailed logging to diagnose issues
4. Fallback to single-node mode if needed

**Testing:** Extensive 3-node testing with failures

---

## Success Metrics

### Phase 1: Local Testnet (Week 1)
- ✅ 2 nodes discover each other
- ✅ Votes propagate Alice → Bob
- ✅ Finality achieved on both nodes
- ✅ Logs show vote reception

### Phase 2: 3-Validator Testnet (Week 2)
- ✅ 3 nodes form consensus
- ✅ Finality with 2/3 supermajority
- ✅ Byzantine fault tolerance demonstrated
- ✅ Performance targets met:
  - Finality latency: <2 seconds
  - Vote propagation: <100ms
  - CPU overhead: <1%

### Phase 3: Documentation & Handoff
- ✅ Code comments updated
- ✅ TRANSPORT_AND_PERFORMANCE.md reflects reality
- ✅ Test suite passes (cargo test)
- ✅ README updated with 3-node setup instructions

---

## Timeline

### Week 1: Implementation
- **Day 1-2:** Implement `broadcast_vote()` + tests
- **Day 3-4:** Implement `run_vote_receiver_static()` + tests
- **Day 5:** Two-node local testing and debugging

### Week 2: Testing & Polish
- **Day 6:** Add Charlie (3rd validator), Byzantine testing
- **Day 7:** Performance measurements and optimization
- **Day 8:** Documentation updates
- **Day 9:** Code review and cleanup
- **Day 10:** Final testing and merge to main

---

## Next Steps After Vote Gossip

Once vote gossip is working, the next priorities are:

1. **Falcon Signature Verification** (Week 3)
   - Replace mock signatures with real Falcon1024
   - Integrate with unified vault
   - Add signature verification in vote validation

2. **Session Key Management** (Week 4)
   - Proper validator key storage
   - Key rotation mechanism
   - Integration with substrate keystore

3. **Deployment Guide** (Week 4)
   - Docker Compose for 3-node testnet
   - Cloud deployment scripts (AWS/GCP)
   - Monitoring setup (Prometheus/Grafana)

---

## Conclusion

The vote gossip protocol is **ready to implement**. The architecture is sound, the infrastructure is in place, and we just need to wire up the actual message passing.

**Effort:** 2 weeks (1 developer)
**Impact:** Unblocks multi-validator testnet
**Risk:** Low (API is stable, architecture is proven)

Let's build it! 🚀

---

**Document Status:** ✅ READY FOR IMPLEMENTATION
**Assigned To:** TBD
**Start Date:** TBD
**Target Completion:** 2 weeks after start
