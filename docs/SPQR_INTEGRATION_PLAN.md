# Signal SPQR Integration Plan for QuantumHarmony

**Goal:** Integrate Signal's Sparse Post-Quantum Ratchet (SPQR) for user ↔ node communication while keeping our ternary/quaternary runtime optimizations.

---

## Understanding the Terminology

### ❌ Common Confusion:

"Triple Ratchet" ≠ "Ternary Encoding"

- **Triple** = 3 ratcheting mechanisms (Signal protocol)
- **Ternary** = Base-3 number system (our runtime encoding)

These are completely different concepts with similar-sounding names!

---

## Current Architecture

```
┌─────────────────────────────────────────────┐
│ USER (Wallet)                                │
│ ├─ Creates transaction                       │
│ └─ Signs with SPHINCS+                       │
└──────────────┬──────────────────────────────┘
               │ (JSON-RPC over HTTP)
               │ ⚠️ No forward secrecy!
               ▼
┌─────────────────────────────────────────────┐
│ NODE (Validator)                             │
│ ├─ Receives transaction                      │
│ ├─ Validates signature                       │
│ └─ Routes to runtime                         │
└──────────────┬──────────────────────────────┘
               │
               ▼
┌─────────────────────────────────────────────┐
│ RUNTIME (512-segment toroidal mesh)          │
│ ├─ Quantum routing ✅                        │
│ ├─ Ternary coordinates ✅                    │
│ └─ Quaternary checksums ✅                   │
└─────────────────────────────────────────────┘
```

### Problems:

1. User ↔ Node communication has no forward secrecy
2. Session keys are static (vulnerable to key compromise)
3. No post-compromise security

---

## Proposed Architecture with SPQR

```
┌─────────────────────────────────────────────┐
│ USER (Wallet)                                │
│ ├─ Creates transaction                       │
│ ├─ Signs with SPHINCS+                       │
│ └─ Encrypts with SPQR session ✅ NEW!        │
└──────────────┬──────────────────────────────┘
               │ (SPQR-encrypted)
               │ ✅ Forward secrecy!
               │ ✅ Post-compromise security!
               ▼
┌─────────────────────────────────────────────┐
│ NODE (Validator)                             │
│ ├─ Decrypts with SPQR session ✅ NEW!        │
│ ├─ Validates SPHINCS+ signature             │
│ └─ Routes to runtime                         │
└──────────────┬──────────────────────────────┘
               │ (Internal - no SPQR needed)
               ▼
┌─────────────────────────────────────────────┐
│ RUNTIME (512-segment toroidal mesh)          │
│ ├─ Quantum routing ✅                        │
│ ├─ Ternary coordinates ✅                    │
│ └─ Quaternary checksums ✅                   │
└─────────────────────────────────────────────┘
```

---

## What is SPQR? (Signal's Protocol)

### The Triple Ratchet:

```rust
/// Signal's approach: Run 3 ratchets in parallel
pub struct TripleRatchet {
    /// Ratchet 1: Classic Double Ratchet (existing)
    /// - ECDH key agreement
    /// - Hash chains
    /// - Fast, proven, but NOT quantum-safe
    double_ratchet: DoubleRatchet,

    /// Ratchet 2: SPQR (Sparse Post-Quantum Ratchet)
    /// - ML-KEM 768 key encapsulation
    /// - Erasure-coded chunks (efficient bandwidth)
    /// - Quantum-safe but slower
    spqr: SpqrState,

    /// Ratchet 3: Hash chains (for forward secrecy)
    /// - One-way hash ratcheting
    /// - Provides FS even if keys compromised
    hash_chain: HashChain,
}

/// When encrypting a message:
pub fn encrypt_message(
    &mut self,
    plaintext: &[u8],
) -> Vec<u8> {
    // Get keys from all 3 ratchets
    let key1 = self.double_ratchet.next_key();  // ECDH
    let key2 = self.spqr.next_key();             // ML-KEM
    let key3 = self.hash_chain.next_key();       // Hash

    // Mix them together (hybrid security)
    let mixed_key = kdf_mix([key1, key2, key3]);

    // Encrypt with mixed key
    aes_gcm_encrypt(plaintext, &mixed_key)
}
```

### Why "Sparse"?

- **Sparse** = Not every message triggers ML-KEM
- ML-KEM is expensive (1KB+ per message)
- Solution: Use erasure codes to spread it across many messages
- Chunks of 100 bytes sent with regular messages
- Full ML-KEM key reconstructed after N chunks received

---

## Integration Steps

### Phase 1: User ↔ Node SPQR Sessions

**Goal:** Add SPQR for external API communication

```rust
// In wallet/src/rpc_client.rs
use spqr::TripleRatchet;

pub struct QuantumHarmonyClient {
    node_url: String,

    /// SPQR session with node
    spqr_session: Option<TripleRatchet>,

    /// SPHINCS+ for transaction signing
    signing_key: SphincsSecretKey,
}

impl QuantumHarmonyClient {
    /// Establish SPQR session with node
    pub async fn connect(&mut self) -> Result<()> {
        // 1. Handshake with node (exchange ML-KEM keys)
        let handshake = self.spqr_handshake().await?;

        // 2. Initialize triple ratchet
        self.spqr_session = Some(TripleRatchet::new(handshake));

        Ok(())
    }

    /// Submit transaction with SPQR encryption
    pub async fn submit_transaction(
        &mut self,
        tx: &Transaction,
    ) -> Result<TxHash> {
        // 1. Sign with SPHINCS+ (long-term identity)
        let signed_tx = self.signing_key.sign(tx)?;

        // 2. Encrypt with SPQR (session key)
        let session = self.spqr_session.as_mut()?;
        let encrypted_tx = session.encrypt(&signed_tx.encode())?;

        // 3. Send to node
        let response = self.post_rpc("submit_tx", encrypted_tx).await?;

        // 4. Decrypt response with SPQR
        let decrypted = session.decrypt(&response)?;

        Ok(TxHash::decode(&decrypted)?)
    }
}
```

**Benefits:**
- ✅ Forward secrecy (old messages safe if key compromised)
- ✅ Post-compromise security (future messages safe after healing)
- ✅ Quantum-safe (ML-KEM 768 is NIST-approved)
- ✅ Efficient (erasure-coded chunks = low overhead)

### Phase 2: Node SPQR Handler

```rust
// In node/src/rpc/spqr_handler.rs

pub struct SpqrRpcHandler {
    /// Active SPQR sessions (one per connected user)
    sessions: HashMap<UserId, TripleRatchet>,

    /// Pending ML-KEM handshakes
    pending_handshakes: HashMap<UserId, MlKemHandshake>,
}

impl SpqrRpcHandler {
    /// Handle SPQR-encrypted RPC request
    pub async fn handle_request(
        &mut self,
        user_id: UserId,
        encrypted_request: Vec<u8>,
    ) -> Result<Vec<u8>> {
        // 1. Get user's SPQR session
        let session = self.sessions.get_mut(&user_id)?;

        // 2. Decrypt request
        let decrypted = session.decrypt(&encrypted_request)?;
        let request: RpcRequest = decode(&decrypted)?;

        // 3. Process (existing runtime logic)
        let response = self.process_request(request).await?;

        // 4. Encrypt response with SPQR
        let encrypted_response = session.encrypt(&response.encode())?;

        Ok(encrypted_response)
    }

    /// Note: Runtime still uses ternary/quaternary internally!
    async fn process_request(
        &self,
        request: RpcRequest,
    ) -> Result<RpcResponse> {
        match request {
            RpcRequest::SubmitTransaction(tx) => {
                // Route to segment (quantum + ternary)
                let segment = route_to_segment_quantum()?;
                let coords = TernarySegmentId::from(segment);

                // Execute (our existing runtime)
                execute_in_segment(coords, tx).await
            },
            // ... other RPC methods
        }
    }
}
```

### Phase 3: No Changes to Runtime

**Important:** Runtime keeps using ternary/quaternary!

```rust
// Runtime segment communication (unchanged!)
pub struct CrossSegmentMessage {
    /// Ternary coordinates (efficient, 12 bits)
    from: TernaryCoordinates,
    to: TernaryCoordinates,

    /// Quaternary checksum (error detection)
    checksum: QuaternaryChecksum,

    /// Payload
    data: Vec<u8>,

    /// NO SPQR here! This is internal runtime communication.
    /// SPQR is only for User ↔ Node.
}
```

---

## Performance Impact

### SPQR Overhead:

```
Per-message overhead:
- Chunk data: ~100 bytes (amortized over many messages)
- Ratchet state: ~1KB in memory
- Encryption: ~0.5ms (AES-GCM with mixed keys)
- Decryption: ~0.5ms

Compared to current:
- No encryption: 0 overhead, 0 security ❌
- SPQR: ~100 bytes + 1ms, quantum-safe ✅
```

### Combined with Our Optimizations:

```
User submits transaction:
├─ SPQR encrypt: +1ms
├─ Send to node: ~50ms (network)
├─ SPQR decrypt: +1ms
├─ Quantum routing: +0.01ms ✅ (our optimization)
├─ Ternary encoding: +0.001ms ✅ (our optimization)
├─ Execute in segment: 512x parallel ✅ (our optimization)
└─ Total: ~52ms (mostly network, minimal crypto overhead)

Without our optimizations:
└─ Total: ~150ms (no parallelism, deterministic routing)

Net result: SPQR + our optimizations = FASTER AND MORE SECURE!
```

---

## Implementation Timeline

### Week 1-2: Research & Dependencies
- [ ] Study Signal's SPQR implementation
- [ ] Evaluate Rust libraries (libcrux-ml-kem, etc.)
- [ ] Design QuantumHarmony-specific API

### Week 3-4: Wallet Integration
- [ ] Add SPQR to wallet RPC client
- [ ] Implement ML-KEM handshake
- [ ] Test session establishment

### Week 5-6: Node Integration
- [ ] Add SPQR handler to node
- [ ] Session management (per-user)
- [ ] Integration tests

### Week 7-8: Testing & Rollout
- [ ] Security audit
- [ ] Performance benchmarks
- [ ] Gradual rollout with fallback

---

## Security Benefits

### Before SPQR:

```
Attacker compromises node at time T:
├─ Gains access to all past messages ❌ (no FS)
├─ Can decrypt future messages ❌ (static keys)
└─ Complete compromise
```

### After SPQR:

```
Attacker compromises node at time T:
├─ Past messages safe ✅ (forward secrecy from hash chains)
├─ Future messages safe after healing ✅ (post-compromise security)
├─ Must compromise BOTH ECDH and ML-KEM ✅ (hybrid security)
└─ Limited compromise, self-healing
```

---

## FAQ

### Q: Does SPQR replace our ternary/quaternary work?
**A: NO!** They operate at different layers:
- SPQR: User ↔ Node (external API)
- Ternary/Quaternary: Segment ↔ Segment (runtime internal)

### Q: Is Signal's "Triple Ratchet" related to "ternary" (base-3)?
**A: NO!** Pure coincidence:
- Triple = 3 ratcheting mechanisms
- Ternary = base-3 number system

### Q: Should we use SPQR for runtime segments too?
**A: NO!** SPQR has overhead (1KB+ state per session).
For 512 segments with 6 neighbors each:
- 3,072 potential segment pairs
- 3,072 × 1KB = 3MB just for SPQR state
- Unnecessary: segments are internal, trusted

Better approach:
- SPQR for external (untrusted) user ↔ node
- Quaternary checksums for internal (trusted) segment ↔ segment

### Q: Can we improve on Signal's SPQR?
**A: Maybe!** Signal's SPQR uses:
- ML-KEM 768 (NIST standard)
- Erasure codes (ReedSolomon)

We could investigate:
- Kyber-1024 (higher security)
- More efficient chunking for blockchain workloads
- Ternary-aware key derivation (mix ternary coordinates into KDF)

---

## Conclusion

**SPQR and Ternary/Quaternary are COMPLEMENTARY, not competing!**

```
Full Stack:
┌─────────────────────────────────────────┐
│ User ↔ Node: SPQR (external) 🆕          │
│ ├─ Forward secrecy                       │
│ ├─ Post-compromise security              │
│ └─ Quantum-safe                          │
└──────────────┬──────────────────────────┘
               │
┌──────────────▼──────────────────────────┐
│ Runtime: Ternary/Quaternary (internal) ✅ │
│ ├─ Efficient encoding                    │
│ ├─ Quantum routing                       │
│ └─ Parallel execution                    │
└─────────────────────────────────────────┘
```

**Result:** Best of both worlds!
- External: Quantum-safe + forward secrecy (SPQR)
- Internal: High performance + efficiency (Ternary/Quaternary)

---

**Next Action:** Should we implement SPQR for user ↔ node communication?
