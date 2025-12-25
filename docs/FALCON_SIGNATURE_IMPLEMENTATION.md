# Falcon1024 Signature Verification Implementation

**Date:** October 27, 2025
**Priority:** CRITICAL (Security)
**Estimated Time:** 2-4 hours
**Status:** Ready for Implementation

---

## Overview

Add Falcon1024 post-quantum signature verification to the vote gossip protocol to ensure votes are cryptographically authenticated and cannot be forged.

## Current State

✅ **Already Implemented:**
- Vote gossip P2P protocol (node/src/coherence_gadget.rs)
- CoherenceVote struct with signature field
- Basic vote validation (score bounds, QBER threshold)
- pqcrypto-falcon dependency available in polkadot-sdk

❌ **Missing:**
- Actual Falcon1024 signature generation
- Signature verification in vote receiver
- Validator public key management
- Test vectors for signature validation

---

## Architecture

### Signature Format

**Message to Sign:**
```
SCALE_encode(validator || block_hash || block_number || coherence_score || quantum_state)
```

**Signature Algorithm:** Falcon1024
- **Public Key Size:** 1,793 bytes
- **Signature Size:** ~1,280 bytes (variable)
- **Security Level:** NIST Level 5 (256-bit quantum security)

### Components

1. **Validator Key Management**
   - Store Falcon1024 keypairs in validator keystore
   - Derive from sr25519 seed for compatibility
   - Public keys stored in genesis config

2. **Signature Generation** (coherence_gadget.rs)
   - Generate signature when creating vote
   - Use validator's Falcon1024 private key
   - Attach to CoherenceVote.signature field

3. **Signature Verification** (coherence_gadget.rs - vote receiver)
   - Extract validator public key from genesis/runtime
   - Verify signature matches vote contents
   - Reject invalid signatures immediately

---

## Implementation Plan

### Step 1: Add Falcon1024 Crypto Module

Create `node/src/falcon_crypto.rs`:

```rust
use pqcrypto_falcon::falcon1024;
use pqcrypto_traits::sign::{PublicKey, SecretKey, SignedMessage};
use codec::Encode;

/// Generate Falcon1024 keypair from seed
pub fn generate_keypair(seed: &[u8]) -> (falcon1024::PublicKey, falcon1024::SecretKey) {
    // Derive from seed for deterministic generation
    let (pk, sk) = falcon1024::keypair();
    (pk, sk)
}

/// Sign a message with Falcon1024
pub fn sign_message(message: &[u8], sk: &falcon1024::SecretKey) -> Vec<u8> {
    let signed = falcon1024::sign(message, sk);
    signed.as_bytes().to_vec()
}

/// Verify a Falcon1024 signature
pub fn verify_signature(
    message: &[u8],
    signature: &[u8],
    pk: &falcon1024::PublicKey,
) -> Result<(), String> {
    match falcon1024::open(signature, pk) {
        Ok(verified_msg) if verified_msg == message => Ok(()),
        Ok(_) => Err("Message mismatch after verification".to_string()),
        Err(e) => Err(format!("Signature verification failed: {:?}", e)),
    }
}

/// Encode vote for signing
pub fn encode_vote_for_signing<AccountId: Encode, BlockNumber: Encode, Hash: Encode>(
    vote: &CoherenceVote<AccountId, BlockNumber, Hash>,
) -> Vec<u8> {
    // SCALE encode: validator || block_hash || block_number || coherence_score || quantum_state
    let mut encoded = Vec::new();
    encoded.extend_from_slice(&vote.validator.encode());
    encoded.extend_from_slice(&vote.block_hash.encode());
    encoded.extend_from_slice(&vote.block_number.encode());
    encoded.extend_from_slice(&vote.coherence_score.encode());
    encoded.extend_from_slice(&vote.quantum_state.encode());
    encoded
}
```

### Step 2: Update CoherenceFinality to Store Validator Keys

Modify `node/src/coherence_gadget.rs`:

```rust
pub struct CoherenceFinality<Block: BlockT, Client, BE> {
    // ... existing fields ...

    /// Validator Falcon1024 public keys (AccountId -> PublicKey)
    validator_keys: Arc<Mutex<HashMap<AccountId, falcon1024::PublicKey>>>,

    /// This validator's Falcon1024 secret key (for signing our votes)
    our_secret_key: Option<falcon1024::SecretKey>,
}
```

### Step 3: Implement Signature Generation

Update `broadcast_vote()` in coherence_gadget.rs:

```rust
fn broadcast_vote(
    &self,
    vote: &mut CoherenceVote<...>,
) -> Result<(), String> {
    // Generate signature if we have a secret key
    if let Some(sk) = &self.our_secret_key {
        let message = falcon_crypto::encode_vote_for_signing(vote);
        let signature = falcon_crypto::sign_message(&message, sk);
        vote.signature = BoundedVec::try_from(signature)
            .map_err(|_| "Signature too large".to_string())?;

        info!("🔐 Signed vote with Falcon1024 ({} bytes)", vote.signature.len());
    }

    // ... rest of broadcast logic ...
}
```

### Step 4: Implement Signature Verification

Update `validate_vote_static()` in coherence_gadget.rs:

```rust
fn validate_vote_static(
    vote: &CoherenceVote<...>,
    validator_keys: &HashMap<AccountId, falcon1024::PublicKey>,
) -> Result<(), String> {
    // Basic validation
    if vote.coherence_score > 100000 {
        return Err(format!("Coherence score {} exceeds maximum", vote.coherence_score));
    }

    if vote.quantum_state.average_qber > 1100 {
        return Err(format!("QBER {} exceeds 11% threshold", vote.quantum_state.average_qber));
    }

    // NEW: Falcon1024 signature verification
    let public_key = validator_keys
        .get(&vote.validator)
        .ok_or_else(|| format!("Unknown validator: {:?}", vote.validator))?;

    if vote.signature.is_empty() {
        return Err("Vote has no signature".to_string());
    }

    let message = falcon_crypto::encode_vote_for_signing(vote);
    falcon_crypto::verify_signature(&message, &vote.signature, public_key)?;

    info!("✅ Falcon1024 signature verified for validator {:?}", vote.validator);
    Ok(())
}
```

### Step 5: Load Validator Keys from Genesis

Update genesis config to include Falcon1024 public keys:

```rust
// In chain_spec.rs or similar
pub struct GenesisValidatorSet {
    pub validators: Vec<(AccountId, falcon1024::PublicKey)>,
}

// Load into CoherenceFinality
impl CoherenceFinality<...> {
    pub fn new(..., genesis_validators: Vec<(AccountId, falcon1024::PublicKey)>) -> Self {
        let validator_keys = genesis_validators.into_iter().collect();

        Self {
            validator_keys: Arc::new(Mutex::new(validator_keys)),
            // ... other fields ...
        }
    }
}
```

---

## Testing Strategy

### Unit Tests

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_falcon_sign_and_verify() {
        let (pk, sk) = falcon_crypto::generate_keypair(&[0u8; 32]);
        let message = b"test vote message";

        let signature = falcon_crypto::sign_message(message, &sk);
        assert!(falcon_crypto::verify_signature(message, &signature, &pk).is_ok());
    }

    #[test]
    fn test_invalid_signature_rejected() {
        let (pk, sk) = falcon_crypto::generate_keypair(&[0u8; 32]);
        let message = b"test vote message";
        let signature = falcon_crypto::sign_message(message, &sk);

        // Try to verify with different message
        let wrong_message = b"wrong message";
        assert!(falcon_crypto::verify_signature(wrong_message, &signature, &pk).is_err());
    }

    #[test]
    fn test_vote_signature_roundtrip() {
        let vote = create_test_vote();
        let (pk, sk) = falcon_crypto::generate_keypair(&[0u8; 32]);

        let message = falcon_crypto::encode_vote_for_signing(&vote);
        let signature = falcon_crypto::sign_message(&message, &sk);

        assert!(falcon_crypto::verify_signature(&message, &signature, &pk).is_ok());
    }
}
```

### Integration Tests

1. **Multi-node signature test:**
   - Alice signs vote with her Falcon1024 key
   - Bob receives vote and verifies Alice's signature
   - Bob rejects votes with invalid signatures

2. **Byzantine attack test:**
   - Attacker tries to forge Alice's signature
   - Network rejects forged vote
   - Valid votes still propagate correctly

---

## Security Considerations

### 1. Key Storage
- ⚠️ Secret keys must be stored securely in validator keystore
- ⚠️ Never expose secret keys over network
- ⚠️ Use secure random for key generation

### 2. Signature Replay Protection
- ✅ Block number in signed message prevents replay
- ✅ Block hash ensures vote can't be reused for different blocks

### 3. Quantum Security
- ✅ Falcon1024 provides 256-bit post-quantum security (NIST Level 5)
- ✅ Resistant to Shor's algorithm (quantum factoring)
- ✅ Resistant to Grover's algorithm (quantum search)

### 4. Performance Impact
- **Signing:** ~1ms per vote
- **Verification:** ~0.5ms per vote
- **Network overhead:** +1,280 bytes per vote
- **Acceptable for Byzantine consensus** (consensus happens every 6 seconds)

---

## Migration Strategy

### Phase 1: Soft Launch (Week 1)
- Add signature generation and verification code
- Signatures optional (validate if present, skip if absent)
- Deploy to testnet

### Phase 2: Monitoring (Week 2)
- Monitor signature verification success rate
- Identify any key management issues
- Fix any bugs

### Phase 3: Hard Requirement (Week 3)
- Make signatures mandatory
- Reject unsigned votes
- Full Byzantine protection active

---

## Dependencies

### Required Crates

Add to `node/Cargo.toml`:
```toml
[dependencies]
pqcrypto-falcon = "0.3"
pqcrypto-traits = "0.3"
```

### Polkadot-SDK Updates
- ✅ Already has pqcrypto-falcon in quantum-crypto pallet
- ⚠️ May need to enable `std` feature for node runtime

---

## Success Criteria

- [ ] Falcon1024 keypairs generated deterministically from sr25519 seeds
- [ ] Votes signed correctly with Falcon1024
- [ ] Signatures verified in vote receiver
- [ ] Invalid signatures rejected with clear error messages
- [ ] Unit tests pass (100% coverage on crypto functions)
- [ ] Integration tests pass (multi-node signature propagation)
- [ ] Performance impact < 2ms per vote
- [ ] Network bandwidth increase < 10% (signatures are large but acceptable)

---

## Next Steps After Completion

1. **Validator Set Updates** - Handle validator key rotation
2. **Pedersen Commitments** - Add privacy layer for votes
3. **STARK Integration** - Verify STARK proofs in votes
4. **Threshold Signatures** - Aggregate signatures for efficiency

---

## References

- [Falcon Specification](https://falcon-sign.info/)
- [NIST PQC Standardization](https://csrc.nist.gov/Projects/post-quantum-cryptography)
- [pqcrypto-falcon Rust docs](https://docs.rs/pqcrypto-falcon/)

---

**Status:** Ready for implementation
**Blocked by:** None
**Estimated completion:** 2-4 hours

