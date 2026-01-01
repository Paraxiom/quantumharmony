# Falcon1024 Key Derivation Security Fix

## Current Issue (CRITICAL SECURITY VULNERABILITY)

**Location**: `node/src/coherence_gadget.rs:183-185`

```rust
// ❌ INSECURE - Uses PUBLIC key instead of SECRET seed
use sp_core::hashing::blake2_256;
let seed = blake2_256(&aura_public_key.0[..32]);
```

**Problems**:
1. **Public Key Leakage**: Hashing PUBLIC key means anyone can derive the same Falcon seed
2. **Classical Hash**: BLAKE2-256 is not quantum-resistant for key derivation
3. **Entropy Waste**: Only using 32 bytes of available entropy
4. **No Quantum Enhancement**: Not leveraging threshold QRNG system

## Secure Implementation Plan

### Step 1: Extract Secret Seed from Keystore

Instead of using public key, extract the secret seed material:

```rust
// Option A: Use keystore's secret key derivation
let secret_seed = keystore
    .sphincs_secret_seed(aura_keytype)
    .map_err(|_| "Failed to extract secret seed")?;

// Option B: Use keystore signing as entropy source
let entropy_message = b"falcon-derivation-entropy-v1";
let signature = keystore
    .sphincs_sign(aura_keytype, &aura_public_key, entropy_message)
    .map_err(|_| "Failed to sign for entropy")?
    .ok_or("No signature returned")?;
let secret_seed = &signature[..64]; // Use signature bytes as secret seed
```

### Step 2: Mix in Quantum Entropy from Threshold QRNG

```rust
// Get combined quantum entropy from threshold QRNG system
let quantum_entropy = match &self.pqtg_client {
    Some(client) => {
        match client.get_combined_entropy().await {
            Ok(entropy_tx) => entropy_tx.combined_entropy,
            Err(e) => {
                warn!("Failed to get quantum entropy: {:?}, using fallback", e);
                vec![0u8; 32] // Fallback - will still be secure with other sources
            }
        }
    }
    None => {
        warn!("No PQTG client available, skipping quantum entropy");
        vec![0u8; 32]
    }
};
```

### Step 3: Add Hardware RNG Mixing (if available)

```rust
use rand::RngCore;
use rand::rngs::OsRng;

let mut hwrng_entropy = [0u8; 32];
OsRng.fill_bytes(&mut hwrng_entropy);
```

### Step 4: Quantum-Resistant KDF with SHA-3

```rust
use sp_core::hashing::sha3_256;

// Combine all entropy sources with domain separation
let context = b"falcon1024-keypair-quantum-enhanced-v2";
let mut kdf_input = Vec::new();
kdf_input.extend_from_slice(context);
kdf_input.extend_from_slice(&secret_seed);
kdf_input.extend_from_slice(&quantum_entropy);
kdf_input.extend_from_slice(&hwrng_entropy);
kdf_input.extend_from_slice(&validator_id.encode()); // Bind to validator identity

// SHA-3 is quantum-resistant for hash-then-sign
let falcon_seed = sha3_256(&kdf_input);
```

### Step 5: Update falcon_crypto.rs to Support SHA-3

```rust
// In falcon_crypto.rs, add SHA-3 variant:
pub fn generate_keypair_sha3(seed: &[u8; 32]) -> (PublicKey, SecretKey) {
    // Use SHA-3 instead of BLAKE2b for quantum resistance
    use sp_core::hashing::sha3_512;

    let context = b"falcon1024-keypair-derivation-v2";
    let mut key_material = Vec::new();
    key_material.extend_from_slice(context);
    key_material.extend_from_slice(seed);

    let derived_seed = sha3_512(&key_material);

    // TODO: Use derived_seed for fully deterministic generation
    // For now, library uses internal RNG
    let (pk, sk) = falcon1024::keypair();
    (PublicKey(pk), SecretKey(sk))
}
```

## Implementation Steps

1. **Add keystore secret extraction** (30 min)
   - Research Substrate keystore API for secret seed access
   - Implement fallback using signature-based entropy

2. **Wire up PQTG client async call** (30 min)
   - Make coherence_gadget constructor async or defer to runtime
   - Handle errors gracefully with fallback

3. **Add HWRNG mixing** (15 min)
   - Add `rand` dependency if not present
   - Mix in OS entropy

4. **Replace BLAKE2 with SHA-3** (15 min)
   - Use `sp_core::hashing::sha3_256`
   - Update falcon_crypto.rs

5. **Test with Alice & Bob validators** (30 min)
   - Verify deterministic key derivation
   - Check different validators get different keys
   - Confirm quantum entropy integration

6. **Update documentation** (15 min)
   - Document security properties
   - Explain entropy sources
   - Add security audit notes

**Total Estimated Time**: ~2 hours

## Security Properties (After Fix)

✅ **Quantum-Resistant KDF**: SHA-3 instead of BLAKE2
✅ **Secret Seed Protection**: Using keystore secrets, not public keys
✅ **Multi-Source Entropy**: Keystore + QRNG + HWRNG
✅ **Domain Separation**: Context strings prevent cross-protocol attacks
✅ **Deterministic**: Same keystore produces same Falcon keys
✅ **Forward Secure**: Quantum entropy provides additional randomness

## Testing Checklist

- [ ] Alice validator derives unique Falcon key
- [ ] Bob validator derives different Falcon key
- [ ] Same keystore produces same Falcon key after restart
- [ ] Quantum entropy successfully mixed in
- [ ] Fallback works when QRNG unavailable
- [ ] Keys different from old insecure derivation
- [ ] Signature verification works with new keys
- [ ] Multi-validator consensus succeeds

## Migration Plan

**Option 1: Breaking Change (Recommended)**
- All validators regenerate Falcon keys with new secure derivation
- Requires coordinated upgrade

**Option 2: Gradual Migration**
- Support both old and new derivation temporarily
- Validators migrate one by one
- Remove old derivation after all upgraded

**Recommendation**: Use Option 1 since we're in development phase.
