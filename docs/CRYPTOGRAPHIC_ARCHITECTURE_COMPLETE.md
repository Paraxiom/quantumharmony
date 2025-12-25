# QuantumHarmony Complete Cryptographic Architecture

**Date**: October 27, 2025
**Purpose**: Comprehensive understanding of all cryptographic components and their interactions
**Status**: Architecture Clarification Document

---

## Table of Contents

1. [System Overview](#1-system-overview)
2. [Hardware Security Modules (HSM/SSM)](#2-hardware-security-modules-hsmssm)
3. [Threshold QRNG System](#3-threshold-qrng-system)
4. [Falcon1024 Signature System](#4-falcon1024-signature-system)
5. [Pedersen Commitments](#5-pedersen-commitments)
6. [Transport Layer Security](#6-transport-layer-security)
7. [Integration Map](#7-integration-map)
8. [Implementation Priority](#8-implementation-priority)

---

## 1. System Overview

### High-Level Architecture

```
┌──────────────────────────────────────────────────────────────────┐
│                    QUANTUM HARDWARE LAYER                        │
├──────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐          │
│  │ Toshiba QRNG │  │ Crypto4A HSM │  │   KIRQ Hub   │          │
│  │              │  │              │  │              │          │
│  │ - BB84 QKD   │  │ - FIPS 140-3 │  │ - Networked  │          │
│  │ - Photons    │  │ - PQ Crypto  │  │ - Redundancy │          │
│  └──────┬───────┘  └──────┬───────┘  └──────┬───────┘          │
│         │                 │                 │                   │
│         └─────────────────┴─────────────────┘                   │
│                           │                                     │
│                    STARK Proofs                                 │
│                  + Shamir Shares                                │
│                  + QBER Metrics                                 │
└──────────────────────────┬───────────────────────────────────────┘
                           ↓
┌──────────────────────────────────────────────────────────────────┐
│              SECURE TRANSPORT LAYER (MISSING!)                   │
├──────────────────────────────────────────────────────────────────┤
│  ❌ Current: Unencrypted JSON-RPC (HTTP/WebSocket)               │
│  ✅ Needed:  Post-Quantum TLS 1.3 (Kyber + Dilithium)           │
│            OR QSSH (Quantum-Secure SSH)                         │
│            OR Direct QKD Links (if hardware supports)           │
└──────────────────────────┬───────────────────────────────────────┘
                           ↓
┌──────────────────────────────────────────────────────────────────┐
│                THRESHOLD QRNG COORDINATOR                        │
├──────────────────────────────────────────────────────────────────┤
│  Location: coherence_gadget.rs                                   │
│                                                                  │
│  Components:                                                     │
│  1. Per-device priority queues (sorted by QBER)                 │
│  2. VRF leader election                                         │
│  3. Shamir secret sharing reconstruction (K-of-M)               │
│  4. STARK proof validation                                      │
│  5. Byzantine consensus (2/3+ validators)                       │
└──────────────────────────┬───────────────────────────────────────┘
                           ↓
┌──────────────────────────────────────────────────────────────────┐
│           COMBINED QUANTUM ENTROPY POOL                          │
├──────────────────────────────────────────────────────────────────┤
│  Output: 32-256 bytes of verified quantum randomness            │
│  Properties:                                                     │
│    - Byzantine fault-tolerant (survives M-K device failures)   │
│    - STARK-proven authenticity                                  │
│    - Consensus-validated                                        │
│    - QBER-quality-sorted                                        │
└──────────────────────────┬───────────────────────────────────────┘
                           ↓
┌──────────────────────────────────────────────────────────────────┐
│            KEY DERIVATION & CRYPTOGRAPHIC OPERATIONS            │
├──────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  FALCON1024 KEY DERIVATION                              │   │
│  │  Location: falcon_crypto.rs                             │   │
│  │                                                          │   │
│  │  Input Sources (in priority order):                     │   │
│  │   1. Keystore Secret (deterministic component)          │   │
│  │   2. Quantum Entropy (from threshold QRNG)              │   │
│  │   3. HWRNG (CPU entropy, optional mixing)               │   │
│  │                                                          │   │
│  │  KDF Algorithm:                                         │   │
│  │   ❌ Current: BLAKE2-256(public_key) [INSECURE!]        │   │
│  │   ✅ Needed:  SHA3-256(keystore_secret || quantum ||    │   │
│  │              hwrng || domain_separator)                 │   │
│  └─────────────────────────────────────────────────────────┘   │
│                           ↓                                     │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  VALIDATOR SIGNING KEYS                                 │   │
│  │  - Falcon1024 Public Key (1,793 bytes)                  │   │
│  │  - Falcon1024 Secret Key (stored in keystore)           │   │
│  │  - Deterministic: Same keystore → Same Falcon keys      │   │
│  └─────────────────────────────────────────────────────────┘   │
│                           ↓                                     │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  VOTE SIGNING                                            │   │
│  │  Location: coherence_gadget.rs::create_vote()           │   │
│  │                                                          │   │
│  │  Message = SCALE(validator || block_hash || block_num   │   │
│  │                  || coherence_score || quantum_state)   │   │
│  │  Signature = Falcon1024.sign(message, secret_key)       │   │
│  │  Output: ~1,280 bytes                                   │   │
│  └─────────────────────────────────────────────────────────┘   │
│                           ↓                                     │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  PEDERSEN COMMITMENTS (Vote Privacy)                    │   │
│  │  Status: 🚧 PLANNED - NOT YET IMPLEMENTED               │   │
│  │                                                          │   │
│  │  Purpose: Hide vote contents until reveal phase         │   │
│  │  Algorithm: Pedersen commitment over elliptic curve     │   │
│  │                                                          │   │
│  │  Commitment = g^vote · h^blinding_factor                │   │
│  │  Reveal = (vote, blinding_factor)                       │   │
│  │                                                          │   │
│  │  Prevents: Censorship, vote manipulation                │   │
│  └─────────────────────────────────────────────────────────┘   │
└──────────────────────────────────────────────────────────────────┘
```

---

## 2. Hardware Security Modules (HSM/SSM)

### What You Have

**Crypto4A HSM** (Hardware Security Module):
- FIPS 140-3 Level 3 certified
- Physical tamper protection
- Stores cryptographic keys in hardware
- Performs signing operations internally
- Keys never leave the device

### Current Status

❌ **NOT INTEGRATED** - HSM communication layer not implemented

### What's Needed

```rust
// HSM Interface (to be created)
pub trait HsmInterface {
    /// Store a Falcon1024 secret key in HSM
    fn store_falcon_key(&self, key_id: &str, secret_key: &[u8])
        -> Result<(), HsmError>;

    /// Sign a message using key stored in HSM
    /// Key never leaves hardware!
    fn sign_with_falcon(&self, key_id: &str, message: &[u8])
        -> Result<Vec<u8>, HsmError>;

    /// Get public key from HSM
    fn get_falcon_public_key(&self, key_id: &str)
        -> Result<Vec<u8>, HsmError>;
}
```

### Transport Layer for HSM

**Current Problem**: No secure transport defined

**Options**:

1. **PKCS#11** (Standard HSM Interface)
   ```rust
   // Use pkcs11 crate
   use pkcs11::Ctx;
   let ctx = Ctx::new_and_initialize(HSM_MODULE_PATH)?;
   ```

2. **Crypto4A Proprietary API**
   - Manufacturer-specific SDK
   - Typically REST API over mTLS
   - May have native library

3. **QKD-Secured Link** (If supported by Crypto4A)
   - Direct BB84/E91 quantum channel
   - Ultimate security

---

## 3. Threshold QRNG System

### Architecture (Already Implemented!)

**Location**: `node/src/threshold_qrng.rs`

**K-of-M Shamir Secret Sharing**:
- K = 2 (minimum shares needed)
- M = 3 (total devices available)
- Devices: Toshiba QRNG, Crypto4A, KIRQ Hub

### Data Flow

```
Device Share Submission:
  QRNG Device → [MISSING TRANSPORT!] → RPC Handler
  → Priority Queue (sorted by QBER) → Leader Election
  → Shamir Reconstruction → Byzantine Consensus
  → Finalized Entropy
```

### Critical Missing Piece: SECURE TRANSPORT

**Current (threshold_qrng_rpc.rs)**:
```rust
// ❌ INSECURE: Unencrypted HTTP/WebSocket
#[method(name = "qrng_submitDeviceShare")]
async fn submit_device_share(&self, request: SubmitShareRequest)
    -> RpcResult<String>;
```

**What's Needed**:
```rust
// ✅ SECURE: Post-Quantum TLS 1.3
use rustls::{ClientConfig, ServerConfig};
use rustls_post_quantum_crypto::{
    KeyExchangeAlgorithm, SignatureAlgorithm
};

let config = ServerConfig::builder()
    .with_key_exchange(KeyExchangeAlgorithm::Kyber1024)
    .with_signature_algorithm(SignatureAlgorithm::Dilithium5)
    .with_cipher_suite(CipherSuite::ChaCha20Poly1305)
    .build();
```

**Alternative: QSSH**:
```bash
# SSH with post-quantum ciphers
ssh -o "KexAlgorithms=kyber1024" \
    -o "HostKeyAlgorithms=sphincs-shake-256f" \
    -o "Ciphers=chacha20-poly1305" \
    qrng@device.local
```

---

## 4. Falcon1024 Signature System

### Current Implementation

**Location**: `node/src/falcon_crypto.rs`, `node/src/coherence_gadget.rs`

**Status**: ✅ Working, but ⚠️ Insecure Key Derivation

### Security Issues

```rust
// ❌ CURRENT (INSECURE):
let seed = blake2_256(&aura_public_key.0[..32]);
//                     ^^^^^^^^^^^^^^^^^^^^
//                     Using PUBLIC key!

// Problems:
// 1. Public key is... public! Anyone can derive same seed
// 2. BLAKE2 is classical hash (not quantum-resistant KDF)
// 3. No quantum entropy mixed in
```

### Correct Implementation

```rust
// ✅ SECURE:
pub fn derive_falcon_seed(
    keystore: &dyn Keystore,
    aura_keytype: KeyTypeId,
    threshold_qrng: Option<&CombinedEntropyTx>,
) -> Result<[u8; 32], String> {
    // 1. Extract SECRET seed from keystore (NOT public key!)
    let keystore_secret = extract_secret_sphincs_seed(keystore, aura_keytype)?;

    // 2. Get quantum entropy (if available)
    let quantum_entropy = threshold_qrng
        .map(|tx| &tx.combined_entropy[..])
        .unwrap_or(&[0u8; 32]);

    // 3. Get HWRNG entropy
    let mut hwrng_entropy = [0u8; 32];
    OsRng.fill_bytes(&mut hwrng_entropy);

    // 4. Combine with SHA-3 (quantum-resistant)
    use sp_core::hashing::sha3_256;

    let mut combined = Vec::new();
    combined.extend_from_slice(b"falcon1024-v2-quantum-enhanced");
    combined.extend_from_slice(&keystore_secret);
    combined.extend_from_slice(quantum_entropy);
    combined.extend_from_slice(&hwrng_entropy);

    Ok(sha3_256(&combined))
}
```

---

## 5. Pedersen Commitments

### Purpose

**Vote Privacy Layer**: Prevent censorship and manipulation

### How It Works

```
Commit Phase (Block N):
  Vote = (validator_id, coherence_score, quantum_state)
  Blinding = random_scalar()
  Commitment = Pedersen(vote, blinding)
  → Broadcast commitment only (vote hidden)

Reveal Phase (Block N+1):
  → Broadcast (vote, blinding)
  → All validators verify: Pedersen(vote, blinding) == commitment
  → If valid, count vote
  → If invalid, slash validator
```

### Implementation (Planned)

```rust
// To be created: node/src/pedersen.rs

use curve25519_dalek::{RistrettoPoint, Scalar};
use sp_core::crypto::SecureRandom;

pub struct PedersenCommitment {
    pub commitment: RistrettoPoint,
}

pub struct PedersenOpening {
    pub vote_hash: [u8; 32],
    pub blinding_factor: Scalar,
}

pub fn commit_vote(vote: &Vote) -> (PedersenCommitment, PedersenOpening) {
    let vote_hash = blake2_256(&vote.encode());
    let blinding = Scalar::random(&mut OsRng);

    // Pedersen: C = g^vote · h^blinding
    let g = constants::RISTRETTO_BASEPOINT_POINT;
    let h = generate_pedersen_h(); // Second generator

    let commitment = g * Scalar::from_bytes_mod_order(vote_hash)
                   + h * blinding;

    (
        PedersenCommitment { commitment },
        PedersenOpening { vote_hash, blinding_factor: blinding }
    )
}

pub fn verify_opening(
    commitment: &PedersenCommitment,
    opening: &PedersenOpening,
) -> bool {
    let g = constants::RISTRETTO_BASEPOINT_POINT;
    let h = generate_pedersen_h();

    let reconstructed = g * Scalar::from_bytes_mod_order(opening.vote_hash)
                      + h * opening.blinding_factor;

    reconstructed == commitment.commitment
}
```

### Status

🚧 **PLANNED** - Not yet implemented

---

## 6. Transport Layer Security

### Current State

❌ **CRITICAL SECURITY HOLE**

All quantum entropy and device communications use:
- Unencrypted JSON-RPC
- HTTP/WebSocket (no TLS)
- No authentication
- No replay protection

### What's Needed

#### Option A: Post-Quantum TLS 1.3 (Recommended)

```rust
// Use rustls with PQ ciphers
use rustls::ClientConfig;

let config = ClientConfig::builder()
    .with_cipher_suites(&[
        TLS13_KYBER1024_DILITHIUM5_WITH_CHACHA20_POLY1305,
        TLS13_KYBER768_DILITHIUM3_WITH_AES_256_GCM,
    ])
    .with_no_client_auth()
    .build();

// Apply to all RPC connections
let client = jsonrpsee::http_client::HttpClientBuilder::new()
    .set_tcp_config(TcpConfig::with_rustls(config))
    .build()?;
```

#### Option B: QSSH (Quantum-Secure SSH)

```bash
# Configure OpenSSH with PQ algorithms
# /etc/ssh/sshd_config:
KexAlgorithms kyber1024,sntrup761x25519-sha512
HostKeyAlgorithms sphincs-shake-256f,ssh-ed25519
Ciphers chacha20-poly1305@openssh.com
MACs hmac-sha3-512
```

#### Option C: Direct QKD Links

If hardware supports BB84/E91 quantum channels:
- Toshiba QRNG likely supports this
- Crypto4A HSM may support
- KIRQ Hub (network-based, probably needs TLS)

---

## 7. Integration Map

### Complete Data Flow with All Components

```
QRNG Devices → [PQ-TLS] → Threshold QRNG RPC
                              ↓
                    Priority Queues (QBER-sorted)
                              ↓
                    VRF Leader Election
                              ↓
                    Shamir Reconstruction
                              ↓
                    STARK Proof Validation
                              ↓
                    Byzantine Consensus (2/3+)
                              ↓
                    Combined Quantum Entropy Pool
                              ↓
          ┌─────────────────┴─────────────────┐
          ↓                                   ↓
    Falcon Key Derivation              Other Uses
    (SHA3-256 KDF)                     (Nonces, IVs, etc.)
          ↓
    Validator Signing Keys
          ↓
    Vote Creation
          ↓
    [Optional] Pedersen Commitment
          ↓
    Vote Broadcasting (P2P gossip)
          ↓
    Falcon Signature Verification
          ↓
    [Optional] Commitment Reveal & Verify
          ↓
    Vote Tallying → Finality
```

### HSM Integration Points

```
Keystore Secret Extraction
          ↓
    [Optional] Store in HSM (Crypto4A)
          ↓
    Falcon Signing Operations
          ↓
    Sign Inside HSM (keys never leave)
          ↓
    Signature returned to validator
```

---

## 8. Implementation Priority

### Phase 1: Security Fixes (CRITICAL - Do Now!)

**Priority**: 🔴 CRITICAL

1. **Fix Falcon Key Derivation**
   - Replace `blake2_256(public_key)` with `sha3_256(secret_seed || quantum || hwrng)`
   - Extract secret seed from keystore (not public key)
   - Mix in quantum entropy from threshold QRNG

2. **Secure Transport for QRNG**
   - Replace JSON-RPC with Post-Quantum TLS 1.3
   - Add device authentication (SPHINCS+ signatures)
   - Implement replay protection (nonces/timestamps)

3. **Test Keystore Integration**
   - Verify deterministic key derivation works
   - Test with Alice & Bob (different keystores)
   - Confirm quantum entropy mixing

**Estimated Time**: 4-6 hours

### Phase 2: HSM Integration (High Priority)

**Priority**: 🟠 HIGH

1. **Crypto4A HSM Driver**
   - Research Crypto4A API/SDK
   - Implement PKCS#11 or proprietary interface
   - Create `HsmInterface` trait

2. **Falcon Key Storage in HSM**
   - Store validator Falcon secret keys in HSM
   - Signing operations inside HSM
   - Never expose keys to software

3. **Testing**
   - Test HSM signing performance
   - Verify keys never leave hardware
   - Benchmark latency impact

**Estimated Time**: 1-2 days

### Phase 3: Pedersen Commitments (Medium Priority)

**Priority**: 🟡 MEDIUM

1. **Pedersen Module**
   - Create `node/src/pedersen.rs`
   - Implement commit/reveal protocol
   - Use Ristretto255 curve

2. **Vote Protocol Updates**
   - Commit phase (broadcast commitment)
   - Reveal phase (broadcast opening)
   - Verification logic

3. **Slashing for Invalid Reveals**
   - Detect mismatched commitments
   - Slash dishonest validators

**Estimated Time**: 1-2 days

### Phase 4: Production Hardening (Low Priority)

**Priority**: 🟢 LOW

1. **QSSH Deployment**
   - Configure OpenSSH with PQ algorithms
   - Deploy to QRNG devices

2. **QKD Links** (if supported)
   - Direct quantum channels to Toshiba QRNG
   - BB84/E91 protocol

3. **HSM Redundancy**
   - Multi-HSM setup
   - Failover logic

**Estimated Time**: 3-5 days

---

## Summary of Current Status

### ✅ What's Working
- Threshold QRNG architecture designed
- Priority queues implemented
- Shamir secret sharing ready
- Falcon1024 signatures integrated
- Vote gossip protocol functional
- Keystore integration (with security issues)

### ⚠️ What's Partially Working
- Falcon key derivation (works but insecure)
- QRNG transport layer (works but unencrypted)

### ❌ What's Missing
- Secure transport (PQ-TLS or QSSH)
- Secret seed extraction from keystore
- Quantum entropy mixing in KDF
- HSM integration
- Pedersen commitments
- Device authentication

### 🔴 Critical Security Issues
1. Falcon keys derived from public key (anyone can derive!)
2. QRNG shares transmitted in plaintext
3. No device authentication
4. Classical hash function (BLAKE2) instead of quantum-resistant (SHA-3)

---

## Recommendations

**Immediate Actions (Today)**:
1. Fix Falcon key derivation security
2. Add SHA-3 hashing
3. Wire up quantum entropy from threshold QRNG

**This Week**:
1. Implement Post-Quantum TLS for QRNG transport
2. Start HSM integration research
3. Test multi-validator setup with secure keystore

**Next Week**:
1. Complete HSM integration
2. Implement Pedersen commitments
3. Production testing

**Question for you**: What would you like to tackle first?
- A) Fix the Falcon key derivation security (most critical)
- B) Secure the QRNG transport layer (prevent MitM)
- C) Start HSM integration (Crypto4A)
- D) Something else?

