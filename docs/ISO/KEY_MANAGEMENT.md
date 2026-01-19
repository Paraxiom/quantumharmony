# Key Management Documentation

## Overview

This document describes the lifecycle management of cryptographic keys in QuantumHarmony, following ISO/TR 23576:2020 and NIST SP 800-57 guidelines.

---

## Key Types

### 1. Validator Session Keys

| Property | Value |
|----------|-------|
| Algorithm | Falcon-1024 (NIST PQC Level V) |
| Purpose | Block signing, GRANDPA voting |
| Lifetime | Per-session (rotatable) |
| Storage | HSM (production), encrypted keystore (dev) |
| Backup | Required, encrypted |

### 2. SPHINCS+ Account Keys

| Property | Value |
|----------|-------|
| Algorithm | SPHINCS+-SHAKE-256f |
| Purpose | Transaction signing |
| Lifetime | Long-term (user-controlled) |
| Storage | User wallet, hardware wallet |
| Backup | User responsibility |

### 3. Node Identity Keys

| Property | Value |
|----------|-------|
| Algorithm | Ed25519 (libp2p) |
| Purpose | P2P authentication |
| Lifetime | Per-node |
| Storage | Node keystore |
| Backup | Optional |

### 4. Reporter Keys

| Property | Value |
|----------|-------|
| Algorithm | Falcon-1024 |
| Purpose | Oracle signal signing |
| Lifetime | While reporter active |
| Storage | Secure keystore |
| Backup | Required |

---

## Key Lifecycle

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         KEY LIFECYCLE PHASES                                 │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  ┌──────────────┐                                                           │
│  │ 1. GENERATION │                                                          │
│  └──────┬───────┘                                                           │
│         │                                                                   │
│         ▼                                                                   │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │ Requirements:                                                        │   │
│  │ • QRNG entropy source (threshold K-of-M)                            │   │
│  │ • Isolated generation environment                                    │   │
│  │ • No network connectivity during generation                          │   │
│  │                                                                       │   │
│  │ Process:                                                             │   │
│  │ 1. Collect entropy from QRNG pool                                   │   │
│  │ 2. Generate key pair in secure enclave                              │   │
│  │ 3. Encrypt private key immediately                                   │   │
│  │ 4. Derive SS58 address from public key                              │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│         │                                                                   │
│         ▼                                                                   │
│  ┌──────────────┐                                                           │
│  │ 2. STORAGE   │                                                          │
│  └──────┬───────┘                                                           │
│         │                                                                   │
│         ▼                                                                   │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │ Production:                                                          │   │
│  │ • HSM (FIPS 140-2 Level 3 minimum)                                  │   │
│  │ • Key never leaves HSM unencrypted                                   │   │
│  │ • Signing operations performed inside HSM                            │   │
│  │                                                                       │   │
│  │ Development:                                                         │   │
│  │ • Encrypted keystore file                                           │   │
│  │ • AES-256-GCM encryption                                            │   │
│  │ • Password-derived key (Argon2id)                                   │   │
│  │                                                                       │   │
│  │ Path: ~/.local/share/quantumharmony/chains/<chain>/keystore/        │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│         │                                                                   │
│         ▼                                                                   │
│  ┌──────────────┐                                                           │
│  │ 3. USAGE     │                                                          │
│  └──────┬───────┘                                                           │
│         │                                                                   │
│         ▼                                                                   │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │ Validator Keys:                                                      │   │
│  │ • Block authoring (BABE)                                            │   │
│  │ • Finality voting (GRANDPA)                                         │   │
│  │ • Governance voting                                                  │   │
│  │                                                                       │   │
│  │ Reporter Keys:                                                       │   │
│  │ • Oracle signal signing                                             │   │
│  │ • Data feed attestation                                             │   │
│  │                                                                       │   │
│  │ User Keys:                                                           │   │
│  │ • Transaction signing                                                │   │
│  │ • Message authentication                                             │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│         │                                                                   │
│         ▼                                                                   │
│  ┌──────────────┐                                                           │
│  │ 4. ROTATION  │                                                          │
│  └──────┬───────┘                                                           │
│         │                                                                   │
│         ▼                                                                   │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │ Triggers:                                                            │   │
│  │ • Scheduled rotation (recommended: annually)                         │   │
│  │ • Suspected compromise                                               │   │
│  │ • Personnel change                                                   │   │
│  │                                                                       │   │
│  │ Process:                                                             │   │
│  │ 1. Generate new key pair                                            │   │
│  │ 2. Submit setKeys extrinsic with new session keys                   │   │
│  │ 3. Wait for next session for activation                             │   │
│  │ 4. Verify new keys are active                                        │   │
│  │ 5. Securely destroy old keys                                         │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│         │                                                                   │
│         ▼                                                                   │
│  ┌──────────────┐                                                           │
│  │ 5. REVOCATION│                                                          │
│  └──────┬───────┘                                                           │
│         │                                                                   │
│         ▼                                                                   │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │ Validator Removal:                                                   │   │
│  │ • Governance vote to remove validator                               │   │
│  │ • Keys become inactive after removal                                 │   │
│  │                                                                       │   │
│  │ Reporter Removal:                                                    │   │
│  │ • Governance vote or self-removal                                   │   │
│  │ • Stake returned after unbonding period                             │   │
│  │                                                                       │   │
│  │ Key Destruction:                                                     │   │
│  │ • Secure erase (multiple overwrites)                                │   │
│  │ • HSM key deletion command                                          │   │
│  │ • Verify destruction in audit log                                    │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Key Generation Commands

### Generate Validator Session Keys

```bash
# Generate new session keys (returns public keys)
curl -X POST http://localhost:9944 \
  -H "Content-Type: application/json" \
  -d '{"jsonrpc":"2.0","id":1,"method":"author_rotateKeys","params":[]}'

# Response: {"jsonrpc":"2.0","id":1,"result":"0x...public_keys..."}
```

### Set Session Keys On-Chain

```bash
# Submit setKeys extrinsic
# Keys format: concatenated BABE + GRANDPA public keys
polkadot-js-api tx.session.setKeys <keys> <proof>
```

### Generate Account Keys

```rust
// Using SPHINCS+ for transaction signing
use pqcrypto_sphincsplus::sphincsshake256frobust::*;

fn generate_account() -> (PublicKey, SecretKey) {
    // Use QRNG entropy
    let entropy = qrng_pool.get_entropy(64)?;
    let (pk, sk) = keypair_from_seed(&entropy);
    (pk, sk)
}
```

---

## Key Storage Formats

### Keystore File Structure

```
~/.local/share/quantumharmony/chains/local/keystore/
├── 62616265<public_key_hex>  # BABE key (prefix: "babe")
├── 6772616e<public_key_hex>  # GRANDPA key (prefix: "gran")
└── 6f726163<public_key_hex>  # Oracle key (prefix: "orac")
```

### Encrypted Key Format

```json
{
  "version": 3,
  "crypto": {
    "cipher": "aes-256-gcm",
    "cipherparams": {
      "iv": "<base64>"
    },
    "ciphertext": "<base64>",
    "kdf": "argon2id",
    "kdfparams": {
      "m": 65536,
      "t": 3,
      "p": 4,
      "salt": "<base64>"
    },
    "mac": "<base64>"
  },
  "address": "<ss58_address>",
  "meta": {
    "name": "Validator Alice",
    "created": "2026-01-19T00:00:00Z"
  }
}
```

---

## Backup Procedures

### Validator Key Backup

```
┌─────────────────────────────────────────────────────────────────┐
│                    BACKUP PROCEDURE                              │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  1. Export encrypted keystore                                   │
│     └── Do NOT export unencrypted keys                          │
│                                                                  │
│  2. Split backup using Shamir Secret Sharing                    │
│     └── 3-of-5 threshold recommended                            │
│                                                                  │
│  3. Store shares in geographically separated locations          │
│     ├── Share 1: Secure facility A                             │
│     ├── Share 2: Secure facility B                             │
│     ├── Share 3: Bank safety deposit box                       │
│     ├── Share 4: Trusted party                                 │
│     └── Share 5: Offline cold storage                          │
│                                                                  │
│  4. Test recovery procedure annually                            │
│                                                                  │
│  5. Update backup after each key rotation                       │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### Recovery Procedure

```bash
# 1. Collect minimum threshold of backup shares
# 2. Reconstruct encrypted keystore
shamir-combine -t 3 share1.txt share2.txt share3.txt > keystore.enc

# 3. Import to new node
quantumharmony-node key insert \
  --keystore-path /path/to/keystore \
  --key-type babe \
  --scheme falcon1024 \
  --suri /path/to/keystore.enc

# 4. Verify keys are functional
curl -X POST http://localhost:9944 \
  -H "Content-Type: application/json" \
  -d '{"jsonrpc":"2.0","id":1,"method":"author_hasSessionKeys","params":["<public_keys>"]}'
```

---

## Security Requirements

### Physical Security

- [ ] HSM stored in locked cabinet
- [ ] Access logged and audited
- [ ] Dual-person control for sensitive operations
- [ ] Video surveillance of secure areas

### Operational Security

- [ ] Key generation on air-gapped system
- [ ] No key material in logs
- [ ] Encrypted transport for any key movement
- [ ] Background checks for key custodians

### Technical Controls

- [ ] FIPS 140-2 Level 3+ HSM for production
- [ ] AES-256 encryption for stored keys
- [ ] Argon2id for password-derived keys
- [ ] Secure key destruction (DoD 5220.22-M)

---

## Audit Requirements

### Key Events to Log

| Event | Required Fields |
|-------|-----------------|
| Key Generation | timestamp, key_id, algorithm, generator |
| Key Usage | timestamp, key_id, operation, result |
| Key Rotation | timestamp, old_key_id, new_key_id, reason |
| Key Revocation | timestamp, key_id, reason, authorizer |
| Backup Created | timestamp, key_id, backup_id, custodians |
| Recovery Performed | timestamp, key_id, backup_id, reason |

### Audit Retention

- Minimum retention: 7 years
- Tamper-evident storage
- Regular integrity verification

---

## References

- [NIST SP 800-57 Part 1](https://csrc.nist.gov/publications/detail/sp/800-57-part-1/rev-5/final) - Key Management Recommendations
- [FIPS 140-2](https://csrc.nist.gov/publications/detail/fips/140/2/final) - Security Requirements for Cryptographic Modules
- [ISO/TR 23576:2020](https://www.iso.org/standard/76072.html) - DLT Security Management
