# Key Rotation Procedures

**Document ID:** ISO-KR-001
**Version:** 1.0
**Effective Date:** 2026-01-19
**Standard Reference:** NIST SP 800-57, ISO 27001 A.10.1.2

---

## 1. Overview

This document provides operational procedures for rotating cryptographic keys in the QuantumHarmony network, including scheduled rotations and emergency key changes.

---

## 2. Rotation Schedule

### 2.1 Standard Rotation Schedule

| Key Type | Rotation Period | Trigger |
|----------|-----------------|---------|
| Validator session keys | Annual | Scheduled |
| Reporter signing keys | Annual | Scheduled |
| TLS certificates | Annual | Expiration |
| API tokens | 90 days | Scheduled |
| Database encryption keys | 2 years | Scheduled |
| HSM access credentials | 90 days | Scheduled |

### 2.2 Emergency Rotation Triggers

Immediate rotation required for:
- Suspected or confirmed key compromise
- Personnel with key access terminated
- Security incident involving key material
- Cryptographic vulnerability discovered

---

## 3. Validator Session Key Rotation

### 3.1 Scheduled Rotation

```
┌─────────────────────────────────────────────────────────────────────────────┐
│              VALIDATOR SESSION KEY ROTATION WORKFLOW                         │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  PRE-ROTATION (T-7 days)                                                    │
│  ┌────────────────────────────────────────────────────────────────────┐     │
│  │ 1. Schedule rotation window                                        │     │
│  │ 2. Notify validator operations team                                │     │
│  │ 3. Verify HSM access and availability                             │     │
│  │ 4. Test key generation in non-production                          │     │
│  └────────────────────────────────────────────────────────────────────┘     │
│                                                                              │
│  KEY GENERATION (T-0)                                                       │
│  ┌────────────────────────────────────────────────────────────────────┐     │
│  │ 1. Generate new Falcon-1024 keys in HSM                           │     │
│  │ 2. Generate new BABE/GRANDPA session keys                         │     │
│  │ 3. Record key hashes in audit log                                 │     │
│  │ 4. Export public keys for submission                              │     │
│  └────────────────────────────────────────────────────────────────────┘     │
│                                                                              │
│  ON-CHAIN UPDATE                                                            │
│  ┌────────────────────────────────────────────────────────────────────┐     │
│  │ 1. Submit set_keys extrinsic with new session keys                │     │
│  │ 2. Wait for next session boundary                                 │     │
│  │ 3. Verify new keys are active                                     │     │
│  │ 4. Monitor block production with new keys                         │     │
│  └────────────────────────────────────────────────────────────────────┘     │
│                                                                              │
│  POST-ROTATION                                                              │
│  ┌────────────────────────────────────────────────────────────────────┐     │
│  │ 1. Verify old keys no longer used                                 │     │
│  │ 2. Archive old keys (secure storage, 1 year)                      │     │
│  │ 3. Update key inventory                                           │     │
│  │ 4. Document rotation in change log                                │     │
│  └────────────────────────────────────────────────────────────────────┘     │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 3.2 CLI Commands

```bash
# Step 1: Generate new session keys (via RPC)
curl -H "Content-Type: application/json" \
  -d '{"id":1, "jsonrpc":"2.0", "method": "author_rotateKeys", "params":[]}' \
  http://localhost:9944

# Response contains new session keys
# {
#   "jsonrpc": "2.0",
#   "result": "0x1234...new_session_keys...",
#   "id": 1
# }

# Step 2: Submit set_keys extrinsic
# Using polkadot-js or custom tooling
qh-cli validator set-keys \
  --keys "0x1234...new_session_keys..." \
  --proof "0x..." \
  --signer validator_account

# Step 3: Verify keys are queued
qh-cli query session queued-keys

# Step 4: After session change, verify active
qh-cli query session validators
```

### 3.3 HSM Key Generation

```bash
# For Thales Luna HSM
# 1. Connect to HSM
lunacm -slot 1

# 2. Generate Falcon-1024 key pair
generateKeyPair -algorithm falcon1024 \
  -label "validator-session-2026" \
  -extractable false \
  -sign true

# 3. Export public key
exportPublicKey -label "validator-session-2026" \
  -output validator_pub_2026.pem

# 4. Update node configuration to use new key
```

---

## 4. Reporter Key Rotation

### 4.1 Standard Rotation

```
1. Generate new Falcon-1024 key pair
   - Use secure random source (QRNG if available)
   - Store in encrypted keystore

2. Submit key update via oracle pallet
   reporter_update_key(new_public_key)

3. Sign test signal with new key
   - Verify signature validation
   - Confirm signal acceptance

4. Archive old key (encrypted backup)
   - Retain for 1 year
   - Record in key inventory

5. Update documentation and inventory
```

### 4.2 Emergency Rotation (Compromise)

```
PRIORITY: IMMEDIATE

1. REVOKE (< 5 minutes)
   □ Stop all signing operations
   □ Disable old key in keystore
   □ Alert operations team

2. GENERATE (< 15 minutes)
   □ Generate new key pair offline
   □ Verify entropy source quality
   □ Store in new, verified keystore

3. SUBMIT (< 30 minutes)
   □ Submit emergency key update
   □ Or: Deregister and re-register if needed
   □ Verify new key accepted

4. INVESTIGATE
   □ Preserve logs for forensics
   □ Identify compromise vector
   □ Implement corrective measures

5. DOCUMENT
   □ Incident report
   □ Update procedures if needed
```

---

## 5. Temporal Ratchet Key Rotation

QuantumHarmony's temporal ratchet automatically rotates encryption keys for P2P communication.

### 5.1 Automatic Rotation

```rust
// Temporal ratchet configuration
const RATCHET_INTERVAL_BLOCKS: u32 = 100;  // Rotate every 100 blocks
const MAX_KEY_AGE_BLOCKS: u32 = 1000;       // Force rotation after 1000 blocks

// Key derivation chain
// block_key[n] = HKDF(master_key, block_hash[n], "temporal-ratchet")
```

### 5.2 Manual Ratchet Trigger

In case of suspected compromise:

```bash
# Force immediate ratchet forward
qh-cli crypto ratchet-forward --steps 10

# This advances the key derivation chain
# All peers will sync to new key within 1 block
```

---

## 6. TLS Certificate Rotation

### 6.1 RPC/API Certificates

```bash
# 1. Generate new certificate (before expiry)
openssl req -x509 -newkey falcon1024 \
  -keyout new_key.pem -out new_cert.pem \
  -days 365 -nodes \
  -subj "/CN=rpc.quantumharmony.network"

# 2. Test new certificate
openssl s_client -connect localhost:9944 \
  -cert new_cert.pem -key new_key.pem

# 3. Update load balancer configuration
# Example: nginx
server {
    listen 443 ssl;
    ssl_certificate /etc/ssl/new_cert.pem;
    ssl_certificate_key /etc/ssl/new_key.pem;
}

# 4. Reload configuration
nginx -s reload

# 5. Verify certificate in use
echo | openssl s_client -connect rpc.quantumharmony.network:443 2>/dev/null | \
  openssl x509 -noout -dates
```

### 6.2 Certificate Monitoring

```yaml
# Prometheus alert for certificate expiry
- alert: CertificateExpiringSoon
  expr: probe_ssl_earliest_cert_expiry - time() < 86400 * 30
  for: 1h
  labels:
    severity: warning
  annotations:
    summary: "TLS certificate expiring in less than 30 days"
```

---

## 7. API Token Rotation

### 7.1 Service Account Tokens

```bash
# 1. Generate new token
NEW_TOKEN=$(qh-cli api generate-token \
  --service monitoring \
  --expires 90d)

# 2. Update service configuration
# Store in secrets manager (Vault, AWS Secrets Manager, etc.)
vault kv put secret/monitoring api_token=$NEW_TOKEN

# 3. Restart service to pick up new token
systemctl restart monitoring-service

# 4. Verify service connectivity
curl -H "Authorization: Bearer $NEW_TOKEN" \
  https://api.quantumharmony.network/health

# 5. Revoke old token
qh-cli api revoke-token --token-id old_token_id
```

### 7.2 Token Rotation Automation

```yaml
# Kubernetes CronJob for automated rotation
apiVersion: batch/v1
kind: CronJob
metadata:
  name: api-token-rotation
spec:
  schedule: "0 0 1 */3 *"  # Every 3 months
  jobTemplate:
    spec:
      template:
        spec:
          containers:
          - name: rotator
            image: qh-tools:latest
            command: ["/bin/sh", "-c"]
            args:
              - |
                NEW_TOKEN=$(qh-cli api generate-token --service $SERVICE)
                vault kv put secret/$SERVICE api_token=$NEW_TOKEN
                kubectl rollout restart deployment/$SERVICE
```

---

## 8. Database Encryption Key Rotation

### 8.1 RocksDB Encryption Rotation

```bash
# 1. Create new encryption key
NEW_KEY=$(qh-cli crypto generate-aes-key --bits 256)

# 2. Re-encrypt database (offline operation)
qh-cli db reencrypt \
  --old-key-file /secure/old_key \
  --new-key-file /secure/new_key \
  --data-dir /var/lib/quantum-harmony

# 3. Verify database integrity
qh-cli db verify --data-dir /var/lib/quantum-harmony

# 4. Update key reference in configuration
# 5. Archive old key (secure, encrypted)
# 6. Destroy old key after retention period
```

---

## 9. Key Inventory

### 9.1 Inventory Template

| Key ID | Type | Purpose | Created | Expires | Location | Owner |
|--------|------|---------|---------|---------|----------|-------|
| VAL-001-2026 | Falcon-1024 | Validator session | 2026-01-19 | 2027-01-19 | HSM Slot 1 | Alice |
| REP-003-2026 | Falcon-1024 | Reporter signing | 2026-01-19 | 2027-01-19 | Keystore | Reporter3 |
| TLS-RPC-2026 | X.509/Falcon | RPC endpoint | 2026-01-19 | 2027-01-19 | /etc/ssl | Ops |
| DB-ENC-001 | AES-256 | Database encryption | 2025-01-01 | 2027-01-01 | KMS | Ops |

### 9.2 Inventory Audit

Quarterly review checklist:
- [ ] All active keys documented
- [ ] No expired keys in use
- [ ] Rotation schedule on track
- [ ] Archived keys properly secured
- [ ] Key owners verified current

---

## 10. Emergency Procedures

### 10.1 Suspected Compromise Response

```
┌─────────────────────────────────────────────────────────────────┐
│               KEY COMPROMISE RESPONSE FLOWCHART                  │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  DETECTION                                                       │
│  ├── Unauthorized signing detected                              │
│  ├── Key material found in logs/breach                          │
│  └── Security alert from monitoring                             │
│           │                                                      │
│           ▼                                                      │
│  IMMEDIATE ACTIONS (< 5 minutes)                                │
│  ├── Disable key (stop signing)                                 │
│  ├── Alert security team                                        │
│  ├── Declare incident                                           │
│  └── Preserve evidence                                          │
│           │                                                      │
│           ▼                                                      │
│  KEY TYPE DETERMINES PATH                                        │
│  ├── Validator key → Governance removal + new key               │
│  ├── Reporter key → Deregister + re-register                    │
│  ├── TLS cert → Revoke + reissue                                │
│  └── API token → Revoke + regenerate                            │
│           │                                                      │
│           ▼                                                      │
│  POST-INCIDENT                                                   │
│  ├── Root cause analysis                                        │
│  ├── Update procedures                                          │
│  └── Strengthen controls                                        │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### 10.2 Emergency Contacts

| Role | Contact | Response Time |
|------|---------|---------------|
| Security On-Call | PagerDuty | 15 minutes |
| HSM Administrator | Direct line | 30 minutes |
| Validator Ops Lead | Direct line | 15 minutes |

---

## 11. Compliance Mapping

| Standard | Requirement | Section |
|----------|-------------|---------|
| NIST 800-57 | Key rotation | Sections 3-6 |
| ISO 27001 A.10.1.2 | Key management | Full document |
| SOC 2 CC6.1 | Logical access | Section 9 |
| PCI DSS 3.6 | Key management | Sections 3-8 |

---

## 12. Document History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0 | 2026-01-19 | Security Team | Initial release |
