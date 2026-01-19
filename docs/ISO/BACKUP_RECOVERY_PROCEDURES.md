# Backup and Recovery Procedures

**Document ID:** ISO-BR-001
**Version:** 1.0
**Effective Date:** 2026-01-19
**Standard Reference:** ISO 27001 A.12.3, SOC 2 A1.2

---

## 1. Overview

This document defines backup and recovery procedures for QuantumHarmony node operators, ensuring data protection and rapid recovery from failures.

---

## 2. Backup Strategy Summary

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         BACKUP STRATEGY OVERVIEW                             │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  DATA TYPE          FREQUENCY    RETENTION    METHOD                        │
│  ─────────────────────────────────────────────────────────────────────────  │
│  Validator Keys     On creation  Permanent    Encrypted offline             │
│  Chain Data         Daily        30 days      Snapshot + archive            │
│  Configuration      On change    90 days      Version control               │
│  Logs               Continuous   Per policy   Streaming + archive           │
│                                                                              │
│  RECOVERY TIME OBJECTIVES (RTO)                                             │
│  ─────────────────────────────────────────────────────────────────────────  │
│  Validator keys:    < 1 hour (critical for block production)                │
│  Chain data:        < 4 hours (can also sync from network)                  │
│  Configuration:     < 30 minutes                                             │
│                                                                              │
│  RECOVERY POINT OBJECTIVES (RPO)                                            │
│  ─────────────────────────────────────────────────────────────────────────  │
│  Validator keys:    0 (no data loss acceptable)                             │
│  Chain data:        24 hours (sync from network fills gap)                  │
│  Configuration:     0 (version controlled)                                   │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 3. Validator Key Backup

### 3.1 Initial Key Backup

**CRITICAL: Perform immediately after key generation.**

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    VALIDATOR KEY BACKUP PROCEDURE                            │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  1. GENERATE BACKUP (Secure Environment)                                    │
│     ┌──────────────────────────────────────────────────────────────────┐    │
│     │ □ Use air-gapped machine                                        │    │
│     │ □ Disable all network interfaces                                │    │
│     │ □ Export key material from HSM/keystore                         │    │
│     │ □ Encrypt with AES-256-GCM                                      │    │
│     │ □ Use separate encryption key (stored separately)               │    │
│     └──────────────────────────────────────────────────────────────────┘    │
│                                                                              │
│  2. SPLIT SECRET (Shamir's Secret Sharing)                                  │
│     ┌──────────────────────────────────────────────────────────────────┐    │
│     │ □ Split encryption key into N shares (e.g., 5)                  │    │
│     │ □ Require K shares to reconstruct (e.g., 3)                     │    │
│     │ □ Distribute shares to different custodians/locations           │    │
│     └──────────────────────────────────────────────────────────────────┘    │
│                                                                              │
│  3. STORE SECURELY                                                          │
│     ┌──────────────────────────────────────────────────────────────────┐    │
│     │ Primary: Bank safe deposit box                                  │    │
│     │ Secondary: Geographic alternate location                        │    │
│     │ Tertiary: Hardware security device (encrypted USB)              │    │
│     └──────────────────────────────────────────────────────────────────┘    │
│                                                                              │
│  4. VERIFY                                                                  │
│     ┌──────────────────────────────────────────────────────────────────┐    │
│     │ □ Test decryption with backup                                   │    │
│     │ □ Verify key matches production (compare public key)            │    │
│     │ □ Document backup location and custodians                       │    │
│     │ □ Schedule annual verification                                  │    │
│     └──────────────────────────────────────────────────────────────────┘    │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 3.2 Key Backup Commands

```bash
# Export session keys (do this on air-gapped machine)
# CAUTION: This exposes raw key material

# For Substrate keystore
qh-cli keys export \
  --keystore-path /var/lib/quantum-harmony/keystore \
  --key-type gran \
  --output gran_backup.json

# Encrypt the backup
age -p -o gran_backup.json.age gran_backup.json

# Securely delete plaintext
shred -u gran_backup.json

# Generate Shamir shares for encryption password
# (Use dedicated tool like ssss or vault)
echo "$PASSWORD" | ssss-split -t 3 -n 5 -q
# Share 1: 1-xxxxx
# Share 2: 2-xxxxx
# ... etc
```

### 3.3 Key Recovery

```bash
# 1. Reconstruct encryption password from shares
ssss-combine -t 3 << EOF
1-share1
2-share2
4-share4
EOF

# 2. Decrypt key backup
age -d -o gran_backup.json gran_backup.json.age

# 3. Import keys to keystore
qh-cli keys insert \
  --keystore-path /var/lib/quantum-harmony/keystore \
  --key-type gran \
  --input gran_backup.json

# 4. Verify key imported correctly
qh-cli keys list --keystore-path /var/lib/quantum-harmony/keystore

# 5. Securely delete plaintext backup
shred -u gran_backup.json
```

---

## 4. Chain Data Backup

### 4.1 Snapshot Strategy

| Backup Type | Frequency | Retention | Use Case |
|-------------|-----------|-----------|----------|
| Hot snapshot | Every 6 hours | 48 hours | Quick recovery |
| Daily snapshot | Daily (02:00 UTC) | 30 days | Standard recovery |
| Weekly archive | Weekly (Sunday) | 90 days | Long-term recovery |
| Monthly archive | Monthly (1st) | 1 year | Compliance |

### 4.2 Snapshot Procedure

```bash
#!/bin/bash
# snapshot-chain.sh - Create chain data snapshot

CHAIN_DIR="/var/lib/quantum-harmony/chains/mainnet"
BACKUP_DIR="/backup/quantum-harmony"
TIMESTAMP=$(date +%Y%m%d_%H%M%S)
SNAPSHOT_NAME="chain_snapshot_${TIMESTAMP}"

# 1. Check if node is running
if pgrep -x "quantum-harmony" > /dev/null; then
    echo "Warning: Node is running. Snapshot may be inconsistent."
    echo "For consistent snapshot, stop node first."
fi

# 2. Create snapshot using RocksDB checkpoint (atomic)
qh-cli db snapshot \
  --chain-dir "$CHAIN_DIR" \
  --output "$BACKUP_DIR/$SNAPSHOT_NAME"

# 3. Calculate checksum
sha256sum "$BACKUP_DIR/$SNAPSHOT_NAME.tar.gz" > \
  "$BACKUP_DIR/$SNAPSHOT_NAME.sha256"

# 4. Compress and encrypt
tar czf - "$BACKUP_DIR/$SNAPSHOT_NAME" | \
  age -R /etc/quantum-harmony/backup_key.pub \
  > "$BACKUP_DIR/${SNAPSHOT_NAME}.tar.gz.age"

# 5. Upload to remote storage
aws s3 cp "$BACKUP_DIR/${SNAPSHOT_NAME}.tar.gz.age" \
  s3://quantum-harmony-backups/chain/

# 6. Clean up local files
rm -rf "$BACKUP_DIR/$SNAPSHOT_NAME"

# 7. Log success
echo "$(date): Snapshot $SNAPSHOT_NAME created successfully" >> \
  /var/log/quantum-harmony/backup.log
```

### 4.3 Automated Backup (Cron)

```cron
# /etc/cron.d/quantum-harmony-backup

# Hot snapshots every 6 hours
0 */6 * * * root /opt/quantum-harmony/scripts/snapshot-chain.sh hot

# Daily snapshot at 02:00 UTC
0 2 * * * root /opt/quantum-harmony/scripts/snapshot-chain.sh daily

# Weekly archive on Sundays at 03:00 UTC
0 3 * * 0 root /opt/quantum-harmony/scripts/snapshot-chain.sh weekly

# Monthly archive on 1st at 04:00 UTC
0 4 1 * * root /opt/quantum-harmony/scripts/snapshot-chain.sh monthly
```

---

## 5. Configuration Backup

### 5.1 Git-Based Configuration Management

```bash
# Directory structure
/etc/quantum-harmony/
├── .git/                    # Version control
├── config.toml              # Main configuration
├── chain-spec.json          # Chain specification
├── prometheus.yml           # Monitoring config
└── secrets/                 # Encrypted secrets (git-crypt)
    ├── .gitattributes       # Encryption rules
    └── api_keys.env
```

### 5.2 Configuration Backup Commands

```bash
# Initialize config repository
cd /etc/quantum-harmony
git init
git-crypt init

# Add encryption for secrets
echo "secrets/** filter=git-crypt diff=git-crypt" >> .gitattributes
git-crypt add-gpg-user security@quantumharmony.network

# Commit configuration
git add .
git commit -m "Configuration update: $(date +%Y-%m-%d)"

# Push to secure remote
git push origin main

# Configuration change triggers webhook → notification
```

### 5.3 Configuration Recovery

```bash
# Clone configuration repository
git clone git@github.com:org/quantum-harmony-config.git /etc/quantum-harmony

# Unlock encrypted secrets
git-crypt unlock

# Verify configuration
qh-cli config verify --config /etc/quantum-harmony/config.toml
```

---

## 6. Recovery Procedures

### 6.1 Full Node Recovery

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                      FULL NODE RECOVERY PROCEDURE                            │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  SCENARIO: Complete node failure (hardware, disaster, etc.)                 │
│  RTO: 4 hours                                                               │
│                                                                              │
│  1. PROVISION NEW HARDWARE (< 30 minutes)                                   │
│     □ Deploy new server/VM                                                  │
│     □ Install base OS                                                       │
│     □ Configure network access                                              │
│                                                                              │
│  2. INSTALL SOFTWARE (< 30 minutes)                                         │
│     □ Install quantum-harmony node                                          │
│     □ Restore configuration from git                                        │
│     □ Verify version matches network                                        │
│                                                                              │
│  3. RESTORE DATA (< 2 hours)                                                │
│     OPTION A: From Snapshot                                                 │
│     □ Download latest snapshot from S3                                      │
│     □ Decrypt and extract                                                   │
│     □ Verify integrity (checksums)                                          │
│     □ Place in chain data directory                                         │
│                                                                              │
│     OPTION B: Sync from Network                                             │
│     □ Start node in sync mode                                               │
│     □ Connect to bootstrap nodes                                            │
│     □ Wait for sync (may take longer)                                       │
│                                                                              │
│  4. RESTORE KEYS (< 30 minutes) [VALIDATORS ONLY]                           │
│     □ Retrieve key backup                                                   │
│     □ Reconstruct encryption password (Shamir)                              │
│     □ Decrypt and import keys                                               │
│     □ Verify key matches registered validator                               │
│                                                                              │
│  5. START AND VERIFY (< 30 minutes)                                         │
│     □ Start node service                                                    │
│     □ Verify sync status                                                    │
│     □ Verify block production (validators)                                  │
│     □ Monitor for errors                                                    │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 6.2 Recovery Commands

```bash
# 1. Download and decrypt snapshot
aws s3 cp s3://quantum-harmony-backups/chain/latest.tar.gz.age /tmp/
age -d -i /secure/backup_key -o /tmp/chain_snapshot.tar.gz /tmp/latest.tar.gz.age

# 2. Verify checksum
sha256sum -c /tmp/chain_snapshot.sha256

# 3. Extract to chain directory
mkdir -p /var/lib/quantum-harmony/chains/mainnet
tar xzf /tmp/chain_snapshot.tar.gz -C /var/lib/quantum-harmony/chains/mainnet

# 4. Restore configuration
git clone git@github.com:org/quantum-harmony-config.git /etc/quantum-harmony
git-crypt unlock

# 5. Restore validator keys (if applicable)
qh-cli keys insert --keystore-path /var/lib/quantum-harmony/keystore \
  --key-type gran --input /secure/gran_backup.json
qh-cli keys insert --keystore-path /var/lib/quantum-harmony/keystore \
  --key-type babe --input /secure/babe_backup.json

# 6. Start node
systemctl start quantum-harmony

# 7. Verify status
qh-cli system health
qh-cli query session validators | grep "$(cat /etc/quantum-harmony/validator_address)"
```

### 6.3 Partial Recovery Scenarios

| Scenario | Data to Restore | Procedure |
|----------|-----------------|-----------|
| Corrupted DB | Chain data only | Restore from snapshot or warp sync |
| Lost keystore | Keys only | Restore from encrypted backup |
| Config error | Configuration | `git checkout` previous version |
| Failed upgrade | Chain + config | Restore snapshot + rollback config |

---

## 7. Backup Verification

### 7.1 Verification Schedule

| Backup Type | Verification Frequency | Method |
|-------------|----------------------|--------|
| Key backups | Monthly | Test decryption (not import) |
| Chain snapshots | Weekly | Restore to test environment |
| Configuration | On change | Automated validation |

### 7.2 Verification Procedure

```bash
#!/bin/bash
# verify-backups.sh - Monthly backup verification

# 1. Download latest key backup
aws s3 cp s3://quantum-harmony-backups/keys/latest.age /tmp/

# 2. Verify decryption works (don't extract keys!)
age -d -i /secure/backup_key -o /dev/null /tmp/latest.age
if [ $? -eq 0 ]; then
    echo "Key backup: VERIFIED"
else
    echo "Key backup: FAILED" | alert-team
fi

# 3. Download and test chain snapshot
aws s3 cp s3://quantum-harmony-backups/chain/latest.tar.gz.age /tmp/
age -d -i /secure/backup_key /tmp/latest.tar.gz.age | tar tzf - > /dev/null
if [ $? -eq 0 ]; then
    echo "Chain snapshot: VERIFIED"
else
    echo "Chain snapshot: FAILED" | alert-team
fi

# 4. Verify config repo accessible
git clone --depth 1 git@github.com:org/quantum-harmony-config.git /tmp/config-test
if [ $? -eq 0 ]; then
    echo "Config backup: VERIFIED"
else
    echo "Config backup: FAILED" | alert-team
fi

# 5. Clean up
rm -rf /tmp/latest.age /tmp/latest.tar.gz.age /tmp/config-test

# 6. Log verification
echo "$(date): Backup verification complete" >> /var/log/quantum-harmony/backup-verify.log
```

---

## 8. Disaster Recovery

### 8.1 DR Scenarios

| Scenario | Impact | Recovery Strategy |
|----------|--------|-------------------|
| Single node failure | Minimal | Restore from backup |
| Data center failure | Moderate | Failover to DR site |
| Region failure | Significant | Multi-region failover |
| Global cloud failure | Severe | Multi-cloud recovery |

### 8.2 DR Site Configuration

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    DISASTER RECOVERY ARCHITECTURE                            │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  PRIMARY SITE (us-east-1)              DR SITE (eu-west-1)                  │
│  ┌─────────────────────────┐           ┌─────────────────────────┐          │
│  │ Active Validator Node   │           │ Standby Validator Node  │          │
│  │ - Live chain data       │──────────▶│ - Replicated snapshots  │          │
│  │ - Active keys (HSM)     │ (Async)   │ - Backup keys (HSM)     │          │
│  └─────────────────────────┘           └─────────────────────────┘          │
│                                                                              │
│  ┌─────────────────────────┐           ┌─────────────────────────┐          │
│  │ S3 Backup Bucket        │──────────▶│ S3 Replica Bucket       │          │
│  │ (Primary)               │ (Cross-   │ (DR)                    │          │
│  └─────────────────────────┘  Region)  └─────────────────────────┘          │
│                                                                              │
│  FAILOVER TRIGGERS:                                                          │
│  - Primary site unreachable > 15 minutes                                    │
│  - Declared disaster by operations                                          │
│                                                                              │
│  FAILOVER PROCEDURE:                                                         │
│  1. Verify primary is truly down                                            │
│  2. Activate DR site validator                                              │
│  3. Update DNS (if applicable)                                              │
│  4. Monitor for conflicts (equivocation!)                                   │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 8.3 DR Checklist

```
DISASTER RECOVERY ACTIVATION

□ Confirm primary site failure (not transient)
□ Page DR activation team
□ Verify latest backup availability at DR site
□ CRITICAL: Ensure primary validator is STOPPED (prevent equivocation)
□ Activate DR validator node
□ Import keys to DR HSM (if not pre-staged)
□ Start DR validator
□ Verify block production
□ Update monitoring to point to DR
□ Notify stakeholders

POST-DISASTER

□ Root cause analysis
□ Repair/rebuild primary site
□ Plan failback (scheduled maintenance window)
□ Test primary site thoroughly before failback
□ Execute failback during low-activity period
□ Update DR procedures with lessons learned
```

---

## 9. Monitoring and Alerts

### 9.1 Backup Monitoring

| Metric | Alert Threshold | Severity |
|--------|-----------------|----------|
| Last backup age | > 24 hours | Warning |
| Last backup age | > 48 hours | Critical |
| Backup size change | > 50% variance | Warning |
| Backup verification failed | Any failure | Critical |
| S3 replication lag | > 1 hour | Warning |

### 9.2 Prometheus Alerts

```yaml
groups:
  - name: backup_alerts
    rules:
      - alert: BackupTooOld
        expr: time() - qh_last_backup_timestamp > 86400
        for: 1h
        labels:
          severity: warning
        annotations:
          summary: "Chain backup older than 24 hours"

      - alert: BackupVerificationFailed
        expr: qh_backup_verification_success == 0
        for: 5m
        labels:
          severity: critical
        annotations:
          summary: "Backup verification failed"
```

---

## 10. Compliance Mapping

| Standard | Requirement | Section |
|----------|-------------|---------|
| ISO 27001 A.12.3.1 | Information backup | Sections 3-5 |
| ISO 22301 8.4 | Business continuity | Section 8 |
| SOC 2 A1.2 | Recovery procedures | Section 6 |
| SOC 2 A1.3 | Backup procedures | Full document |

---

## 11. Document History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0 | 2026-01-19 | Operations Team | Initial release |
