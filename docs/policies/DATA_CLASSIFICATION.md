# Data Classification Policy

**Document ID:** POL-DC-001
**Version:** 1.0
**Effective Date:** 2026-01-19
**Review Cycle:** Annual
**Owner:** Security Team
**Classification:** Internal

---

## 1. Purpose

This policy establishes a framework for classifying data based on sensitivity and criticality, ensuring appropriate protection controls are applied throughout the data lifecycle.

---

## 2. Scope

This policy applies to all data:
- Processed by QuantumHarmony nodes
- Stored in on-chain or off-chain systems
- Transmitted between network participants
- Managed by operators and administrators

---

## 3. Classification Levels

### 3.1 Overview

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                      DATA CLASSIFICATION HIERARCHY                           │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │ CRITICAL                                                             │    │
│  │ Compromise causes severe, potentially irreversible damage           │    │
│  │ Examples: Private keys, HSM credentials, sudo access                │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                                    │                                         │
│                                    ▼                                         │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │ CONFIDENTIAL                                                         │    │
│  │ Internal use only, disclosure causes significant harm               │    │
│  │ Examples: Operator credentials, internal configs, security reports  │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                                    │                                         │
│                                    ▼                                         │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │ INTERNAL                                                             │    │
│  │ General internal information, not for public release               │    │
│  │ Examples: Architecture docs, operational procedures, meeting notes │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                                    │                                         │
│                                    ▼                                         │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │ PUBLIC                                                               │    │
│  │ Freely shareable, no restrictions                                   │    │
│  │ Examples: Documentation, open source code, block data              │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 3.2 Classification Details

| Level | Label | Color | Impact of Disclosure |
|-------|-------|-------|---------------------|
| CRITICAL | `[CRITICAL]` | Red | Catastrophic - key compromise, funds loss, network halt |
| CONFIDENTIAL | `[CONFIDENTIAL]` | Orange | Significant - unauthorized access, reputational damage |
| INTERNAL | `[INTERNAL]` | Yellow | Moderate - competitive disadvantage, operational exposure |
| PUBLIC | `[PUBLIC]` | Green | None - intended for public consumption |

---

## 4. Data Inventory

### 4.1 Critical Data

| Data Type | Description | Storage | Retention |
|-----------|-------------|---------|-----------|
| Validator private keys | Falcon-1024 signing keys | HSM only | Permanent (until rotated) |
| Session keys | BABE/GRANDPA session keys | HSM or encrypted keystore | Until rotation |
| Sudo key (if active) | Emergency governance key | Multi-sig HSM | Until deprecated |
| HSM credentials | Access to hardware security modules | Physical secure storage | Permanent |
| Key backup material | Recovery seeds, backup keys | Air-gapped, encrypted | Permanent |
| Database encryption keys | Keys for encrypted storage | Key management system | Until rotation |

**Required Controls:**
- Encryption at rest: AES-256-GCM
- Encryption in transit: TLS 1.3 minimum
- Access: Need-to-know only, multi-person control
- Storage: HSM or air-gapped systems
- Logging: All access attempts logged
- Backup: Encrypted, geographically distributed

### 4.2 Confidential Data

| Data Type | Description | Storage | Retention |
|-----------|-------------|---------|-----------|
| Operator credentials | SSH keys, cloud credentials | Encrypted vault | Until rotation |
| API keys | Service authentication tokens | Secrets manager | Until rotation |
| Security audit reports | Penetration test results | Encrypted storage | 3 years |
| Incident reports | Security incident details | Encrypted storage | 3 years |
| Internal configurations | Non-public node configs | Version control (private) | 1 year |
| Access logs | Authentication/authorization logs | Log aggregation | 1 year |
| Reporter private keys | Oracle reporter signing keys | Encrypted keystore | Until rotation |

**Required Controls:**
- Encryption at rest: AES-256
- Encryption in transit: TLS 1.3
- Access: Role-based, authenticated
- Storage: Encrypted filesystems
- Logging: Access logged
- Sharing: Approved recipients only

### 4.3 Internal Data

| Data Type | Description | Storage | Retention |
|-----------|-------------|---------|-----------|
| Architecture diagrams | System design documents | Internal wiki | Current |
| Operational runbooks | Procedures and playbooks | Internal wiki | Current |
| Meeting notes | Team meeting records | Collaboration tools | 1 year |
| Development roadmap | Feature planning | Project management | Current |
| Performance metrics | Internal monitoring data | Metrics systems | 90 days |
| Support tickets | Internal support issues | Ticketing system | 1 year |

**Required Controls:**
- Encryption in transit: TLS
- Access: Authenticated employees/contractors
- Storage: Internal systems
- Logging: Standard access logs
- Sharing: Within organization

### 4.4 Public Data

| Data Type | Description | Storage | Retention |
|-----------|-------------|---------|-----------|
| Block data | On-chain transactions, state | Blockchain (replicated) | Permanent |
| Open source code | Node software, pallets | GitHub (public) | Permanent |
| API documentation | RPC methods, schemas | Public docs site | Current |
| User guides | Setup and usage instructions | Public docs site | Current |
| Press releases | Public announcements | Website | Permanent |
| Public addresses | Account addresses (non-private) | Blockchain | Permanent |

**Required Controls:**
- Integrity: Signed releases, verified commits
- Availability: CDN, multiple mirrors
- No sensitive data: Verify before publishing

---

## 5. Handling Requirements

### 5.1 Handling Matrix

| Activity | Critical | Confidential | Internal | Public |
|----------|:--------:|:------------:|:--------:|:------:|
| **Storage** |
| Encryption at rest | AES-256 + HSM | AES-256 | Recommended | Optional |
| Access logging | Required | Required | Required | Optional |
| Backup encryption | Required | Required | Required | N/A |
| **Transmission** |
| Encryption in transit | TLS 1.3 + E2E | TLS 1.3 | TLS 1.2+ | HTTPS |
| Secure channel only | Required | Required | Recommended | N/A |
| **Access** |
| Multi-person control | Required | Recommended | N/A | N/A |
| Need-to-know | Required | Required | Required | N/A |
| Access approval | Executive | Manager | Team lead | N/A |
| **Disposal** |
| Secure deletion | Cryptographic erase | Secure delete | Standard delete | N/A |
| Media destruction | Physical destruction | Degaussing/wipe | Wipe | N/A |

### 5.2 Labeling Requirements

| Level | Document Label | Email Subject | File Naming |
|-------|---------------|---------------|-------------|
| CRITICAL | `[CRITICAL]` header | `[CRITICAL]` prefix | `_CRITICAL_` suffix |
| CONFIDENTIAL | `[CONFIDENTIAL]` header | `[CONFIDENTIAL]` prefix | `_CONF_` suffix |
| INTERNAL | `[INTERNAL]` header | None required | None required |
| PUBLIC | None required | None required | None required |

---

## 6. Data Lifecycle

### 6.1 Creation/Collection

```
┌─────────────────────────────────────────────────────────────────┐
│                    DATA CREATION WORKFLOW                        │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  1. Identify data type                                          │
│     └── What is being created/collected?                        │
│                                                                  │
│  2. Classify according to policy                                │
│     └── Apply appropriate classification level                  │
│                                                                  │
│  3. Apply required controls                                     │
│     └── Encryption, access controls, labeling                   │
│                                                                  │
│  4. Document data owner                                         │
│     └── Who is responsible for this data?                       │
│                                                                  │
│  5. Determine retention period                                  │
│     └── How long must this data be kept?                        │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### 6.2 Storage

| Classification | Primary Storage | Backup Storage | Geographic Restrictions |
|----------------|-----------------|----------------|------------------------|
| CRITICAL | HSM / Air-gapped | Encrypted, distributed | May have restrictions |
| CONFIDENTIAL | Encrypted servers | Encrypted backup | Organizational locations |
| INTERNAL | Internal systems | Standard backup | None |
| PUBLIC | Public infrastructure | CDN / mirrors | None |

### 6.3 Transmission

| Classification | Internal Network | External Network | Removable Media |
|----------------|-----------------|------------------|-----------------|
| CRITICAL | TLS 1.3 + E2E encryption | Prohibited without approval | Prohibited |
| CONFIDENTIAL | TLS 1.3 | TLS 1.3 + approval | Encrypted only |
| INTERNAL | TLS recommended | TLS required | Encrypted |
| PUBLIC | Any | Any | Any |

### 6.4 Retention and Disposal

| Classification | Minimum Retention | Maximum Retention | Disposal Method |
|----------------|-------------------|-------------------|-----------------|
| CRITICAL | As needed | Until rotated/deprecated | Cryptographic erasure |
| CONFIDENTIAL | Per legal/regulatory | 7 years (default) | Secure deletion |
| INTERNAL | As needed | 3 years (default) | Standard deletion |
| PUBLIC | N/A | N/A | N/A |

**Disposal Procedures:**

```
CRITICAL DATA:
1. Verify disposal is authorized
2. Document disposal decision
3. Perform cryptographic erasure (key destruction)
4. Physical destruction of media if applicable
5. Record disposal in audit log
6. Verify disposal (independent check)

CONFIDENTIAL DATA:
1. Verify retention period expired
2. Use secure deletion (multiple overwrites)
3. Record disposal in audit log

INTERNAL DATA:
1. Standard deletion acceptable
2. Document if required by policy
```

---

## 7. Special Data Categories

### 7.1 Blockchain Data (On-Chain)

| Data Element | Classification | Notes |
|--------------|----------------|-------|
| Transaction data | PUBLIC | Visible to all nodes |
| Account balances | PUBLIC | Visible to all nodes |
| Block hashes | PUBLIC | Network consensus |
| Validator identities | PUBLIC | Required for consensus |
| Reporter identities | PUBLIC | Required for oracle |
| Governance votes | PUBLIC | Transparency requirement |
| Smart contract code | PUBLIC | Stored on-chain |
| Smart contract state | PUBLIC | Stored on-chain |

**Note:** Even though blockchain data is public, users may have privacy expectations. Use ZK proofs where privacy is needed.

### 7.2 Off-Chain Data

| Data Element | Classification | Notes |
|--------------|----------------|-------|
| Node logs | CONFIDENTIAL | May contain operational details |
| Performance metrics | INTERNAL | Operational data |
| User support requests | CONFIDENTIAL | May contain account details |
| Validator operational configs | CONFIDENTIAL | Security-relevant |

### 7.3 Cryptographic Material

| Material Type | Classification | Special Handling |
|---------------|----------------|------------------|
| Private keys (validator) | CRITICAL | HSM only, multi-person |
| Private keys (reporter) | CRITICAL | Encrypted keystore |
| Session keys | CRITICAL | Rotate regularly |
| Public keys | PUBLIC | No restrictions |
| Key derivation seeds | CRITICAL | Air-gapped backup |
| Certificates | CONFIDENTIAL | Secure storage |

---

## 8. Roles and Responsibilities

| Role | Responsibilities |
|------|------------------|
| **Data Owner** | Classify data, approve access, ensure controls |
| **Data Custodian** | Implement controls, maintain systems, report issues |
| **Security Team** | Define policy, audit compliance, investigate incidents |
| **All Personnel** | Handle data according to classification, report violations |

---

## 9. Compliance Mapping

| Framework | Requirement | Section |
|-----------|-------------|---------|
| ISO 27001 A.8.2 | Information classification | Section 3, 4 |
| ISO 27001 A.8.2.1 | Classification of information | Section 3 |
| ISO 27001 A.8.2.2 | Labeling of information | Section 5.2 |
| ISO 27001 A.8.2.3 | Handling of assets | Section 5.1 |
| SOC 2 CC6.1 | Logical access security | Section 5 |
| SOC 2 C1.1 | Confidentiality commitments | Section 4 |

---

## 10. Exceptions

Exceptions to this policy require:
1. Written justification
2. Risk assessment
3. Compensating controls
4. Approval from Security Team lead
5. Time limit (90 days maximum)
6. Documentation and review

---

## 11. Document History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0 | 2026-01-19 | Security Team | Initial release |
