# Access Control Policy

**Document ID:** POL-AC-001
**Version:** 1.0
**Effective Date:** 2026-01-19
**Review Cycle:** Annual
**Owner:** Security Team
**Classification:** Internal

---

## 1. Purpose

This policy establishes requirements for controlling access to QuantumHarmony systems, data, and network resources based on the principle of least privilege.

---

## 2. Scope

This policy applies to:
- All network participants (validators, reporters, users)
- System administrators and operators
- Developers with production access
- Automated systems and service accounts

---

## 3. Access Control Model

### 3.1 Role-Based Access Control (RBAC)

QuantumHarmony implements a hierarchical role-based access control model:

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         ACCESS CONTROL HIERARCHY                             │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │ SUDO (Emergency Only)                                                │    │
│  │ • Emergency runtime upgrades                                        │    │
│  │ • Critical parameter changes                                         │    │
│  │ • Removable after network stabilization                             │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                                    │                                         │
│                                    ▼                                         │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │ VALIDATOR                                                            │    │
│  │ • Block production (BABE)                                           │    │
│  │ • Finality voting (GRANDPA)                                         │    │
│  │ • Governance participation                                           │    │
│  │ • Reporter approval/removal                                          │    │
│  │ • New validator voting                                               │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                                    │                                         │
│                                    ▼                                         │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │ REPORTER                                                             │    │
│  │ • Oracle signal submission (approved feeds only)                    │    │
│  │ • Price feed updates                                                 │    │
│  │ • QRNG entropy contribution                                          │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                                    │                                         │
│                                    ▼                                         │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │ USER                                                                 │    │
│  │ • Transaction submission                                            │    │
│  │ • Balance transfers                                                  │    │
│  │ • State queries                                                      │    │
│  │ • Attestation requests                                               │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                                    │                                         │
│                                    ▼                                         │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │ PUBLIC (Unauthenticated)                                            │    │
│  │ • Read-only chain queries                                           │    │
│  │ • Block explorer access                                              │    │
│  │ • Public RPC methods                                                 │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 3.2 Role Permissions Matrix

| Permission | Sudo | Validator | Reporter | User | Public |
|------------|:----:|:---------:|:--------:|:----:|:------:|
| Runtime upgrade | Yes | Vote | - | - | - |
| Emergency actions | Yes | - | - | - | - |
| Produce blocks | - | Yes | - | - | - |
| GRANDPA voting | - | Yes | - | - | - |
| Approve validators | - | Yes | - | - | - |
| Approve reporters | - | Yes | - | - | - |
| Submit oracle signals | - | - | Yes | - | - |
| Submit transactions | - | Yes | Yes | Yes | - |
| Transfer funds | - | Yes | Yes | Yes | - |
| Query state | - | Yes | Yes | Yes | Yes |
| View blocks | - | Yes | Yes | Yes | Yes |

---

## 4. Authentication Requirements

### 4.1 Cryptographic Authentication

All authenticated operations require Falcon-1024 digital signatures:

| Operation | Signature Required | Key Type |
|-----------|-------------------|----------|
| Block production | Yes | Validator session key |
| GRANDPA vote | Yes | Validator session key |
| Governance vote | Yes | Validator account key |
| Oracle signal | Yes | Reporter key |
| Transaction | Yes | Account key |
| RPC (sensitive) | Yes | Account key |

### 4.2 Key Requirements

| Role | Key Storage | Key Type | Rotation |
|------|-------------|----------|----------|
| Validator | HSM (production) | Falcon-1024 | Annual minimum |
| Reporter | Encrypted keystore | Falcon-1024 | Annual minimum |
| User | User-managed | SPHINCS+ or Falcon | User discretion |

### 4.3 Multi-Factor Authentication

For administrative access to infrastructure:
- SSH access: Key-based + hardware token
- Cloud console: Password + TOTP/hardware key
- Monitoring dashboards: SSO with MFA

---

## 5. Access Provisioning

### 5.1 Validator Onboarding

```
┌─────────────────────────────────────────────────────────────────┐
│                 VALIDATOR PROVISIONING WORKFLOW                  │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  1. Application                                                 │
│     └── Candidate submits application with:                     │
│         • Technical specifications                              │
│         • Security attestation                                  │
│         • Geographic location                                   │
│                                                                  │
│  2. Technical Review                                            │
│     └── Verify:                                                 │
│         • Node specifications meet requirements                 │
│         • Key management practices                              │
│         • Network connectivity                                  │
│                                                                  │
│  3. Governance Proposal                                         │
│     └── Existing validator proposes candidate                   │
│         • propose_validator(candidate, session_keys)            │
│                                                                  │
│  4. Voting Period                                               │
│     └── Validators vote (100 block period)                      │
│         • 2/3+ approval required                                │
│                                                                  │
│  5. Finalization                                                │
│     └── If approved:                                            │
│         • Validator added to active set                         │
│         • Session keys activated                                │
│                                                                  │
│  6. Monitoring                                                  │
│     └── Performance monitored for:                              │
│         • Uptime (>99% expected)                                │
│         • Block production                                      │
│         • Voting participation                                  │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### 5.2 Reporter Onboarding

```
1. Proposal Submission
   - propose_reporter(candidate, stake, supported_feeds)
   - Stake locked from candidate account

2. Validator Voting
   - Active reporters vote (100 block period)
   - Simple majority required
   - Minimum 2 votes

3. Approval/Rejection
   - If approved: Reporter added, stake remains locked
   - If rejected: Stake returned to candidate

4. Operational
   - Reporter can submit signals to approved feeds
   - Reputation system tracks accuracy
   - Stake slashable for misbehavior
```

### 5.3 System Administrator Access

| Access Type | Provisioning | Approval | Duration |
|-------------|--------------|----------|----------|
| Read-only monitoring | Ticket request | Team lead | Permanent |
| Production SSH | Ticket + justification | Security + Manager | 90 days |
| Database access | Ticket + justification | Security + DBA | 30 days |
| Key management | Ticket + justification | Security + Executive | Per-task |

---

## 6. Access Reviews

### 6.1 Review Schedule

| Access Type | Review Frequency | Reviewer |
|-------------|------------------|----------|
| Validator set | Continuous (on-chain) | All validators |
| Reporter set | Continuous (on-chain) | Validators |
| Admin access | Quarterly | Security Team |
| Service accounts | Monthly | Operations |
| API keys | Quarterly | Security Team |

### 6.2 Review Checklist

- [ ] Is access still required for job function?
- [ ] Has the user/system been active in the past 90 days?
- [ ] Are permissions appropriate (least privilege)?
- [ ] Are credentials current (not expired)?
- [ ] Are there any security concerns?

### 6.3 Dormant Account Policy

| Inactivity Period | Action |
|-------------------|--------|
| 90 days | Warning notification |
| 120 days | Account disabled |
| 180 days | Account deleted (with notice) |

---

## 7. Access Revocation

### 7.1 Immediate Revocation Triggers

| Trigger | Action | Timeline |
|---------|--------|----------|
| Termination | Revoke all access | Immediate |
| Role change | Review and adjust | Within 24 hours |
| Security incident | Revoke affected access | Immediate |
| Policy violation | Revoke as appropriate | Within 4 hours |

### 7.2 Validator Removal

```
1. Governance Proposal
   - Any validator proposes removal
   - propose_validator_removal(validator, reason)

2. Voting Period
   - All validators vote
   - 2/3+ required for removal

3. Finalization
   - If approved: Validator removed from active set
   - Session keys invalidated
   - Stake unbonding begins (if applicable)

4. Post-Removal
   - Key rotation recommended for other validators
   - Incident review if removal was for cause
```

### 7.3 Reporter Removal

```
1. Self-Removal
   - Reporter calls deregister_reporter()
   - Stake returned after unbonding period

2. Forced Removal (Slashing)
   - Evidence of malicious behavior
   - Governance votes to slash
   - Stake partially or fully slashed
   - Reporter removed from approved list
```

---

## 8. Privileged Access Management

### 8.1 Sudo Access (Emergency)

**Sudo capabilities:**
- Emergency parameter changes
- Runtime upgrades without governance delay
- Force transaction inclusion

**Sudo controls:**
- Multi-signature required (if configured)
- All sudo actions logged on-chain
- Automatic alerts on sudo usage
- Planned deprecation after network maturity

### 8.2 Administrative Access

| Principle | Implementation |
|-----------|----------------|
| Just-in-time access | Access granted only when needed |
| Time-limited | Maximum 8-hour sessions |
| Logged | All commands recorded |
| Audited | Quarterly review of admin actions |

### 8.3 Service Accounts

| Requirement | Implementation |
|-------------|----------------|
| Unique per service | No shared service accounts |
| Minimal permissions | Only required operations |
| No interactive login | API/automated use only |
| Credential rotation | Every 90 days |
| Monitoring | Alert on unusual activity |

---

## 9. External Access

### 9.1 Third-Party Access

| Vendor Type | Access Level | Duration | Review |
|-------------|--------------|----------|--------|
| Audit firm | Read-only + specific systems | Per engagement | Post-engagement |
| Security researcher | Testnet only | Per program | Per finding |
| Integration partner | API access only | Per contract | Quarterly |

### 9.2 API Access Control

```
Public API (rate-limited):
- system_* methods
- chain_* methods
- state_* read methods
- No authentication required
- Rate limit: 100 req/s per IP

Authenticated API:
- author_* methods
- gateway_* methods
- Requires signed request
- Rate limit: 1000 req/s per account

Validator API:
- author_rotateKeys
- Session key management
- Validator node only
- localhost or authenticated
```

---

## 10. Audit and Compliance

### 10.1 Access Logging

All access attempts MUST be logged:
- Timestamp (UTC)
- Account/identity
- Action attempted
- Success/failure
- Source IP (for network access)

### 10.2 Audit Trail

| Event | Logged | Retention |
|-------|--------|-----------|
| Authentication | Yes | 1 year |
| Authorization decisions | Yes | 1 year |
| Configuration changes | Yes | 3 years |
| Access provisioning | Yes | 3 years |
| Access revocation | Yes | 3 years |

### 10.3 Compliance Mapping

| Control | SOC 2 Criteria | ISO 27001 |
|---------|----------------|-----------|
| Role-based access | CC6.1, CC6.2 | A.9.1, A.9.2 |
| Authentication | CC6.1 | A.9.4 |
| Access review | CC6.2, CC6.3 | A.9.2.5 |
| Revocation | CC6.3 | A.9.2.6 |
| Privileged access | CC6.1, CC6.2 | A.9.2.3 |

---

## 11. Document History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0 | 2026-01-19 | Security Team | Initial release |
