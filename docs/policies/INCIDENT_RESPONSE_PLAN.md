# Incident Response Plan

**Document ID:** POL-IR-001
**Version:** 1.0
**Effective Date:** 2026-01-19
**Review Cycle:** Annual
**Owner:** Security Team
**Classification:** Internal

---

## 1. Purpose

This plan establishes procedures for detecting, responding to, and recovering from security incidents affecting QuantumHarmony network operations.

---

## 2. Scope

This plan covers:
- Security breaches and unauthorized access
- Service disruptions and outages
- Data integrity issues
- Consensus failures
- Key compromise scenarios
- Malicious validator/reporter activity

---

## 3. Incident Classification

### 3.1 Severity Levels

| Level | Name | Criteria | Response Time | Examples |
|-------|------|----------|---------------|----------|
| SEV-1 | Critical | Network halt, funds at risk, key compromise | < 15 minutes | Consensus failure, validator key leak |
| SEV-2 | High | Degraded service, potential data exposure | < 1 hour | RPC unavailable, high latency |
| SEV-3 | Medium | Minor service impact, no data at risk | < 4 hours | Single validator offline |
| SEV-4 | Low | Minimal impact, informational | < 24 hours | Failed login attempts, cosmetic bugs |

### 3.2 Incident Categories

| Category | Description | Default Severity |
|----------|-------------|------------------|
| Consensus | Block production or finality issues | SEV-1 |
| Key Compromise | Private key exposure or theft | SEV-1 |
| Unauthorized Access | Unapproved system access | SEV-2 |
| Service Outage | System unavailability | SEV-2 |
| Data Integrity | Incorrect or corrupted data | SEV-2 |
| Malicious Actor | Validator/reporter misbehavior | SEV-2 |
| Configuration | Misconfiguration issues | SEV-3 |
| Performance | Degraded performance | SEV-3 |
| Informational | Suspicious but unconfirmed activity | SEV-4 |

---

## 4. Incident Response Team

### 4.1 Roles and Responsibilities

| Role | Responsibilities | Contact |
|------|------------------|---------|
| **Incident Commander (IC)** | Overall coordination, decision authority | On-call rotation |
| **Technical Lead** | Technical investigation and remediation | Engineering team |
| **Communications Lead** | Stakeholder communication | Community team |
| **Scribe** | Documentation and timeline | Assigned per incident |

### 4.2 Escalation Matrix

```
SEV-4 → On-call engineer
         ↓ (if unresolved 4 hours)
SEV-3 → Engineering lead
         ↓ (if unresolved 2 hours)
SEV-2 → Incident Commander + Technical Lead
         ↓ (if unresolved 1 hour or escalates)
SEV-1 → Full incident response team + Executive notification
```

### 4.3 On-Call Schedule

- Primary on-call: 24/7 coverage, 1-week rotations
- Secondary on-call: Backup for escalations
- Escalation timeout: 15 minutes for SEV-1/SEV-2

---

## 5. Incident Response Phases

### 5.1 Phase 1: Detection

**Automated Detection:**
```
Prometheus Alerts → PagerDuty → On-call engineer
                          ↓
              Alert acknowledged within SLA
```

**Alert Categories:**
- `consensus_failure` → SEV-1 automatic
- `validator_offline` → SEV-3, escalates to SEV-2 if multiple
- `rpc_error_rate_high` → SEV-3
- `unauthorized_access_attempt` → SEV-2

**Manual Detection:**
- User reports via support channels
- Community Discord alerts
- Security researcher reports

### 5.2 Phase 2: Triage

**Initial Assessment Checklist:**
- [ ] What systems are affected?
- [ ] Is the issue ongoing or resolved?
- [ ] What is the potential impact?
- [ ] Are funds or keys at risk?
- [ ] Is this a known issue or new?

**Severity Assignment:**
1. Assess against severity criteria
2. When in doubt, escalate higher
3. Severity can be adjusted as more information is available

**Incident Declaration:**
```
IF impact is confirmed AND severity >= SEV-3:
    Declare incident
    Create incident channel (#incident-YYYYMMDD-XX)
    Assign Incident Commander
    Begin formal response
```

### 5.3 Phase 3: Containment

**Immediate Actions by Category:**

#### Consensus Failure
1. Identify affected validators
2. Check for network partition
3. Coordinate validator restart if needed
4. Consider emergency governance action

#### Key Compromise
1. **IMMEDIATELY** rotate affected keys
2. Revoke compromised validator via governance
3. Notify affected parties
4. Preserve evidence (do not delete logs)

#### Unauthorized Access
1. Disable compromised credentials
2. Block attacking IPs
3. Preserve logs and evidence
4. Assess scope of access

#### Service Outage
1. Identify root cause (network, application, infrastructure)
2. Redirect traffic if possible
3. Scale resources if capacity issue
4. Communicate status to users

### 5.4 Phase 4: Eradication

**Root Cause Analysis:**
1. Collect all relevant logs
2. Build timeline of events
3. Identify initial entry point
4. Determine full scope of impact

**Remediation Actions:**
- Patch vulnerabilities
- Update configurations
- Rotate credentials
- Deploy fixes

**Verification:**
- [ ] Root cause addressed
- [ ] Attack vector closed
- [ ] No persistence mechanisms remain
- [ ] Systems verified clean

### 5.5 Phase 5: Recovery

**Recovery Checklist:**
- [ ] Systems restored to normal operation
- [ ] Monitoring confirms stability
- [ ] Performance metrics normal
- [ ] No recurrence detected (minimum 30 minutes)

**Gradual Restoration:**
1. Restore in stages (not all at once)
2. Monitor each stage before proceeding
3. Have rollback plan ready
4. Communicate restoration progress

### 5.6 Phase 6: Post-Incident

**Timeline:** Within 48 hours of resolution

**Post-Incident Review Meeting:**
- All incident responders
- Timeline review
- What went well / what didn't
- Action items

**Post-Incident Report Contents:**
```
1. Executive Summary
2. Timeline of Events
3. Impact Assessment
4. Root Cause Analysis
5. Actions Taken
6. Lessons Learned
7. Recommendations
8. Action Items with Owners
```

---

## 6. Communication Templates

### 6.1 Internal Escalation

```
INCIDENT DECLARED: [Category] - [Brief Description]
Severity: SEV-[X]
Time Detected: [Timestamp UTC]
Incident Commander: [Name]
Channel: #incident-[ID]

Current Status: [Investigating/Mitigating/Resolved]
Impact: [Description of impact]
ETA: [If known]

Join incident channel for updates.
```

### 6.2 External Communication (SEV-1/SEV-2)

```
[STATUS UPDATE - QuantumHarmony Network]

We are currently investigating [brief description].

Impact: [What users may experience]
Start Time: [Timestamp UTC]
Current Status: [Investigating/Identified/Monitoring/Resolved]

We will provide updates every [30 minutes/1 hour].

For questions: [contact channel]
```

### 6.3 Resolution Notice

```
[RESOLVED - QuantumHarmony Network]

The [issue description] has been resolved.

Duration: [Start] to [End]
Root Cause: [Brief description]
Resolution: [What was done]

A detailed post-incident report will be published within 48 hours.

We apologize for any inconvenience caused.
```

---

## 7. Specific Runbooks

### 7.1 Validator Key Compromise

```
PRIORITY: IMMEDIATE (SEV-1)

1. CONTAIN (< 5 minutes)
   □ Identify compromised validator
   □ Initiate emergency key rotation
   □ Alert other validators via secure channel

2. ERADICATE (< 15 minutes)
   □ Submit governance proposal to remove validator
   □ Fast-track voting (if supported)
   □ Block compromised key from producing blocks

3. RECOVER (< 1 hour)
   □ Generate new keys in secure environment
   □ Submit new validator proposal (if continuing)
   □ Verify network stability

4. POST-INCIDENT
   □ Forensic analysis of compromise
   □ Review key storage practices
   □ Update security procedures
```

### 7.2 Consensus Failure

```
PRIORITY: IMMEDIATE (SEV-1)

1. ASSESS (< 5 minutes)
   □ Check block production status
   □ Check finality status
   □ Identify affected validators (>1/3?)

2. COORDINATE (< 15 minutes)
   □ Contact all validators via emergency channel
   □ Identify common cause (if any)
   □ Agree on coordinated action

3. RESOLVE
   □ If software bug: coordinate rollback
   □ If network partition: restore connectivity
   □ If validator failures: restart affected nodes

4. VERIFY
   □ Block production resumed
   □ Finality catching up
   □ All validators online
```

### 7.3 Oracle Data Manipulation

```
PRIORITY: HIGH (SEV-2)

1. DETECT
   □ Identify anomalous price submissions
   □ Compare against external sources
   □ Identify responsible reporter(s)

2. CONTAIN
   □ Temporarily suspend affected feed
   □ Use last known good value
   □ Alert dependent systems

3. INVESTIGATE
   □ Review reporter submission history
   □ Check for coordinated manipulation
   □ Assess financial impact

4. REMEDIATE
   □ Slash malicious reporter(s)
   □ Remove from approved list
   □ Resume feed with remaining reporters
```

---

## 8. Tools and Resources

### 8.1 Monitoring Tools

| Tool | Purpose | Access |
|------|---------|--------|
| Prometheus | Metrics collection | Internal |
| Grafana | Visualization | Internal |
| PagerDuty | Alerting | On-call team |
| Substrate UI | Chain explorer | Public |

### 8.2 Communication Channels

| Channel | Purpose | Access |
|---------|---------|--------|
| #incident-* | Active incident coordination | Responders |
| #security | Security team discussions | Security team |
| Discord #status | Public status updates | Public |
| Email list | Validator notifications | Validators |

### 8.3 Evidence Collection

**What to Preserve:**
- System logs (do not delete or modify)
- Network captures (if available)
- Memory dumps (for malware analysis)
- Configuration files
- Timestamps of all actions taken

**Chain of Custody:**
- Document who accessed evidence
- Use write-once storage
- Calculate and record hashes
- Maintain access log

---

## 9. Testing and Maintenance

### 9.1 Tabletop Exercises

- Frequency: Quarterly
- Scenarios: Rotate through incident categories
- Participants: All potential responders
- Output: Updated runbooks, training needs

### 9.2 Plan Review

- Frequency: Annual (minimum)
- Trigger: Also after any SEV-1 incident
- Owner: Security Team
- Approval: Security Team lead

---

## 10. Document History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0 | 2026-01-19 | Security Team | Initial release |
