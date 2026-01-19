# Audit Logging Specification

**Document ID:** ISO-AL-001
**Version:** 1.0
**Effective Date:** 2026-01-19
**Standard Reference:** ISO 27001 A.12.4, SOC 2 CC7.2

---

## 1. Overview

This document specifies audit logging requirements for QuantumHarmony nodes, ensuring comprehensive traceability of security-relevant events.

---

## 2. Log Architecture

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                        AUDIT LOGGING ARCHITECTURE                            │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  ┌─────────────────┐  ┌─────────────────┐  ┌─────────────────┐             │
│  │  Node Runtime   │  │   RPC Server    │  │  P2P Network    │             │
│  │  (Pallets)      │  │                 │  │                 │             │
│  └────────┬────────┘  └────────┬────────┘  └────────┬────────┘             │
│           │                    │                    │                       │
│           ▼                    ▼                    ▼                       │
│  ┌─────────────────────────────────────────────────────────────┐           │
│  │                    Substrate Logging                         │           │
│  │                    (tracing crate)                          │           │
│  └─────────────────────────────┬───────────────────────────────┘           │
│                                │                                            │
│           ┌────────────────────┼────────────────────┐                      │
│           ▼                    ▼                    ▼                       │
│  ┌─────────────┐      ┌─────────────┐      ┌─────────────┐                 │
│  │ Local Files │      │   stdout    │      │   Syslog    │                 │
│  │ (JSON/Text) │      │  (Docker)   │      │  (Remote)   │                 │
│  └──────┬──────┘      └──────┬──────┘      └──────┬──────┘                 │
│         │                    │                    │                        │
│         └────────────────────┼────────────────────┘                        │
│                              ▼                                              │
│  ┌─────────────────────────────────────────────────────────────┐           │
│  │              Log Aggregation (Prometheus/Loki)              │           │
│  └─────────────────────────────────────────────────────────────┘           │
│                              │                                              │
│                              ▼                                              │
│  ┌─────────────────────────────────────────────────────────────┐           │
│  │                Long-term Storage (S3/GCS)                   │           │
│  └─────────────────────────────────────────────────────────────┘           │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 3. Event Categories

### 3.1 Authentication Events

| Event | Log Level | Fields | Retention |
|-------|-----------|--------|-----------|
| `auth.session_key_set` | INFO | validator_id, key_hash, block | 1 year |
| `auth.session_key_rotate` | INFO | validator_id, old_hash, new_hash | 1 year |
| `auth.rpc_signed_request` | DEBUG | account, method, signature_valid | 90 days |
| `auth.rpc_auth_failure` | WARN | account, method, reason | 1 year |

**Example Log Entry:**
```json
{
  "timestamp": "2026-01-19T12:34:56.789Z",
  "level": "INFO",
  "target": "quantum_harmony::auth",
  "event": "auth.session_key_set",
  "fields": {
    "validator_id": "5GrwvaEF5zXb26Fz9rcQpDWS57CtERHpNehXCPcNoHGKutQY",
    "key_hash": "0x1234...abcd",
    "block_number": 123456
  }
}
```

### 3.2 Authorization Events

| Event | Log Level | Fields | Retention |
|-------|-----------|--------|-----------|
| `authz.extrinsic_submit` | DEBUG | origin, call, weight | 90 days |
| `authz.sudo_call` | WARN | origin, call, result | 3 years |
| `authz.governance_vote` | INFO | voter, proposal_id, vote | 1 year |
| `authz.permission_denied` | WARN | origin, call, reason | 1 year |

### 3.3 Consensus Events

| Event | Log Level | Fields | Retention |
|-------|-----------|--------|-----------|
| `consensus.block_authored` | INFO | author, block_hash, block_number | 1 year |
| `consensus.finality_proof` | INFO | block_hash, validators_signed | 1 year |
| `consensus.missed_block` | WARN | expected_author, slot | 1 year |
| `consensus.equivocation` | ERROR | offender, proof | 3 years |

### 3.4 Oracle Events

| Event | Log Level | Fields | Retention |
|-------|-----------|--------|-----------|
| `oracle.signal_submitted` | INFO | reporter, feed, value | 1 year |
| `oracle.signal_aggregated` | INFO | feed, median, reporters | 1 year |
| `oracle.reporter_slashed` | WARN | reporter, amount, reason | 3 years |
| `oracle.reporter_added` | INFO | reporter, stake, feeds | 1 year |
| `oracle.reporter_removed` | INFO | reporter, reason | 1 year |

### 3.5 QRNG Events

| Event | Log Level | Fields | Retention |
|-------|-----------|--------|-----------|
| `qrng.entropy_requested` | DEBUG | requester, bytes | 90 days |
| `qrng.entropy_delivered` | DEBUG | source_count, combined_hash | 90 days |
| `qrng.source_offline` | WARN | source_id | 1 year |
| `qrng.threshold_degraded` | WARN | available, required | 1 year |

### 3.6 Network Events

| Event | Log Level | Fields | Retention |
|-------|-----------|--------|-----------|
| `network.peer_connected` | DEBUG | peer_id, address | 30 days |
| `network.peer_disconnected` | DEBUG | peer_id, reason | 30 days |
| `network.gossip_received` | TRACE | topic, sender, size | 7 days |
| `network.dos_detected` | WARN | peer_id, pattern | 1 year |

### 3.7 Configuration Events

| Event | Log Level | Fields | Retention |
|-------|-----------|--------|-----------|
| `config.parameter_changed` | WARN | parameter, old, new, changer | 3 years |
| `config.runtime_upgrade` | WARN | old_version, new_version, block | 3 years |
| `config.node_restart` | INFO | reason, version | 1 year |

---

## 4. Log Format

### 4.1 Structured JSON Format

All logs MUST use structured JSON format for machine processing:

```json
{
  "timestamp": "2026-01-19T12:34:56.789012Z",
  "level": "INFO",
  "target": "quantum_harmony::pallet_name",
  "span": {
    "name": "process_extrinsic",
    "block_number": 123456
  },
  "event": "event.name",
  "fields": {
    "field1": "value1",
    "field2": 123,
    "field3": true
  },
  "node_id": "alice",
  "version": "1.0.0"
}
```

### 4.2 Required Fields

| Field | Type | Description |
|-------|------|-------------|
| `timestamp` | ISO 8601 | UTC timestamp with microseconds |
| `level` | string | TRACE, DEBUG, INFO, WARN, ERROR |
| `target` | string | Source module (e.g., `quantum_harmony::oracle`) |
| `event` | string | Event identifier (e.g., `oracle.signal_submitted`) |
| `fields` | object | Event-specific structured data |
| `node_id` | string | Node identifier |
| `version` | string | Software version |

### 4.3 Sensitive Data Handling

**NEVER log:**
- Private keys or key material
- Full signatures (use truncated hashes)
- Personal identifiable information (PII)
- Passwords or credentials

**Redaction examples:**
```json
// WRONG - exposes key material
{ "private_key": "0x1234...full_key..." }

// CORRECT - uses hash reference
{ "key_hash": "0x1234...abcd (first 8 chars)" }
```

---

## 5. Implementation

### 5.1 Rust Implementation

```rust
use tracing::{info, warn, error, instrument};

// Structured event logging
#[instrument(skip(signature))]
pub fn submit_oracle_signal(
    reporter: &AccountId,
    feed: FeedId,
    value: u128,
    signature: &Signature,
) -> Result<(), Error> {
    info!(
        event = "oracle.signal_submitted",
        reporter = %reporter,
        feed = ?feed,
        value = %value,
        sig_hash = %truncate_hash(signature),
        "Oracle signal submitted"
    );

    // ... implementation

    Ok(())
}

// Security event logging
pub fn log_auth_failure(account: &AccountId, method: &str, reason: &str) {
    warn!(
        event = "auth.rpc_auth_failure",
        account = %account,
        method = %method,
        reason = %reason,
        "RPC authentication failure"
    );
}

// Consensus event logging
pub fn log_equivocation(offender: &ValidatorId, proof: &EquivocationProof) {
    error!(
        event = "consensus.equivocation",
        offender = %offender,
        slot = ?proof.slot,
        proof_hash = %hash(proof),
        "Equivocation detected - validator misbehavior"
    );
}
```

### 5.2 Node Configuration

```toml
# config.toml

[logging]
# Default log level
level = "info"

# Module-specific levels
[logging.targets]
"quantum_harmony::oracle" = "debug"
"quantum_harmony::consensus" = "info"
"quantum_harmony::network" = "warn"
"quantum_harmony::auth" = "info"

# Output configuration
[logging.output]
format = "json"
file = "/var/log/quantum-harmony/node.log"
rotation = "daily"
retention_days = 90

# Remote syslog (optional)
[logging.syslog]
enabled = true
address = "logs.example.com:514"
facility = "local0"
```

---

## 6. Log Collection

### 6.1 Local Storage

```
/var/log/quantum-harmony/
├── node.log                    # Current log file
├── node.log.2026-01-18.gz      # Rotated, compressed
├── node.log.2026-01-17.gz
├── security/                   # Security events (longer retention)
│   ├── auth.log
│   └── consensus.log
└── audit/                      # Audit trail (immutable)
    └── changes.log
```

### 6.2 Remote Aggregation

```yaml
# Vector/Fluentd configuration
sources:
  node_logs:
    type: file
    include:
      - /var/log/quantum-harmony/*.log

transforms:
  parse_json:
    type: json_parser
    inputs: ["node_logs"]

  filter_security:
    type: filter
    inputs: ["parse_json"]
    condition: '.level == "WARN" or .level == "ERROR" or starts_with(.event, "auth.") or starts_with(.event, "consensus.")'

sinks:
  prometheus:
    type: prometheus_exporter
    inputs: ["parse_json"]
    address: "0.0.0.0:9090"

  long_term_storage:
    type: aws_s3
    inputs: ["filter_security"]
    bucket: "quantum-harmony-logs"
    compression: gzip
```

---

## 7. Monitoring and Alerting

### 7.1 Key Metrics

| Metric | Query | Alert Threshold |
|--------|-------|-----------------|
| Auth failures/hour | `count(auth.rpc_auth_failure)` | > 100 |
| Missed blocks/day | `count(consensus.missed_block)` | > 10 |
| Sudo calls | `count(authz.sudo_call)` | Any |
| Reporter slashing | `count(oracle.reporter_slashed)` | Any |
| Equivocations | `count(consensus.equivocation)` | Any |

### 7.2 Prometheus Metrics

```rust
// Expose metrics for Prometheus
lazy_static! {
    static ref AUTH_FAILURES: IntCounter = register_int_counter!(
        "qh_auth_failures_total",
        "Total authentication failures"
    ).unwrap();

    static ref CONSENSUS_MISSED_BLOCKS: IntCounter = register_int_counter!(
        "qh_consensus_missed_blocks_total",
        "Total missed block slots"
    ).unwrap();
}
```

---

## 8. Audit Trail Requirements

### 8.1 Immutability

Audit logs for configuration changes and security events MUST be:
- Append-only (no modification or deletion)
- Cryptographically signed or hashed
- Replicated to immutable storage

### 8.2 Chain of Custody

For incident investigation:
1. Preserve original logs (do not modify)
2. Calculate and record SHA-256 hashes
3. Document access to log files
4. Use write-once storage (S3 Object Lock, etc.)

---

## 9. Retention Schedule

| Log Category | Active Storage | Archive Storage | Total Retention |
|--------------|----------------|-----------------|-----------------|
| Security events | 90 days | 275 days | 1 year |
| Configuration changes | 90 days | 2.75 years | 3 years |
| Consensus events | 90 days | 275 days | 1 year |
| Application logs | 30 days | 60 days | 90 days |
| Debug logs | 7 days | 0 | 7 days |

---

## 10. Compliance Mapping

| Standard | Requirement | Implementation |
|----------|-------------|----------------|
| ISO 27001 A.12.4.1 | Event logging | Sections 3-5 |
| ISO 27001 A.12.4.2 | Protection of log information | Section 8 |
| ISO 27001 A.12.4.3 | Administrator logs | Section 3.2 |
| ISO 27001 A.12.4.4 | Clock synchronization | UTC timestamps |
| SOC 2 CC7.2 | System monitoring | Section 7 |

---

## 11. Document History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0 | 2026-01-19 | Engineering Team | Initial release |
