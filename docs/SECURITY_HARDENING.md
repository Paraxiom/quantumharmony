# Security Hardening Guide

**Status:** Pre-audit | Testnet Only
**Last Updated:** January 2025

---

## 1. RPC Endpoint Security

### The Problem

The README and docker-compose examples use permissive RPC settings for ease of testing:

```bash
--rpc-external \
--rpc-cors=all \
--rpc-methods=Safe
```

**This is a footgun for production deployments.**

### What These Flags Do

| Flag | Effect | Risk |
|------|--------|------|
| `--rpc-external` | Binds RPC to 0.0.0.0 (all interfaces) | Exposes RPC to internet |
| `--rpc-cors=all` | Allows any origin to make RPC calls | Enables CSRF-style attacks |
| `--rpc-methods=Safe` | Exposes "safe" subset of RPC | Still includes `author_*` methods |

### Production Recommendations

```bash
# Option 1: Local-only RPC (recommended for validators)
./quantumharmony-node \
    --chain=production \
    --rpc-port=9944 \
    # No --rpc-external, binds to 127.0.0.1 only

# Option 2: Restricted external RPC (for public RPC nodes)
./quantumharmony-node \
    --chain=production \
    --rpc-external \
    --rpc-cors="https://your-app.example.com" \
    --rpc-methods=Safe \
    --rpc-max-connections=100 \
    --rpc-rate-limit=10
```

### Reverse Proxy Hardening

For public RPC nodes, always use a reverse proxy:

```nginx
# /etc/nginx/sites-available/quantumharmony-rpc
upstream node_rpc {
    server 127.0.0.1:9944;
}

server {
    listen 443 ssl http2;
    server_name rpc.example.com;

    ssl_certificate /path/to/cert.pem;
    ssl_certificate_key /path/to/key.pem;

    # Rate limiting
    limit_req_zone $binary_remote_addr zone=rpc:10m rate=10r/s;
    limit_req zone=rpc burst=20 nodelay;

    # Block dangerous methods even if node exposes them
    location / {
        # Reject Unsafe methods at proxy level
        if ($request_body ~* "(author_insertKey|author_rotateKeys|system_addReservedPeer)") {
            return 403;
        }

        proxy_pass http://node_rpc;
        proxy_http_version 1.1;
        proxy_set_header Upgrade $http_upgrade;
        proxy_set_header Connection "upgrade";
        proxy_set_header Host $host;
        proxy_set_header X-Real-IP $remote_addr;

        # WebSocket support for subscriptions
        proxy_read_timeout 86400;
    }
}
```

### Firewall Rules

```bash
# UFW example - validator node
ufw default deny incoming
ufw default allow outgoing
ufw allow 30333/tcp  # P2P
ufw allow 22/tcp     # SSH (restrict source IP in production)
# Do NOT allow 9944 (RPC) or 9615 (Prometheus) externally

# For public RPC behind nginx
ufw allow 443/tcp    # HTTPS only
```

---

## 2. Pallet Authority Model

### Complexity Warning

QuantumHarmony combines multiple authority domains:

```
┌─────────────────────────────────────────────────────────────────┐
│                    AUTHORITY DOMAINS                             │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  Governance          Legal/Notarial       Cryptographic         │
│  ┌──────────┐        ┌──────────┐        ┌──────────┐          │
│  │Democracy │        │Fideicommis│       │Pedersen  │          │
│  │Scheduler │        │Notarial   │       │Commitment│          │
│  │Proxy     │        │Ricardian  │       │Oracle    │          │
│  │Preimage  │        │Academic   │       │Entropy   │          │
│  └────┬─────┘        └────┬─────┘        └────┬─────┘          │
│       │                   │                   │                 │
│       └───────────────────┴───────────────────┘                 │
│                           │                                      │
│                    Potential "unexpected                         │
│                    authority" edges                              │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### Known Interaction Risks

#### 1. Scheduler + Proxy + Democracy

**Risk:** A democracy proposal could schedule a proxied call that bypasses intended restrictions.

```rust
// Hypothetical attack path (not currently possible, but illustrates the concern):
// 1. Create democracy proposal
// 2. Proposal schedules a call at future block
// 3. Scheduled call uses proxy to act as another account
// 4. Proxy call has elevated privileges
```

**Mitigation:**
- `Scheduler` uses `EnsureRoot` origin for privileged scheduling
- Proxy filters restrict which calls can be proxied
- Democracy proposals require substantial stake + voting period

#### 2. Fideicommis + Balances

**Risk:** Trust distributions could drain accounts if balance checks are bypassable.

**Mitigation:**
- All balance operations go through `pallet-balances` with proper reservations
- Fideicommis holds funds in escrow via `ReservableCurrency`
- Claims validate against trust state machine

#### 3. Oracle + Stablecoin

**Risk:** Manipulated oracle prices could trigger improper liquidations.

**Mitigation:**
- Price feeds require multiple reporters
- Deviation bounds reject outlier prices
- Aggregation period delays price updates
- Slashing for malicious reporters

### Authority Audit Checklist

Before mainnet, verify:

- [ ] All `EnsureRoot` usages are intentional
- [ ] No pallet can escalate privileges via another
- [ ] Proxy filter configuration reviewed
- [ ] Scheduler cannot bypass origin checks
- [ ] Democracy cannot execute arbitrary runtime calls
- [ ] No call path allows unauthorized balance transfers

---

## 3. Entropy System Threat Model

### Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                    ENTROPY FLOW                                  │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  Off-Chain Sources         On-Chain Commitment                  │
│  ┌──────────────┐         ┌──────────────────┐                 │
│  │ QRNG Device  │────────►│ Entropy Commit   │                 │
│  │ HRNG Device  │────────►│ (hash only)      │                 │
│  │ QKD Session  │────────►│                  │                 │
│  └──────────────┘         └────────┬─────────┘                 │
│                                    │                            │
│                                    ▼                            │
│                           ┌──────────────────┐                 │
│                           │ Aggregation      │                 │
│                           │ (XOR + hash)     │                 │
│                           └────────┬─────────┘                 │
│                                    │                            │
│                                    ▼                            │
│                           ┌──────────────────┐                 │
│                           │ qVRF Seeding     │                 │
│                           └──────────────────┘                 │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### Threat Actors

| Actor | Capability | Goal |
|-------|-----------|------|
| Malicious Validator | Controls their entropy source | Bias validator selection |
| External Attacker | Network-level observation | Predict/influence randomness |
| Colluding Validators | Control multiple sources | Majority bias |
| Hardware Vendor | Backdoored QRNG | Deterministic "random" output |

### Attack Vectors

#### 1. Entropy Source Manipulation

**Attack:** Validator replaces QRNG with deterministic source.

**Detection:**
- Statistical tests on committed entropy
- Comparison with other validators' contributions

**Mitigation:**
- XOR aggregation: single honest source prevents bias
- Commit-reveal: validators commit before seeing others' values
- Slashing for statistically anomalous contributions

#### 2. Timing Attacks

**Attack:** Validator withholds entropy until advantageous block.

**Detection:**
- Monitor entropy submission timing
- Flag validators who frequently submit late

**Mitigation:**
- Entropy must be committed N blocks before use
- Missing commitments result in validator exclusion

#### 3. QKD Session Manipulation

**Attack:** Fake QKD session reports to inject controlled entropy.

**Detection:**
- QKD sessions should be verifiable via network logs
- Key material should match expected QKD protocol output

**Mitigation:**
- QKD is supplementary, not required
- Multiple entropy sources XORed together
- QKD contribution weight-limited

### What's Provable vs. Trusted

| Property | Provable On-Chain | Off-Chain Trust |
|----------|-------------------|-----------------|
| Entropy was committed | Yes (hash stored) | - |
| Entropy matches commitment | Yes (reveal verified) | - |
| Entropy is truly random | No | Trust hardware |
| Entropy wasn't pre-selected | Partially (commit-reveal) | Trust timing |
| Hardware wasn't backdoored | No | Trust vendor/audit |

### Minimum Viable Security

For testnet: Current design is acceptable with monitoring.

For mainnet, require:
1. **Mandatory commit-reveal** with economic penalties
2. **Statistical monitoring** of entropy distributions
3. **Multi-source requirement** (at least 2 independent sources per validator)
4. **Formal verification** of aggregation logic

---

## 4. Key Management

### SPHINCS+ Key Security

SPHINCS+ keys are larger and signing is slower:

| Property | SPHINCS+-256f | Ed25519 |
|----------|---------------|---------|
| Secret Key | 128 bytes | 32 bytes |
| Public Key | 64 bytes | 32 bytes |
| Signature | ~29 KB | 64 bytes |
| Sign Time | ~100ms | <1ms |

**Implications:**
- Key backup requires secure handling of larger secrets
- HSM support requires SPHINCS+ firmware (limited availability)
- Key derivation from mnemonic is non-standard

### Validator Key Rotation

```bash
# Generate new session keys (requires node running)
curl -H "Content-Type: application/json" \
     -d '{"id":1, "jsonrpc":"2.0", "method": "author_rotateKeys", "params":[]}' \
     http://localhost:9944

# NEVER expose author_rotateKeys to external RPC
```

---

## 5. Incident Response

### If Validator Key Compromised

1. **Immediately** submit `session.set_keys` with new keys
2. Notify network operators via secure channel
3. Investigate: check node logs, access logs, key storage
4. If stake at risk: use governance to freeze if available

### If Oracle Manipulated

1. Check reported prices vs. external sources
2. Identify malicious reporters via deviation analysis
3. Submit slashing evidence if applicable
4. Governance proposal to adjust price if needed

### If Entropy Bias Detected

1. Document statistical anomalies
2. Identify suspect validators
3. Exclude from validator set via governance
4. Review entropy aggregation logs

---

## 6. Pre-Mainnet Checklist

- [ ] Professional security audit completed
- [ ] RPC hardening documentation followed
- [ ] Pallet authority model formally verified
- [ ] Entropy system threat model reviewed
- [ ] Key management procedures documented
- [ ] Incident response plan tested
- [ ] Bug bounty program launched
- [ ] Rate limiting on all public endpoints
- [ ] Monitoring and alerting configured

---

## Contact

Security issues: security@quantumharmony.network (placeholder - set up before mainnet)
