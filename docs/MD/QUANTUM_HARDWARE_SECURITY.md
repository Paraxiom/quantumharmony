# Quantum Hardware Security Architecture

**Date**: October 24, 2025
**Version**: 1.0
**Status**: Production Deployment Guidelines

---

## Executive Summary

When deploying QuantumHarmony validators with integrated QRNG (Quantum Random Number Generator) and QKD (Quantum Key Distribution) hardware, proper physical and network security is critical. This document outlines the security architecture for production deployments.

---

## 1. Physical Security Requirements

### Validator Node + Quantum Hardware Colocation

**The operator (validator node) MUST be physically colocated with quantum hardware** for these reasons:

1. **QRNG Integration**: Direct hardware access required for entropy generation
2. **QKD Integration**: Quantum channels require physical fiber connections
3. **Latency**: Quantum operations need microsecond-level response times
4. **Security**: Prevents man-in-the-middle attacks on quantum channels

### Recommended Physical Setup

```
┌─────────────────────────────────────────────────────────┐
│  SECURE FACILITY (Tier 3+ Data Center or Caged Area)   │
│                                                         │
│  ┌──────────────────────────────────────────────────┐ │
│  │  Rack 1: Quantum Hardware                        │ │
│  │                                                   │ │
│  │  • QRNG Device (PCI-e card or USB)              │ │
│  │  • QKD Transmitter/Receiver                      │ │
│  │  • Quantum Optical Equipment                     │ │
│  │  • Environmental Monitoring (temp, vibration)    │ │
│  └──────────────────────────────────────────────────┘ │
│           ↓ Direct connection (fiber/PCIe)            │
│  ┌──────────────────────────────────────────────────┐ │
│  │  Rack 2: Validator Node                         │ │
│  │                                                   │ │
│  │  • Server running quantumharmony-node            │ │
│  │  • HSM (Hardware Security Module) for keys       │ │
│  │  • UPS (Uninterruptible Power Supply)           │ │
│  │  • Firewall/Router (air-gapped or secured)       │ │
│  └──────────────────────────────────────────────────┘ │
│                                                         │
│  Access Control:                                        │
│  • Biometric authentication                             │
│  • 24/7 video surveillance                              │
│  • Access logs                                          │
│  • Two-person rule for maintenance                      │
└─────────────────────────────────────────────────────────┘
                         ↓
              Secured Network Connection
                         ↓
              Public Internet / Other Validators
```

---

## 2. Network Security Architecture

### Three-Tier Network Model

```
┌────────────────────────────────────────────────────┐
│  TIER 1: Quantum Layer (Air-gapped)               │
│                                                    │
│  • QRNG hardware → Validator (PCIe/USB)           │
│  • QKD nodes ↔ QKD nodes (Fiber only)             │
│  • NO internet access                             │
│  • NO external connections                        │
└────────────────┬───────────────────────────────────┘
                 │ One-way data flow
                 │ (hardware → validator only)
                 ↓
┌────────────────────────────────────────────────────┐
│  TIER 2: Validator Layer (Secured)                │
│                                                    │
│  • Validator node (blockchain consensus)          │
│  • Firewall rules:                                │
│    - ALLOW: P2P port (30333) to other validators  │
│    - ALLOW: RPC/WS (9944) from localhost only     │
│    - DENY: All other inbound traffic              │
│  • Rate limiting on all ports                     │
│  • DDoS protection                                │
└────────────────┬───────────────────────────────────┘
                 │ Filtered connection
                 │ (P2P only, rate-limited)
                 ↓
┌────────────────────────────────────────────────────┐
│  TIER 3: Public API Layer (Optional DMZ)          │
│                                                    │
│  • Reverse proxy (nginx/traefik)                  │
│  • Public RPC/WS endpoint (rate-limited)          │
│  • DDoS protection (Cloudflare, etc.)             │
│  • API key authentication                         │
│  • Read-only queries (no sudo/signing allowed)    │
└────────────────────────────────────────────────────┘
                 ↓
         Public Internet / Client Applications
```

---

## 3. Access Control Matrix

### Who Can Access What

| Component | Physical Access | Network Access | Permissions |
|-----------|----------------|----------------|-------------|
| **QRNG Hardware** | Data center staff only | None (air-gapped) | Read entropy only |
| **QKD Hardware** | Data center staff only | None (fiber-only) | Read keys only |
| **Validator Node** | Data center staff only | Localhost + P2P peers | Full control (sudo in dev, governance in prod) |
| **Public RPC** | No physical access | Public internet | Read-only queries |
| **Client Wallets** | No physical access | Public RPC or own node | Sign transactions only |

### Development vs Production Access

#### Development Mode (Current):
```rust
// Alice has sudo access for testing
sudo_key: Some(get_account_id_from_seed::<sr25519::Public>("Alice"))
```

- **Physical**: Developer workstation
- **Network**: Localhost only
- **Security**: Minimal (testing only)

#### Production Mode (Recommended):
```rust
// NO sudo key - governance only
sudo_key: None,

// Democracy pallet enabled
Democracy: pallet_democracy,
Council: pallet_collective::<Instance1>,
TechnicalCommittee: pallet_collective::<Instance2>,
```

- **Physical**: Secure data center cage
- **Network**: Firewalled, rate-limited, monitored
- **Security**: Multi-signature governance, HSM for keys

---

## 4. Threat Model & Mitigations

### Threat 1: Physical Access to Quantum Hardware

**Risk**: Attacker gains physical access to QRNG/QKD devices

**Mitigation**:
- ✅ Biometric access control
- ✅ 24/7 surveillance
- ✅ Tamper-evident seals on equipment
- ✅ Hardware security modules (HSM) for key storage
- ✅ Two-person rule for maintenance

### Threat 2: Network Attack on Validator

**Risk**: DDoS or remote exploitation of validator node

**Mitigation**:
- ✅ Firewall rules (only P2P port exposed)
- ✅ Rate limiting on all ports
- ✅ DDoS protection (Cloudflare, AWS Shield)
- ✅ Regular security updates
- ✅ Intrusion detection system (IDS)

### Threat 3: Compromised RPC/WS Endpoint

**Risk**: Attacker exploits public API to disrupt service

**Mitigation**:
- ✅ Reverse proxy with authentication
- ✅ Read-only queries (no sudo/signing)
- ✅ Rate limiting (per IP, per API key)
- ✅ Separate from validator node (DMZ)
- ✅ Monitor for abuse patterns

### Threat 4: Supply Chain Attack on Hardware

**Risk**: Quantum hardware is tampered with before deployment

**Mitigation**:
- ✅ Purchase from reputable vendors (ID Quantique, QuintessenceLabs, etc.)
- ✅ Verify hardware signatures/certificates
- ✅ Test entropy quality (NIST randomness tests)
- ✅ Continuous monitoring of entropy output
- ✅ Multi-vendor approach (use multiple QRNG sources)

### Threat 5: Insider Threat

**Risk**: Malicious data center staff compromise system

**Mitigation**:
- ✅ Background checks for staff
- ✅ Two-person rule for access
- ✅ All actions logged and audited
- ✅ No single person has full control (governance)
- ✅ Hardware-based key storage (HSM)

---

## 5. Configuration Examples

### Firewall Rules (iptables)

```bash
#!/bin/bash
# QuantumHarmony Validator Firewall Rules

# Flush existing rules
iptables -F

# Default policies
iptables -P INPUT DROP
iptables -P FORWARD DROP
iptables -P OUTPUT ACCEPT

# Allow loopback
iptables -A INPUT -i lo -j ACCEPT

# Allow established connections
iptables -A INPUT -m state --state ESTABLISHED,RELATED -j ACCEPT

# Allow SSH (from trusted IPs only)
iptables -A INPUT -p tcp --dport 22 -s 10.0.0.0/8 -j ACCEPT

# Allow P2P port (other validators)
iptables -A INPUT -p tcp --dport 30333 -m limit --limit 100/s -j ACCEPT

# Allow RPC/WS from localhost ONLY
iptables -A INPUT -p tcp --dport 9944 -s 127.0.0.1 -j ACCEPT

# Log and drop everything else
iptables -A INPUT -j LOG --log-prefix "DROPPED: "
iptables -A INPUT -j DROP
```

### Node Configuration (systemd)

```ini
[Unit]
Description=QuantumHarmony Validator Node
After=network.target

[Service]
Type=simple
User=quantumharmony
Group=quantumharmony

# Security hardening
NoNewPrivileges=true
PrivateTmp=true
ProtectSystem=strict
ProtectHome=true
ReadWritePaths=/var/lib/quantumharmony

# Resource limits
LimitNOFILE=65535
LimitNPROC=4096

# Run validator
ExecStart=/usr/local/bin/quantumharmony-node \
  --validator \
  --name "MySecureValidator" \
  --base-path /var/lib/quantumharmony \
  --chain mainnet \
  --port 30333 \
  --rpc-port 9944 \
  --rpc-cors localhost \
  --rpc-methods Safe \
  --no-telemetry \
  --prometheus-external

Restart=on-failure
RestartSec=30

[Install]
WantedBy=multi-user.target
```

### Reverse Proxy (nginx) for Public RPC

```nginx
# /etc/nginx/sites-available/quantumharmony-rpc

upstream quantumharmony_rpc {
    server 127.0.0.1:9944;
}

# Rate limiting zones
limit_req_zone $binary_remote_addr zone=rpc_limit:10m rate=10r/s;
limit_conn_zone $binary_remote_addr zone=conn_limit:10m;

server {
    listen 443 ssl http2;
    server_name rpc.quantumharmony.example.com;

    # SSL configuration
    ssl_certificate /etc/letsencrypt/live/rpc.quantumharmony.example.com/fullchain.pem;
    ssl_certificate_key /etc/letsencrypt/live/rpc.quantumharmony.example.com/privkey.pem;
    ssl_protocols TLSv1.3;
    ssl_ciphers HIGH:!aNULL:!MD5;

    # Rate limiting
    limit_req zone=rpc_limit burst=20 nodelay;
    limit_conn conn_limit 10;

    # Headers
    add_header Strict-Transport-Security "max-age=31536000" always;
    add_header X-Content-Type-Options nosniff;
    add_header X-Frame-Options DENY;

    location / {
        proxy_pass http://quantumharmony_rpc;
        proxy_http_version 1.1;
        proxy_set_header Upgrade $http_upgrade;
        proxy_set_header Connection "upgrade";
        proxy_set_header Host $host;
        proxy_set_header X-Real-IP $remote_addr;
        proxy_set_header X-Forwarded-For $proxy_add_x_forwarded_for;
        proxy_set_header X-Forwarded-Proto $scheme;

        # Timeouts
        proxy_connect_timeout 60s;
        proxy_send_timeout 60s;
        proxy_read_timeout 60s;
    }
}
```

---

## 6. Monitoring & Alerting

### Key Metrics to Monitor

```yaml
# Example Prometheus alerts.yml

groups:
  - name: quantumharmony_validator
    interval: 30s
    rules:
      # Block production
      - alert: ValidatorNotProducingBlocks
        expr: increase(substrate_block_height{status="finalized"}[5m]) == 0
        for: 10m
        labels:
          severity: critical
        annotations:
          summary: "Validator has stopped producing blocks"

      # Quantum entropy
      - alert: QRNGEntropyLow
        expr: qrng_entropy_quality < 0.95
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "QRNG entropy quality below threshold"

      # QKD key rate
      - alert: QKDKeyRateLow
        expr: qkd_key_generation_rate < 1000
        for: 10m
        labels:
          severity: warning
        annotations:
          summary: "QKD key generation rate below 1000 bits/s"

      # Network peers
      - alert: ValidatorFewPeers
        expr: substrate_sub_libp2p_peers_count < 3
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "Validator has fewer than 3 peers"

      # CPU/Memory
      - alert: HighCPUUsage
        expr: process_cpu_seconds_total > 80
        for: 15m
        labels:
          severity: warning
        annotations:
          summary: "Validator CPU usage above 80%"
```

---

## 7. Deployment Checklist

### Pre-Deployment

- [ ] Secure facility/cage arranged (Tier 3+ data center)
- [ ] QRNG hardware procured and tested (NIST randomness tests)
- [ ] QKD hardware procured and fiber connections established
- [ ] HSM for key storage configured
- [ ] Background checks completed for data center staff
- [ ] Biometric access control installed
- [ ] 24/7 surveillance cameras installed
- [ ] Fire suppression and cooling verified
- [ ] UPS and backup power tested

### Deployment

- [ ] Quantum hardware installed and tested
- [ ] Validator node installed and configured
- [ ] Firewall rules applied and tested
- [ ] Network segregation verified (QRNG air-gapped)
- [ ] Monitoring and alerting configured
- [ ] Backup procedures tested
- [ ] Disaster recovery plan documented
- [ ] Incident response plan documented

### Post-Deployment

- [ ] 24/7 monitoring active
- [ ] Regular security audits scheduled
- [ ] Penetration testing completed
- [ ] Staff training completed
- [ ] Audit logs reviewed daily
- [ ] Entropy quality monitored continuously
- [ ] QKD key rate monitored continuously
- [ ] Incident response drills conducted quarterly

---

## 8. Cost Estimate

### Typical Production Deployment

| Item | Cost (USD) | Notes |
|------|------------|-------|
| **Hardware** | | |
| QRNG Device (ID Quantique, etc.) | $5,000 - $15,000 | Per device |
| QKD System (transmitter + receiver) | $50,000 - $200,000 | Per link |
| Validator Server (high-end) | $5,000 - $10,000 | Dell/HP/Supermicro |
| HSM (Hardware Security Module) | $3,000 - $10,000 | Thales, Utimaco |
| Network Equipment (firewall, etc.) | $2,000 - $5,000 | Cisco, Juniper |
| **Facility** | | |
| Data center cage (1/4 rack) | $500 - $2,000/month | Tier 3+ facility |
| Power and cooling | $200 - $500/month | Depends on usage |
| Cross-connects (fiber) | $100 - $500/month | Per connection |
| **Security** | | |
| Biometric access control | $2,000 - $5,000 | One-time |
| Surveillance cameras | $1,000 - $3,000 | One-time |
| Security audits | $5,000 - $20,000/year | Annual |
| **Staff** | | |
| System administrator (part-time) | $50,000 - $100,000/year | Shared role |
| Security monitoring (outsourced) | $5,000 - $20,000/year | 24/7 SOC |
| **Total (Year 1)** | **$130,000 - $390,000** | Includes hardware + 1 year ops |
| **Total (Year 2+)** | **$65,000 - $135,000/year** | Recurring ops costs |

**Note**: For testing/development, you can use software-based QRNG simulation for ~$0 additional cost.

---

## 9. Development vs Production

### Development Setup (What You Have Now)

```bash
# Simple, insecure, local testing
./target/release/quantumharmony-node --dev --tmp

# Features:
# ✅ Alice has sudo access
# ✅ No quantum hardware required
# ✅ Runs on laptop
# ✅ No security hardening
# ❌ NOT for production
```

### Production Setup (What Clients Need)

```bash
# Secure, hardened, data center deployment
systemctl start quantumharmony-validator

# Features:
# ✅ No sudo (governance only)
# ✅ QRNG/QKD hardware integrated
# ✅ Runs in secure facility
# ✅ Full security hardening
# ✅ 24/7 monitoring
# ✅ Backed by SLA
```

---

## 10. Summary: Answering Your Question

**Q: "How do we manage security I guess the operator has to be caged in with the QRNG/QKD nodes?"**

**A: YES, absolutely!**

For production deployments:

1. **Physical Colocation**: Validator node MUST be in the same secure facility as quantum hardware
2. **Network Segregation**: Quantum hardware should be air-gapped or on isolated VLAN
3. **Access Control**: Biometric authentication, surveillance, two-person rule
4. **Firewall**: Only P2P port exposed to internet, RPC/WS localhost-only or via DMZ
5. **Monitoring**: 24/7 monitoring of validator, quantum entropy, and key generation

For development/testing (what you're doing now):

1. **Local Testing**: Run everything on your laptop
2. **No Quantum Hardware**: Use software simulation
3. **No Security Hardening**: Alice has sudo for convenience
4. **Perfect for demos and client presentations!**

---

## Next Steps

1. **For Now (Development)**:
   - Test with `--dev` mode on laptop
   - Demo forkless upgrades to clients
   - Show the simple wallet CLI

2. **For Client Production Deployments**:
   - Follow this security architecture
   - Budget $130K-$390K for first year
   - Engage data center and quantum hardware vendors
   - Conduct security audit before launch

---

**Questions? Need help with production deployment planning?**

Contact the QuantumHarmony team for enterprise support and security consulting.

*This document is for production deployment planning. Always consult security professionals for critical infrastructure.*
