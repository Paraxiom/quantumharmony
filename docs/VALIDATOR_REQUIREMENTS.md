# QuantumHarmony Validator Requirements

**Version**: 1.0
**Last Updated**: January 2026
**Network Status**: Public Beta Testnet

---

## Overview

QuantumHarmony validators secure the first post-quantum Layer 1 blockchain. Validators participate in Proof of Coherence consensus using SPHINCS+ signatures and earn rewards for block production and finalization.

---

## Hardware Requirements

### Minimum Specifications

| Resource | Minimum | Recommended |
|----------|---------|-------------|
| **CPU** | 4 cores | 8+ cores |
| **RAM** | 8 GB | 16 GB |
| **Storage** | 100 GB SSD | 500 GB NVMe SSD |
| **Network** | 100 Mbps | 1 Gbps |
| **IP** | Dynamic OK | Static preferred |

### Operating System

| OS | Support |
|----|---------|
| Ubuntu 22.04 LTS | Recommended |
| Debian 12 | Supported |
| macOS (Apple Silicon) | Supported (Docker) |
| Windows | Via WSL2/Docker |

### Cloud Provider Estimates

| Provider | Instance Type | Monthly Cost |
|----------|---------------|--------------|
| DigitalOcean | s-4vcpu-8gb | ~$48/mo |
| Linode | Dedicated 8GB | ~$72/mo |
| Vultr | High Frequency 4 vCPU | ~$48/mo |
| AWS | t3.xlarge | ~$120/mo |
| OVH | B2-15 | ~$30/mo |

---

## Capital Requirements

### Testnet (Current)

| Item | Amount | Notes |
|------|--------|-------|
| **Minimum Stake** | 10,000 QMHY | Locked during validation |
| **Hardware** | $30-120/mo | Cloud VPS |
| **Total Initial** | 10,000 QMHY + ~$50 | First month |

### Mainnet (Planned)

| Item | Amount | Notes |
|------|--------|-------|
| **Minimum Stake** | TBD | Subject to governance |
| **Recommended Stake** | TBD | Higher stake = higher selection probability |

---

## Expected Returns (Testnet)

> **Note**: Testnet rewards are for testing the reward distribution mechanism. Mainnet tokenomics will be finalized before launch.

### Current Reward Structure

| Metric | Value |
|--------|-------|
| Block Reward | Distributed per session |
| Session Length | 7,200 blocks (~6 hours) |
| Validators | 3 active (expanding) |
| Reward Distribution | Equal split among active validators |

### ROI Calculation Framework

```
Monthly Revenue = (Blocks Produced × Block Reward) + (Finalization Rewards)
Monthly Cost = Hardware + Opportunity Cost of Staked Capital
Net ROI = (Monthly Revenue - Monthly Cost) / Staked Capital
```

Exact values depend on:
- Total validator count
- Network transaction volume
- Governance decisions on inflation

---

## Quick Start

### Option 1: One-Command Docker Deployment

```bash
# Clone repository
git clone https://github.com/Paraxiom/quantumharmony.git
cd quantumharmony/node-operator-dashboard

# Start node + dashboard
./start.sh fresh

# View logs
./start.sh logs
```

**Services started:**
- Dashboard: http://localhost:8080
- RPC: http://localhost:9944
- P2P: port 30333

### Option 2: Manual Setup

```bash
# Install dependencies
apt update && apt install -y build-essential git clang curl libssl-dev

# Install Rust
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
source ~/.cargo/env

# Clone and build
git clone https://github.com/Paraxiom/quantumharmony.git
cd quantumharmony
cargo build --release

# Run node
./target/release/quantumharmony-node \
  --chain=/path/to/chainspec.json \
  --validator \
  --name="YourValidatorName" \
  --rpc-external \
  --rpc-cors=all
```

---

## Becoming a Validator

### Step 1: Sync Your Node

Wait for full synchronization:
```bash
curl -s http://localhost:9944 -H "Content-Type: application/json" \
  -d '{"jsonrpc":"2.0","method":"system_health","params":[],"id":1}'
```

Response should show `"isSyncing": false`

### Step 2: Generate Session Keys

```bash
curl -s http://localhost:9944 -H "Content-Type: application/json" \
  -d '{"jsonrpc":"2.0","method":"author_rotateKeys","params":[],"id":1}'
```

Save the returned session keys (hex string).

### Step 3: Register Keys On-Chain

Using Polkadot.js Apps (https://polkadot.js.org/apps):
1. Connect to `ws://localhost:9944`
2. Go to Developer > Extrinsics
3. Select `session` > `setKeys`
4. Enter your session keys and proof (`0x00`)
5. Submit transaction

### Step 4: Request Validator Addition

Contact the team via:
- GitHub Issues
- Discord (link in README)

Provide:
- Your account address
- Session keys
- Node name and location
- Stake amount

---

## Network Information

### Current Validators

| Name | Location | Status |
|------|----------|--------|
| Alice | Montreal, Canada | Active |
| Bob | Beauharnois, Canada | Active |
| Charlie | Frankfurt, Germany | Active |

### Bootnodes

```
/ip4/51.79.26.123/tcp/30333/p2p/12D3KooWDmLjhsvwEh3Xdat6daVhRm87ed88J9Sx4ti44osaDM8W
/ip4/51.79.26.168/tcp/30333/p2p/12D3KooWDQp7gSEEHgpGpvnui67v8s3PQ6RvYpocu96WvyuYwak1
/ip4/209.38.225.4/tcp/30333/p2p/12D3KooWPA9JZqTaDokCDToirUuA6DcfPuc2QN9DSzaJvMe3Yvcy
```

### Network Parameters

| Parameter | Value |
|-----------|-------|
| Block Time | 6 seconds |
| Session Length | 7,200 blocks |
| Epoch Length | 14,400 blocks |
| Finality | Deterministic (2/3 BFT) |
| Consensus | Proof of Coherence |
| Signatures | SPHINCS+-256s |

---

## Security Considerations

### Post-Quantum Cryptography

QuantumHarmony uses NIST-approved post-quantum algorithms:

| Component | Algorithm | Security |
|-----------|-----------|----------|
| Signatures | SPHINCS+-SHAKE-256s | 256-bit PQ |
| Key Exchange | ML-KEM-1024 | 256-bit PQ |
| P2P Identity | Falcon-1024 | 256-bit PQ |

### Validator Security Best Practices

1. **Key Management**
   - Store validator keys offline when not in use
   - Use hardware security modules (HSM) for production
   - Never share private keys

2. **Server Hardening**
   - Enable firewall (only 30333 P2P required public)
   - Disable root SSH login
   - Use key-based authentication
   - Keep system updated

3. **Monitoring**
   - Set up alerts for downtime
   - Monitor block production
   - Track peer connections

---

## Slashing Conditions

Validators may be slashed for:

| Offense | Penalty |
|---------|---------|
| Double signing | Up to 100% stake |
| Extended downtime | Proportional to duration |
| Equivocation | Variable based on severity |

> **Testnet**: Slashing is enabled for testing but can be reversed by governance.

---

## Support & Resources

### Documentation
- [Lightpaper](/docs/MD/LIGHTPAPER.md)
- [Architecture](/docs/CCAE_ARCHITECTURE.md)
- [GitHub Repository](https://github.com/Paraxiom/quantumharmony)

### Community
- GitHub Issues: Bug reports and feature requests
- Discord: Real-time support (link in README)

### RPC Endpoints
- Local: `http://localhost:9944`
- Alice (Public): `http://51.79.26.123:9944`

---

## FAQ

**Q: Can I run a validator on a Raspberry Pi?**
A: Not recommended. SPHINCS+ signatures require significant CPU for signing/verification.

**Q: What's the minimum stake for testnet?**
A: Currently 10,000 QMHY. Contact team for testnet tokens.

**Q: How long does initial sync take?**
A: 5-15 minutes depending on network and hardware.

**Q: Can I run multiple validators?**
A: Yes, but each requires separate stake and session keys.

**Q: What happens if my node goes offline?**
A: You stop earning rewards. Extended downtime may result in slashing on mainnet.

---

*Document maintained by QuantumVerse Protocols*
*Last updated: January 2026*
