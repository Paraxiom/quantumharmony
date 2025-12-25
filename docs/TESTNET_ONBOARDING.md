# QuantumHarmony Testnet Onboarding Guide

Welcome to QuantumHarmony - the first post-quantum secure blockchain using multi-scheme PQC signatures (SPHINCS+ & Falcon1024).

## Network Information

| Property | Value |
|----------|-------|
| Network Name | QuantumHarmony Testnet |
| Token Symbol | QHT |
| Token Decimals | 12 |
| Block Time | ~6 seconds |
| Consensus | Aura (Authority Round) |
| Transaction Signatures | SPHINCS+-SHAKE-128f (post-quantum) |
| Consensus Signatures | Falcon1024 (post-quantum) |
| **Current TPS** | **< 10** (post-quantum signatures are computationally expensive) |

### Public Endpoints

| Service | URL | Status |
|---------|-----|--------|
| Alice RPC | `http://YOUR_NODE_IP:9944` | Online |
| Bob RPC | `http://YOUR_NODE_IP:9944` | Online |
| Admin Dashboard | `http://YOUR_NODE_IP:8080` | Online |
| Block Explorer | [Polkadot.js Apps](https://polkadot.js.org/apps/?rpc=ws://YOUR_NODE_IP:9944) | Online |

### Validators

| Validator | Location | IP | RPC Port | P2P Port |
|-----------|----------|-----|----------|----------|
| Alice (V1) | Canada (OVH) | YOUR_NODE_IP | 9944 | 30333 |
| Bob (V2) | Canada (OVH) | YOUR_NODE_IP | 9944 | 30334 |

> **Note (Dec 2025)**: Charlie validator (DigitalOcean Frankfurt) was decommissioned.
> Network currently runs with 2 validators. Third validator slot available for new operators.

---

## Getting Started

### 1. Get Testnet Tokens

Use the faucet to get free QMHY tokens for testing:

**Web Interface:**
Open http://YOUR_NODE_IP:8080 in your browser.

**API:**
```bash
curl -X POST http://YOUR_NODE_IP:8080/drip \
  -H "Content-Type: application/json" \
  -d '{"address": "YOUR_SS58_ADDRESS"}'
```

Response:
```json
{
  "success": true,
  "message": "Tokens sent successfully!",
  "tx_hash": "0x...",
  "amount": "10 QHT"
}
```

**Rate Limit:** 1 request per 60 seconds per address.
**Drip Amount:** 10 QHT per request.

### 2. Check Your Balance

```bash
curl "http://YOUR_NODE_IP:8080/balance?address=YOUR_SS58_ADDRESS"
```

Or via RPC:
```bash
curl -H "Content-Type: application/json" \
  -d '{"jsonrpc":"2.0","id":1,"method":"gateway_balance","params":["YOUR_SS58_ADDRESS"]}' \
  https://v1.quantumharmony.network
```

### 3. Connect via Polkadot.js Apps

1. Go to https://polkadot.js.org/apps
2. Click the network selector (top left)
3. Choose "Development" → "Custom"
4. Enter: `wss://v1.quantumharmony.network`
5. Click "Switch"

---

## Sending Transactions

QuantumHarmony uses SPHINCS+ post-quantum signatures. The `gateway_submit` RPC handles signing:

```bash
curl -H "Content-Type: application/json" \
  -d '{
    "jsonrpc": "2.0",
    "id": 1,
    "method": "gateway_submit",
    "params": [{
      "from": "YOUR_SS58_ADDRESS",
      "to": "RECIPIENT_SS58_ADDRESS",
      "amount": "1000000000000000000",
      "nonce": 0,
      "genesisHash": "0x...",
      "secretKey": "0x..."
    }]
  }' \
  https://v1.quantumharmony.network
```

**Fields:**
- `from`: Your SS58 address
- `to`: Recipient's SS58 address
- `amount`: Amount in smallest units (1 QMHY = 10^18)
- `nonce`: Your account nonce (get via `gateway_nonce`)
- `genesisHash`: Chain genesis hash (get via `gateway_genesisHash`)
- `secretKey`: Your 128-byte SPHINCS+ secret key (hex, with 0x prefix)

---

## Running a Full Node

### Option 1: Build from Source

```bash
# Clone repository
git clone https://github.com/QuantumVerseProtocols/quantumharmony.git
cd quantumharmony

# Build (requires Rust nightly)
rustup default nightly
cargo build --release

# Run node
./target/release/quantumharmony-node \
  --chain local \
  --name "MyNode" \
  --bootnodes /ip4/YOUR_NODE_IP/tcp/30333/p2p/12D3KooWNpaTf134DUqez17tRCLPwdgBeQGAwh7hV94iPnd1u37d
```

### Option 2: Use Pre-built Binary

Download from releases (when available) or request from the team.

### Node Flags

| Flag | Description |
|------|-------------|
| `--chain local` | Use local testnet chain spec |
| `--name "NAME"` | Node name shown in telemetry |
| `--bootnodes URL` | Connect to existing network |
| `--rpc-external` | Allow external RPC connections |
| `--ws-external` | Allow external WebSocket connections |
| `--validator` | Run as validator (requires keys) |

---

## Generating SPHINCS+ Keys

QuantumHarmony uses SPHINCS+ post-quantum cryptography. To generate keys:

```bash
# Using the node binary
./target/release/quantumharmony-node key generate --scheme sphincs

# Output:
# Secret phrase: <mnemonic>
# Secret key: 0x... (128 bytes)
# Public key: 0x... (64 bytes)
# SS58 Address: 5...
```

**Important:**
- SPHINCS+ keys are 128 bytes (secret) and 64 bytes (public)
- SS58 addresses derived from SPHINCS+ public keys start with `5`
- Keep your secret key secure - it provides post-quantum security!

---

## RPC Methods

### Gateway Methods (Post-Quantum)

| Method | Description |
|--------|-------------|
| `gateway_balance` | Get account balance |
| `gateway_nonce` | Get account nonce |
| `gateway_genesisHash` | Get genesis hash |
| `gateway_submit` | Submit signed transaction |

### Standard Substrate RPC

| Method | Description |
|--------|-------------|
| `chain_getHeader` | Get latest block header |
| `chain_getBlock` | Get block by hash |
| `chain_getBlockHash` | Get block hash by number |
| `system_health` | Node health status |
| `system_peers` | Connected peers |

---

## Network Performance

**Real-world tested performance on 3-validator testnet:**

| Metric | Value |
|--------|-------|
| Block Time | 6 seconds |
| **Actual TPS** | **< 10** |
| SPHINCS+ Signature Size | 17,088 bytes |
| Falcon1024 Signature Size | 1,280 bytes |
| SPHINCS+ Verify Time | ~250ms |
| Falcon1024 Verify Time | ~0.1ms |

**Why is TPS limited?**

QuantumHarmony uses SPHINCS+ post-quantum signatures which are computationally expensive (~250ms per verification). This is the trade-off for quantum resistance:

| Blockchain | Signature | TPS | Quantum-Safe? |
|------------|-----------|-----|---------------|
| Bitcoin | ECDSA | ~7 | No |
| Ethereum | ECDSA | ~15-30 | No |
| Solana | Ed25519 | ~65,000 | No |
| **QuantumHarmony** | **SPHINCS+** | **< 10** | **Yes** |

> **Note:** When quantum computers arrive, all non-PQC blockchains will need to migrate.
> QuantumHarmony is quantum-safe TODAY.

---

## Troubleshooting

### Node won't sync
- Check bootnode is reachable: `nc -zv YOUR_NODE_IP 30333`
- Verify chain spec matches network
- Check firewall allows port 30333

### Transaction not included
- Verify nonce is correct (use `gateway_nonce`)
- Check account has sufficient balance
- Ensure genesis hash matches current chain

### RPC connection failed
- Try both HTTP and WebSocket endpoints
- Check CORS if using browser

---

## Support

- GitHub Issues: https://github.com/QuantumVerseProtocols/quantumharmony/issues
- Documentation: https://github.com/QuantumVerseProtocols/quantumharmony/docs

---

## Security Notes

QuantumHarmony is a **testnet**. Do not use real funds or sensitive keys.

The SPHINCS+ implementation provides:
- Post-quantum security against Shor's algorithm
- 128-bit security level (NIST Level 1)
- Stateless signatures (no state management required)
