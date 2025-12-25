# QuantumHarmony Faucet Deployment Procedure

This document describes how to properly configure and deploy the testnet faucet for QuantumHarmony.

## Overview

The faucet dispenses testnet QMHY tokens to users. It requires:
1. A funded account (must have genesis balance or receive tokens via transfer)
2. The 128-byte SPHINCS+ secret key for that account
3. Network connectivity to an RPC node

## Key Concepts

### SPHINCS+-256s Keys

QuantumHarmony uses post-quantum SPHINCS+-256s signatures with:
- **Secret key**: 128 bytes (hex: 256 characters + 0x prefix)
- **Public key**: 64 bytes (hex: 128 characters + 0x prefix)
- **Account ID**: 32 bytes derived from public key

### Address Formats

The blockchain accepts two address formats:
- **SS58 Address**: Human-readable format (e.g., `5Efq7V6VtMrZPpGo6YqtFD2bHEQigdapdrQhhFZ3SNvCvKqS`)
- **Raw Hex**: 32-byte hex format (e.g., `0xe40ec85c92436dda...`)

**IMPORTANT**: Genesis-funded accounts may be stored using raw hex account IDs, not SS58 addresses.

## Finding Funded Accounts

### Step 1: Query Genesis Balances

```bash
# Get all balance storage keys
curl -s -X POST -H "Content-Type: application/json" \
  -d '{"jsonrpc":"2.0","id":1,"method":"state_getKeys","params":["0x26aa394eea5630e07c48ae0c9558cef7b99d880ec681799c0cf30e8886371da9"]}' \
  http://VALIDATOR_IP:9944
```

### Step 2: Check Balance for Each Account

```bash
# Use gateway_balance RPC (accepts both SS58 and hex addresses)
curl -s -X POST -H "Content-Type: application/json" \
  -d '{"jsonrpc":"2.0","id":1,"method":"gateway_balance","params":["ADDRESS_HERE"]}' \
  http://VALIDATOR_IP:9944
```

### Step 3: Match Account to Known Keys

Check `keys/production/validators.json` for the mapping between:
- Validator names
- Public keys (64 bytes)
- Secret keys (128 bytes)
- Server IPs

## Faucet Configuration

### Required Files

1. **Faucet Script**: `scripts/faucet.py`
2. **Key Reference**: `keys/production/validators.json`
3. **Test Accounts**: `node/src/test_accounts.rs`

### Configuration Variables

```python
# Faucet address (SS58 or hex format)
FAUCET_ADDRESS = "5ERStq5d3WCxkvTMP8NaRvKoE3v1WEaB9QmHe5Z3KvnJVChQ"

# 128-byte SPHINCS+ secret key (REQUIRED - not the 48-byte seed!)
FAUCET_SECRET_KEY = "0x3baad4edc957a870f42961263763fabe..."
```

### Common Errors

| Error | Cause | Solution |
|-------|-------|----------|
| `InvalidTransaction::Payment` | Faucet account has 0 balance | Use a genesis-funded account |
| `BadSignature` | Wrong secret key format | Ensure 128-byte secret key, not 48-byte seed |
| `balance: 0` | Account not funded | Check genesis config or transfer tokens |

## Deployment Steps

### 1. Identify a Funded Account

```bash
# Check balances of known validator accounts
curl -s -X POST -H "Content-Type: application/json" \
  -d '{"jsonrpc":"2.0","id":1,"method":"gateway_balance","params":["5ERStq5d3WCxkvTMP8NaRvKoE3v1WEaB9QmHe5Z3KvnJVChQ"]}' \
  http://YOUR_NODE_IP:9944
```

### 2. Update Faucet Configuration

Edit `scripts/faucet.py` with the correct:
- `FAUCET_ADDRESS`: Account with funds
- `FAUCET_SECRET_KEY`: Corresponding 128-byte secret key

### 3. Deploy and Start

```bash
# Upload to server
scp -i ~/.ssh/ovh_simple scripts/faucet.py ubuntu@your-server:~/quantumharmony/scripts/

# Start faucet
ssh -i ~/.ssh/ovh_simple ubuntu@your-server '
  cd ~/quantumharmony/scripts
  nohup python3 faucet.py --port 8081 --rpc http://localhost:9944 > /tmp/faucet.log 2>&1 &
'
```

### 4. Verify Operation

```bash
# Check status
curl http://YOUR_NODE_IP:8081/status

# Test drip (replace with target address)
curl -X POST -H "Content-Type: application/json" \
  -d '{"address":"5TARGET_ADDRESS_HERE"}' \
  http://YOUR_NODE_IP:8081/drip
```

## Key Files Reference

| File | Purpose |
|------|---------|
| `keys/production/validators.json` | Production validator keys (SS58, public, secret, node keys) |
| `keys/local-testnet/key-mapping.json` | Local testnet key mapping |
| `node/src/test_accounts.rs` | Hardcoded test account keys in Rust |
| `node/src/chain_spec.rs` | Genesis configuration including endowed accounts |

## Troubleshooting

### Faucet Reports 0 Balance

1. Check if the configured address is actually funded:
   ```bash
   curl -s -X POST -H "Content-Type: application/json" \
     -d '{"jsonrpc":"2.0","id":1,"method":"gateway_balance","params":["FAUCET_ADDRESS"]}' \
     http://localhost:9944
   ```

2. If 0, the genesis may have funded a different account format (hex vs SS58)

3. Query all genesis accounts and find one with balance

### Secret Key Issues

- The faucet needs the **128-byte secret key**, NOT the 48-byte seed
- Seeds are for key derivation; the full secret key is needed for signing
- Find secret keys in `validators.json` under `secret_hex`

### Network Issues

- Ensure RPC node is running and accessible
- Check firewall allows connections on port 9944 (RPC) and 8081 (faucet)
- Verify with: `curl http://localhost:9944/health`

## Production Checklist

- [ ] Faucet account is funded with sufficient QMHY
- [ ] Correct 128-byte secret key is configured
- [ ] Faucet service is running on port 8081
- [ ] Rate limiting is enabled (default: 60s per address)
- [ ] Logs are being captured to /tmp/faucet.log
- [ ] Status endpoint returns valid balance
- [ ] Test drip transaction succeeds

## Related Documentation

- `QUICKSTART.md` - Full network deployment guide
- `keys/production/validators.json` - Validator key reference
- `node/src/chain_spec.rs` - Genesis configuration
