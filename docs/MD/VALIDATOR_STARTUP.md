# QuantumHarmony Validator Startup Guide

## CRITICAL: Understanding Key Architecture

QuantumHarmony uses **SPHINCS+ post-quantum signatures**. Due to SPHINCS+ non-determinism, the keys are **hardcoded** in `node/src/test_accounts.rs`.

### How It Works

1. **Keys are hardcoded** in `test_accounts.rs`:
   - Alice, Bob, Charlie have complete keypairs (seed + public + 128-byte secret)
   - These MUST match the chain spec genesis

2. **The `--alice`/`--bob`/`--charlie` flags ARE CORRECT**:
   - They trigger `service.rs` to inject the hardcoded keys from `test_accounts.rs`
   - Without these flags, keys won't be injected

3. **Chain spec must use same keys**:
   - `chain_spec.rs` calls `authority_keys_from_seed_aura()` which uses `test_accounts::get_test_public()`
   - This ensures genesis and keystore have matching keys

## Correct Startup Procedure

### Option 1: Use the Production Script (Recommended)

```bash
cd quantumharmony/scripts
./start-production-validators.sh start
```

### Option 2: Manual Startup

**Alice (YOUR_NODE_IP):**
```bash
./target/release/quantumharmony-node \
    --chain dev3-chainspec-noboot.json \
    --base-path ~/quantumharmony/data/alice \
    --alice \
    --validator \
    --port 30333 \
    --rpc-port 9944 \
    --rpc-external \
    --rpc-cors all \
    --rpc-methods Unsafe \
    --node-key 0000000000000000000000000000000000000000000000000000000000000001
```

**Bob (YOUR_NODE_IP):**
```bash
./target/release/quantumharmony-node \
    --chain dev3-chainspec-noboot.json \
    --base-path ~/quantumharmony/data/bob \
    --bob \
    --validator \
    --port 30333 \
    --rpc-port 9944 \
    --rpc-external \
    --rpc-cors all \
    --rpc-methods Unsafe \
    --node-key 0000000000000000000000000000000000000000000000000000000000000002 \
    --reserved-nodes /ip4/YOUR_NODE_IP/tcp/30333/p2p/12D3KooWEyoppNCUx8Yx66oV9fJnriXwCcXwDDUA2kj6vnc6iDEp
```

## IMPORTANT: What NOT to Do

### DO NOT use `--bootnodes` CLI argument

This causes a `SelectNextSome polled after terminated` crash due to a race condition.

**Bad:**
```bash
--bootnodes /ip4/.../tcp/30333/p2p/...  # CRASH!
```

**Good:**
```bash
--reserved-nodes /ip4/.../tcp/30333/p2p/...  # Works
```

Or better: Remove bootnodes from chain spec and use `--reserved-nodes`.

### DO NOT start with `--dev` flag

This creates a single-validator development chain, not a multi-validator network.

### DO NOT use `/tmp/` for data

Temporary directories are cleared on reboot. Use persistent paths:
- `~/quantumharmony/data/alice`
- `~/quantumharmony/data/bob`

## Chain Spec Generation

If you need to regenerate the chain spec:

```bash
# Generate dev3 spec (without raw encoding)
./target/release/quantumharmony-node build-spec --chain dev3 > dev3-chainspec.json

# Remove bootnodes to prevent crashes
cat dev3-chainspec.json | python3 -c "
import json, sys
spec = json.load(sys.stdin)
spec['bootNodes'] = []
print(json.dumps(spec, indent=2))
" > dev3-chainspec-noboot.json
```

## Key Information

### Validator Keys (from test_accounts.rs)

| Validator | SS58 Address | Location |
|-----------|--------------|----------|
| Alice | `5Efq7V6VtMrZPpGo6YqtFD2bHEQigdapdrQhhFZ3SNvCvKqS` | Montreal (YOUR_NODE_IP) |
| Bob | `5FxMdDFWWg7n4EFGD3ENNuKhQww1PRRSK9Y2igsdJ9uKTMNc` | Beauharnois (YOUR_NODE_IP) |
| Charlie | Not currently deployed | Frankfurt (YOUR_NODE_IP) |

### Peer IDs (from fixed node keys)

| Validator | Peer ID |
|-----------|---------|
| Alice | `12D3KooWEyoppNCUx8Yx66oV9fJnriXwCcXwDDUA2kj6vnc6iDEp` |
| Bob | `12D3KooWHdiAxVd8uMQR1hGWXccidmfCwLqcMpGwR6QcTP6QRMuD` |

## Troubleshooting

### "SelectNextSome polled after terminated"
- **Cause**: Using `--bootnodes` CLI argument
- **Fix**: Use `--reserved-nodes` instead, or remove bootnodes from chain spec

### "NetworkKeyNotFound"
- **Cause**: Missing network directory
- **Fix**: Ensure base-path directories exist, or use `--node-key` for deterministic peer ID

### Keys not working / Block signing fails
- **Cause**: Chain spec keys don't match keystore keys
- **Fix**: Ensure you're using the correct chain spec (`dev3`) which uses `test_accounts.rs` keys

### "No peers" / Validators not connecting
- **Cause**: Incorrect peer IDs in reserved-nodes
- **Fix**: Use the fixed peer IDs above (derived from deterministic node keys)

## Monitoring

Check network health:
```bash
# Via RPC
curl -s http://YOUR_NODE_IP:9944 -H "Content-Type: application/json" \
  -d '{"id":1,"jsonrpc":"2.0","method":"system_health","params":[]}' | jq

# Check block height
curl -s http://YOUR_NODE_IP:9944 -H "Content-Type: application/json" \
  -d '{"id":1,"jsonrpc":"2.0","method":"chain_getHeader","params":[]}' | jq '.result.number'
```

Check logs:
```bash
ssh ubuntu@your-server "tail -50 ~/quantumharmony/alice.log | grep -E '(Imported|finalized|peer|error)'"
```
