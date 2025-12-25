# QuantumHarmony Runtime Upgrade Guide

## Overview

This guide documents the process for performing forkless runtime upgrades on the QuantumHarmony blockchain using SPHINCS+ post-quantum signatures.

## Prerequisites

- Access to a validator node with `--rpc-methods unsafe` enabled
- The SPHINCS+ 128-byte secret key for the sudo account
- Python 3 with `requests` library installed
- Built runtime WASM file

## Building the Runtime

```bash
cd /path/to/quantumharmony

# Build the runtime WASM (this takes ~5-10 minutes)
SKIP_WASM_BUILD=0 cargo build --release -p quantumharmony-runtime

# The WASM file will be at:
# target/release/wbuild/quantumharmony-runtime/quantumharmony_runtime.compact.compressed.wasm
```

## Upgrade Methods

### Method 1: Chunked Upgrade RPC (Recommended)

The chunked upgrade system splits the WASM into 64KB chunks to fit within block size limits.

#### Available RPC Methods

| Method | Parameters | Description |
|--------|------------|-------------|
| `chunkedUpgrade_initiate` | `(wasm_hex, secret_key)` | Start upgrade with full WASM |
| `chunkedUpgrade_uploadChunk` | `(index, chunk_hex, secret_key)` | Upload individual chunk |
| `chunkedUpgrade_finalize` | `(secret_key)` | Apply the upgrade |
| `chunkedUpgrade_status` | `()` | Check pending upgrade status |
| `chunkedUpgrade_cancel` | `(secret_key)` | Cancel pending upgrade |
| `chunkedUpgrade_calculateChunks` | `(size)` | Calculate chunks needed |

#### Python Upgrade Script

```python
#!/usr/bin/env python3
"""
QuantumHarmony Runtime Upgrade Script

Usage:
    python3 runtime_upgrade.py --wasm <path> --endpoint <url> --secret-key <hex>
"""

import requests
import json
import time
import argparse

def rpc_call(endpoint, method, params=None):
    """Make a JSON-RPC call"""
    payload = {
        "jsonrpc": "2.0",
        "id": 1,
        "method": method,
        "params": params or []
    }
    response = requests.post(endpoint, json=payload, timeout=300)
    return response.json()

def main():
    parser = argparse.ArgumentParser(description="QuantumHarmony Runtime Upgrade")
    parser.add_argument("--wasm", required=True, help="Path to runtime WASM file")
    parser.add_argument("--endpoint", default="http://127.0.0.1:9944", help="RPC endpoint")
    parser.add_argument("--secret-key", required=True, help="128-byte SPHINCS+ secret key (hex)")
    args = parser.parse_args()

    # Read WASM
    with open(args.wasm, "rb") as f:
        wasm_data = f.read()

    wasm_hex = "0x" + wasm_data.hex()
    secret_hex = args.secret_key if args.secret_key.startswith("0x") else "0x" + args.secret_key

    print(f"WASM size: {len(wasm_data)} bytes ({len(wasm_data)/1024:.1f} KB)")

    # Check current version
    result = rpc_call(args.endpoint, "state_getRuntimeVersion")
    current_version = result.get("result", {}).get("specVersion", 0)
    print(f"Current spec_version: {current_version}")

    # Step 1: Initiate
    print("\n[1/3] Initiating chunked upgrade...")
    result = rpc_call(args.endpoint, "chunkedUpgrade_initiate", [wasm_hex, secret_hex])
    if "error" in result:
        print(f"Error: {result['error']}")
        return
    print(f"Upgrade initiated: {result.get('result', {})}")

    # Step 2: Upload chunks
    CHUNK_SIZE = 65536
    num_chunks = (len(wasm_data) + CHUNK_SIZE - 1) // CHUNK_SIZE
    print(f"\n[2/3] Uploading {num_chunks} chunks...")

    for i in range(num_chunks):
        start = i * CHUNK_SIZE
        end = min(start + CHUNK_SIZE, len(wasm_data))
        chunk = wasm_data[start:end]
        chunk_hex = "0x" + chunk.hex()

        result = rpc_call(args.endpoint, "chunkedUpgrade_uploadChunk", [i, chunk_hex, secret_hex])
        if "error" in result:
            print(f"Chunk {i} error: {result['error']}")
            return
        print(f"  Chunk {i+1}/{num_chunks} uploaded")
        time.sleep(6)  # Wait for block inclusion

    # Step 3: Finalize
    print("\n[3/3] Finalizing upgrade...")
    result = rpc_call(args.endpoint, "chunkedUpgrade_finalize", [secret_hex])
    if "error" in result:
        print(f"Error: {result['error']}")
        return
    print(f"Finalize tx: {result.get('result')}")

    # Verify
    print("\nWaiting for upgrade to take effect...")
    for i in range(12):
        time.sleep(10)
        result = rpc_call(args.endpoint, "state_getRuntimeVersion")
        new_version = result.get("result", {}).get("specVersion", 0)
        if new_version != current_version:
            print(f"\n✅ UPGRADE SUCCESSFUL!")
            print(f"   Old version: {current_version}")
            print(f"   New version: {new_version}")
            return
        print(f"  {(i+1)*10}s - still at version {new_version}")

    print("\n⚠️  Timeout - check node logs for errors")

if __name__ == "__main__":
    main()
```

### Method 2: Direct Binary (runtime-upgrade tool)

```bash
# Build the upgrade tool
cargo build --release -p runtime-upgrade

# Run the upgrade
./target/release/runtime-upgrade \
    --endpoint http://NODE_IP:9944 \
    --wasm target/release/wbuild/quantumharmony-runtime/quantumharmony_runtime.compact.compressed.wasm
```

## SPHINCS+ Keys

### Test Account Keys (Development Only)

The test accounts in `node/src/test_accounts.rs` have hardcoded SPHINCS+ keys:

| Account | SS58 Address | Role |
|---------|--------------|------|
| Alice | 5HDjAbVHMuJzezSccj6eFrEA6nKjonrFRm8h7aTiJXSHP5Qi | Sudo + Validator |
| Bob | 5CAgvufYLRan7pybcGWqTxsxXRAj922Qep6UJmZuVWu8Uv11 | Validator |
| Charlie | 5En9M95WwS354QWCM29UyFLsdQgXZ8WzdBvmHa3u6w1bmTS1 | Validator |

### Key Format

SPHINCS+ keys consist of:
- **Seed**: 48 bytes - Used to derive the keypair
- **Public Key**: 64 bytes - Used for verification
- **Secret Key**: 128 bytes - Required for signing (seed + public concatenated)

### Extracting Keys from test_accounts.rs

```rust
// Alice's keys (from node/src/test_accounts.rs)
pub const ALICE_SPHINCS_SEED: [u8; 48] = [...];
pub const ALICE_SPHINCS_PUBLIC: [u8; 64] = [...];
pub const ALICE_SPHINCS_SECRET: [u8; 128] = [...];  // This is needed for upgrades
```

## Node Configuration

Nodes must be started with unsafe RPC methods enabled:

```bash
./quantumharmony-node \
    --chain /path/to/chainspec.json \
    --validator \
    --name Alice \
    --rpc-cors all \
    --unsafe-rpc-external \
    --rpc-methods unsafe \
    --base-path /data/alice
```

## Verification

After upgrade, verify on all nodes:

```bash
# Check spec_version
curl -s http://NODE_IP:9944 \
    -H "Content-Type: application/json" \
    -d '{"id":1,"jsonrpc":"2.0","method":"state_getRuntimeVersion"}' \
    | python3 -c "import sys,json; print('spec_version:', json.load(sys.stdin)['result']['specVersion'])"

# Check block production
curl -s http://NODE_IP:9944 \
    -H "Content-Type: application/json" \
    -d '{"id":1,"jsonrpc":"2.0","method":"chain_getHeader"}' \
    | python3 -c "import sys,json; print('Block:', int(json.load(sys.stdin)['result']['number'], 16))"

# Check peers
curl -s http://NODE_IP:9944 \
    -H "Content-Type: application/json" \
    -d '{"id":1,"jsonrpc":"2.0","method":"system_peers"}' \
    | python3 -c "import sys,json; print('Peers:', len(json.load(sys.stdin)['result']))"
```

## Troubleshooting

### "Invalid SPHINCS+ key size"
- Ensure the secret key is exactly 128 bytes (256 hex characters)

### "BadOrigin" or "RequireSudo"
- The signing key doesn't match the sudo account on chain
- Verify the sudo key: query `state_getStorage` with sudo pallet key

### Upgrade not taking effect
- Check node logs for transaction errors
- Ensure all chunks were uploaded successfully
- Verify the finalize transaction was included in a block

### Block production stopped
- Runtime upgrade may have broken consensus
- Rollback by restarting nodes with previous binary

## Security Considerations

1. **Never expose secret keys** - Use secure key management
2. **Test on devnet first** - Always test upgrades before production
3. **Backup chain data** - Create snapshots before upgrades
4. **Monitor validators** - Ensure all validators upgrade successfully
5. **Keep old binary** - In case rollback is needed

## Production Checklist

- [ ] Runtime built and tested locally
- [ ] WASM hash verified
- [ ] All validators notified
- [ ] Chain data backed up
- [ ] Old binary available for rollback
- [ ] Monitoring in place
- [ ] Secret key secured
- [ ] RPC methods enabled on upgrade node
