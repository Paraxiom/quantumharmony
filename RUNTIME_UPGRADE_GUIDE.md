# QuantumHarmony Runtime Upgrade Guide

## Overview

This guide explains how to perform quantum-safe runtime upgrades on QuantumHarmony using SPHINCS+-SHAKE-256s signatures.

## What You Need

1. **Updated Runtime WASM**: Build the new runtime
```bash
cd /Users/sylvaincormier/QuantumVerseProtocols/quantumharmony
cargo build --release -p quantumharmony-runtime
```

The WASM will be at:
```
target/release/wbuild/quantumharmony-runtime/quantumharmony_runtime.compact.compressed.wasm
```

2. **Access to Charlie's Node**: Charlie has sudo authority
   - IP: `YOUR_NODE_IP`
   - RPC Port: `9944`
   - WebSocket: `ws://YOUR_NODE_IP:9944`

3. **Sudo Authority**: Only Charlie (`5FLSigC9HGRKVhB9FiEo4Y3koPsNmBmLJbpXg2mp1hXcS59Y`) can perform upgrades

## Method 1: Polkadot-JS Apps UI (RECOMMENDED)

This is the **quantum-safe** method that works NOW.

### Step-by-Step Instructions

1. **Open Polkadot-JS Apps**
   - Go to https://polkadot.js.org/apps

2. **Connect to Charlie's Node**
   - Click the network name in the top-left corner
   - Select "Development" → "Custom endpoint"
   - Enter: `ws://YOUR_NODE_IP:9944`
   - Click "Switch"
   - Wait for connection (you should see a green dot)

3. **Navigate to Extrinsics**
   - Go to **Developer** → **Extrinsics**

4. **Configure the Runtime Upgrade Transaction**
   - **Account**: Select `CHARLIE`
   - **Submit the following extrinsic**: `sudo` → `sudoUncheckedWeight(call, weight)`
   - **For the `call` parameter**:
     * Select: `system` → `setCode(code)`
     * Click the file upload button next to the code field
     * Select your WASM file: `quantumharmony_runtime.compact.compressed.wasm`
   - **For the `weight` parameter**:
     * Set `refTime`: `0` (the runtime will auto-calculate)
     * Set `proofSize`: `0` (the runtime will auto-calculate)

5. **Sign and Submit**
   - Click "Submit Transaction"
   - The browser will show a signing dialog
   - **THE SIGNING HAPPENS ON THE NODE** using Charlie's SPHINCS+ keystore
   - Click "Sign and Submit"

6. **Monitor the Upgrade**
   - Watch for the transaction to be included in a block
   - Go to **Network** → **Explorer** to see recent events
   - Look for `system.CodeUpdated` event
   - Check **Developer** → **RPC calls** → `state` → `getRuntimeVersion()` to confirm the new spec_version

### Why This is Quantum-Safe

- The node has Charlie's SPHINCS+ private key in its keystore
- Polkadot-JS Apps sends the transaction to the node for signing
- The node signs with SPHINCS+-SHAKE-256s (post-quantum)
- No classical cryptography is involved in the signing process

## Method 2: CLI Tool (Preparation Only)

The Rust CLI tool at `tools/runtime-upgrade` can help you **prepare** and **verify** the upgrade transaction, but currently cannot sign it with SPHINCS+.

### Using the CLI Tool

```bash
cd /Users/sylvaincormier/QuantumVerseProtocols/quantumharmony
cargo build --release -p quantumharmony-runtime-upgrade

./target/release/runtime-upgrade \
  --endpoint ws://YOUR_NODE_IP:9944 \
  --wasm ./target/release/wbuild/quantumharmony-runtime/quantumharmony_runtime.compact.compressed.wasm \
  --signer 5FLSigC9HGRKVhB9FiEo4Y3koPsNmBmLJbpXg2mp1hXcS59Y
```

This will:
- Connect to the node
- Verify the WASM file
- Check sudo authority
- Get the current runtime version
- Encode the transaction
- Show you what would be submitted

Then use Method 1 (Polkadot-JS Apps) to actually submit.

## Future: Fully Automated CLI Upgrades

To enable fully automated, quantum-safe CLI upgrades, we would need to:

1. **Add SPHINCS+ Signing to the Rust CLI Tool**:
```rust
use pqcrypto_sphincsplus::sphincsshake256ssimple::{sign, PublicKey, SecretKey};
```

2. **Securely Load Charlie's Private Key**:
   - From HSM
   - From encrypted keystore
   - From secure environment variable

3. **Build and Submit the Signed Extrinsic**:
```rust
let signature = sign(&message, &secret_key);
let signed_extrinsic = create_signed_extrinsic(call, signature, ...);
client.request("author_submitExtrinsic", rpc_params![signed_extrinsic]).await?;
```

## Democracy Pallet (Future Governance)

For decentralized, community-driven upgrades without sudo:

1. **Enable the Democracy Pallet** (currently commented out in `runtime/src/lib.rs:566`)
2. **Configure Voting Parameters**:
   - Voting period
   - Enactment delay
   - Minimum deposit
3. **Submit Proposals via Democracy**:
   - Anyone can propose a runtime upgrade
   - Token holders vote
   - Approved upgrades execute automatically

## Troubleshooting

### Cannot Connect to Node
```bash
curl -H "Content-Type: application/json" \
  -d '{"id":1,"jsonrpc":"2.0","method":"system_chain","params":[]}' \
  http://YOUR_NODE_IP:9944
```

Should return: `{"jsonrpc":"2.0","result":"QuantumHarmony Testnet","id":1}`

### Sudo Key Mismatch

Check current sudo key:
```bash
curl -H "Content-Type: application/json" \
  -d '{"id":1,"jsonrpc":"2.0","method":"state_getStorage","params":["0x50a63a871aced22e88ee6466fe5aa5d9"]}' \
  http://YOUR_NODE_IP:9944
```

### WASM File Issues

Verify WASM size (should be 500-600 KB):
```bash
ls -lh target/release/wbuild/quantumharmony-runtime/quantumharmony_runtime.compact.compressed.wasm
```

## Important Notes

- **Always increment `spec_version`** in `runtime/src/lib.rs` before building
- **Test on a local network first** before upgrading production
- **Backup your chain state** before major upgrades
- **Monitor the network** during and after the upgrade for any issues

## Summary

**For quantum-safe runtime upgrades RIGHT NOW**:
→ Use Polkadot-JS Apps UI (Method 1)

**For preparation and verification**:
→ Use the CLI tool (`tools/runtime-upgrade`)

**For future automated governance**:
→ Enable the Democracy pallet
