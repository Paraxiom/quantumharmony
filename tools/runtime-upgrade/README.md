# QuantumHarmony Runtime Upgrade Tool

A command-line utility for preparing and submitting runtime upgrades to the QuantumHarmony blockchain.

## Overview

This tool helps prepare runtime upgrade transactions for QuantumHarmony's production testnet. It connects to your node via RPC, reads the runtime WASM blob, encodes the upgrade transaction, and provides guidance for submitting it.

## Current Limitations

QuantumHarmony uses **SPHINCS+-SHAKE-256s** post-quantum signatures, which are not supported by standard Substrate tooling (subxt, polkadot-js). Therefore, this tool can:

- ✅ Connect to your node and query chain state
- ✅ Read and validate the runtime WASM file
- ✅ Encode the `sudo.sudoUncheckedWeight(system.setCode(...))` transaction
- ✅ Prepare transaction call data for manual signing

But it **cannot** sign and submit the transaction directly. You must use one of the workarounds below.

## Installation

Build the tool from the quantumharmony workspace root:

```bash
cd /path/to/quantumharmony
cargo build --release -p quantumharmony-runtime-upgrade
```

The binary will be located at:
```
target/release/runtime-upgrade
```

## Usage

### Basic Command

```bash
./target/release/runtime-upgrade \
  --endpoint http://YOUR_NODE_IP:9944 \
  --wasm ./target/release/wbuild/quantumharmony-runtime/quantumharmony_runtime.compact.compressed.wasm \
  --signer 5FLSigC9HGRKVhB9FiEo4Y3koPsNmBmLJbpXg2mp1hXcS59Y
```

### Options

- `--endpoint, -e`: HTTP RPC endpoint of the node (required)
  - Example: `http://YOUR_NODE_IP:9944` or `ws://YOUR_NODE_IP:9944`
  - The tool accepts both `http://` and `ws://` URLs

- `--wasm, -w`: Path to the runtime WASM file (required)
  - Usually located at: `target/release/wbuild/quantumharmony-runtime/quantumharmony_runtime.compact.compressed.wasm`

- `--signer, -s`: Account address that will sign the transaction
  - Default: `5FLSigC9HGRKVhB9FiEo4Y3koPsNmBmLJbpXg2mp1hXcS59Y` (Charlie's address)
  - Must have sudo authority on the chain

- `--dry-run`: Only prepare the transaction without attempting submission
  - Useful for validating the WASM file and transaction encoding

### Example Output

```
=====================================
QuantumHarmony Runtime Upgrade Tool
=====================================

Reading WASM file: "target/release/wbuild/quantumharmony-runtime/quantumharmony_runtime.compact.compressed.wasm"
  WASM size: 596 KB (610584 bytes)

Connecting to node: http://YOUR_NODE_IP:9944
✓ Connected to chain: QuantumHarmony Testnet
  Current spec_version: 100
  Current impl_version: 1

Account: 5FLSigC9HGRKVhB9FiEo4Y3koPsNmBmLJbpXg2mp1hXcS59Y
  Nonce: 42

Encoding runtime upgrade transaction...
✓ Transaction encoded
  Method: sudo.sudoUncheckedWeight(system.setCode(...))
  Call data length: 610592 bytes
  Call data (hex): 0x09020000...
```

## Performing Runtime Upgrades

Since QuantumHarmony uses SPHINCS+-SHAKE-256s (post-quantum signatures), you have these quantum-safe options:

### Option 1: Polkadot-JS Apps UI (RECOMMENDED for Manual Upgrades)

This is the simplest method and is **fully quantum-safe** - it delegates signing to your node's SPHINCS+ keystore.

1. **Start**: Open [Polkadot-JS Apps](https://polkadot.js.org/apps)

2. **Connect**: Click top-left corner → Development → Custom endpoint
   - Enter: `ws://YOUR_NODE_IP:9944` (Charlie's node)
   - Click "Switch"

3. **Navigate**: Go to **Developer → Extrinsics**

4. **Configure the Upgrade**:
   - Account: Select **CHARLIE** (the account with sudo authority)
   - Submit the following extrinsic: **sudo** → **sudoUncheckedWeight(call, weight)**
   - For the **call** parameter:
     * Select: **system** → **setCode(code)**
     * Click the file upload icon
     * Select your WASM file: `quantumharmony_runtime.compact.compressed.wasm`
   - For the **weight** parameter:
     * ref_time: `0` (auto-calculate)
     * proof_size: `0` (auto-calculate)

5. **Sign and Submit**:
   - Click **Submit Transaction**
   - The node will use Charlie's SPHINCS+ key from its keystore to sign
   - Wait for inclusion confirmation

**Note**: This method is quantum-safe because:
- The signing happens on the node using SPHINCS+ keys
- The transaction is signed with post-quantum cryptography
- No classical signature algorithms are involved

### Option 2: Automated CLI Runtime Upgrade (Future Enhancement)

For fully automated upgrades, you would need to:

1. Build SPHINCS+ signing into the Rust CLI tool by linking against `pqcrypto-sphincsplus`
2. Load Charlie's private key securely (HSM, encrypted keystore, etc.)
3. Construct and sign the extrinsic with SPHINCS+-SHAKE-256s
4. Submit via `author_submitExtrinsic`

This requires implementing:
```rust
use pqcrypto_sphincsplus::sphincsshake256ssimple::{sign, PublicKey, SecretKey};
use sp_core::sphincs::{Public, Signature};
```

**Current Status**: Not yet implemented. The Polkadot-JS UI method (Option 1) provides a quantum-safe solution for now.

## Production Testnet Details

### Validators

- **Alice** (OVH): `ws://YOUR_NODE_IP:9944`
  - Bootnode for the network

- **Bob** (OVH): `ws://YOUR_NODE_IP:9944`

- **Charlie** (DigitalOcean): `ws://YOUR_NODE_IP:9944`
  - **Has sudo authority** - use this node for runtime upgrades

### Sudo Authority

Only Charlie currently has sudo authority to perform runtime upgrades. This can be verified with:

```bash
./target/release/runtime-upgrade \
  --endpoint http://YOUR_NODE_IP:9944 \
  --wasm path/to/wasm \
  --dry-run
```

The tool will confirm if the signer has sudo access.

## Building the Runtime WASM

To compile a new runtime for upgrade:

```bash
cd /path/to/quantumharmony
cargo build --release --package quantumharmony-runtime
```

The compiled WASM will be at:
```
target/release/wbuild/quantumharmony-runtime/quantumharmony_runtime.compact.compressed.wasm
```

### Important Notes

- Always increment the `spec_version` in `runtime/src/lib.rs` before building
- The WASM file is typically 500-600 KB in size
- Test on a local network before upgrading production

## Troubleshooting

### Connection Errors

If you can't connect to the node:

1. Check the node is running: `curl http://YOUR_NODE_IP:9944 -H "Content-Type: application/json" -d '{"id":1,"jsonrpc":"2.0","method":"system_chain","params":[]}'`
2. Verify RPC is enabled with `--rpc-external --rpc-cors all`
3. Try using `ws://` instead of `http://` in the endpoint URL

### WASM File Not Found

Make sure you've built the runtime first:

```bash
cargo build --release --package quantumharmony-runtime
ls -lh target/release/wbuild/quantumharmony-runtime/
```

### Sudo Authority Issues

Only Charlie (`5FLSigC9HGRKVhB9FiEo4Y3koPsNmBmLJbpXg2mp1hXcS59Y`) has sudo authority in the current testnet. If you need to change this, submit a `sudo.setKey` transaction.

## Architecture

### Transaction Encoding

The tool manually encodes the runtime upgrade transaction using SCALE encoding:

1. **Inner call**: `system.setCode(wasm_code)`
   - Pallet index: 0 (System)
   - Call index: 0 (set_code)
   - Parameters: WASM code with compact-encoded length prefix

2. **Sudo wrapper**: `sudo.sudoUncheckedWeight(inner_call, weight)`
   - Pallet index: 9 (Sudo)
   - Call index: 2 (sudo_unchecked_weight)
   - Parameters: Inner call + weight (0 for auto-calculation)

### RPC Methods Used

- `system_chain`: Get chain name
- `state_getRuntimeVersion`: Get current runtime version
- `system_accountNextIndex`: Get account nonce
- `state_getStorage`: Query sudo key from storage

## Future Improvements

Potential enhancements when SPHINCS+ tooling becomes available:

- Direct transaction signing and submission
- Watch for transaction inclusion and finalization
- Automatic runtime version verification
- Multi-step upgrade coordination
- Rollback capabilities

## License

This tool is part of the QuantumHarmony project.

## Support

For issues or questions:
- Open an issue on the QuantumHarmony GitHub repository
- Contact the development team
