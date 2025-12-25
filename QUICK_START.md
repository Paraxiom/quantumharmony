# QuantumHarmony Quick Start Guide

## What's Ready ✅

1. **Quantum-Resistant Blockchain Node** - Running on port 9944
2. **Runtime with SPHINCS+ Signatures** - NIST-approved post-quantum crypto
3. **Runtime Compiler Service** - HTTP API for dynamic runtime compilation
4. **Upgrade-Ready Runtime** - spec_version 2 compiled and ready

## Quick Commands

### Start the Node
```bash
cd /Users/sylvaincormier/QuantumVerseProtocols/quantumharmony
./target/release/quantumharmony-node --dev --tmp
```

**Access**: ws://127.0.0.1:9944

### Start the Runtime Compiler
```bash
cd /Users/sylvaincormier/QuantumVerseProtocols/quantumharmony/runtime-compiler
cargo run --release
```

**Access**: http://127.0.0.1:3030

### Check Node Status
```bash
curl -H "Content-Type: application/json" -d '{
  "jsonrpc": "2.0",
  "method": "state_getRuntimeVersion",
  "params": [],
  "id": 1
}' http://127.0.0.1:9944
```

## Runtime Upgrade (Via Wallet)

### Step 1: Prepare
- **WASM Location**: `target/release/wbuild/quantumharmony-runtime/quantumharmony_runtime.compact.compressed.wasm`
- **Size**: 377 KB
- **New Version**: spec_version 2

### Step 2: Submit via Wallet
1. Connect quantum-qpp-wallet to `ws://127.0.0.1:9944`
2. Use Alice's account (`//Alice`)
3. Submit extrinsic:
   ```
   sudo.sudoUncheckedWeight(
     system.setCode(code),
     { ref_time: 500000000000, proof_size: 5000000 }
   )
   ```
4. Upload WASM file from path above

### Step 3: Verify
```bash
# Should show specVersion: 2
curl -H "Content-Type: application/json" -d '{
  "jsonrpc": "2.0",
  "method": "state_getRuntimeVersion",
  "params": [],
  "id": 1
}' http://127.0.0.1:9944 | jq .result.specVersion
```

## Runtime Compiler Usage

### Compile from Git
```bash
curl -X POST http://127.0.0.1:3030/compile \
  -H "Content-Type: application/json" \
  -d '{
    "git_url": "https://github.com/Paraxiom/QuantumVerseProtocols",
    "git_ref": "main",
    "package": "quantumharmony-runtime",
    "release": true
  }'
```

### Compile from Source
```bash
curl -X POST http://127.0.0.1:3030/compile \
  -H "Content-Type: application/json" \
  -d '{
    "source": "/* Your Rust runtime code */",
    "release": true
  }'
```

## Test Wallet Connectivity

```bash
cd /Users/sylvaincormier/QuantumVerseProtocols/quantumharmony/quantum-qpp-wallet

# Check example code
cat examples/send_quantum_tx.rs
```

## Key Features

✅ **SPHINCS+ Signatures** - 49KB signatures, quantum-resistant
✅ **Aura Consensus** - Authority-based block production
✅ **Session Management** - Validator rotation support
✅ **Runtime Upgrades** - Forkless upgrades via sudo.setCode
✅ **Dynamic Compilation** - HTTP service for runtime compilation
✅ **Quantum Hasher** - Keccak-256 based hashing

## Architecture

```
┌─────────────────┐
│  Quantum Wallet │
│   (SPHINCS+)    │
└────────┬────────┘
         │
         ↓ ws://9944
┌─────────────────┐         ┌──────────────────┐
│ QuantumHarmony  │←────────│ Runtime Compiler │
│      Node       │ WASM    │    Service       │
│   (Aura + PQ)   │         │  (HTTP :3030)    │
└─────────────────┘         └──────────────────┘
         │
         ↓
┌─────────────────┐
│  Runtime WASM   │
│  (spec_v2)      │
└─────────────────┘
```

## Files to Know

- `RUNTIME_UPGRADE_INFO.md` - Detailed upgrade instructions
- `SESSION_SUMMARY.md` - Full session report
- `runtime-compiler/README.md` - Compiler service docs

## Development Accounts

**Alice** (Sudo)
- Seed: `//Alice`
- Has sudo privileges
- Use for runtime upgrades

**Bob, Charlie, Dave, Eve, Ferdie**
- Pre-funded test accounts
- Use for testing transactions

## Troubleshooting

### Node won't start?
```bash
# Check if port 9944 is in use
lsof -i :9944

# View logs
cat /tmp/node-startup-test.log
```

### Runtime compiler fails?
```bash
# Check if port 3030 is in use
lsof -i :3030

# Test manually
cd runtime-compiler
cargo check
```

### Wallet can't connect?
```bash
# Verify node is running
curl http://127.0.0.1:9944 -H "Content-Type: application/json" -d '{
  "jsonrpc": "2.0",
  "method": "system_health",
  "params": [],
  "id": 1
}'
```

## Next Steps

1. ✅ Start node (if not running)
2. ⏳ Submit runtime upgrade via wallet
3. ⏳ Verify upgrade successful (spec_version = 2)
4. ⏳ Test SPHINCS+ transaction signing
5. ⏳ Start runtime compiler service
6. ⏳ Test dynamic runtime compilation

---

**Node**: ws://127.0.0.1:9944
**Compiler**: http://127.0.0.1:3030
**Status**: ✅ Ready for testing
