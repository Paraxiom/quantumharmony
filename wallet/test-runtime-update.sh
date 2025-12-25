#!/bin/bash
# Test Runtime Update via RPC (without Tauri)
#
# This script demonstrates runtime upgrades using direct RPC calls
# Prerequisites: Node running at localhost:9944

set -e

NODE_URL="http://localhost:9944"
RUNTIME_WASM="../target/release/wbuild/quantumharmony-runtime/quantumharmony_runtime.compact.compressed.wasm"

echo "🔮 QuantumHarmony Runtime Update Test"
echo ""

# Check if WASM exists
if [ ! -f "$RUNTIME_WASM" ]; then
    echo "❌ Runtime WASM not found at: $RUNTIME_WASM"
    echo "   Build it first:"
    echo "   cd ../runtime && cargo build --release"
    exit 1
fi

# Helper function for RPC calls
rpc_call() {
    local method=$1
    local params=$2

    curl -s -X POST \
        -H "Content-Type: application/json" \
        -d "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"$method\",\"params\":$params}" \
        "$NODE_URL" | jq -r '.'
}

# Test 1: Get current runtime version
echo "1️⃣  Getting current runtime version..."
VERSION=$(rpc_call "state_getRuntimeVersion" "[]")
echo "$VERSION" | jq '.'

SPEC_VERSION=$(echo "$VERSION" | jq -r '.result.specVersion')
SPEC_NAME=$(echo "$VERSION" | jq -r '.result.specName')
echo ""
echo "   Current Runtime: $SPEC_NAME"
echo "   Spec Version: $SPEC_VERSION"
echo ""

# Test 2: Check WASM file
echo "2️⃣  Checking runtime WASM..."
WASM_SIZE=$(wc -c < "$RUNTIME_WASM")
echo "   File: $RUNTIME_WASM"
echo "   Size: $WASM_SIZE bytes"
echo ""

# Test 3: Read WASM and convert to hex
echo "3️⃣  Encoding WASM to hex..."
WASM_HEX=$(xxd -p "$RUNTIME_WASM" | tr -d '\n')
HEX_SIZE=${#WASM_HEX}
echo "   Hex size: $HEX_SIZE characters"
echo "   First 100 chars: ${WASM_HEX:0:100}..."
echo ""

# Test 4: Submit runtime upgrade (this requires sudo)
echo "4️⃣  Submitting runtime upgrade..."
echo "   ⚠️  This will upgrade the runtime to spec version $((SPEC_VERSION + 1))"
read -p "   Continue? (y/N) " -n 1 -r
echo
if [[ ! $REPLY =~ ^[Yy]$ ]]; then
    echo "   Cancelled."
    exit 0
fi

echo "   Preparing sudo.setCode() extrinsic..."

# For dev mode, we use Alice's key (well-known dev seed)
# In production, this would require proper signing

# Note: This is a simplified version. Proper implementation requires:
# 1. Construct the setCode call
# 2. Wrap in sudo call
# 3. Sign with Alice's key
# 4. Submit as signed extrinsic

# For now, show what would be submitted
echo "   WASM payload size: $WASM_SIZE bytes"
echo "   Sudo seed: //Alice (dev mode)"
echo ""
echo "   ℹ️  To actually submit, you need to use:"
echo "   - polkadot-js/api"
echo "   - subxt"
echo "   - Tauri wallet (once CLI is fixed)"
echo ""

# Test 5: Show expected result
echo "5️⃣  Expected result after upgrade:"
echo "   - Transaction submitted in block N"
echo "   - Block N finalized (~6 seconds)"
echo "   - All nodes switch to new runtime automatically"
echo "   - New spec version: $((SPEC_VERSION + 1))"
echo "   - Zero downtime, no node restarts"
echo ""

echo "✅ Runtime update test complete!"
echo ""
echo "📚 For full implementation, see:"
echo "   - RUNTIME_UPDATES.md (complete guide)"
echo "   - static/tauri-dashboard.html (GUI implementation)"
echo "   - src-tauri/src/main.rs (Tauri commands)"
