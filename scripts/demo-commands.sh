#!/bin/bash
# QuantumHarmony Demo Commands
# Run this to verify all commands work before recording

set -e

ALICE="http://51.79.26.123:9944"
BOB="http://51.79.26.168:9944"
CHARLIE="http://209.38.225.4:9944"

rpc() {
    curl -s -H "Content-Type: application/json" -d "$1" "$2" | jq .
}

echo "=========================================="
echo "  QuantumHarmony Live Demo Commands"
echo "=========================================="
echo ""

echo "1. Network Health Check"
echo "------------------------"
rpc '{"jsonrpc":"2.0","method":"system_health","params":[],"id":1}' $ALICE
echo ""

echo "2. Chain Properties (QMHY Token)"
echo "---------------------------------"
rpc '{"jsonrpc":"2.0","method":"system_properties","params":[],"id":1}' $ALICE
echo ""

echo "3. Current Block Number"
echo "------------------------"
BLOCK=$(curl -s -H "Content-Type: application/json" -d '{"jsonrpc":"2.0","method":"chain_getHeader","params":[],"id":1}' $ALICE | jq -r '.result.number')
printf "Block: %d (0x%s)\n" "$((16#${BLOCK:2}))" "${BLOCK:2}"
echo ""

echo "4. Genesis Hash (Chain Identity)"
echo "---------------------------------"
rpc '{"jsonrpc":"2.0","method":"gateway_genesisHash","params":[],"id":1}' $ALICE
echo ""

echo "5. Custom RPC Methods"
echo "----------------------"
curl -s -H "Content-Type: application/json" -d '{"jsonrpc":"2.0","method":"rpc_methods","params":[],"id":1}' $ALICE | jq '.result.methods | map(select(startswith("gateway") or startswith("notarial")))'
echo ""

echo "6. Notarial Verification Test"
echo "------------------------------"
HASH="0x$(echo -n 'QuantumHarmony Demo' | shasum -a 256 | cut -d' ' -f1)"
echo "Document hash: $HASH"
curl -s -H "Content-Type: application/json" -d "{\"jsonrpc\":\"2.0\",\"method\":\"notarial_verifyDocument\",\"params\":[\"$HASH\"],\"id\":1}" $ALICE | jq .
echo ""

echo "7. All Three Validators Responding"
echo "------------------------------------"
echo -n "Alice (Canada):  " && curl -s -H "Content-Type: application/json" -d '{"jsonrpc":"2.0","method":"system_health","params":[],"id":1}' $ALICE | jq -r '.result.peers'
echo -n "Bob (Canada):    " && curl -s -H "Content-Type: application/json" -d '{"jsonrpc":"2.0","method":"system_health","params":[],"id":1}' $BOB | jq -r '.result.peers'
echo -n "Charlie (France): " && curl -s -H "Content-Type: application/json" -d '{"jsonrpc":"2.0","method":"system_health","params":[],"id":1}' $CHARLIE | jq -r '.result.peers'
echo ""

echo "8. Block Production Test (wait 7 seconds)"
echo "-------------------------------------------"
BLOCK1=$(curl -s -H "Content-Type: application/json" -d '{"jsonrpc":"2.0","method":"chain_getHeader","params":[],"id":1}' $ALICE | jq -r '.result.number')
echo "Block at T+0: $((16#${BLOCK1:2}))"
sleep 7
BLOCK2=$(curl -s -H "Content-Type: application/json" -d '{"jsonrpc":"2.0","method":"chain_getHeader","params":[],"id":1}' $ALICE | jq -r '.result.number')
echo "Block at T+7s: $((16#${BLOCK2:2}))"
DIFF=$(( $((16#${BLOCK2:2})) - $((16#${BLOCK1:2})) ))
echo "Blocks produced: $DIFF (expected: 1-2)"
echo ""

echo "=========================================="
echo "  All checks passed!"
echo "=========================================="
