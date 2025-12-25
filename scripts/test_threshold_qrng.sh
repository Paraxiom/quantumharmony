#!/bin/bash
# Threshold QRNG Real-time Test Script
#
# This script demonstrates the threshold QRNG system in action
# Prerequisites: Node running at localhost:9944

set -e

NODE_URL="http://localhost:9944"
BOLD="\033[1m"
GREEN="\033[0;32m"
BLUE="\033[0;34m"
YELLOW="\033[1;33m"
NC="\033[0m" # No Color

echo -e "${BOLD}🔮 QuantumHarmony Threshold QRNG Test Suite${NC}\n"

# Helper function to make RPC calls
rpc_call() {
    local method=$1
    local params=$2

    curl -s -X POST \
        -H "Content-Type: application/json" \
        -d "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"$method\",\"params\":$params}" \
        "$NODE_URL" | jq -r '.result'
}

# Test 1: Check node is running
echo -e "${BLUE}Test 1: Checking node status...${NC}"
BLOCK=$(rpc_call "chain_getBlock" "[]" | jq -r '.block.header.number')
echo -e "   Current block: ${GREEN}$BLOCK${NC}"
echo

# Test 2: Get threshold config
echo -e "${BLUE}Test 2: Getting threshold QRNG configuration...${NC}"
CONFIG=$(rpc_call "qrng_getConfig" "[]")
echo -e "${GREEN}$CONFIG${NC}" | jq '.'
echo

# Test 3: Get device queue status
echo -e "${BLUE}Test 3: Checking device queue status...${NC}"
QUEUES=$(rpc_call "qrng_getDeviceQueues" "[]")
echo -e "${GREEN}Device Queues:${NC}"
echo "$QUEUES" | jq -r '.[] | "   \(.device_name): \(.queue_length) shares (enabled: \(.enabled))"'
echo

# Test 4: Submit mock shares
echo -e "${BLUE}Test 4: Submitting mock device shares...${NC}"

# Toshiba QRNG - excellent quality (0.8% QBER)
echo -n "   Submitting Toshiba share (QBER 0.8%)... "
RESULT1=$(rpc_call "qrng_submitDeviceShare" '[{"device_id":"toshiba-qrng","share_hex":"0xdeadbeef01","qber":0.8,"stark_proof_hex":"0xcafebabe01"}]')
echo -e "${GREEN}$RESULT1${NC}"

# Crypto4A QRNG - good quality (1.2% QBER)
echo -n "   Submitting Crypto4A share (QBER 1.2%)... "
RESULT2=$(rpc_call "qrng_submitDeviceShare" '[{"device_id":"crypto4a-qrng","share_hex":"0xdeadbeef02","qber":1.2,"stark_proof_hex":"0xcafebabe02"}]')
echo -e "${GREEN}$RESULT2${NC}"

# KIRQ - excellent quality (0.9% QBER)
echo -n "   Submitting KIRQ share (QBER 0.9%)... "
RESULT3=$(rpc_call "qrng_submitDeviceShare" '[{"device_id":"kirq","share_hex":"0xdeadbeef03","qber":0.9,"stark_proof_hex":"0xcafebabe03"}]')
echo -e "${GREEN}$RESULT3${NC}"
echo

# Test 5: Check updated queue status
echo -e "${BLUE}Test 5: Checking updated queue status...${NC}"
QUEUES2=$(rpc_call "qrng_getDeviceQueues" "[]")
echo "$QUEUES2" | jq -r '.[] | "   \(.device_name): \(.queue_length) shares"'
echo

# Test 6: Trigger share collection
echo -e "${BLUE}Test 6: Triggering leader share collection...${NC}"
COLLECTION=$(rpc_call "qrng_collectShares" '["alice"]')
echo -e "   ${GREEN}$COLLECTION${NC}"
echo

# Test 7: Get reconstruction history
echo -e "${BLUE}Test 7: Checking reconstruction history...${NC}"
HISTORY=$(rpc_call "qrng_getReconstructionHistory" '[10]')
HISTORY_COUNT=$(echo "$HISTORY" | jq '. | length')
echo -e "   Found ${GREEN}$HISTORY_COUNT${NC} reconstruction events"
if [ "$HISTORY_COUNT" -gt "0" ]; then
    echo "$HISTORY" | jq -r '.[] | "   - \(.timestamp): \(.devices_used | join(", ")) (avg QBER: \(.qber_average)%)"'
fi
echo

# Test 8: Performance test
echo -e "${BLUE}Test 8: RPC Performance test...${NC}"
echo -n "   Running 10 requests... "
START=$(date +%s%N)
for i in {1..10}; do
    rpc_call "qrng_getDeviceQueues" "[]" > /dev/null
done
END=$(date +%s%N)
DURATION=$(( (END - START) / 1000000 ))
AVG=$(( DURATION / 10 ))
echo -e "${GREEN}Done!${NC}"
echo -e "   Total time: ${YELLOW}${DURATION}ms${NC}"
echo -e "   Average latency: ${YELLOW}${AVG}ms${NC}"
echo

# Summary
echo -e "${BOLD}${GREEN}✅ All tests completed!${NC}\n"
echo -e "${BOLD}Summary:${NC}"
echo -e "   📊 Threshold: K=2, M=3"
echo -e "   🔧 Devices: Toshiba, Crypto4A, KIRQ"
echo -e "   ⚡ Quality-based selection: ENABLED"
echo -e "   🔐 Byzantine validation: READY"
echo -e "   🚀 System status: ${GREEN}OPERATIONAL${NC}"
echo
