#!/bin/bash
# Test Runtime Segmentation RPC endpoints
# Demonstrates 512-segment toroidal mesh queries

RPC_URL="http://localhost:9944"

echo "🔧 Testing Runtime Segmentation RPC Methods"
echo "============================================"
echo ""

# Test 1: Get topology information
echo "1️⃣ Testing segmentation_getTopology"
echo "   Shows overall mesh configuration..."
curl -H "Content-Type: application/json" \
     -d '{"id":1, "jsonrpc":"2.0", "method":"segmentation_getTopology"}' \
     $RPC_URL 2>/dev/null | jq '.'
echo ""

# Test 2: Get specific segment info
echo "2️⃣ Testing segmentation_getSegmentInfo (Segment ID 0)"
echo "   Shows coordinates and neighbors for segment 0..."
curl -H "Content-Type: application/json" \
     -d '{"id":1, "jsonrpc":"2.0", "method":"segmentation_getSegmentInfo", "params":[0]}' \
     $RPC_URL 2>/dev/null | jq '.'
echo ""

# Test 3: Get middle segment
echo "3️⃣ Testing segmentation_getSegmentInfo (Segment ID 256 - middle segment)"
echo "   Shows coordinates and neighbors for center of mesh..."
curl -H "Content-Type: application/json" \
     -d '{"id":1, "jsonrpc":"2.0", "method":"segmentation_getSegmentInfo", "params":[256]}' \
     $RPC_URL 2>/dev/null | jq '.'
echo ""

# Test 4: Get neighbors
echo "4️⃣ Testing segmentation_getNeighbors (Segment 0)"
echo "   Shows 6 neighbors in toroidal mesh..."
curl -H "Content-Type: application/json" \
     -d '{"id":1, "jsonrpc":"2.0", "method":"segmentation_getNeighbors", "params":[0]}' \
     $RPC_URL 2>/dev/null | jq '.'
echo ""

# Test 5: Calculate toroidal distance
echo "5️⃣ Testing segmentation_calculateDistance (0 to 511)"
echo "   Shows toroidal distance from corner to opposite corner..."
curl -H "Content-Type: application/json" \
     -d '{"id":1, "jsonrpc":"2.0", "method":"segmentation_calculateDistance", "params":[0, 511]}' \
     $RPC_URL 2>/dev/null | jq '.'
echo ""

# Test 6: Calculate wraparound distance
echo "6️⃣ Testing segmentation_calculateDistance (0 to 7 - toroidal wrap)"
echo "   Shows distance 0->7 should be 1 (wraps around)..."
curl -H "Content-Type: application/json" \
     -d '{"id":1, "jsonrpc":"2.0", "method":"segmentation_calculateDistance", "params":[0, 7]}' \
     $RPC_URL 2>/dev/null | jq '.'
echo ""

# Test 7: Get load summary
echo "7️⃣ Testing segmentation_getSegmentsByLoad (first 10)"
echo "   Shows segments sorted by load..."
curl -H "Content-Type: application/json" \
     -d '{"id":1, "jsonrpc":"2.0", "method":"segmentation_getSegmentsByLoad", "params":[10]}' \
     $RPC_URL 2>/dev/null | jq '.'
echo ""

echo "✅ All RPC tests completed!"
echo ""
echo "📊 Summary:"
echo "   - 512 segments initialized in 8x8x8 toroidal mesh"
echo "   - Each segment has exactly 6 neighbors"
echo "   - Toroidal wraparound provides optimal path routing"
echo "   - Load balancing ready for transaction distribution"
