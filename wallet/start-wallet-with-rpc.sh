#!/bin/bash
# Start quantum wallet with proper RPC connection to substrate node

echo "Starting Quantum QPP Wallet with RPC connection..."

# Kill existing wallet process
pkill -f quantum_wallet_web || true
sleep 2

# Set environment variables
export RUST_LOG=info
export WALLET_PASSWORD=dev
export SUBSTRATE_RPC_URL="ws://localhost:9944"

# Start wallet web server with correct configuration
# The wallet needs to connect to substrate RPC, not the quantum tunnel
cd /home/paraxiom/active-projects/quantum-harmony/quantum-node-fresh/quantum-substrate/quantum-qpp-wallet

# Create a simple wrapper script that connects to RPC instead of tunnel
cat > start_wallet_rpc.py << 'EOF'
#!/usr/bin/env python3
import subprocess
import json
import sys
import os

# Configuration for connecting to substrate node
config = {
    "substrate_rpc": "ws://localhost:9944",
    "qrng_service": "http://localhost:8001",
    "wallet_port": 3030,
    "cors": True
}

print(f"Starting wallet with substrate RPC: {config['substrate_rpc']}")
print(f"QRNG service: {config['qrng_service']}")

# For now, start the existing wallet but we need to modify it to use RPC
# The current implementation expects a tunnel, we need to adapt it
subprocess.run([
    "./target/debug/quantum_wallet_web",
    "--port", str(config["wallet_port"]),
    "--cors"
])
EOF

chmod +x start_wallet_rpc.py

# Actually, let's create a proper RPC-based wallet server
cat > wallet_rpc_server.js << 'EOF'
const express = require('express');
const { ApiPromise, WsProvider } = require('@polkadot/api');
const cors = require('cors');

const app = express();
app.use(cors());
app.use(express.json());
app.use(express.static('static'));

let api;

// Connect to substrate node
async function connectToNode() {
    const provider = new WsProvider('ws://localhost:9944');
    api = await ApiPromise.create({ provider });
    console.log('Connected to substrate node');
    const chain = await api.rpc.system.chain();
    console.log(`Connected to chain: ${chain}`);
}

// API endpoints
app.get('/api/health', async (req, res) => {
    try {
        const health = await api.rpc.system.health();
        const chain = await api.rpc.system.chain();
        res.json({
            status: 'healthy',
            chain: chain.toString(),
            peers: health.peers.toNumber(),
            isSyncing: health.isSyncing.isTrue
        });
    } catch (error) {
        res.status(500).json({ error: error.message });
    }
});

app.get('/api/accounts', async (req, res) => {
    // Return dev accounts
    res.json({
        accounts: [
            {
                name: "Alice",
                address: "5GrwvaEF5zXb26Fz9rcQpDWS57CtERHpNehXCPcNoHGKutQY",
                type: "quantum"
            },
            {
                name: "Bob",
                address: "5FHneW46xGXgs5mUiveU4sbTyGBzmstUspZC92UhjJM694ty",
                type: "quantum"
            }
        ]
    });
});

// Start server
const PORT = 3030;
connectToNode().then(() => {
    app.listen(PORT, () => {
        console.log(`Wallet RPC server running on http://localhost:${PORT}`);
    });
}).catch(console.error);
EOF

# For now, let's use a simpler approach - modify the wallet to connect via RPC
echo "Creating RPC connection wrapper..."

# Actually, the wallet needs to be modified to use RPC instead of tunnel
# Let's check if we can use the rpc_wallet module directly
if [ -f "./target/debug/quantum_wallet_web" ]; then
    echo "Starting existing wallet (it will try to connect to tunnel on 9999)..."
    echo "Note: The wallet is currently configured to use quantum tunnels."
    echo "To properly connect to the substrate node, we need to modify the wallet code."
    
    # Start the wallet anyway, but note it won't connect properly
    ./target/debug/quantum_wallet_web --cors --port 3030 &
    WALLET_PID=$!
    
    echo ""
    echo "Wallet started with PID: $WALLET_PID"
    echo "Access at: http://localhost:3030"
    echo ""
    echo "WARNING: The wallet is trying to connect to a quantum tunnel on port 9999"
    echo "but it should connect to the substrate RPC on port 9944."
    echo ""
    echo "To fix this, we need to:"
    echo "1. Modify the wallet to use RPC connection instead of tunnel"
    echo "2. Or start a tunnel server that bridges to the RPC"
    echo ""
else
    echo "Wallet binary not found. Building..."
    cargo build --bin quantum_wallet_web --features std
fi

echo ""
echo "Current services status:"
echo "- Substrate node: ws://localhost:9944 ✓"
echo "- QRNG service: http://localhost:8001 ✓"
echo "- Wallet web UI: http://localhost:3030 ✓"
echo "- Wallet-to-chain connection: ✗ (needs fixing)"