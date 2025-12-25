#!/bin/bash
# Connect to QuantumHarmony node from anywhere

NODE_HOST="${1:-localhost}"
NODE_WS_PORT="${2:-9944}"
USE_SSH_TUNNEL="${3:-false}"

echo "🌍 Connecting to QuantumHarmony Node"
echo "  Host: $NODE_HOST"
echo "  Port: $NODE_WS_PORT"

if [ "$USE_SSH_TUNNEL" = "true" ]; then
    echo "🔒 Creating SSH tunnel..."
    ssh -N -L 9944:localhost:9944 user@$NODE_HOST &
    SSH_PID=$!
    sleep 2
    NODE_URL="ws://localhost:9944"
else
    NODE_URL="ws://$NODE_HOST:$NODE_WS_PORT"
fi

echo "📡 Connecting to: $NODE_URL"

# Use wscat to test WebSocket connection
if command -v wscat &> /dev/null; then
    echo '{"jsonrpc":"2.0","method":"system_health","params":[],"id":1}' | wscat -c $NODE_URL
else
    echo "Install wscat for WebSocket testing: npm install -g wscat"
fi

if [ ! -z "$SSH_PID" ]; then
    kill $SSH_PID
fi
