#!/bin/bash
# KIRQ Node Setup Script
# Run this on your KIRQ network nodes to connect to the droplet

set -e

echo "=== KIRQ Node Quantum Tunnel Setup ==="
echo

# Configuration
DROPLET_IP="${DROPLET_IP:-your.droplet.ip}"
DROPLET_PORT="${DROPLET_PORT:-9999}"
NODE_ID="${NODE_ID:-kirq-node-1}"
QKD_DEVICE="${QKD_DEVICE:-/dev/qkd0}"

# Check if running as root
if [ "$EUID" -eq 0 ]; then 
    echo "Do not run as root"
    exit 1
fi

# Install Rust if needed
if ! command -v cargo &> /dev/null; then
    echo "Installing Rust..."
    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
    source $HOME/.cargo/env
fi

# Clone repository
echo "Setting up quantum tunnel client..."
if [ ! -d "$HOME/quantumharmony" ]; then
    git clone https://github.com/QuantumVerseProtocols/quantumharmony.git $HOME/quantumharmony
fi

cd $HOME/quantumharmony/active-projects/quantum-harmony/quantum-node-fresh/quantum-substrate/quantum-qpp-wallet

# Build the client
echo "Building KIRQ tunnel client..."
cargo build --release --bin kirq_tunnel_client

# Create configuration directory
mkdir -p $HOME/.quantum-tunnel

# Create configuration file
cat > $HOME/.quantum-tunnel/config.toml << EOF
# KIRQ Node Configuration
node_id = "$NODE_ID"
droplet_server = "$DROPLET_IP:$DROPLET_PORT"
local_bind = "0.0.0.0:9998"

[qkd]
enabled = true
device_path = "$QKD_DEVICE"
entropy_interval = 60

[logging]
level = "info"
EOF

# Create systemd user service
mkdir -p $HOME/.config/systemd/user
cat > $HOME/.config/systemd/user/quantum-tunnel-client.service << EOF
[Unit]
Description=KIRQ Quantum Tunnel Client
After=network.target

[Service]
Type=simple
ExecStart=$HOME/quantumharmony/active-projects/quantum-harmony/quantum-node-fresh/quantum-substrate/quantum-qpp-wallet/target/release/kirq_tunnel_client --server $DROPLET_IP:$DROPLET_PORT --node-id $NODE_ID
Restart=always
RestartSec=10
Environment="RUST_LOG=info"

[Install]
WantedBy=default.target
EOF

# Create helper scripts
echo "Creating helper scripts..."

# Status script
cat > $HOME/bin/tunnel-status << 'EOF'
#!/bin/bash
systemctl --user status quantum-tunnel-client
EOF
chmod +x $HOME/bin/tunnel-status

# Logs script
cat > $HOME/bin/tunnel-logs << 'EOF'
#!/bin/bash
journalctl --user -u quantum-tunnel-client -f
EOF
chmod +x $HOME/bin/tunnel-logs

# QKD test script
cat > $HOME/bin/test-qkd << 'EOF'
#!/bin/bash
echo "Testing QKD device..."
if [ -e /dev/qkd0 ]; then
    echo "QKD device found"
    # Add actual QKD test commands here
else
    echo "QKD device not found at /dev/qkd0"
    echo "Using simulated quantum random"
fi
EOF
chmod +x $HOME/bin/test-qkd

# Enable and start service
echo "Starting quantum tunnel client..."
systemctl --user daemon-reload
systemctl --user enable quantum-tunnel-client
systemctl --user start quantum-tunnel-client

# Print summary
echo
echo "=== KIRQ Node Setup Complete ==="
echo
echo "Quantum tunnel client is running!"
echo "Connecting to: $DROPLET_IP:$DROPLET_PORT"
echo "Node ID: $NODE_ID"
echo
echo "Commands:"
echo "  tunnel-status  - Check connection status"
echo "  tunnel-logs    - View client logs"
echo "  test-qkd       - Test QKD device"
echo
echo "To manually run:"
echo "  cd $HOME/quantumharmony/active-projects/quantum-harmony/quantum-node-fresh/quantum-substrate/quantum-qpp-wallet"
echo "  ./target/release/kirq_tunnel_client --server $DROPLET_IP:$DROPLET_PORT"
echo