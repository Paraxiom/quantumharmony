# Step-by-Step Dev Wallet Setup on Droplet

## Step 1: Connect to Your Droplet

```bash
# From your local machine
ssh root@your-droplet-ip
```

## Step 2: Install Prerequisites

```bash
# Update system
apt update && apt upgrade -y

# Install required packages
apt install -y build-essential pkg-config libssl-dev git curl

# Install Rust
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
source $HOME/.cargo/env

# Verify Rust installation
rustc --version
cargo --version
```

## Step 3: Clone the Wallet Code

```bash
# Create a directory for the project
mkdir -p /opt/quantum
cd /opt/quantum

# Clone the QuantumHarmony repository
git clone https://github.com/QuantumVerseProtocols/quantumharmony.git

# Navigate to the wallet directory
cd quantumharmony/active-projects/quantum-harmony/quantum-node-fresh/quantum-substrate/quantum-qpp-wallet

# Check that you're in the right place
ls -la
# You should see: Cargo.toml, src/, examples/, etc.
```

## Step 4: Build the Wallet

```bash
# Build the wallet binaries
cargo build --release --features std

# This will take a few minutes...
# The compiled binaries will be in: target/release/

# Verify the build succeeded
ls -la target/release/
# You should see: quantum_wallet_web, quantum_tunnel_server, etc.
```

## Step 5: Create a Simple Start Script

```bash
# Create a start script
cat > /opt/quantum/start-dev-wallet.sh << 'EOF'
#!/bin/bash
cd /opt/quantum/quantumharmony/active-projects/quantum-harmony/quantum-node-fresh/quantum-substrate/quantum-qpp-wallet

# Set environment variables
export RUST_LOG=info
export WALLET_PASSWORD=dev

# Start the wallet web server
./target/release/quantum_wallet_web \
    --port 3030 \
    --cors
EOF

# Make it executable
chmod +x /opt/quantum/start-dev-wallet.sh
```

## Step 6: Open Firewall Port

```bash
# If using ufw
ufw allow 3030/tcp
ufw reload

# Or using iptables
iptables -A INPUT -p tcp --dport 3030 -j ACCEPT
```

## Step 7: Run the Dev Wallet

```bash
# Option 1: Run directly
cd /opt/quantum/quantumharmony/active-projects/quantum-harmony/quantum-node-fresh/quantum-substrate/quantum-qpp-wallet
RUST_LOG=info ./target/release/quantum_wallet_web --port 3030 --cors

# Option 2: Use the start script
/opt/quantum/start-dev-wallet.sh

# You should see output like:
# [INFO] Starting Quantum Wallet Web Server on port 3030
# [INFO] CORS enabled for development
```

## Step 8: Access the Wallet

Open your browser and go to:
```
http://your-droplet-ip:3030
```

You should see the QuantumHarmony wallet interface!

## Step 9: (Optional) Run in Background

To keep the wallet running after you disconnect:

```bash
# Using screen
apt install -y screen
screen -S quantum-wallet
/opt/quantum/start-dev-wallet.sh
# Press Ctrl+A then D to detach

# To reattach later:
screen -r quantum-wallet

# Or using nohup
nohup /opt/quantum/start-dev-wallet.sh > wallet.log 2>&1 &

# Check if it's running
ps aux | grep quantum_wallet_web
```

## Step 10: (Optional) Create Systemd Service

For automatic startup:

```bash
# Create service file
cat > /etc/systemd/system/quantum-wallet.service << 'EOF'
[Unit]
Description=QuantumHarmony Dev Wallet
After=network.target

[Service]
Type=simple
WorkingDirectory=/opt/quantum/quantumharmony/active-projects/quantum-harmony/quantum-node-fresh/quantum-substrate/quantum-qpp-wallet
ExecStart=/opt/quantum/quantumharmony/active-projects/quantum-harmony/quantum-node-fresh/quantum-substrate/quantum-qpp-wallet/target/release/quantum_wallet_web --port 3030 --cors
Restart=always
Environment="RUST_LOG=info"
Environment="WALLET_PASSWORD=dev"

[Install]
WantedBy=multi-user.target
EOF

# Enable and start
systemctl daemon-reload
systemctl enable quantum-wallet
systemctl start quantum-wallet

# Check status
systemctl status quantum-wallet
```

## Quick Test Commands

Once the wallet is running:

```bash
# Test if wallet is responding
curl http://localhost:3030/api/health

# Should return something like:
# {"status":"healthy","version":"0.1.0"}
```

## Troubleshooting

### Build Errors
```bash
# If cargo build fails, try:
cargo clean
cargo update
cargo build --release --features std
```

### Port Already in Use
```bash
# Check what's using port 3030
lsof -i :3030

# Kill the process if needed
kill -9 <PID>
```

### Can't Access from Browser
```bash
# Check if wallet is actually running
ps aux | grep quantum_wallet_web

# Test locally first
curl http://localhost:3030

# Check firewall
ufw status
```

## Summary

That's it! You now have the QuantumHarmony dev wallet running on your droplet. The key steps were:

1. ✅ Install Rust and dependencies
2. ✅ Clone the repository
3. ✅ Build the wallet
4. ✅ Open firewall port
5. ✅ Run the wallet
6. ✅ Access via browser

The wallet is now accessible at `http://your-droplet-ip:3030`