# QuantumHarmony Dev Wallet Setup on Droplet

## Overview

This guide sets up the QuantumHarmony development wallet on your droplet, including:
- The quantum-safe QPP wallet
- Web interface accessible via browser
- Quantum tunnel connection to KIRQ network
- Dev account with pre-funded tokens

## Quick Setup Script

```bash
#!/bin/bash
# Save this as setup-dev-wallet.sh and run with sudo

set -e

echo "=== QuantumHarmony Dev Wallet Setup ==="
echo

# Check if running as root
if [ "$EUID" -ne 0 ]; then 
    echo "Please run as root (use sudo)"
    exit 1
fi

# Install dependencies
apt update
apt install -y build-essential pkg-config libssl-dev git curl

# Install Rust
if ! command -v cargo &> /dev/null; then
    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
    source $HOME/.cargo/env
fi

# Create directories
mkdir -p /opt/quantum-wallet
cd /opt/quantum-wallet

# Clone the repository
if [ ! -d "quantum-substrate" ]; then
    git clone https://github.com/QuantumVerseProtocols/quantumharmony.git .
    cd active-projects/quantum-harmony/quantum-node-fresh/quantum-substrate
fi

# Build the wallet
cd quantum-qpp-wallet
cargo build --release --features std

# Create the dev wallet configuration
mkdir -p /etc/quantum-wallet
cat > /etc/quantum-wallet/dev-wallet.json << 'EOF'
{
  "name": "QuantumHarmony Dev Wallet",
  "dev_mode": true,
  "accounts": [
    {
      "name": "Alice",
      "address": "5GrwvaEF5zXb26Fz9rcQpDWS57CtERHpNehXCPcNoHGKutQY",
      "type": "quantum",
      "balance": "1000000000000000000",
      "mnemonic": "//Alice"
    },
    {
      "name": "Bob", 
      "address": "5FHneW46xGXgs5mUiveU4sbTyGBzmstUspZC92UhjJM694ty",
      "type": "quantum",
      "balance": "1000000000000000000",
      "mnemonic": "//Bob"
    },
    {
      "name": "Dev Account",
      "address": "5GNJqTPyNqANBkUVMN1LPPrxXnFouWXoe2wNSmmEoLctxiZY",
      "type": "hybrid",
      "balance": "10000000000000000000",
      "mnemonic": "//Dev"
    }
  ],
  "network": {
    "endpoint": "ws://localhost:9944",
    "quantum_endpoint": "ws://localhost:9999"
  }
}
EOF

# Create systemd service
cat > /etc/systemd/system/quantum-dev-wallet.service << 'EOF'
[Unit]
Description=QuantumHarmony Dev Wallet
After=network.target

[Service]
Type=simple
User=root
WorkingDirectory=/opt/quantum-wallet/active-projects/quantum-harmony/quantum-node-fresh/quantum-substrate/quantum-qpp-wallet
Environment="RUST_LOG=info"
Environment="DEV_MODE=true"
Environment="WALLET_PASSWORD=dev"
ExecStart=/opt/quantum-wallet/active-projects/quantum-harmony/quantum-node-fresh/quantum-substrate/quantum-qpp-wallet/target/release/quantum_wallet_web --port 3030 --cors
Restart=always
RestartSec=10

[Install]
WantedBy=multi-user.target
EOF

# Start the service
systemctl daemon-reload
systemctl enable quantum-dev-wallet
systemctl start quantum-dev-wallet

echo
echo "=== Dev Wallet Setup Complete ==="
echo "Access the wallet at: http://$(curl -s ifconfig.me):3030"
echo "Default dev accounts are pre-loaded with tokens"
echo
```

## Manual Setup Steps

### 1. Install Dependencies

```bash
# Update system
sudo apt update && sudo apt upgrade -y

# Install required packages
sudo apt install -y \
    build-essential \
    pkg-config \
    libssl-dev \
    git \
    curl \
    nginx

# Install Rust
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
source $HOME/.cargo/env
```

### 2. Get the Wallet Code

```bash
# Create working directory
sudo mkdir -p /opt/quantum-wallet
cd /opt/quantum-wallet

# Clone repository
git clone https://github.com/QuantumVerseProtocols/quantumharmony.git .

# Navigate to wallet directory
cd active-projects/quantum-harmony/quantum-node-fresh/quantum-substrate/quantum-qpp-wallet
```

### 3. Build the Wallet

```bash
# Build with all features
cargo build --release --features std

# The binaries will be in:
# target/release/quantum_wallet_web
# target/release/quantum_tunnel_server
```

### 4. Configure Dev Accounts

Create `/opt/quantum-wallet/dev-accounts.json`:

```json
{
  "accounts": [
    {
      "name": "Alice (Dev)",
      "mnemonic": "//Alice",
      "address": "5GrwvaEF5zXb26Fz9rcQpDWS57CtERHpNehXCPcNoHGKutQY",
      "balance": "1000000 QH",
      "type": "quantum"
    },
    {
      "name": "Bob (Dev)",
      "mnemonic": "//Bob", 
      "address": "5FHneW46xGXgs5mUiveU4sbTyGBzmstUspZC92UhjJM694ty",
      "balance": "1000000 QH",
      "type": "quantum"
    },
    {
      "name": "Charlie (Dev)",
      "mnemonic": "//Charlie",
      "address": "5FLSigC9HGRKVhB9FiEo4Y3koPsNmBmLJbpXg2mp1hXcS59Y",
      "balance": "1000000 QH",
      "type": "hybrid"
    },
    {
      "name": "Dev Treasury",
      "mnemonic": "//Treasury",
      "address": "5EYCAe5ijiYfyeZ2JJCGq56LmPyNRAKzpG4QkoQkkQNB5e6Z",
      "balance": "10000000 QH",
      "type": "quantum"
    }
  ]
}
```

### 5. Create Launch Script

Create `/opt/quantum-wallet/start-dev-wallet.sh`:

```bash
#!/bin/bash
# Dev Wallet Launch Script

export RUST_LOG=info
export DEV_MODE=true
export WALLET_PASSWORD=dev

# Start with dev configuration
./target/release/quantum_wallet_web \
    --port 3030 \
    --cors \
    --dev-accounts /opt/quantum-wallet/dev-accounts.json \
    --tunnel localhost:9999
```

Make it executable:
```bash
chmod +x /opt/quantum-wallet/start-dev-wallet.sh
```

### 6. Configure Nginx (Optional)

For production-like setup with HTTPS:

```nginx
server {
    listen 80;
    server_name your-droplet-domain.com;

    location / {
        proxy_pass http://localhost:3030;
        proxy_http_version 1.1;
        proxy_set_header Upgrade $http_upgrade;
        proxy_set_header Connection 'upgrade';
        proxy_set_header Host $host;
        proxy_cache_bypass $http_upgrade;
    }
}
```

### 7. Set Up Firewall

```bash
# Allow wallet port
sudo ufw allow 3030/tcp

# If using nginx
sudo ufw allow 80/tcp
sudo ufw allow 443/tcp

# Enable firewall
sudo ufw enable
```

### 8. Create Development Helper Scripts

Create `/usr/local/bin/quantum-dev`:

```bash
#!/bin/bash
# Quantum Dev Wallet Helper

case "$1" in
    start)
        sudo systemctl start quantum-dev-wallet
        echo "Dev wallet started"
        ;;
    stop)
        sudo systemctl stop quantum-dev-wallet
        echo "Dev wallet stopped"
        ;;
    status)
        sudo systemctl status quantum-dev-wallet
        ;;
    logs)
        sudo journalctl -u quantum-dev-wallet -f
        ;;
    accounts)
        echo "=== Dev Accounts ==="
        echo "Alice:    5GrwvaEF5zXb26Fz9rcQpDWS57CtERHpNehXCPcNoHGKutQY"
        echo "Bob:      5FHneW46xGXgs5mUiveU4sbTyGBzmstUspZC92UhjJM694ty"
        echo "Charlie:  5FLSigC9HGRKVhB9FiEo4Y3koPsNmBmLJbpXg2mp1hXcS59Y"
        echo "Treasury: 5EYCAe5ijiYfyeZ2JJCGq56LmPyNRAKzpG4QkoQkkQNB5e6Z"
        ;;
    reset)
        echo "Resetting dev wallet state..."
        sudo systemctl stop quantum-dev-wallet
        rm -rf /var/lib/quantum-wallet/*
        sudo systemctl start quantum-dev-wallet
        echo "Dev wallet reset complete"
        ;;
    *)
        echo "Usage: quantum-dev {start|stop|status|logs|accounts|reset}"
        ;;
esac
```

Make it executable:
```bash
sudo chmod +x /usr/local/bin/quantum-dev
```

## Access the Dev Wallet

### 1. Direct Access
```
http://your-droplet-ip:3030
```

### 2. SSH Tunnel (Secure)
```bash
# On your local machine
ssh -L 3030:localhost:3030 user@your-droplet-ip

# Then access at
http://localhost:3030
```

### 3. With Domain (After nginx setup)
```
https://your-domain.com
```

## Dev Wallet Features

### Pre-loaded Accounts
- **Alice**: 1M QH tokens (Quantum account)
- **Bob**: 1M QH tokens (Quantum account)  
- **Charlie**: 1M QH tokens (Hybrid account)
- **Treasury**: 10M QH tokens (Quantum account)

### Development Tools
- Transaction builder
- Account viewer
- Balance checker
- Signature tester
- Quantum state inspector

### API Endpoints
- `GET /api/accounts` - List all dev accounts
- `POST /api/transfer` - Send tokens
- `POST /api/sign` - Sign messages
- `GET /api/balance/{address}` - Check balance
- `GET /api/health` - Health check

## Testing the Wallet

### 1. Check Health
```bash
curl http://localhost:3030/api/health
```

### 2. List Accounts
```bash
curl http://localhost:3030/api/accounts
```

### 3. Transfer Tokens
```bash
curl -X POST http://localhost:3030/api/transfer \
  -H "Content-Type: application/json" \
  -d '{
    "from": "//Alice",
    "to": "5FHneW46xGXgs5mUiveU4sbTyGBzmstUspZC92UhjJM694ty",
    "amount": "1000000000000"
  }'
```

## Connecting to Substrate Node

If you have a substrate node running:

```bash
# Update the wallet config
sudo nano /etc/quantum-wallet/dev-wallet.json

# Change endpoint to your node
"endpoint": "ws://your-node-ip:9944"

# Restart wallet
sudo systemctl restart quantum-dev-wallet
```

## Troubleshooting

### Wallet Won't Start
```bash
# Check logs
sudo journalctl -u quantum-dev-wallet -n 100

# Check if port is in use
sudo lsof -i :3030

# Manually test
cd /opt/quantum-wallet/active-projects/quantum-harmony/quantum-node-fresh/quantum-substrate/quantum-qpp-wallet
RUST_LOG=debug ./target/release/quantum_wallet_web
```

### Can't Access from Browser
```bash
# Check firewall
sudo ufw status

# Check if service is running
curl localhost:3030/api/health

# Check nginx (if used)
sudo nginx -t
sudo systemctl status nginx
```

### Reset Everything
```bash
# Stop service
sudo systemctl stop quantum-dev-wallet

# Clear data
sudo rm -rf /var/lib/quantum-wallet/*

# Rebuild
cd /opt/quantum-wallet/active-projects/quantum-harmony/quantum-node-fresh/quantum-substrate/quantum-qpp-wallet
cargo clean
cargo build --release

# Start again
sudo systemctl start quantum-dev-wallet
```

## Security Notes

⚠️ **For Development Only!**
- Dev accounts use well-known seeds
- CORS is enabled for all origins
- No authentication required
- Not suitable for production

For production deployment, use the full secure setup with:
- Proper key management
- HTTPS only
- Authentication
- Restricted CORS
- Quantum tunnel encryption