#!/bin/bash
# Quantum Wallet Deployment Script for Ubuntu/Debian Droplet

set -e

echo "=== QuantumHarmony QPP Wallet Deployment ==="
echo "This script will install and configure the quantum wallet on your droplet"
echo

# Check if running as root
if [ "$EUID" -ne 0 ]; then 
    echo "Please run as root (use sudo)"
    exit 1
fi

# Update system
echo "Updating system packages..."
apt update && apt upgrade -y

# Install dependencies
echo "Installing dependencies..."
apt install -y \
    build-essential \
    pkg-config \
    libssl-dev \
    git \
    curl \
    ufw \
    nginx \
    certbot \
    python3-certbot-nginx \
    prometheus \
    grafana

# Install Rust if not already installed
if ! command -v cargo &> /dev/null; then
    echo "Installing Rust..."
    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
    source $HOME/.cargo/env
fi

# Create quantum user
if ! id -u quantum &>/dev/null; then
    echo "Creating quantum user..."
    useradd -m -s /bin/bash quantum
    usermod -aG sudo quantum
fi

# Clone repository
echo "Cloning QuantumHarmony repository..."
cd /opt
if [ ! -d "quantumharmony" ]; then
    git clone https://github.com/QuantumVerseProtocols/quantumharmony.git
    chown -R quantum:quantum quantumharmony
fi

# Build the wallet
echo "Building quantum wallet..."
cd /opt/quantumharmony/active-projects/quantum-harmony/quantum-node-fresh/quantum-substrate/quantum-qpp-wallet
sudo -u quantum cargo build --release --features std

# Create directories
echo "Creating directories..."
mkdir -p /etc/quantum-wallet
mkdir -p /var/log/quantum-wallet
mkdir -p /var/lib/quantum-wallet
chown -R quantum:quantum /etc/quantum-wallet /var/log/quantum-wallet /var/lib/quantum-wallet

# Create configuration file
echo "Creating configuration..."
cat > /etc/quantum-wallet/config.toml << EOF
# Quantum Wallet Configuration

[server]
# Web server port
port = 3030
# Enable CORS for development
cors = false

[tunnel]
# Tunnel server listen address
listen = "0.0.0.0:9999"
# Key rotation interval (blocks)
rotation_interval = 1000
# Enable post-quantum algorithms
post_quantum = true
# Enable QKD (if hardware available)
use_qkd = false

[security]
# Allowed KIRQ network IPs (comma separated)
# Leave empty to allow all
allowed_ips = ""

[logging]
# Log level: trace, debug, info, warn, error
level = "info"
# Log file
file = "/var/log/quantum-wallet/quantum-wallet.log"
EOF

# Configure firewall
echo "Configuring firewall..."
ufw --force reset
ufw default deny incoming
ufw default allow outgoing
ufw allow 22/tcp    # SSH
ufw allow 80/tcp    # HTTP
ufw allow 443/tcp   # HTTPS
ufw allow 9999/tcp  # Quantum tunnel
ufw allow 9090/tcp  # Metrics (localhost only)
ufw --force enable

# Restrict metrics to localhost
iptables -A INPUT -p tcp --dport 9090 ! -s 127.0.0.1 -j DROP
iptables-save > /etc/iptables/rules.v4

# Create systemd services
echo "Creating systemd services..."

# Tunnel server service
cat > /etc/systemd/system/quantum-tunnel.service << EOF
[Unit]
Description=Quantum Tunnel Server
After=network.target

[Service]
Type=simple
User=quantum
WorkingDirectory=/opt/quantumharmony/active-projects/quantum-harmony/quantum-node-fresh/quantum-substrate/quantum-qpp-wallet
ExecStart=/opt/quantumharmony/active-projects/quantum-harmony/quantum-node-fresh/quantum-substrate/quantum-qpp-wallet/target/release/quantum_tunnel_server
Restart=always
RestartSec=10
Environment="RUST_LOG=info"
StandardOutput=append:/var/log/quantum-wallet/tunnel.log
StandardError=append:/var/log/quantum-wallet/tunnel.log

[Install]
WantedBy=multi-user.target
EOF

# Web server service
cat > /etc/systemd/system/quantum-wallet.service << EOF
[Unit]
Description=Quantum Wallet Web Server
After=network.target quantum-tunnel.service
Requires=quantum-tunnel.service

[Service]
Type=simple
User=quantum
WorkingDirectory=/opt/quantumharmony/active-projects/quantum-harmony/quantum-node-fresh/quantum-substrate/quantum-qpp-wallet
ExecStart=/opt/quantumharmony/active-projects/quantum-harmony/quantum-node-fresh/quantum-substrate/quantum-qpp-wallet/target/release/quantum_wallet_web
Restart=always
RestartSec=10
Environment="RUST_LOG=info"
Environment="WALLET_PASSWORD=changeme"
StandardOutput=append:/var/log/quantum-wallet/web.log
StandardError=append:/var/log/quantum-wallet/web.log

[Install]
WantedBy=multi-user.target
EOF

# Configure nginx reverse proxy
echo "Configuring nginx..."
cat > /etc/nginx/sites-available/quantum-wallet << 'EOF'
server {
    listen 80;
    server_name _;
    
    location / {
        proxy_pass http://localhost:3030;
        proxy_http_version 1.1;
        proxy_set_header Upgrade $http_upgrade;
        proxy_set_header Connection 'upgrade';
        proxy_set_header Host $host;
        proxy_cache_bypass $http_upgrade;
        proxy_set_header X-Real-IP $remote_addr;
        proxy_set_header X-Forwarded-For $proxy_add_x_forwarded_for;
        proxy_set_header X-Forwarded-Proto $scheme;
    }
}
EOF

ln -sf /etc/nginx/sites-available/quantum-wallet /etc/nginx/sites-enabled/
rm -f /etc/nginx/sites-enabled/default
nginx -t && systemctl restart nginx

# Configure Prometheus
echo "Configuring Prometheus..."
cat >> /etc/prometheus/prometheus.yml << EOF

  - job_name: 'quantum-tunnel'
    static_configs:
    - targets: ['localhost:9090']
EOF

systemctl restart prometheus

# Enable and start services
echo "Starting services..."
systemctl daemon-reload
systemctl enable quantum-tunnel quantum-wallet
systemctl start quantum-tunnel
sleep 5
systemctl start quantum-wallet

# Create helper scripts
echo "Creating helper scripts..."

# Status check script
cat > /usr/local/bin/quantum-status << 'EOF'
#!/bin/bash
echo "=== Quantum Wallet Status ==="
echo
echo "Services:"
systemctl status quantum-tunnel --no-pager | grep Active
systemctl status quantum-wallet --no-pager | grep Active
echo
echo "Tunnel connections:"
ss -tnp | grep :9999
echo
echo "Recent logs:"
tail -n 20 /var/log/quantum-wallet/tunnel.log
EOF
chmod +x /usr/local/bin/quantum-status

# Log viewer script
cat > /usr/local/bin/quantum-logs << 'EOF'
#!/bin/bash
case "$1" in
    tunnel)
        tail -f /var/log/quantum-wallet/tunnel.log
        ;;
    web)
        tail -f /var/log/quantum-wallet/web.log
        ;;
    *)
        echo "Usage: quantum-logs [tunnel|web]"
        ;;
esac
EOF
chmod +x /usr/local/bin/quantum-logs

# Print summary
echo
echo "=== Installation Complete ==="
echo
echo "Quantum Wallet is now running!"
echo "Web UI: http://$(curl -s ifconfig.me)"
echo "Tunnel port: 9999"
echo
echo "Next steps:"
echo "1. Set up SSL certificate:"
echo "   sudo certbot --nginx -d yourdomain.com"
echo
echo "2. Update wallet password:"
echo "   sudo nano /etc/systemd/system/quantum-wallet.service"
echo "   Change WALLET_PASSWORD=changeme"
echo "   sudo systemctl daemon-reload"
echo "   sudo systemctl restart quantum-wallet"
echo
echo "3. Configure allowed KIRQ IPs:"
echo "   sudo nano /etc/quantum-wallet/config.toml"
echo "   Add your KIRQ network IPs"
echo
echo "Helper commands:"
echo "  quantum-status     - Check service status"
echo "  quantum-logs       - View logs"
echo
echo "Monitoring:"
echo "  Prometheus: http://localhost:9090"
echo "  Grafana: http://localhost:3000"
echo