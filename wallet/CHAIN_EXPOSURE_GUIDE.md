# Chain Exposure Guide: Wallet Access via Tunnel or Direct

## Current Situation
- Substrate node running on droplet at port 9933
- Currently exposed directly (anyone can connect)
- Need to decide: Tunnel-only or hybrid access?

## Option 1: Direct Access (Current - Quick Testing)

Keep it simple for now:

```bash
# Your chain is already accessible at:
ws://162.251.207.16:9933

# Or using your domain:
wss://your-domain.com:9933  # (needs SSL setup)
```

### Wallet Configuration for Direct Access:
```javascript
// In quantum-wallet-kirq-integrated.html
const QUANTUM_NODE = 'ws://162.251.207.16:9933';

// Or for production with SSL:
const QUANTUM_NODE = 'wss://api.quantumharmony.network:9944';
```

### Quick SSL Setup:
```bash
# Install certbot
sudo apt install certbot python3-certbot-nginx

# Get certificate
sudo certbot certonly --standalone -d api.quantumharmony.network

# Configure substrate to use SSL
./substrate-node-working \
  --rpc-cors all \
  --rpc-external \
  --rpc-port 9944 \
  --rpc-ssl-cert /etc/letsencrypt/live/api.quantumharmony.network/fullchain.pem \
  --rpc-ssl-key /etc/letsencrypt/live/api.quantumharmony.network/privkey.pem
```

## Option 2: Nginx Reverse Proxy (Better Security)

```bash
# Install nginx
sudo apt install nginx

# Create config
sudo nano /etc/nginx/sites-available/quantum-rpc
```

```nginx
map $http_upgrade $connection_upgrade {
    default upgrade;
    '' close;
}

server {
    listen 443 ssl http2;
    server_name api.quantumharmony.network;

    ssl_certificate /etc/letsencrypt/live/api.quantumharmony.network/fullchain.pem;
    ssl_certificate_key /etc/letsencrypt/live/api.quantumharmony.network/privkey.pem;

    # Rate limiting
    limit_req_zone $binary_remote_addr zone=rpc:10m rate=10r/s;
    limit_req zone=rpc burst=20;

    location / {
        # CORS headers
        add_header Access-Control-Allow-Origin "*";
        add_header Access-Control-Allow-Methods "POST, GET, OPTIONS";
        add_header Access-Control-Allow-Headers "Content-Type";

        # WebSocket support
        proxy_http_version 1.1;
        proxy_set_header Upgrade $http_upgrade;
        proxy_set_header Connection $connection_upgrade;
        proxy_set_header Host $host;

        # Proxy to substrate
        proxy_pass http://localhost:9933;
    }
}
```

```bash
# Enable and restart
sudo ln -s /etc/nginx/sites-available/quantum-rpc /etc/nginx/sites-enabled/
sudo nginx -t
sudo systemctl restart nginx

# Update substrate to local only
./substrate-node-working --dev --rpc-port 9933 # No --rpc-external
```

## Option 3: Quantum Tunnel (Full Security)

### Step 1: Start Tunnel Gateway
```bash
cd quantum-qpp-wallet
./target/release/quantum_tunnel_server \
  --listen 0.0.0.0:9999 \
  --allowed-ips "KIRQ_NETWORK_IPS"
```

### Step 2: Configure Wallet for Tunnel
```javascript
// In wallet
const tunnelConfig = {
    gateway: 'wss://tunnel.quantumharmony.network:9999',
    certificate: await loadCertificate(),
    blockchain: 'ws://localhost:9933' // Through tunnel
};
```

### Step 3: Close Direct Access
```bash
# Firewall rules
sudo ufw deny 9933
sudo ufw allow 9999

# Substrate local only
./substrate-node-working --dev --rpc-port 9933
```

## For KIRQ Integration

Based on the KIRQ instructions, you need:

1. **Quantum Key Registry Pallet**:
```bash
# Already in your substrate runtime
# Just needs to be configured
```

2. **Update Wallet Endpoints**:
```javascript
// In quantum-wallet-kirq-integrated.html
const config = {
    // Quantum entropy from KIRQ
    entropyAPI: 'https://api.paraxiom.org/api/quantum/entropy',
    
    // Your QuantumHarmony node
    nodeEndpoint: 'wss://api.quantumharmony.network:9944',
    
    // Node discovery (optional)
    nodeDiscovery: 'https://api.quantumharmony.network/nodes'
};
```

## Quick Test Setup (Recommended to Start)

```bash
# 1. Keep your current setup running
# Node is already at ws://162.251.207.16:9933

# 2. Update the wallet to connect
sed -i 's|wss://quantum.kirq.network|ws://162.251.207.16:9933|g' \
  quantum-wallet-kirq-integrated.html

# 3. Test connection
# Open http://162.251.207.16:8080/quantum-wallet-kirq-integrated.html
# Should connect to your node!
```

## Production Setup Later

1. **Set up SSL certificates**
2. **Configure nginx reverse proxy**
3. **Implement quantum tunnel gateway**
4. **Add authentication/rate limiting**

## The Key Decision

- **For Testing Now**: Use direct access (already working!)
- **For Production**: Implement tunnel or nginx proxy
- **For KIRQ Integration**: They need your WebSocket endpoint

Your chain is already exposed and ready. The wallet just needs the correct endpoint!