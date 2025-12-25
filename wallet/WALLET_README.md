# QuantumHarmony QPP Wallet

## Overview

This wallet combines the rich user-facing features of the nokia-demo wallet with the Quantum Preservation Pattern (QPP) enforcement and quantum tunnel security.

## Features

### From nokia-demo wallet:
- ✨ Setup wizard for new users
- 📊 Account management
- 💸 Transfers
- ⚛️ Quantum features
- 🔐 QKD hardware support
- 📦 Runtime upgrades
- 🌐 Network information
- ⚙️ Settings
- 🐳 Docker integration
- 🎨 LCARS-style UI (Star Trek inspired)

### From quantum-qpp-wallet:
- 🔒 **QPP (Quantum Preservation Pattern)**: Compile-time quantum safety
- 🌉 **Quantum Tunnels**: QKD-secured communication channels
- 🎯 **SPHINCS+ Integration**: Post-quantum cryptography
- 🚫 **No-Clone Enforcement**: Rust type system prevents quantum state cloning
- 📡 **QSSH-RPC**: Quantum-secure RPC on port 42 (when node supports it)

## Architecture

```
┌─────────────────────────────────────────────────────────────┐
│  Nokia Demo Wallet UI (215KB)                               │
│  - LCARS interface                                           │
│  - Setup wizard                                              │
│  - Account management                                        │
│  - Docker controls                                           │
└──────────────────────┬──────────────────────────────────────┘
                       │ HTTP/HTTPS
┌──────────────────────▼──────────────────────────────────────┐
│  quantum_wallet_web (5.8MB Rust binary)                     │
│  - Warp web server                                           │
│  - QPP enforcement                                           │
│  - API endpoints: /api/health, /api/accounts, /api/sign     │
└──────────────────────┬──────────────────────────────────────┘
                       │ Quantum Tunnel
┌──────────────────────▼──────────────────────────────────────┐
│  quantum_tunnel_server (5.2MB)                              │
│  - QKD key distribution                                      │
│  - Tunnel management                                         │
│  - Session key derivation                                    │
└──────────────────────┬──────────────────────────────────────┘
                       │ QSSH-RPC (port 42) or fallback WS (9944)
┌──────────────────────▼──────────────────────────────────────┐
│  QuantumHarmony SPHINCS+ Aura Node                          │
│  - Post-quantum consensus                                    │
│  - Quantum-safe cryptography                                 │
│  - KIRQ integration                                          │
└─────────────────────────────────────────────────────────────┘
```

## Binaries

The wallet consists of 3 compiled binaries:

1. **quantum_wallet_web** (5.8MB)
   - Main wallet web server
   - Serves UI on port 3030 (default)
   - Provides QPP-enforced API endpoints
   - Manages quantum tunnels

2. **quantum_tunnel_server** (5.2MB)
   - Handles quantum tunnel creation
   - QKD key distribution
   - Session management

3. **kirq_tunnel_client** (3.4MB)
   - KIRQ network tunnel client
   - Connects wallet to KIRQ nodes
   - QKD hardware integration

## Running the Wallet

### Option 1: Run wallet web server

```bash
cd /Users/sylvaincormier/QuantumVerseProtocols/quantumharmony

# Set wallet password (optional)
export WALLET_PASSWORD="your_secure_password"

# Run the web server (default port 3030)
./target/release/quantum_wallet_web

# Or specify custom port and tunnel server
./target/release/quantum_wallet_web \
  --port 8080 \
  --tunnel 127.0.0.1:9999 \
  --cors  # Enable CORS for development
```

Then open: http://localhost:3030

### Option 2: Run with TLS (TODO - requires warp-tls feature)

```bash
./target/release/quantum_wallet_web \
  --port 443 \
  --cert /path/to/cert.pem \
  --key /path/to/key.pem \
  --tunnel 127.0.0.1:9999
```

### Option 3: Run tunnel server separately

```bash
# Terminal 1: Start tunnel server
./target/release/quantum_tunnel_server --port 9999

# Terminal 2: Start wallet web server
./target/release/quantum_wallet_web --tunnel 127.0.0.1:9999
```

### Option 4: Connect to KIRQ network

```bash
# Terminal 1: Start KIRQ tunnel client
./target/release/kirq_tunnel_client \
  --kirq-node <kirq-node-address> \
  --local-port 9999

# Terminal 2: Start wallet
./target/release/quantum_wallet_web --tunnel 127.0.0.1:9999
```

## API Endpoints

The wallet server provides these endpoints:

### GET /api/health
Health check and status

**Response:**
```json
{
  "status": "healthy",
  "version": "0.1.0",
  "tunnel_active": true,
  "accounts_loaded": true
}
```

### GET /api/accounts
Get wallet accounts

**Response:**
```json
{
  "accounts": [
    {
      "address": "5GrwvaEF5zXb26Fz9rcQpDWS57CtERHpNehXCPcNoHGKutQY",
      "name": "Alice",
      "account_type": "quantum",
      "balance": "1000000"
    }
  ]
}
```

### POST /api/sign
Sign a transaction with quantum key

**Request:**
```json
{
  "tx_data": "hex_encoded_transaction",
  "account_index": 0,
  "use_quantum": true
}
```

**Response:**
```json
{
  "signature": "hex_encoded_signature",
  "tx_hash": "0x..."
}
```

### GET /api/tunnel/stats
Get quantum tunnel statistics

**Response:**
```json
{
  "active_tunnels": 1,
  "total_uptime": 3600,
  "average_idle": 0.5,
  "using_qkd": false
}
```

## Security Features

### QPP Enforcement

The wallet enforces quantum physics laws at compile time:

- **No-Clone Types**: Quantum keys wrapped in `NoClone<T>` cannot be cloned
- **Linear Types**: Keys must be consumed after use
- **State Machines**: Transaction builder uses type states to prevent invalid operations

```rust
// This will NOT compile:
let key = quantum_key.clone(); // ❌ Error: Clone not implemented

// This is the only way to use keys:
let signature = key.use_key()?; // ✅ Consumes the key
```

### Quantum Tunnels

Communications use quantum-secured tunnels:

1. **Handshake**: Ephemeral key exchange
2. **QKD**: Optional quantum key distribution
3. **Session Keys**: Derived from QKD or classical ECDH
4. **Authenticated Encryption**: ChaCha20-Poly1305

## Migration Path

### Current State
- Nokia wallet connects directly to port 9944 (INSECURE - bypasses quantum gateway)

### Target State
- Wallet → QSSH-RPC (port 42) → Node
- Full quantum security stack
- QPP enforcement at all layers

### Migration Steps

1. ✅ Build quantum-qpp-wallet binaries
2. ✅ Merge nokia UI with QPP backend
3. ⏳ Test connection with SPHINCS+ node
4. ⏳ Migrate from port 9944 to QSSH-RPC port 42
5. ⏳ Integrate quantum tunnels
6. ⏳ End-to-end security testing

## Development

### Build from source

```bash
cd /Users/sylvaincormier/QuantumVerseProtocols/quantumharmony
cargo build --release -p quantum-qpp-wallet
```

### Run tests

```bash
cargo test -p quantum-qpp-wallet
```

### Add TLS support

TODO: Add `warp-tls` feature to Cargo.toml

## Troubleshooting

### Port already in use

```bash
# Find process using port 3030
lsof -i :3030

# Kill it
kill -9 <PID>
```

### Tunnel connection failed

Check that the tunnel server is running:

```bash
./target/release/quantum_tunnel_server --port 9999
```

### CORS errors (development)

Run with `--cors` flag:

```bash
./target/release/quantum_wallet_web --cors
```

## Next Steps

1. Implement live account management from QPP wallet state
2. Implement live transaction signing with SPHINCS+ keys
3. Connect to QSSH-RPC port 42 instead of 9944
4. Add QKD hardware integration for kirq_tunnel_client
5. Implement TLS support with warp-tls
6. Add metrics and monitoring
7. Create Docker compose setup for full stack

## References

- [COMPLETE_QUANTUM_ARCHITECTURE.md](./COMPLETE_QUANTUM_ARCHITECTURE.md) - Full system design
- [QUANTUM_TUNNEL_THEORY.md](./QUANTUM_TUNNEL_THEORY.md) - Tunnel cryptography
- [QUANTUM_TUNNEL_KYC_ARCHITECTURE.md](./QUANTUM_TUNNEL_KYC_ARCHITECTURE.md) - KYC integration
- [QPP_THRESHOLD_PRESERVATION.md](./QPP_THRESHOLD_PRESERVATION.md) - Threshold signatures
