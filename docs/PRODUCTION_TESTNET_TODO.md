# Production Testnet Deployment Checklist

This document tracks the work needed to deploy a production-ready QuantumHarmony testnet with Docker images, proper key management, and reverse proxy infrastructure.

## Current State

| Component | Status | Location |
|-----------|--------|----------|
| Basic Dockerfile | Exists | `Dockerfile` |
| Docker Compose (local) | Exists | `docker-compose.yml`, `docker-compose.quantum.yml` |
| Key injection script | Exists | `insert-alice-key.sh` |
| Monitoring stack | Exists | `docker-compose.quantum.yml` (Prometheus/Grafana) |
| Network scripts | Exists | `scripts/start-network.sh`, `scripts/test-network.sh` |

---

## 1. Docker Infrastructure

- [x] **Multi-stage Dockerfile** - `Dockerfile.production`
  - Stage 1: Rust builder with all dependencies
  - Stage 2: Minimal runtime image (~100MB vs ~2GB)
  - Configurable via build args (features, profile)

- [x] **Production docker-compose** - `docker-compose.production.yml`
  - Docker secrets for key injection
  - 3-validator testnet with nginx, prometheus, grafana
  - Volume mounts for persistent chain data

- [x] **Container health checks** - Included in entrypoint and compose

---

## 2. Key Management (Critical)

- [x] **SPHINCS+ keygen CLI tool** - `node/src/sphincs_keygen.rs`
  - Generate new SPHINCS+-SHAKE-256s keypairs
  - Output: secret key (128 bytes), public key (64 bytes), SS58 address
  - `sphincs-key generate`, `sphincs-key inspect`, `sphincs-key validator-set`

- [x] **Key injection entrypoint script** - `docker/entrypoint.sh`
  - Read keys from Docker secrets or environment variables
  - Inject via `author_insertKey` RPC on startup
  - Support for both Aura (block production) and account keys

- [x] **Node key vs Session key separation**
  - Node key: libp2p identity (Ed25519, 32 bytes) - via NODE_KEY env
  - Session key: Block signing (SPHINCS+, 128 bytes) - via SPHINCS_SECRET_KEY env
  - Generate and manage separately

- [ ] **Key backup/rotation procedures**
  - Document secure key storage
  - Session key rotation via `author_rotateKeys`

---

## 3. Chain Specification

- [ ] **Production chain spec generator**
  - Script to generate testnet chain spec
  - Configure validator set from generated keys
  - Set proper genesis balances

- [ ] **Custom validator accounts**
  - Replace Alice/Bob/Charlie with named validators
  - Validator1, Validator2, Validator3, etc.

- [ ] **Bootnode configuration**
  - Embed bootnode peer IDs in chain spec
  - Support for multiple bootnodes

- [ ] **Testnet vs Mainnet differentiation**
  - Different chain IDs
  - Clear naming in spec

---

## 4. Reverse Proxy & Security

- [x] **Nginx configuration** - `docker/nginx.conf`
  - TLS termination (Let's Encrypt compatible)
  - WebSocket upgrade support for subscriptions
  - Rate limiting per IP
  - Request size limits (1MB for SPHINCS+ signatures)

- [x] **RPC method restrictions**
  - Public endpoints: `Safe` methods only (blocks author_* etc)
  - Admin endpoints: `Unsafe` methods via authenticated path

- [ ] **Firewall configuration**
  - P2P port (30333): Open to world
  - RPC port (9944): Only accessible via reverse proxy
  - Metrics port (9615): Internal only

- [x] **DDoS protection** - In nginx.conf
  - Connection limits (50/IP)
  - Request throttling (10 req/s RPC, 5 req/s WS)

---

## 5. Monitoring & Operations

- [x] **Prometheus scrape configuration** - `docker/prometheus.yml`
  - Node metrics (block height, peers, finality)
  - Scrapes all 3 validators on port 9615
  - 30-day retention

- [ ] **Grafana dashboards**
  - Network overview
  - Per-validator status
  - Transaction throughput

- [ ] **Alerting rules**
  - Block production stalled
  - Peer count drops below threshold
  - Finality lag
  - Disk space warnings

- [ ] **Log aggregation**
  - Structured logging
  - Central log collection (optional)

---

## 6. Deployment Scripts

- [ ] **One-click deployment script**
  - Generate keys
  - Build Docker images
  - Deploy to target servers
  - Verify network health

- [ ] **Upgrade procedures**
  - Runtime upgrade (forkless) - Already tested!
  - Node binary upgrade
  - Rollback procedures

---

## Implementation Priority

1. **SPHINCS+ keygen tool** - Foundation for real keys
2. **Multi-stage Dockerfile** - Reproducible builds
3. **Production chain spec generator** - Real validator accounts
4. **Reverse proxy config** - Secure public access
5. **Monitoring dashboards** - Operational visibility

---

---

## 7. Quantum-Safe Transport (QSSH/QSSL Integration)

The QuantumHarmony blockchain uses SPHINCS+ for signatures, but the transport layers
(SSH for admin, TLS for RPC, libp2p for P2P) use classical crypto. This section
tracks the integration of our quantum-safe transport protocols.

### Current Quantum Security Status

| Component | Protocol | Quantum-Safe? | Solution |
|-----------|----------|---------------|----------|
| Block signing | SPHINCS+ | Yes | Done |
| TX signatures | SPHINCS+ | Yes | Done |
| P2P networking | libp2p/Noise (Ed25519) | **No** | QSSL transport |
| Server admin | SSH (RSA/Ed25519) | **No** | QSSH |
| RPC/API | TLS (ECDHE) | **No** | QSSL proxy |

### Phase 1: QSSH for Server Management

- [x] **QSSH deployment script** - `scripts/deploy-qssh.sh`
  - Builds QSSH from source on validators
  - Generates Falcon-512 keypairs
  - Configures qsshd on port 42
  - Distributes public keys for mutual auth

- [ ] **Deploy QSSH to validators**
  - Run `./scripts/deploy-qssh.sh`
  - Test with `qssh ubuntu@your-server`
  - Disable classical SSH once verified

### Phase 2: QSSL for RPC/API

- [x] **QSSL proxy configuration** - `docker/qssl-proxy.conf`
  - SPHINCS+ KEM (patent-free, no Kyber)
  - Rate limiting and RPC filtering
  - WebSocket support for subscriptions

- [ ] **Build QSSL proxy Docker image**
  - Create Dockerfile for qssl-proxy
  - Add to docker-compose.production.yml

- [ ] **Deploy QSSL reverse proxy**
  - Replace nginx TLS with QSSL
  - Test with QSSL client

### Phase 3: QSSL for P2P Transport (Future)

This requires changes to Substrate's libp2p networking layer.

- [ ] **Research libp2p transport adapters**
  - Investigate custom transport in sc-network
  - Design QSSL transport wrapper

- [ ] **Implement QSSL transport for libp2p**
  - Create `QsslTransport` implementing `libp2p::Transport`
  - Handle SPHINCS+ handshake in connection upgrade

- [ ] **Coordinate network-wide upgrade**
  - All validators must upgrade simultaneously
  - Create migration plan

### Quantum Security Architecture

```
                    QUANTUM-SAFE BOUNDARY
                           |
  ┌────────────────────────|────────────────────────┐
  │                        v                        │
  │  ┌─────────────────────────────────────────┐   │
  │  │           QuantumHarmony Node           │   │
  │  │  ┌─────────────────────────────────┐    │   │
  │  │  │  Consensus: SPHINCS+ Aura       │ ✓  │   │
  │  │  │  Transactions: SPHINCS+ sigs    │ ✓  │   │
  │  │  │  Runtime: SPHINCS+ upgrades     │ ✓  │   │
  │  │  └─────────────────────────────────┘    │   │
  │  │                    │                     │   │
  │  │          ┌─────────┴─────────┐          │   │
  │  │          v                   v          │   │
  │  │    ┌──────────┐       ┌───────────┐     │   │
  │  │    │   RPC    │       │    P2P    │     │   │
  │  │    │ :9944    │       │  :30333   │     │   │
  │  │    └────┬─────┘       └─────┬─────┘     │   │
  │  └─────────|───────────────────|───────────┘   │
  │            │                   │               │
  │     ┌──────v──────┐     ┌──────v──────┐       │
  │     │ QSSL Proxy  │     │ QSSL P2P    │       │
  │     │ (Phase 2)   │ ✓   │ (Phase 3)   │ TODO  │
  │     └──────┬──────┘     └──────┬──────┘       │
  │            │                   │               │
  └────────────|───────────────────|───────────────┘
               │                   │
        ┌──────v──────┐     ┌──────v──────┐
        │   Clients   │     │    Peers    │
        │ (wallets)   │     │ (validators)│
        └─────────────┘     └─────────────┘

Admin Access:
  ┌─────────────┐     QSSH      ┌─────────────┐
  │  Operator   │ ────────────► │  Validator  │
  │  Workstation│   Port 42     │   Server    │
  │             │   Falcon-512  │             │
  └─────────────┘               └─────────────┘
```

### QSSH Usage (After Deployment)

```bash
# Connect to validator with quantum-safe SSH
qssh ubuntu@your-server

# Execute command
qssh ubuntu@your-server -c "tail -f /tmp/alice.log"

# Copy files
qscp chainspec.json ubuntu@your-server:/tmp/

# Port forward (quantum-safe tunnel)
qssh -L 9944:localhost:9944 ubuntu@your-server
```

### QSSL Client Usage (After Phase 2)

```bash
# Connect to RPC with quantum-safe TLS
curl --qssl https://rpc.quantumharmony.io/health

# Or use the QSSL client library in your wallet
use qssl::QsslConnection;
let conn = QsslConnection::connect("rpc.quantumharmony.io:443").await?;
```

---

## Related Files

### Docker Infrastructure
- `Dockerfile` - Current basic Dockerfile
- `Dockerfile.production` - Multi-stage production build
- `docker-compose.yml` - Local 3-validator network
- `docker-compose.quantum.yml` - Full stack with monitoring
- `docker-compose.production.yml` - Production testnet with secrets
- `docker/entrypoint.sh` - Docker entrypoint with key injection
- `docker/nginx.conf` - Nginx reverse proxy (classical TLS)
- `docker/qssl-proxy.conf` - QSSL reverse proxy (quantum-safe)
- `docker/prometheus.yml` - Prometheus scrape configuration

### Key Management
- `node/src/sphincs_keygen.rs` - SPHINCS+ keygen CLI
- `insert-alice-key.sh` - Key injection example

### Network Scripts
- `scripts/start-network.sh` - Manual network startup
- `scripts/test-network.sh` - Network health tests
- `scripts/deploy-qssh.sh` - QSSH deployment to validators

### QSSH/QSSL Integration
- QSSH repo: https://github.com/Paraxiom/qssh
- QSSL repo: https://github.com/Paraxiom/qssl
- `insert-alice-key.sh` - Key injection example
- `scripts/start-network.sh` - Manual network startup
- `scripts/test-network.sh` - Network health tests

---

## Notes

- Current testnet uses dev keys (Alice/Bob/Charlie) - NOT SECURE for production
- Runtime upgrades work (tested spec_version 10 -> 11)
- SPHINCS+-SHAKE-256s provides post-quantum security
- 3 validators minimum for Aura consensus
