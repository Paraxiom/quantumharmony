# Running QuantumHarmony with Docker

## Quick Start - Join Testnet

```bash
# Clone the repository
git clone https://github.com/QuantumVerseProtocols/quantumharmony.git
cd quantumharmony

# Start a node connected to testnet
docker-compose -f docker-compose.testnet.yml up -d

# View logs
docker-compose -f docker-compose.testnet.yml logs -f

# Stop the node
docker-compose -f docker-compose.testnet.yml down
```

## Docker Images

### Using Pre-built Binary (Recommended)

```bash
# Build the node binary first (requires Rust)
cargo build --release -p quantumharmony-node

# Build Docker image
docker build -t quantumharmony:latest .

# Run
docker run -d --name my-node \
  -p 9944:9944 -p 30333:30333 \
  quantumharmony:latest \
  --chain=local \
  --name=MyNode \
  --rpc-external \
  --bootnodes=/ip4/YOUR_NODE_IP/tcp/30333/p2p/12D3KooWNpaTf134DUqez17tRCLPwdgBeQGAwh7hV94iPnd1u37d
```

### Building from Source (Multi-stage)

```bash
# This builds everything inside Docker (takes ~30 minutes)
docker build -f Dockerfile.multinode -t quantumharmony:latest ..
```

## Docker Compose Configurations

### docker-compose.testnet.yml
Connect to the live QuantumHarmony testnet:
```bash
docker-compose -f docker-compose.testnet.yml up -d
```

### docker-compose.yml
Run a local 3-validator network for development:
```bash
docker-compose up -d
```

### docker-compose.production.yml
Production deployment configuration.

## Configuration Options

### Environment Variables

| Variable | Description | Default |
|----------|-------------|---------|
| `RUST_LOG` | Logging level | `info` |

### Command Line Flags

| Flag | Description |
|------|-------------|
| `--chain=local` | Chain specification |
| `--name=NAME` | Node name |
| `--validator` | Run as validator |
| `--rpc-external` | Allow external RPC |
| `--bootnodes=URL` | Bootstrap nodes |

### Ports

| Port | Purpose |
|------|---------|
| 30333 | P2P networking |
| 9944 | RPC (HTTP + WebSocket) |
| 9615 | Prometheus metrics |

## Data Persistence

Chain data is stored in `/data` inside the container. Use Docker volumes:

```bash
docker run -v my-chain-data:/data quantumharmony:latest ...
```

## Health Check

```bash
curl http://localhost:9944/health
```

## Monitoring

Prometheus metrics available at `http://localhost:9615/metrics`

## Troubleshooting

### Node not syncing
- Check bootnode is reachable
- Ensure port 30333 is not blocked
- Verify chain spec matches network

### RPC connection refused
- Check `--rpc-external` flag is set
- Verify port 9944 is mapped correctly

### Container exits immediately
- Check logs: `docker logs container-name`
- Ensure binary is compatible with container OS
