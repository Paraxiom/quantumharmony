# Docker Multi-Node Testing Guide

This guide explains how to test the vote gossip protocol with multiple validator nodes using Docker Compose.

**Date:** October 27, 2025
**Status:** Ready for testing
**Purpose:** Test vote propagation between validators in isolated container network

---

## Prerequisites

- Docker and Docker Compose installed
- QuantumHarmony repository cloned
- Release binary built (`cargo build --release`)

---

## Quick Start

### 1. Build Docker Image

```bash
# From the quantumharmony directory
docker-compose build
```

This will build the Docker image with the latest release binary including vote gossip protocol.

### 2. Start 3-Validator Network

```bash
docker-compose up
```

This starts three validator nodes:
- **Alice** (172.20.0.10) - RPC: localhost:9944
- **Bob** (172.20.0.11) - RPC: localhost:9945
- **Charlie** (172.20.0.12) - RPC: localhost:9946

### 3. Monitor Vote Gossip

```bash
# Watch all logs
docker-compose logs -f

# Watch specific node
docker-compose logs -f alice

# Filter for vote gossip events
docker-compose logs -f | grep -E "(📡|vote|peer|Vote|notification stream)"
```

### 4. Stop Network

```bash
docker-compose down

# Remove volumes (clean state)
docker-compose down -v
```

---

## What to Look For

### Successful Vote Gossip Indicators

✅ **Vote Receiver Started:**
```
📡 Vote receiver task starting...
```

✅ **Peer Discovery:**
```
discovered peer on address peer=12D3KooW... address=/ip4/172.20.0.11/...
```

✅ **Peer Connection:**
```
🤝 Peer 12D3KooW... opened notification stream
```

✅ **Vote Reception:**
```
📨 Received vote from peer 12D3KooW... for block #1
✅ Vote stored: 1 total votes for block 0x...
```

✅ **Vote Broadcasting:**
```
📡 Broadcasting vote to 2 connected peers
✅ Vote broadcasted to 2 validators
```

### Troubleshooting

⚠️ **No Peers Connected:**
```
💤 Idle (0 peers)
```
**Solution:** Check bootnode addresses and network connectivity

⚠️ **Chain Spec Mismatch:**
```
Error: Spec mismatch: ...
```
**Solution:** Ensure all nodes use the same chain spec

---

## Network Architecture

```
Docker Network: 172.20.0.0/16 (quantum-net)
├── Alice (172.20.0.10:30333)
│   └── Bootnode for Bob and Charlie
├── Bob (172.20.0.11:30333)
│   └── Connects to Alice
└── Charlie (172.20.0.12:30333)
    └── Connects to Alice
```

### Port Mapping

| Node | RPC Port | P2P Port | Prometheus |
|------|----------|----------|------------|
| Alice | 9944 | 30333 | 9615 |
| Bob | 9945 | 30334 | 9616 |
| Charlie | 9946 | 30335 | 9617 |

---

## Testing Scenarios

### Test 1: Basic Connectivity

**Objective:** Verify all nodes start and connect

```bash
# Start network
docker-compose up -d

# Check status
docker-compose ps

# Verify 3 nodes running
# Expected: alice, bob, charlie all "Up"
```

**Success Criteria:**
- All 3 containers running
- Vote receiver started on each node
- Peers discovered via mDNS or bootnodes

### Test 2: Vote Propagation

**Objective:** Verify votes are broadcast and received

```bash
# Start with logs
docker-compose up

# In another terminal, trigger block production
curl -H "Content-Type: application/json" \
     -d '{"id":1, "jsonrpc":"2.0", "method":"author_rotateKeys", "params":[]}' \
     http://localhost:9944
```

**Success Criteria:**
- Alice broadcasts vote
- Bob and Charlie receive vote
- Vote count increases on all nodes
- No errors in logs

### Test 3: Byzantine Fault Tolerance

**Objective:** Verify consensus with one node offline

```bash
# Start all nodes
docker-compose up -d

# Stop Charlie
docker-compose stop charlie

# Check if Alice and Bob continue (2/3 majority)
docker-compose logs -f alice bob
```

**Success Criteria:**
- Alice and Bob continue producing blocks
- Finality achieved with 2/3 votes
- Network remains operational

### Test 4: Network Partition Recovery

**Objective:** Test resilience to network issues

```bash
# Start network
docker-compose up -d

# Pause Bob (simulate network partition)
docker-compose pause bob

# Wait 30 seconds

# Resume Bob
docker-compose unpause bob

# Check logs for reconnection
docker-compose logs -f bob
```

**Success Criteria:**
- Bob reconnects to Alice and Charlie
- Vote receiver resumes
- Network synchronizes

---

## Advanced Testing

### Custom Chain Spec

To use a custom chain spec (recommended to avoid `--chain local` issues):

1. Generate chain spec:
```bash
./target/release/quantumharmony-node build-spec \
  --chain=local \
  --disable-default-bootnode \
  2>/dev/null > customspec.json
```

2. Convert to raw format:
```bash
./target/release/quantumharmony-node build-spec \
  --chain=customspec.json \
  --raw \
  --disable-default-bootnode \
  2>/dev/null > customspec-raw.json
```

3. Update docker-compose.yml to mount and use the custom spec:
```yaml
volumes:
  - ./customspec-raw.json:/chain-spec/customspec-raw.json:ro
command: >
  --chain=/chain-spec/customspec-raw.json
  ...
```

### Performance Monitoring

Monitor Prometheus metrics:

```bash
# Alice metrics
curl http://localhost:9615/metrics | grep coherence

# Bob metrics
curl http://localhost:9616/metrics | grep coherence

# Charlie metrics
curl http://localhost:9617/metrics | grep coherence
```

### Log Analysis

Extract vote gossip statistics:

```bash
# Count vote receptions
docker-compose logs | grep "📨 Received vote" | wc -l

# Count vote broadcasts
docker-compose logs | grep "📡 Broadcasting" | wc -l

# Count peer connections
docker-compose logs | grep "🤝 Peer.*opened" | wc -l

# Check for errors
docker-compose logs | grep -E "(ERROR|Error|error)" | tail -20
```

---

## Debugging

### Container Shell Access

```bash
# Access Alice container
docker exec -it quantumharmony-alice sh

# Check node process
ps aux | grep quantumharmony

# Check network connectivity
ping 172.20.0.11  # Bob
ping 172.20.0.12  # Charlie
```

### Network Inspection

```bash
# Inspect Docker network
docker network inspect quantumharmony_quantum-net

# Check container IPs
docker inspect quantumharmony-alice | grep IPAddress
docker inspect quantumharmony-bob | grep IPAddress
docker inspect quantumharmony-charlie | grep IPAddress
```

### Clean Restart

```bash
# Stop and remove everything
docker-compose down -v

# Remove dangling images
docker system prune

# Rebuild and restart
docker-compose build --no-cache
docker-compose up
```

---

## Expected Output

### Successful 3-Node Startup

```
alice      | 📡 Vote receiver task starting...
alice      | 🏷  Local node identity is: 12D3KooWEyopp...
bob        | 📡 Vote receiver task starting...
bob        | 🔍 Discovered new external address: /ip4/172.20.0.11/...
bob        | discovered peer: 12D3KooWEyopp...
charlie    | 📡 Vote receiver task starting...
charlie    | discovered peer: 12D3KooWEyopp...
alice      | 🤝 Peer 12D3KooWaU8c... opened notification stream
alice      | 🤝 Peer 12D3KooWbVx9... opened notification stream
alice      | ✨ Imported #1 (0x1234...)
alice      | 📡 Broadcasting vote to 2 connected peers
bob        | 📨 Received vote from peer 12D3KooWEyopp... for block #1
charlie    | 📨 Received vote from peer 12D3KooWEyopp... for block #1
```

---

## Next Steps

After successful Docker testing:

1. **Cloud Deployment:** Deploy to AWS/GCP/Azure for production testing
2. **Kubernetes:** Convert to K8s deployment for scalability testing
3. **Testnet:** Deploy public testnet with 10+ validators
4. **Monitoring:** Set up Grafana dashboards for Prometheus metrics
5. **Signature Verification:** Implement Falcon1024 signature checks

---

## Troubleshooting Common Issues

### Issue: Containers Exit Immediately

**Symptom:**
```
alice exited with code 1
```

**Solution:**
Check logs for the error:
```bash
docker-compose logs alice
```

Common causes:
- Chain spec mismatch
- Missing binary in Docker image
- Port already in use

### Issue: Peers Not Connecting

**Symptom:**
```
💤 Idle (0 peers)
```

**Solution:**
1. Verify bootnode peer ID matches Alice's identity
2. Check network connectivity between containers
3. Ensure firewall rules allow container communication

### Issue: Vote Receiver Not Starting

**Symptom:**
No "📡 Vote receiver task starting..." message

**Solution:**
1. Check RUST_LOG includes `coherence=debug`
2. Verify notification service initialization
3. Check for panics during startup

---

## Performance Expectations

### Latency

| Metric | Expected Value |
|--------|---------------|
| Vote broadcast | < 10ms |
| Vote reception | < 5ms |
| Peer discovery | < 2s |
| Block finality | 1-2 blocks |

### Throughput

| Network Size | Votes/Second | Bandwidth |
|--------------|--------------|-----------|
| 3 validators | ~30 | ~33 KB/s |
| 10 validators | ~100 | ~110 KB/s |
| 100 validators | ~1000 | ~1.1 MB/s |

---

## Conclusion

Docker Compose provides an isolated, reproducible environment for testing vote gossip protocol. This setup allows verification of:

- ✅ Vote receiver functionality
- ✅ Peer discovery and connection
- ✅ Vote propagation between containers
- ✅ Byzantine fault tolerance (2/3 majority)
- ✅ Network partition recovery

For production deployment, use this as a foundation and expand with Kubernetes for scalability.

---

**Status:** Ready for testing
**Last Updated:** October 27, 2025
**Author:** QuantumHarmony Development Team
