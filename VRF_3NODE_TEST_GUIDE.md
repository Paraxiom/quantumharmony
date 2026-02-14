# VRF Determinism Fix - 3-Node Network Test Guide

## Overview

This guide provides step-by-step instructions for testing the VRF determinism fix on a local 3-node network as required by PR #11.

## Prerequisites

- Docker and Docker Compose installed
- VRF determinism fix applied (VrfProof extended to 128 bytes)
- All code changes committed

## Test Steps

### 1. Build and Start the Network

```bash
cd quantumharmony
docker-compose up --build
```

This will:

- Build the quantumharmony node with the VRF fix
- Start 3 validator nodes (Alice, Bob, Charlie)
- Initialize the network with the production chainspec

### 2. Monitor Block Production

Watch the logs to verify blocks are being produced:

```bash
# In a separate terminal
docker-compose logs -f
```

Expected output:

- Blocks being produced regularly
- All 3 nodes staying in sync
- No VRF verification errors
- Block numbers increasing consistently

### 3. Verify Node Synchronization

Check that all nodes are at the same block height:

```bash
# Check Alice's block height
curl -H "Content-Type: application/json" -d '{"id":1, "jsonrpc":"2.0", "method": "chain_getHeader"}' http://localhost:9933

# Check Bob's block height
curl -H "Content-Type: application/json" -d '{"id":1, "jsonrpc":"2.0", "method": "chain_getHeader"}' http://localhost:9934

# Check Charlie's block height
curl -H "Content-Type: application/json" -d '{"id":1, "jsonrpc":"2.0", "method": "chain_getHeader"}' http://localhost:9935
```

All three should return the same block number.

### 4. Wait for ~50 Blocks

Monitor the network until at least 50 blocks have been produced. This typically takes:

- With 6-second block time: ~5 minutes
- With 12-second block time: ~10 minutes

### 5. Verify VRF Determinism

Check the logs for VRF-related messages:

```bash
docker-compose logs | grep -i "vrf\|quantum"
```

Expected:

- ✅ No "VRF verification failed" errors
- ✅ No "QuantumEntropyUnavailable" errors during verification
- ✅ VRF proofs being generated and verified successfully

### 6. Check Finality

Verify that blocks are being finalized:

```bash
curl -H "Content-Type: application/json" -d '{"id":1, "jsonrpc":"2.0", "method": "chain_getFinalizedHead"}' http://localhost:9933
```

### 7. Collect Test Results

Document the following:

1. **Block Production**
   - Total blocks produced: \_\_\_
   - Time elapsed: \_\_\_
   - Average block time: \_\_\_

2. **Node Synchronization**
   - Alice final block: \_\_\_
   - Bob final block: \_\_\_
   - Charlie final block: \_\_\_
   - All in sync: ✅ / ❌

3. **VRF Verification**
   - VRF verification errors: \_\_\_
   - Entropy unavailable errors: \_\_\_
   - Successful verifications: \_\_\_

4. **Finality**
   - Finalized blocks: \_\_\_
   - Finality lag: \_\_\_

### 8. Stop the Network

```bash
docker-compose down
```

## Success Criteria

The test is successful if:

- ✅ All 3 nodes produce and sync at least 50 blocks
- ✅ No VRF verification failures occur
- ✅ All nodes remain at the same block height
- ✅ Blocks are being finalized
- ✅ No consensus errors in logs

## Troubleshooting

### Issue: Nodes not syncing

**Solution:**

1. Check network connectivity between containers
2. Verify bootnodes are configured correctly
3. Check firewall settings

### Issue: VRF verification failures

**Solution:**

1. Verify VrfProof is 128 bytes
2. Check that entropy is being stored in proof (bytes 96-127)
3. Verify `verify_quantum_vrf` extracts entropy from proof

### Issue: Out of memory during build

**Solution:**

1. Increase Docker memory limit
2. Build with `--release` flag
3. Close other applications
4. Use `cargo build --release -j 1` for single-threaded build

## Reporting Results

Post the following to PR #11:

```markdown
## 3-Node Network Test Results

**Test Duration:** [X minutes]
**Blocks Produced:** [X blocks]
**Nodes:** Alice, Bob, Charlie

### Results

- ✅ All nodes stayed in sync
- ✅ No VRF verification errors
- ✅ [X] blocks finalized
- ✅ Average block time: [X]s

### Logs

[Attach relevant log snippets showing successful VRF verification]

### Conclusion

The VRF determinism fix successfully allows all nodes to verify VRF proofs deterministically using the stored entropy in the proof.
```

## Additional Tests

### Test VRF Proof Size

```bash
# Inside a running container
docker exec -it quantumharmony_alice_1 /bin/bash
# Run a test to verify VrfProof size
cargo test -p pallet-quantum-crypto test_vrf_proof_structure -- --nocapture
```

### Test Entropy Tampering

```bash
# Verify that tampering with entropy doesn't affect verification
cargo test -p pallet-quantum-crypto test_vrf_tamper_entropy -- --nocapture
```

### Test Crypto Tampering

```bash
# Verify that tampering with crypto material fails verification
cargo test -p pallet-quantum-crypto test_vrf_tamper_crypto -- --nocapture
```

## References

- PR #11: https://github.com/Paraxiom/quantumharmony/pull/11
- VRF Determinism Fix Documentation: `VRF_DETERMINISM_FIX.md`
- Docker Multi-Node Testing: `docs/MD/DOCKER_MULTINODE_TESTING.md`
