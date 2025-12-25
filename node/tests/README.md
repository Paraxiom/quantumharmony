# QuantumHarmony Wallet Integration Tests

Comprehensive test suite for wallet operations, transaction gateway RPC, and runtime upgrades.

## Test Suites

###  1. Wallet Integration Tests (`wallet_integration_tests.rs`)

Tests all wallet-related functionality:

- **Balance Queries**: Test `gateway_balance` RPC method
- **Nonce Queries**: Test `gateway_nonce` RPC method
- **Genesis Hash**: Test `gateway_genesisHash` RPC method
- **Transaction Submission**: Test `gateway_submit` RPC method
- **End-to-End Transfers**: Complete transfer flow with balance verification
- **Account Creation**: New account handling
- **Nonce Increments**: Sequential transaction handling
- **Invalid Address Handling**: Error cases
- **System Health**: Node health checks
- **Chain Properties**: Chain metadata

### 2. Runtime Upgrade Tests (`runtime_upgrade_tests.rs`)

Tests runtime upgrade capabilities:

- **Runtime Version Query**: Test version information
- **Runtime Metadata**: Test metadata queries
- **Sudo Key**: Test sudo functionality (if available)
- **Pallet Constants**: Test pallet metadata
- **Block Production**: Verify continuous block production
- **Storage Queries**: Before/after transaction storage
- **Finalized Head**: Test finality progression
- **Extrinsic Format**: Test transaction formatting
- **Concurrent RPC**: Test parallel RPC calls
- **Chain Identity**: Test chain name and type

## Running Tests

### Prerequisites

1. Build the node:
```bash
cd /Users/sylvaincormier/QuantumVerseProtocols/quantumharmony/active-projects/quantum-harmony/quantum-node-fresh/quantum-substrate
cargo build --release -p quantumharmony
```

2. Start the node in development mode:
```bash
./target/release/quantumharmony --dev --tmp
```

The node must be running on `http://127.0.0.1:9944` (default RPC port).

### Run All Tests

```bash
cargo test --release --test wallet_integration_tests
cargo test --release --test runtime_upgrade_tests
```

### Run Specific Tests

```bash
# Run only balance tests
cargo test --release --test wallet_integration_tests test_transaction_gateway_balance

# Run only runtime version test
cargo test --release --test runtime_upgrade_tests test_runtime_version_query

# Run with output
cargo test --release --test wallet_integration_tests -- --nocapture
```

### Run Tests in Parallel

```bash
cargo test --release --tests -- --test-threads=1
```

Note: Use `--test-threads=1` to avoid conflicts when tests modify blockchain state.

## Test Script

Use the provided test script for automated testing:

```bash
./run_tests.sh
```

This will:
1. Check if node is running
2. Start node if needed
3. Run all test suites
4. Generate test report

## Continuous Integration

For CI/CD integration:

```bash
# Start node in background
./target/release/quantumharmony --dev --tmp > /tmp/node.log 2>&1 &
NODE_PID=$!

# Wait for node to be ready
sleep 5

# Run tests
cargo test --release --tests -- --test-threads=1

# Cleanup
kill $NODE_PID
```

## Test Coverage

The test suite covers:

✅ Transaction Gateway RPC (all 4 methods)
✅ Balance transfers
✅ Account management
✅ Nonce handling
✅ Runtime metadata
✅ Block production
✅ Storage queries
✅ Error handling
✅ Concurrent operations
✅ Chain identity

## Troubleshooting

### Node Not Running

If tests fail with connection errors:

```bash
# Check if node is running
lsof -ti:9944

# Start node manually
./target/release/quantumharmony --dev --tmp
```

### Test Timeouts

If tests timeout:

- Increase timeout in test code
- Check node is producing blocks
- Verify RPC port is accessible

### Balance/Nonce Mismatches

If balance or nonce tests fail:

- Start with fresh chain: `--tmp` flag
- Run tests sequentially: `--test-threads=1`
- Clear old state: `rm -rf /tmp/substrate*`

## Adding New Tests

To add new tests:

1. Add test function to appropriate file
2. Mark with `#[tokio::test]`
3. Use `wait_for_node()` helper
4. Follow existing test patterns
5. Document test purpose

Example:

```rust
#[tokio::test]
async fn test_my_new_feature() {
    let client = wait_for_node().await;

    // Your test code here
    let result: Value = client
        .request("my_rpc_method", rpc_params![])
        .await
        .expect("Should succeed");

    assert!(result.is_object());
}
```

## Test Data

Tests use Substrate's development accounts:

- **Alice**: Well-funded account for testing
- **Bob**: Receiver account for transfers
- **Charlie/Dave/Eve**: Additional test accounts

All accounts have known mnemonics and keys for testing purposes.

**⚠️ WARNING**: Never use these accounts on mainnet or with real funds!

## Performance

Expected test execution times:

- Wallet Integration Tests: ~30-60 seconds
- Runtime Upgrade Tests: ~30-45 seconds
- Total: ~1-2 minutes

Tests run faster with:
- Release builds (`--release`)
- Faster block times in dev mode
- SSD storage
- Parallel test execution (when safe)

## CI/CD Integration

Example GitHub Actions workflow:

```yaml
name: Integration Tests

on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2
      - uses: actions-rs/toolchain@v1
        with:
          toolchain: stable
      - name: Build
        run: cargo build --release -p quantumharmony
      - name: Start Node
        run: ./target/release/quantumharmony --dev --tmp &
      - name: Wait for Node
        run: sleep 10
      - name: Run Tests
        run: cargo test --release --tests -- --test-threads=1
```

## Support

For issues or questions:

1. Check test logs: `cargo test -- --nocapture`
2. Check node logs: Look at node output
3. Verify node is running: `lsof -ti:9944`
4. Review test documentation above
