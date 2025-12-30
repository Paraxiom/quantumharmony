# QuantumHarmony Node Operator Interface - Test Plan

## Overview

This document describes the comprehensive test suite for the Node Operator Interface (wallet). The interface is a Tauri desktop application that manages QuantumHarmony blockchain nodes.

## Test Categories

### 1. Unit Tests (`src-tauri/tests/`)

#### Node Management (`node_management.rs`)
| Test | Description | Status |
|------|-------------|--------|
| `test_node_state_initialization` | Verify initial state is correct | ✅ |
| `test_output_buffer_add_lines` | Buffer accepts new lines | ✅ |
| `test_output_buffer_last_n_lines` | Retrieve last N lines works | ✅ |
| `test_output_buffer_truncation` | Buffer truncates at 1000 lines | ✅ |
| `test_clear_output_buffer` | Buffer clears completely | ✅ |
| `test_node_not_running_initially` | Node starts in stopped state | ✅ |
| `test_node_running_state_toggle` | Start/stop state changes | ✅ |
| `test_prevent_double_start` | Cannot start twice | ✅ |
| `test_prevent_stop_when_not_running` | Cannot stop if not running | ✅ |
| `test_error_line_formatting` | Error prefix applied | ✅ |
| `test_concurrent_buffer_access` | Thread-safe buffer access | ✅ |

#### Runtime Upgrade (`runtime_upgrade.rs`)
| Test | Description | Status |
|------|-------------|--------|
| `test_wasm_file_magic_bytes` | WASM magic byte validation | ✅ |
| `test_wasm_file_minimum_size` | Size validation | ✅ |
| `test_wasm_path_validation` | Path extension check | ✅ |
| `test_compressed_wasm_detection` | Detect compressed WASM | ✅ |
| `test_valid_seed_formats` | Dev seed format check | ✅ |
| `test_mnemonic_seed_format` | Mnemonic validation | ✅ |
| `test_hex_seed_format` | Hex seed validation | ✅ |
| `test_runtime_version_fields` | Version struct fields | ✅ |
| `test_spec_version_increment` | Version increases | ✅ |
| `test_wasm_size_limits` | Size bounds checking | ✅ |
| `test_path_traversal_prevention` | Security check | ✅ |

### 2. RPC Integration Tests (`src-tauri/tests/rpc_integration.rs`)

Require a running node at `localhost:9944`.

#### System RPC
| Test | RPC Method | Description |
|------|------------|-------------|
| `test_system_health` | `system_health` | Node health status |
| `test_system_chain` | `system_chain` | Chain name retrieval |
| `test_system_name` | `system_name` | Node name retrieval |
| `test_system_version` | `system_version` | Version string |
| `test_system_peers` | `system_peers` | Connected peer list |

#### Chain RPC
| Test | RPC Method | Description |
|------|------------|-------------|
| `test_chain_get_header` | `chain_getHeader` | Latest block header |
| `test_chain_get_block_hash` | `chain_getBlockHash` | Block hash lookup |
| `test_chain_get_finalized_head` | `chain_getFinalizedHead` | Finalized block |

#### State RPC
| Test | RPC Method | Description |
|------|------------|-------------|
| `test_state_get_runtime_version` | `state_getRuntimeVersion` | Runtime version info |
| `test_state_get_metadata` | `state_getMetadata` | Chain metadata |

#### Gateway RPC (QuantumHarmony Custom)
| Test | RPC Method | Description |
|------|------------|-------------|
| `test_gateway_genesis_hash` | `gateway_genesisHash` | Genesis hash |
| `test_gateway_balance` | `gateway_balance` | Account balance |
| `test_gateway_nonce` | `gateway_nonce` | Account nonce |

#### QRNG RPC (Threshold QRNG)
| Test | RPC Method | Description |
|------|------------|-------------|
| `test_qrng_get_config` | `qrng_getConfig` | QRNG configuration |
| `test_qrng_get_device_queues` | `qrng_getDeviceQueues` | Device queue status |
| `test_qrng_get_reconstruction_history` | `qrng_getReconstructionHistory` | History |

#### Error Handling
| Test | Description |
|------|-------------|
| `test_invalid_method` | Unknown method returns error |
| `test_invalid_params` | Bad params returns error |
| `test_connection_refused` | Handles unreachable node |

### 3. End-to-End Scenarios (`tests/e2e_scenarios.rs`)

| Scenario | Description | Requirement |
|----------|-------------|-------------|
| Fresh Node Startup | Complete startup flow | Node binary |
| Runtime Version Check | Verify version info | Running node |
| Network Connectivity | Peer connections | Running node |
| Balance Check | Account balance lookup | Running node |
| QRNG Device Status | QRNG subsystem check | QRNG enabled |
| Block Explorer | Block/extrinsic display | Running node |

---

## Running Tests

### Unit Tests (No Node Required)

```bash
cd wallet/src-tauri
cargo test
```

### Integration Tests (Node Required)

```bash
# Terminal 1: Start node
./target/release/quantumharmony-node --dev --tmp

# Terminal 2: Run integration tests
cd wallet/src-tauri
cargo test --features integration
```

### E2E Scenarios

```bash
# With node running
cd wallet
cargo test --test e2e_scenarios -- --nocapture
```

### All Tests

```bash
./wallet/run-tests.sh
```

---

## Test Coverage Requirements

### Critical Paths (Must Pass)
- [ ] Node start/stop functionality
- [ ] RPC connection establishment
- [ ] Runtime version retrieval
- [ ] Block number updates
- [ ] Error message display

### Important Paths (Should Pass)
- [ ] Peer connection display
- [ ] Balance queries
- [ ] QRNG configuration display
- [ ] Output buffer management

### Nice to Have
- [ ] Device queue visualization
- [ ] Governance proposal display
- [ ] Staking interface

---

## Manual Testing Checklist

### Node Control Panel
- [ ] Click "Start Node" - node starts, terminal shows output
- [ ] Click "Stop Node" - node stops cleanly
- [ ] Click "Clear Terminal" - output clears
- [ ] Observe real-time log streaming

### Network Panel
- [ ] Click "Connect" - connection establishes
- [ ] Block number updates automatically
- [ ] Status dot turns green when connected
- [ ] Click "Disconnect" - connection closes

### Runtime Upgrade Panel
- [ ] Click "Get Runtime Version" - displays version info
- [ ] Click "Select WASM" - file dialog opens
- [ ] Select valid WASM file - path displays
- [ ] Click "Submit" - confirmation dialog appears
- [ ] Confirm upgrade - submission proceeds

### QRNG Panel
- [ ] Click "Refresh Config" - K, M values display
- [ ] Click "Refresh Queues" - device cards populate
- [ ] Click "Simulate Shares" - queue lengths increase
- [ ] Click "Collect & Reconstruct" - collection triggers

### Wallet Tab
- [ ] Balance displays correctly
- [ ] Transaction history shows
- [ ] Quick actions buttons respond

### Governance Tab
- [ ] Proposals display with details
- [ ] Vote buttons are clickable
- [ ] Progress bars show percentages

---

## Known Limitations

1. **File Dialog**: `select_wasm_file` returns error (tauri-plugin-dialog not configured)
2. **Mobile Platforms**: Update checks skip on Android/iOS
3. **QRNG Methods**: May return errors if pallet not enabled
4. **Gateway Methods**: Custom to QuantumHarmony, may not exist on vanilla nodes

---

## Test Environment

- **OS**: macOS, Linux, Windows (Tauri supported)
- **Rust**: 1.75+ (nightly for node build)
- **Node**: QuantumHarmony v0.30.0+
- **RPC Port**: 9944 (default)
- **WebSocket**: ws://localhost:9944

---

## Adding New Tests

### Unit Test
```rust
#[test]
fn test_new_feature() {
    // Arrange
    let state = MockNodeState::new();

    // Act
    // ... perform action

    // Assert
    assert!(condition, "Expected condition");
}
```

### Integration Test
```rust
#[tokio::test]
async fn test_new_rpc_method() {
    if !is_node_available().await {
        println!("SKIP: Node not available");
        return;
    }

    let result = rpc_call("new_method", json!([])).await;
    assert!(result.is_ok());
}
```

### E2E Scenario
```rust
#[tokio::test]
async fn scenario_new_workflow() {
    println!("=== SCENARIO: New Workflow ===\n");

    // Step 1
    println!("Step 1: ...");
    // ...

    println!("=== SCENARIO COMPLETE ===");
}
```
