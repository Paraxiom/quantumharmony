# Substrate Runtime Updates (Forkless Upgrades)

**The most important feature for blockchain governance and evolution**

## What are Substrate Runtime Updates?

Runtime updates are **forkless upgrades** that allow you to upgrade the blockchain's logic (runtime) **without requiring all nodes to manually update their software**. This is a unique capability of Substrate-based chains.

### Traditional Blockchain Upgrades (Hard Forks)
- Require coordinating all node operators
- Risk of chain splits if not everyone upgrades
- Downtime during migration
- Complex coordination

### Substrate Runtime Updates (Forkless)
- ✅ Upload new WASM runtime via transaction
- ✅ All nodes automatically switch after finalization
- ✅ Zero downtime
- ✅ No manual node updates required
- ✅ Governed by on-chain governance (sudo in dev mode)

## How It Works

1. **Build New Runtime**
   ```bash
   cd /Users/sylvaincormier/QuantumVerseProtocols/quantumharmony/runtime
   cargo build --release
   ```

2. **Locate Runtime WASM**
   ```
   ../target/release/wbuild/quantumharmony-runtime/quantumharmony_runtime.compact.compressed.wasm
   ```

3. **Submit via Wallet**
   - Open QuantumHarmony Wallet
   - Click "Get Runtime Version" to see current version
   - Click "Select Runtime WASM" → choose the `.compact.compressed.wasm` file
   - Click "Submit Runtime Upgrade"
   - Confirm the upgrade

4. **Automatic Switch**
   - Transaction included in next block
   - After finalization (~6-12 seconds), **all nodes automatically switch**
   - No node restart required

## Using the Wallet

### View Current Runtime

```javascript
// In the wallet dashboard:
1. Click "Get Runtime Version"
2. See current specName, specVersion, implVersion
```

Display shows:
- **Runtime Version**: e.g., "quantumharmony"
- **Spec Version**: e.g., "100"
- **Impl Version**: Implementation version number

### Submit Runtime Upgrade

**Prerequisites:**
- Node must be running
- Connected to RPC
- Runtime WASM file built and ready
- Sudo access (dev mode: //Alice)

**Steps:**

1. **Build Latest Runtime**
   ```bash
   cd quantumharmony/runtime
   # Make your changes to lib.rs, pallets, etc.
   cargo build --release
   ```

2. **Open Wallet Dashboard**
   ```bash
   cd quantumharmony/wallet
   cargo tauri dev
   ```

3. **Start Node**
   - Click "Start Node"
   - Wait for connection

4. **Check Current Version**
   - Click "Get Runtime Version"
   - Note the current spec_version

5. **Select New Runtime**
   - Click "Select Runtime WASM"
   - Navigate to: `../target/release/wbuild/quantumharmony-runtime/`
   - Select: `quantumharmony_runtime.compact.compressed.wasm`

6. **Submit Upgrade**
   - Click "Submit Runtime Upgrade"
   - Confirm the dialog
   - Wait for transaction to be included (~6 seconds)

7. **Verify Upgrade**
   - After ~10 seconds, click "Get Runtime Version" again
   - Spec version should have incremented
   - All nodes are now running the new runtime!

## Technical Details

### What Gets Updated

The runtime WASM contains:
- **Pallet logic**: All on-chain business logic
- **Storage layouts**: Database structures (with migrations)
- **Extrinsic definitions**: Transaction types
- **Runtime APIs**: RPC interface
- **Consensus rules**: Block validation

### What Doesn't Get Updated

The node binary (`quantumharmony-node`) is NOT updated:
- P2P networking
- Database backend
- RPC server
- Block authoring mechanics

**Note**: If the node binary needs updating (new Substrate version, networking changes), that requires a traditional node upgrade.

### Runtime Versioning

Edit `runtime/src/lib.rs`:

```rust
pub const VERSION: RuntimeVersion = RuntimeVersion {
    spec_name: create_runtime_str!("quantumharmony"),
    impl_name: create_runtime_str!("quantumharmony"),
    authoring_version: 1,
    spec_version: 101,  // INCREMENT THIS for runtime upgrades
    impl_version: 1,
    apis: RUNTIME_API_VERSIONS,
    transaction_version: 1,
    state_version: 1,
};
```

**Important**: Always increment `spec_version` when upgrading the runtime!

### Storage Migrations

If you change storage layouts, add a migration:

```rust
// runtime/src/lib.rs
pub mod migrations {
    use frame_support::weights::Weight;

    pub fn migrate_to_v2<T: Config>() -> Weight {
        // Migration logic here
        Weight::from_parts(10_000, 0)
    }
}

impl frame_system::Config for Runtime {
    // ...
    type OnSetCode = migrations::migrate_to_v2::<Runtime>;
}
```

## Tauri Commands

The wallet exposes these commands for runtime updates:

### Get Runtime Version

```javascript
const version = await invoke('get_runtime_version');
// Returns:
// {
//   specName: "quantumharmony",
//   implName: "quantumharmony-node",
//   authoringVersion: 1,
//   specVersion: 100,
//   implVersion: 1,
//   transactionVersion: 1
// }
```

### Select WASM File

```javascript
const path = await invoke('select_wasm_file');
// Opens native file picker, returns path to .wasm file
```

### Submit Runtime Upgrade

```javascript
const result = await invoke('submit_runtime_upgrade', {
    wasmPath: '/path/to/runtime.wasm',
    sudoSeed: '//Alice'  // Dev mode only
});
// Returns success message with WASM size
```

## Example Workflow: Add a New Pallet

Let's say you want to add a new pallet to the runtime:

### 1. Create the Pallet

```bash
cd quantumharmony/pallets
mkdir my-new-pallet
# Create pallet code...
```

### 2. Add to Runtime

Edit `runtime/Cargo.toml`:
```toml
[dependencies]
pallet-my-new = { path = "../pallets/my-new-pallet", default-features = false }
```

Edit `runtime/src/lib.rs`:
```rust
// Increment version
pub const VERSION: RuntimeVersion = RuntimeVersion {
    spec_version: 101,  // Was 100
    // ...
};

// Add pallet config
impl pallet_my_new::Config for Runtime {
    type RuntimeEvent = RuntimeEvent;
}

// Add to construct_runtime!
construct_runtime!(
    pub struct Runtime {
        // ...
        MyNewPallet: pallet_my_new,
    }
);
```

### 3. Build Runtime

```bash
cd runtime
cargo build --release
```

### 4. Submit via Wallet

1. Open wallet: `cd ../wallet && cargo tauri dev`
2. Start node
3. Get current version (should be 100)
4. Select WASM: `../target/release/wbuild/quantumharmony-runtime/quantumharmony_runtime.compact.compressed.wasm`
5. Submit runtime upgrade
6. Wait ~10 seconds
7. Get version again (should now be 101)

### 5. Verify

The new pallet is now live! You can:
- Call its extrinsics
- Query its storage
- Listen to its events

**All without restarting any nodes!**

## Production Considerations

### Governance

In production, runtime upgrades should be governed:

```rust
// Instead of sudo.setCode(), use democracy or council:
pallet_democracy::Pallet::<Runtime>::external_propose(
    Origin::signed(proposer),
    upgrade_proposal
);
```

### Testing

**ALWAYS test runtime upgrades on a testnet first!**

1. Deploy testnet
2. Submit upgrade
3. Verify all functionality
4. Check storage migrations
5. Monitor for issues
6. Then apply to mainnet

### Rollback

If an upgrade fails:

```rust
// Submit another upgrade with the previous runtime WASM
// (Keep old WASM files backed up!)
```

### Monitoring

After upgrade:
- Check node logs for errors
- Verify runtime version across all nodes
- Test all critical functionality
- Monitor block production

## Common Issues

### "Runtime upgrade failed: ..."

**Cause**: WASM file too large, spec_version not incremented, or storage migration failed

**Solution**:
- Check runtime WASM size (< 2MB ideal)
- Verify `spec_version` was incremented
- Test storage migrations on testnet first

### "Node stopped producing blocks"

**Cause**: Incompatible runtime change

**Solution**:
- Submit rollback with previous WASM
- Check consensus rule changes
- Verify runtime API compatibility

### "Transaction pool emptied"

**Cause**: Transaction version changed

**Solution**: Expected behavior - users may need to resubmit pending transactions

## Best Practices

1. **Always increment `spec_version`**
2. **Test migrations on testnet first**
3. **Keep old WASM files for rollback**
4. **Document breaking changes**
5. **Coordinate with frontend teams** (API changes)
6. **Monitor after upgrade** (at least 100 blocks)
7. **Use versioned storage** for complex migrations

## Security

### Sudo in Dev Mode

Development chains use `sudo` for runtime upgrades:
- **Sudoer**: `//Alice` (well-known dev seed)
- **Risk**: Anyone with Alice's key can upgrade
- **Use**: Development and testing ONLY

### Production Governance

Use proper governance:
- **Council voting**: Elected representatives
- **Democracy**: Token holder voting
- **Technical committee**: Emergency upgrades
- **Time delays**: Prevent sudden changes

## Resources

- Substrate Docs: https://docs.substrate.io/maintain/runtime-upgrades/
- Polkadot Wiki: https://wiki.polkadot.network/docs/learn-runtime-upgrades
- QuantumHarmony Runtime: `../runtime/src/lib.rs`

---

**Runtime updates are the killer feature of Substrate** - use them wisely!
