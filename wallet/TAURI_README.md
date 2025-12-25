# QuantumHarmony Tauri Desktop Application

A professional desktop application for managing QuantumHarmony nodes with **runtime update capabilities**.

## Features

### Core Functionality
- **Node Process Management**: Start, stop, and monitor your QuantumHarmony node directly from the GUI
- **Real-time Terminal Output**: See node logs streaming in real-time
- **Threshold QRNG Monitoring**: Track device queues, QBER metrics, and share collection
- **Reporter Management**: Register as a proof reporter and submit STARK proofs
- **Network Connection**: Monitor blockchain state, current block, and connection status

### **MOST IMPORTANT: Runtime Updates**
- **Application Auto-Update**: Automatically check for and install wallet application updates
- **Node Binary Update**: Update the blockchain node binary without reinstalling the wallet
- **Zero Downtime**: Download and prepare updates in the background
- **Rollback Support**: Automatic backup of previous node binary

## Architecture

```
wallet/
├── static/
│   ├── quantum-wallet-ui.html    # Web version (for browser access)
│   └── tauri-dashboard.html      # Tauri version (for desktop app)
└── src-tauri/
    ├── src/
    │   └── main.rs                # Rust backend with process management
    ├── Cargo.toml                 # Rust dependencies (tauri, tokio, reqwest)
    ├── tauri.conf.json            # Tauri configuration & updater settings
    └── build.rs                   # Build script
```

## Prerequisites

1. **Rust**: Install from [rustup.rs](https://rustup.rs/)
   ```bash
   curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
   ```

2. **System Dependencies** (macOS):
   ```bash
   xcode-select --install
   ```

3. **QuantumHarmony Node Binary**: Must be built first
   ```bash
   cd /Users/sylvaincormier/QuantumVerseProtocols/quantumharmony
   cargo build --release -p quantumharmony-node
   ```

## Installation

### 1. Install Tauri CLI

```bash
cargo install tauri-cli --version 2.1.0
```

### 2. Build the Desktop App

```bash
cd /Users/sylvaincormier/QuantumVerseProtocols/quantumharmony/wallet
cargo tauri build
```

This will create a distributable application in `src-tauri/target/release/bundle/`:
- **macOS**: `QuantumHarmony Wallet.app`
- **Linux**: `.deb`, `.appimage`
- **Windows**: `.msi`, `.exe`

### 3. Development Mode

For development with hot-reload:

```bash
cargo tauri dev
```

## Usage

### Starting the Application

**Production (Bundled App)**:
- **macOS**: Double-click `QuantumHarmony Wallet.app`
- **Linux**: Run the AppImage or install the .deb package
- **Windows**: Run the installer or execute the .exe

**Development**:
```bash
cd wallet
cargo tauri dev
```

### Node Management

1. **Start Node**: Click "Start Node" button
   - Node binary launched with `--dev --tmp` flags
   - Terminal output streams in real-time
   - Auto-connects to RPC after 3 seconds

2. **Stop Node**: Click "Stop Node" button
   - Gracefully terminates the node process
   - Disconnects RPC connection

3. **Monitor Output**: View live logs in the "Node Terminal" panel

### Runtime Updates

#### Application Updates (Automatic)

The wallet checks for updates on startup. When an update is available:

1. Update banner appears at the top
2. Click "Install Update" to download
3. Progress shown during download
4. Restart application to apply

**Manual Check**:
```javascript
// In browser console (dev mode):
await window.__TAURI__.core.invoke('check_for_updates')
```

#### Node Binary Updates (Manual)

To update just the node binary without reinstalling the wallet:

1. Click "Check for Node Update" button
2. Enter the download URL for the new binary (e.g., `https://releases.quantumharmony.io/quantumharmony-node-darwin-arm64-v1.1.0`)
3. Old binary automatically backed up to `.bak`
4. New binary downloaded and made executable
5. Restart node to use new version

**Backend Implementation** (main.rs:169-218):
```rust
#[tauri::command]
async fn update_node_binary(
    app: AppHandle,
    download_url: String,
) -> Result<String, String> {
    // Downloads new binary
    // Backs up old binary
    // Makes new binary executable
    // Returns success message
}
```

## Configuration

### Update Server

Edit `src-tauri/tauri.conf.json` to configure the update server:

```json
{
  "plugins": {
    "updater": {
      "active": true,
      "endpoints": [
        "https://releases.quantumharmony.io/{{target}}/{{arch}}/{{current_version}}"
      ],
      "dialog": true,
      "pubkey": "YOUR_PUBLIC_KEY_HERE"
    }
  }
}
```

### Generate Update Signing Keys

```bash
cd src-tauri
cargo tauri signer generate
```

This creates:
- Private key (keep secret!)
- Public key (put in `tauri.conf.json`)

### Bundled Resources

The node binary is automatically bundled with the app:

```json
{
  "bundle": {
    "resources": ["../target/release/quantumharmony-node"],
    "externalBin": ["quantumharmony-node"]
  }
}
```

## API Reference

### Tauri Commands

All commands exposed to frontend via `window.__TAURI__.core.invoke()`:

#### Node Management

```javascript
// Start the node
await invoke('start_node')
// Returns: "Node started successfully"

// Stop the node
await invoke('stop_node')
// Returns: "Node stopped successfully"

// Get node status
await invoke('get_node_status')
// Returns: true (running) | false (stopped)

// Get terminal output
await invoke('get_node_output', { lastN: 100 })
// Returns: { lines: string[] }

// Clear terminal buffer
await invoke('clear_node_output')
```

#### Runtime Updates

```javascript
// Check for application updates
await invoke('check_for_updates')
// Returns: { version: string, date: string, body: string } | null

// Install application update
await invoke('install_update')
// Returns: "Update installed successfully. Restart the application to apply."

// Update node binary
await invoke('update_node_binary', {
  downloadUrl: 'https://releases.quantumharmony.io/node-v1.1.0'
})
// Returns: "Node binary updated successfully to version from <url>"
```

### Events

Listen for events using `window.__TAURI__.event.listen()`:

```javascript
// Node output stream
listen('node-output', (event) => {
    console.log('Node:', event.payload); // string
});

// Update available notification
listen('update-available', (event) => {
    const update = event.payload; // { version, date, body }
    console.log('Update available:', update.version);
});

// Update progress
listen('update-progress', (event) => {
    const [downloaded, total] = event.payload;
    console.log(`Progress: ${downloaded}/${total} bytes`);
});

// Update complete
listen('update-complete', () => {
    console.log('Update download complete!');
});
```

## Deployment

### Creating a Release

1. **Build the node binary**:
   ```bash
   cd /Users/sylvaincormier/QuantumVerseProtocols/quantumharmony
   cargo build --release -p quantumharmony-node
   ```

2. **Build the Tauri app**:
   ```bash
   cd wallet
   cargo tauri build
   ```

3. **Sign the update** (for auto-updater):
   ```bash
   cargo tauri signer sign ./src-tauri/target/release/bundle/macos/QuantumHarmony\ Wallet.app
   ```

4. **Upload to release server**:
   - App bundle
   - Signature file (.sig)
   - Update manifest (JSON)

### Update Manifest Format

```json
{
  "version": "0.2.0",
  "pub_date": "2025-10-21T00:00:00Z",
  "url": "https://releases.quantumharmony.io/darwin/aarch64/QuantumHarmonyWallet-0.2.0.app.tar.gz",
  "signature": "dW50cnVzdGVkIGNvbW1lbnQ6...",
  "notes": "## What's New\n- Improved threshold QRNG monitoring\n- Bug fixes"
}
```

## Troubleshooting

### Node Won't Start

**Error**: `Node binary not found`

**Solution**:
```bash
# Ensure node is built
cd /Users/sylvaincormier/QuantumVerseProtocols/quantumharmony
cargo build --release -p quantumharmony-node

# Check path
ls -la target/release/quantumharmony-node
```

### Terminal Not Showing Output

**Issue**: No logs in terminal panel

**Solution**: Check that node started successfully. Look for errors in the Console Log panel.

### Update Check Fails

**Error**: `Update check failed`

**Cause**: Update server not configured or unreachable

**Solution**:
1. Check `tauri.conf.json` has correct endpoint
2. Ensure public key is set
3. In development, updates may be disabled

### Binary Update Fails

**Error**: `Failed to write new binary`

**Cause**: Permissions issue or node still running

**Solution**:
1. Stop the node first
2. Ensure write permissions on the binary
3. On Unix: Check file is executable (`chmod +x`)

## Development

### Project Structure

```
src-tauri/src/main.rs
├── NodeState            # Shared state (process, output buffer)
├── start_node()         # Spawn node process, capture stdout/stderr
├── stop_node()          # Kill node process
├── get_node_output()    # Retrieve buffered output
├── check_for_updates()  # Query update server
├── install_update()     # Download & install app update
└── update_node_binary() # Download & replace node binary
```

### Adding New Commands

1. **Define the command** in `main.rs`:
   ```rust
   #[tauri::command]
   async fn my_command(arg: String) -> Result<String, String> {
       // Implementation
       Ok("Success".to_string())
   }
   ```

2. **Register the handler**:
   ```rust
   .invoke_handler(tauri::generate_handler![
       start_node,
       my_command,  // Add here
   ])
   ```

3. **Call from frontend**:
   ```javascript
   await invoke('my_command', { arg: 'value' })
   ```

### Testing

```bash
# Run Rust tests
cd src-tauri
cargo test

# Run in dev mode
cd ..
cargo tauri dev
```

## Security

### Update Verification

All updates are cryptographically signed:
1. Release builds signed with private key
2. Client verifies with public key (in `tauri.conf.json`)
3. Rejects tampered updates

### Node Binary Updates

- Old binary backed up before replacement
- Downloads verified (size, integrity)
- Executable permissions set automatically
- Rollback possible by renaming `.bak` file

## Performance

- **Startup Time**: ~2 seconds (depends on node binary size)
- **Memory**: ~50MB (app) + node memory
- **Update Download**: Depends on bandwidth and binary size
- **Output Buffer**: Limited to 1000 lines (auto-pruned)

## License

GPL-3.0-only

## Support

- Issues: https://github.com/QuantumVerseProtocols/quantumharmony/issues
- Documentation: https://docs.quantumharmony.io
