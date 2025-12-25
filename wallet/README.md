# QuantumHarmony Wallet

**Desktop application for managing QuantumHarmony blockchain nodes**

## Quick Start

```bash
# 1. Build the node binary
cd /Users/sylvaincormier/QuantumVerseProtocols/quantumharmony
cargo build --release -p quantumharmony-node

# 2. Install Tauri CLI
cargo install tauri-cli

# 3. Run in development mode
cd wallet
cargo tauri dev

# 4. Or build for production
cargo tauri build
```

## Features

- 🚀 **Start/Stop Node** from GUI with real-time terminal output
- 🔄 **Runtime Updates** - Update both wallet app and node binary
- 📊 **Threshold QRNG** monitoring and management
- 🔐 **Reporter** registration and STARK proof submission
- 🎨 **Professional UI** - Clean dark theme, modern design

## Most Important Feature: Substrate Runtime Updates

This wallet enables **forkless blockchain upgrades** - update the runtime (blockchain logic) without restarting nodes:

- **Substrate Runtime Updates**: Upload new runtime WASM via GUI
- **Automatic Upgrade**: All nodes switch to new runtime after finalization
- **Zero Downtime**: No node restarts or coordination required
- **Governance**: Sudo in dev mode, democracy/council in production
- **Versioning**: Track runtime versions, spec changes

See **[RUNTIME_UPDATES.md](./RUNTIME_UPDATES.md)** for complete guide.

## Documentation

- **[TAURI_README.md](./TAURI_README.md)** - Complete usage guide, API reference, deployment
- **[IMPLEMENTATION_SUMMARY.md](./IMPLEMENTATION_SUMMARY.md)** - Implementation details, architecture

## Project Structure

```
wallet/
├── static/
│   ├── quantum-wallet-ui.html    # Web version
│   └── tauri-dashboard.html      # Desktop version
└── src-tauri/
    ├── src/main.rs                # Backend (process mgmt, updates)
    ├── Cargo.toml                 # Dependencies
    └── tauri.conf.json            # Configuration
```

## Requirements

- Rust 1.70+
- Node binary at `../target/release/quantumharmony-node`
- macOS: Xcode Command Line Tools
- Linux: webkit2gtk, gtk+3
- Windows: WebView2

## License

GPL-3.0-only
