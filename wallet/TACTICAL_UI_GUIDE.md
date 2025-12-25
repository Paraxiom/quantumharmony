# QuantumHarmony Tactical Operations Interface

**Professional Safe Graphical Interface for Node Operators**

---

## Overview

The QuantumHarmony Tactical UI is a secure, professional desktop application and CLI suite for managing Substrate blockchain nodes, runtime upgrades, and quantum randomness generation.

### Design Philosophy

- **Tactical/Radar Aesthetic**: Green wireframe graphics inspired by operational interfaces
- **Security First**: Sandboxed Tauri desktop app with strict CSP policies
- **Developer Friendly**: Both GUI and CLI for different workflows
- **Real-time Monitoring**: Live status updates, block production, network topology

---

## Components

### 1. Tactical Dashboard (GUI)

**File**: `static/tactical-dashboard.html`

**Features**:
- **Radar Display**: Network topology visualization with scanning animation
- **Node Status Panel**: Connection, block height, peers, runtime version
- **Runtime Control**: Get version, select WASM, submit forkless upgrades
- **Threshold QRNG**: K=2, M=3 configuration, queue monitoring
- **Reporter System**: Registration status, proof counts, rewards
- **System Metrics**: Real-time time, uptime, memory, CPU

**Design Elements**:
- Monospace terminal fonts (Share Tech Mono, Orbitron)
- Green (#00ff41) on black (#000000) color scheme
- Scanline effects for authentic CRT appearance
- Glitch animations on hover
- Pulsing radar blips for network nodes
- Professional status indicators (ONLINE/OFFLINE)

**How to Launch**:
```bash
cd wallet/src-tauri
cargo run
```

### 2. Command-Line Interface (CLI)

**File**: `wallet/quantumharmony-cli`

**Commands**:
```bash
# Check node status and chain info
./quantumharmony-cli status

# Get current runtime version
./quantumharmony-cli version

# Submit runtime upgrade (forkless)
./quantumharmony-cli upgrade [/path/to/runtime.wasm]

# Check threshold QRNG status
./quantumharmony-cli qrng

# View reporter system status
./quantumharmony-cli reporter

# Show help
./quantumharmony-cli help
```

**Environment Variables**:
- `NODE_URL`: RPC endpoint (default: http://localhost:9944)
- `RUNTIME_DIR`: Path to runtime WASM directory

---

## Use Cases

### For Node Operators

**Daily Operations**:
1. Launch tactical dashboard
2. Start node from GUI
3. Monitor block production
4. Check peer connections
5. View QRNG device shares
6. Track reporter rewards

**Runtime Upgrades**:
1. Build new runtime: `cd runtime && cargo build --release`
2. Open tactical dashboard
3. Click "GET VERSION" to see current spec_version
4. Click "SELECT WASM" and choose `.compact.compressed.wasm`
5. Click "UPGRADE" to submit
6. Wait 10 seconds for finalization
7. All nodes automatically switch to new runtime

### For Developers

**Quick Status Checks**:
```bash
# Fast CLI check
./quantumharmony-cli status

# Expected Output:
# ╔════════════════════════════════════════════════════════╗
# ║     QUANTUMHARMONY TACTICAL OPERATIONS CLI v1.0       ║
# ╚════════════════════════════════════════════════════════╝
#
# [STATUS] Checking node connection...
# ✓ Node is ONLINE at http://localhost:9944
# [RUNTIME] quantumharmony v2
# [CHAIN] Block height: 680
```

**CI/CD Integration**:
```bash
#!/bin/bash
# Build new runtime
cd runtime
cargo build --release

# Check current version
CURRENT_VER=$(./wallet/quantumharmony-cli version | jq -r '.specVersion')

# Increment and submit
NEW_VER=$((CURRENT_VER + 1))
./wallet/quantumharmony-cli upgrade

# Verify upgrade
sleep 12
UPGRADED_VER=$(./wallet/quantumharmony-cli version | jq -r '.specVersion')

if [ "$UPGRADED_VER" -eq "$NEW_VER" ]; then
    echo "Runtime upgraded successfully: $CURRENT_VER -> $NEW_VER"
else
    echo "ERROR: Runtime upgrade failed"
    exit 1
fi
```

---

## Security Features

### Tauri Sandboxing

The desktop application runs in a secure Tauri sandbox:

```json
{
  "security": {
    "csp": "default-src 'self';
            script-src 'self' 'unsafe-inline';
            style-src 'self' 'unsafe-inline' https://fonts.googleapis.com;
            font-src 'self' https://fonts.gstatic.com;
            connect-src 'self' http://localhost:* ws://localhost:*"
  }
}
```

**Protections**:
- No remote code execution
- Limited network access (localhost only)
- File system access via native dialogs only
- All commands run through Rust backend

### Runtime Upgrade Safety

**Development Mode** (Current):
- Uses `sudo.setCode()` with `//Alice` key
- Instant upgrades for testing
- **NOT for production**

**Production Mode** (TODO):
- Democracy pallet voting
- Council approval required
- Time delays for review
- Emergency technical committee

---

## Visual Design

### Color Palette

| Element | Color | Hex | Usage |
|---------|-------|-----|-------|
| Background | Black | #000000 | Main background |
| Primary | Neon Green | #00ff41 | Text, borders, UI elements |
| Secondary | Dark Green | #00dd35 | Labels, secondary text |
| Warning | Orange | #ffaa41 | Warnings, pending states |
| Error | Red | #ff4141 | Errors, offline status |
| Panel BG | Dark Green Alpha | rgba(0, 20, 0, 0.6) | Panel backgrounds |

### Typography

- **Headings**: Orbitron 900 weight, all-caps, 3px letter-spacing
- **Monospace**: Share Tech Mono for terminal-style text
- **Status Values**: Bold with text-shadow glow effect

### Animations

```css
/* Radar sweep - 4 second rotation */
@keyframes sweep {
    0% { transform: rotate(0deg); }
    100% { transform: rotate(360deg); }
}

/* Scanline effect - moving gradient */
@keyframes scan {
    0% { transform: translateY(0); opacity: 0.5; }
    50% { opacity: 1; }
    100% { transform: translateY(400px); opacity: 0.5; }
}

/* Radar blip pulse */
@keyframes pulse {
    0%, 100% { opacity: 1; transform: scale(1); }
    50% { opacity: 0.5; transform: scale(1.3); }
}
```

---

## Technical Architecture

### Frontend → Backend Communication

```javascript
// Frontend (tactical-dashboard.html)
const { invoke } = window.__TAURI__.core;

// Call Rust backend
const version = await invoke('get_runtime_version');

// Display result
document.getElementById('runtime-ver').textContent = version.specName;
```

### Rust Backend Commands

```rust
// src-tauri/src/main.rs

#[tauri::command]
async fn get_runtime_version() -> Result<RuntimeVersion, String> {
    // RPC call to node
}

#[tauri::command]
async fn select_wasm_file() -> Result<String, String> {
    // Native file picker
}

#[tauri::command]
async fn submit_runtime_upgrade(
    wasm_path: String,
    sudo_seed: String,
) -> Result<String, String> {
    // Read WASM, encode hex, submit extrinsic
}

#[tauri::command]
async fn start_node() -> Result<String, String> {
    // Spawn node process
}

#[tauri::command]
async fn stop_node() -> Result<String, String> {
    // Kill node process
}
```

### RPC Communication

```bash
# Example RPC call (used by both GUI and CLI)
curl -X POST http://localhost:9944 \
  -H "Content-Type: application/json" \
  -d '{
    "jsonrpc":"2.0",
    "id":1,
    "method":"state_getRuntimeVersion",
    "params":[]
  }'

# Response:
# {
#   "jsonrpc":"2.0",
#   "result":{
#     "specName":"quantumharmony",
#     "specVersion":2,
#     "implVersion":1,
#     ...
#   },
#   "id":1
# }
```

---

## Comparison: GUI vs CLI

| Feature | Tactical Dashboard (GUI) | quantumharmony-cli |
|---------|-------------------------|-------------------|
| **Interface** | Visual, radar-style | Terminal |
| **Best For** | Node operators | Developers, automation |
| **Launch Time** | ~5 seconds | Instant |
| **Node Control** | Start/stop buttons | Manual |
| **Runtime Upgrade** | File picker + button | Command with path |
| **Visual Feedback** | Animated radar, graphs | Text output |
| **Automation** | No | Yes (scriptable) |
| **Learning Curve** | Low | Medium |

**Recommendation**: Use GUI for daily operations, CLI for automation and scripting.

---

## File Structure

```
wallet/
├── static/
│   ├── tactical-dashboard.html    # NEW: Tactical UI (green/black)
│   ├── tauri-dashboard.html       # OLD: Professional UI (gray/emerald)
│   └── quantum-wallet-ui.html     # OLDEST: Original UI
├── src-tauri/
│   ├── src/
│   │   └── main.rs                # Tauri backend with runtime update commands
│   ├── Cargo.toml                 # Dependencies
│   ├── tauri.conf.json            # Tauri configuration
│   └── build.rs                   # Build script
├── quantumharmony-cli             # NEW: Developer CLI tool
├── RUNTIME_UPDATES.md             # Comprehensive runtime upgrade guide
├── TACTICAL_UI_GUIDE.md           # This file
├── FINAL_SUMMARY.md               # Implementation summary
└── README.md                      # Project overview
```

---

## Customization

### Change Color Scheme

Edit `tactical-dashboard.html`:

```css
/* Replace neon green with your color */
:root {
    --primary: #00ff41;      /* Change this */
    --secondary: #00dd35;    /* And this */
    --warning: #ffaa41;
    --error: #ff4141;
}
```

### Add New Panels

```html
<div class="panel">
    <div class="panel-title">YOUR PANEL TITLE</div>
    <div class="status-item">
        <span class="status-label">METRIC</span>
        <span class="status-value" id="your-value">---</span>
    </div>
    <button class="btn" onclick="yourFunction()">ACTION</button>
</div>
```

```javascript
window.yourFunction = async function() {
    const result = await invoke('your_backend_command');
    document.getElementById('your-value').textContent = result;
}
```

### Add New CLI Commands

Edit `quantumharmony-cli`:

```bash
cmd_your_command() {
    echo -e "${CYAN}[YOUR_COMMAND]${NC} Doing something..."

    local result=$(rpc_call "your_rpc_method" "[]")
    echo "$result" | jq -r '.result'
}

# In main dispatcher:
case "${1:-help}" in
    # ...
    your-cmd)
        cmd_your_command
        ;;
esac
```

---

## Troubleshooting

### GUI Won't Launch

**Error**: `error: no such command: tauri`

**Fix**:
```bash
# Use cargo run directly instead
cd wallet/src-tauri
cargo run
```

**Error**: `cannot find type 'Error' in crate 'tauri_macos_sign'`

**Fix**: Tauri CLI v2.9.0 has a compile error. Use direct cargo run as above.

### CLI Shows "Node is OFFLINE"

**Check Node**:
```bash
# Is node running?
ps aux | grep quantumharmony-node

# If not, start it:
./target/release/quantumharmony-node --dev --tmp --rpc-port 9944

# Or use custom endpoint:
NODE_URL=http://remote-node:9944 ./quantumharmony-cli status
```

### Runtime Upgrade Fails

**Common Issues**:

1. **WASM file not found**
   ```bash
   # Build runtime first
   cd runtime
   cargo build --release
   ```

2. **spec_version not incremented**
   ```rust
   // Edit runtime/src/lib.rs
   pub const VERSION: RuntimeVersion = RuntimeVersion {
       spec_version: 101,  // Must be > current version
       // ...
   };
   ```

3. **Sudo key invalid**
   - Dev mode uses `//Alice` (well-known test key)
   - Production needs proper governance

---

## Future Enhancements

### Short-term

- [ ] Reporter pallet backend implementation
- [ ] STARK proof submission
- [ ] Live log streaming in terminal panel
- [ ] Network topology from peer discovery
- [ ] Chart.js integration for metrics graphs

### Long-term

- [ ] Democracy/council governance UI
- [ ] Multi-signature wallet integration
- [ ] Mobile app (React Native + Tauri Core)
- [ ] Web3 integration (polkadot.js extension)
- [ ] Prometheus metrics dashboard
- [ ] Alert system for chain events

---

## Resources

- **Tauri Docs**: https://tauri.app/
- **Substrate Docs**: https://docs.substrate.io/
- **Runtime Upgrades**: See `RUNTIME_UPDATES.md`
- **Design Inspiration**: Tactical military interfaces, retro CRT terminals

---

## Credits

**Design**: Tactical/radar aesthetic inspired by military operational interfaces

**Technology Stack**:
- Tauri v2.9
- Substrate (Polkadot SDK)
- HTML5 Canvas (radar display)
- CSS3 animations
- Bash (CLI tool)

**Fonts**:
- Orbitron (Google Fonts)
- Share Tech Mono (Google Fonts)

---

**Status**: ✅ Complete and ready for testing

**Author**: Paraxiom
**License**: GPL-3.0-only
**Date**: October 21, 2025
