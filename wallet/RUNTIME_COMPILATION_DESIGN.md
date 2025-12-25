# Runtime Compilation from Wallet - Design Document

## Overview

**Game-changing feature**: Compile and upgrade the QuantumHarmony runtime directly from the wallet UI, without leaving the browser.

## Architecture

```
┌──────────────────────────────────────────────────────────────────┐
│  Browser UI (LCARS Wallet)                                        │
│                                                                    │
│  Runtime Upgrades Section:                                        │
│  ┌─────────────────┐ ┌─────────────────┐ ┌──────────────────┐  │
│  │ Compile WASM    │ │ Compile Node    │ │ Upload & Upgrade │  │
│  │ Runtime ▶       │ │ Binary ▶        │ │ ▶                │  │
│  └─────────────────┘ └─────────────────┘ └──────────────────┘  │
│                                                                    │
│  Build Progress:                                                  │
│  ████████████████░░░░ 85% - Compiling sp-core                    │
│  Console Output: [real-time build logs streaming]                │
└───────────────┬──────────────────────────────────────────────────┘
                │ POST /api/build/runtime
                │ POST /api/build/node
                │ GET  /api/build/status/:job_id (SSE stream)
                │ POST /api/upgrade/submit
┌───────────────▼──────────────────────────────────────────────────┐
│  quantum_wallet_web Server (Rust/Warp)                            │
│                                                                    │
│  Build Manager:                                                   │
│  - Job queue (one build at a time)                               │
│  - Real-time log streaming (SSE)                                  │
│  - Build artifact caching                                         │
│  - Build status tracking                                          │
│                                                                    │
│  Upgrade Manager:                                                 │
│  - WASM blob validation                                           │
│  - Transaction construction (sudo.setCode or democracy proposal)  │
│  - Signature with QPP-protected keys                              │
└───────────────┬──────────────────────────────────────────────────┘
                │ tokio::process::Command
┌───────────────▼──────────────────────────────────────────────────┐
│  Build System (Docker or Local Cargo)                             │
│                                                                    │
│  Runtime Build:                                                   │
│  $ cd /path/to/quantumharmony                                     │
│  $ SKIP_WASM_BUILD=0 cargo build --release -p quantumharmony-runtime│
│                                                                    │
│  Node Build:                                                      │
│  $ cargo build --release -p quantumharmony-node                   │
└───────────────┬──────────────────────────────────────────────────┘
                │ Output
┌───────────────▼──────────────────────────────────────────────────┐
│  Build Artifacts                                                  │
│                                                                    │
│  Runtime WASM:                                                    │
│  target/release/wbuild/quantumharmony_runtime/                    │
│    quantumharmony_runtime.compact.compressed.wasm (1-2MB)         │
│                                                                    │
│  Node Binary:                                                     │
│  target/release/quantumharmony-node (200-500MB)                   │
└───────────────────────────────────────────────────────────────────┘
```

## API Endpoints

### 1. POST /api/build/runtime

Trigger runtime WASM compilation.

**Request:**
```json
{
  "use_docker": false,
  "clean": false,
  "features": ["std", "try-runtime"]
}
```

**Response:**
```json
{
  "job_id": "build-runtime-1634567890",
  "status": "queued",
  "message": "Runtime build queued",
  "sse_endpoint": "/api/build/status/build-runtime-1634567890"
}
```

### 2. POST /api/build/node

Trigger node binary compilation.

**Request:**
```json
{
  "use_docker": false,
  "clean": false,
  "target": "release"
}
```

**Response:**
```json
{
  "job_id": "build-node-1634567891",
  "status": "queued",
  "message": "Node build queued",
  "sse_endpoint": "/api/build/status/build-node-1634567891"
}
```

### 3. GET /api/build/status/:job_id

Server-Sent Events (SSE) stream of build progress.

**Response (SSE stream):**
```
event: progress
data: {"percent": 15, "message": "Compiling sp-core v28.0.0"}

event: progress
data: {"percent": 45, "message": "Compiling frame-system v28.0.0"}

event: log
data: {"level": "info", "message": "   Compiling sp-runtime v31.0.1"}

event: complete
data: {"status": "success", "wasm_path": "target/release/wbuild/...", "size": 1456789}

event: error
data: {"status": "failed", "error": "Compilation error in pallet-balances"}
```

### 4. GET /api/build/artifacts

List available build artifacts.

**Response:**
```json
{
  "runtime_wasm": {
    "path": "target/release/wbuild/.../quantumharmony_runtime.compact.compressed.wasm",
    "size": 1456789,
    "hash": "0x1234...",
    "built_at": "2025-10-09T14:30:00Z"
  },
  "node_binary": {
    "path": "target/release/quantumharmony-node",
    "size": 345678900,
    "hash": "0x5678...",
    "built_at": "2025-10-09T14:25:00Z"
  }
}
```

### 5. POST /api/upgrade/submit

Submit runtime upgrade transaction.

**Request:**
```json
{
  "wasm_path": "target/release/wbuild/.../quantumharmony_runtime.compact.compressed.wasm",
  "upgrade_type": "sudo",  // or "democracy_proposal"
  "account_index": 0,
  "use_quantum_sig": true
}
```

**Response:**
```json
{
  "tx_hash": "0xabcd...",
  "block_hash": "0xef01...",
  "success": true,
  "events": [
    "sudo.Sudid",
    "system.CodeUpdated"
  ]
}
```

## Build Manager Implementation

### Job Queue

```rust
use std::sync::{Arc, Mutex};
use tokio::sync::broadcast;

pub struct BuildJob {
    pub id: String,
    pub job_type: BuildType,
    pub status: BuildStatus,
    pub progress: u8,
    pub logs: Vec<BuildLog>,
}

pub enum BuildType {
    Runtime { use_docker: bool, clean: bool },
    Node { use_docker: bool, clean: bool },
}

pub enum BuildStatus {
    Queued,
    Running,
    Success,
    Failed(String),
}

pub struct BuildManager {
    jobs: Arc<Mutex<HashMap<String, BuildJob>>>,
    progress_tx: broadcast::Sender<BuildProgress>,
}

impl BuildManager {
    pub async fn queue_runtime_build(&self, config: RuntimeBuildConfig) -> String {
        let job_id = format!("build-runtime-{}", std::time::SystemTime::now()...);
        // Add to queue
        // Spawn tokio task to run build
        job_id
    }

    pub async fn run_build(&self, job_id: String) -> Result<(), BuildError> {
        // Update status to Running

        // Spawn cargo build process
        let mut cmd = tokio::process::Command::new("cargo");
        cmd.args(&["build", "--release", "-p", "quantumharmony-runtime"])
            .env("SKIP_WASM_BUILD", "0")
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());

        let mut child = cmd.spawn()?;

        // Stream stdout/stderr to SSE clients
        let stdout = child.stdout.take().unwrap();
        let reader = BufReader::new(stdout);

        for line in reader.lines() {
            let line = line?;
            // Parse cargo output for progress
            let progress = self.parse_cargo_progress(&line);

            // Broadcast to SSE clients
            self.progress_tx.send(BuildProgress {
                job_id: job_id.clone(),
                progress,
                message: line.clone(),
            })?;
        }

        // Wait for completion
        let status = child.wait().await?;

        if status.success() {
            // Find WASM artifact
            let wasm_path = self.find_wasm_artifact()?;
            self.update_job_success(job_id, wasm_path);
        } else {
            self.update_job_failed(job_id, "Build failed");
        }

        Ok(())
    }

    fn parse_cargo_progress(&self, line: &str) -> u8 {
        // Parse cargo output like "Compiling sp-core v28.0.0 (45/200)"
        // Extract progress percentage
        // ...
    }
}
```

### SSE Streaming

```rust
use warp::sse::ServerSentEvent;
use futures_util::stream::Stream;

async fn build_status_handler(
    job_id: String,
    manager: Arc<BuildManager>,
) -> Result<impl Reply, Rejection> {
    let mut rx = manager.subscribe_to_job(&job_id)?;

    let stream = async_stream::stream! {
        while let Ok(progress) = rx.recv().await {
            yield Ok::<_, warp::Error>(warp::sse::Event::default()
                .event("progress")
                .json_data(&progress)
                .unwrap());
        }
    };

    Ok(warp::sse::reply(stream))
}
```

## UI Integration

### JavaScript Client

```javascript
// Trigger runtime build
async function compileRuntime() {
    const response = await fetch('/api/build/runtime', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
            use_docker: false,
            clean: false,
            features: []
        })
    });

    const { job_id, sse_endpoint } = await response.json();

    // Connect to SSE stream
    const eventSource = new EventSource(sse_endpoint);

    eventSource.addEventListener('progress', (e) => {
        const { percent, message } = JSON.parse(e.data);
        updateProgressBar(percent);
        appendLog(message);
    });

    eventSource.addEventListener('complete', (e) => {
        const { status, wasm_path, size } = JSON.parse(e.data);
        showSuccess(`Build complete! WASM: ${(size / 1024 / 1024).toFixed(2)} MB`);
        enableUpgradeButton(wasm_path);
        eventSource.close();
    });

    eventSource.addEventListener('error', (e) => {
        const { error } = JSON.parse(e.data);
        showError(`Build failed: ${error}`);
        eventSource.close();
    });
}

// Submit runtime upgrade
async function upgradeRuntime(wasmPath) {
    const response = await fetch('/api/upgrade/submit', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
            wasm_path: wasmPath,
            upgrade_type: 'sudo',
            account_index: 0,
            use_quantum_sig: true
        })
    });

    const { tx_hash, success } = await response.json();

    if (success) {
        showSuccess(`Runtime upgraded! Tx: ${tx_hash}`);
        setTimeout(() => {
            window.location.reload(); // Refresh to use new runtime
        }, 3000);
    }
}
```

## Security Considerations

### 1. Build Isolation

- **Docker mode**: Builds run in isolated containers
- **Filesystem access**: Limit to project directory only
- **Resource limits**: CPU/memory caps to prevent DoS

### 2. Authentication

- **Required**: User must be authenticated with sudo account
- **QPP signatures**: Upgrade transactions use quantum-safe keys
- **Rate limiting**: Max 1 build per 5 minutes

### 3. Validation

- **WASM validation**: Check blob is valid Substrate runtime
- **Size limits**: Max 10MB WASM blob
- **Hash verification**: Compute and display WASM hash before upgrade

## Development vs Production

### Development Mode
- ✅ Sudo-based instant upgrades
- ✅ Local cargo builds (faster)
- ✅ Hot reload support
- ⚠️ No governance required

### Production Mode
- 🔐 Democracy/Council governance required
- 🐳 Docker-based builds (reproducible)
- 📊 Upgrade proposal voting period
- ✅ QKD-secured submissions

## Benefits

1. **Developer Experience**: No context switching between terminal and UI
2. **Transparency**: Real-time build logs visible to all users
3. **Safety**: QPP enforcement prevents key misuse during upgrades
4. **Efficiency**: Cached builds, progress tracking, artifact management
5. **Quantum-Safe**: All upgrade transactions use SPHINCS+ signatures

## Future Enhancements

1. **Source code editor**: Edit pallets directly in browser
2. **Diff viewer**: Compare runtime versions before upgrade
3. **Rollback support**: Quick revert to previous runtime
4. **Multi-node coordination**: Upgrade multiple validator nodes
5. **Governance integration**: Vote on proposals from wallet
6. **Build caching**: Store artifacts in distributed cache

## Next Steps

1. Implement BuildManager backend
2. Add SSE streaming support
3. Create runtime upgrade transaction builder
4. Integrate with nokia wallet UI
5. Add Docker build mode
6. Test with real node deployment
