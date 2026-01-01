# QuantumHarmony: Unified 3D Spiral Architecture

**Date:** October 28, 2025
**Purpose:** Reconcile all architectural views into single 3D spiral model
**Vision:** Self-documenting wallet as interactive architecture explorer

---

## 1. The 3D Spiral Architecture Concept

Instead of traditional linear layers, QuantumHarmony's architecture is organized as a **3D double helix spiral** where:
- **Vertical axis (Z)**: Security depth (Layer 1 → Layer 5)
- **Radial distance (R)**: Component proximity to core consensus
- **Angular position (θ)**: Functional domain (cryptography, networking, application)
- **Spiral path**: Data/entropy flow through the system

### Why Spiral Architecture?

**Traditional layering problems:**
- Implies strict top-down flow
- Hides lateral interactions between components
- Doesn't show feedback loops

**Spiral architecture benefits:**
- Shows **cyclic nature** of consensus rounds
- Reveals **entropy flow** from QKD → commitments → finality
- Demonstrates **toroidal mesh** wrapping (ends connect)
- Visualizes **double ratchet** key rotation

---

## 2. The Double Helix Structure

```
                    ╭─────────────────╮
                    │  Layer 5: App   │  ← QSBR RPC, Ternary Coords
                    ╰─────────────────╯
                         ↗        ↖
                       ↗            ↖
                     ↗                ↖
          ╭─────────────────╮    ╭─────────────────╮
          │ Helix A:        │    │ Helix B:        │
          │ Data Flow       │    │ Key Management  │
          ╰─────────────────╯    ╰─────────────────╯
                ↓                        ↓
           Signatures              Triple Ratchet
          (SPHINCS+)              (Forward Secrecy)
                ↓                        ↓
            Network                  Consensus
           (QUIC)                (Toroidal Mesh)
                ↓                        ↓
              ╰─────────────┬─────────────╯
                            ↓
                    [Entropy Pool]
                    (QKD Devices)
```

### Helix A: Data Flow (Outward Spiral)
```
Block N → Commit entropy → Hide with Pedersen → Gossip to peers
   ↓
Block N+1 → Reveal entropy → Verify STARK → Reconstruct Shamir
   ↓
Block N+2 → Finalize block → Update state → Emit RPC events
   ↓
[Cycle repeats, spiral continues]
```

### Helix B: Key Management (Inward Spiral)
```
Session Start → Generate Falcon1024 → Derive sub-keys → Rotate Triple Ratchet
   ↓
Every 100 blocks → VRF shard assignment → Re-key sessions → Archive old keys
   ↓
Emergency rekey → Quantum entropy injection → Forward secrecy maintained
   ↓
[Cycle repeats, spiral continues]
```

---

## 3. 3D Coordinate System

### Z-Axis: Security Layers (Vertical)
```
Z=5 ━━━━━ Application Layer ━━━━━━━━━━━━━━━━━━━━━━━━━━
        │ QSBR RPC, Ternary Encoding, Quaternary Checksums
        │
Z=4 ━━━━━ Signature Layer ━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        │ SPHINCS+ (transaction signing)
        │ Falcon1024 (session keys)
        │ Lamport chains (one-time proofs)
        │
Z=3 ━━━━━ Key Management Layer ━━━━━━━━━━━━━━━━━━━━━━━
        │ Triple Ratchet (forward secrecy)
        │ SPQDR (key derivation)
        │ VRF (deterministic randomness)
        │
Z=2 ━━━━━ Network Layer ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        │ QUIC (encrypted transport)
        │ libp2p (peer discovery)
        │ Vote gossip protocol
        │
Z=1 ━━━━━ Consensus Layer ━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        │ Aura (block authoring)
        │ GRANDPA (finality)
        │ Coherence (Byzantine voting)
        │ Toroidal mesh (parallel execution)
        │
Z=0 ━━━━━ Entropy Foundation ━━━━━━━━━━━━━━━━━━━━━━━━━
        │ QKD devices (quantum entropy)
        │ HSM (secure storage)
        │ Priority queues (QBER-sorted)
```

### R-Axis: Radial Distance from Core (Component Proximity)
```
R=0 (Center) → Core consensus (Aura, GRANDPA, Coherence)
R=1          → Validators (block producers, finalizers)
R=2          → Full nodes (transaction relay, state sync)
R=3          → Light clients (header verification only)
R=4          → RPC endpoints (wallet interactions)
R=5 (Edge)   → End users (wallet UI, applications)
```

### θ-Axis: Angular Position (Functional Domain)
```
θ=0°   → Cryptography domain (signatures, keys, proofs)
θ=72°  → Consensus domain (voting, finality, blocks)
θ=144° → Network domain (P2P, gossip, sync)
θ=216° → Storage domain (state, database, history)
θ=288° → Application domain (RPC, wallet, UX)

[Cycle repeats at θ=360° = θ=0°, demonstrating toroidal wrap-around]
```

---

## 4. Spiral Path: Entropy Flow Through Consensus Rounds

### Visual Representation (Side View)
```
     Layer 5 (Application)
         │
    ┌────┴────┐
    │  RPC    │  ← External apps consume finalized entropy
    └────┬────┘
         │
     Layer 4 (Signatures)
         │
    ┌────┴────┐
    │SPHINCS+ │  ← Sign commitment reveal transaction
    └────┬────┘
         │
     Layer 3 (Key Management)
         │
    ┌────┴────┐
    │ Triple  │  ← Encrypt entropy during gossip
    │ Ratchet │
    └────┬────┘
         │
     Layer 2 (Network)
         │
    ┌────┴────┐
    │  QUIC   │  ← Gossip commitments to peers
    └────┬────┘
         │
     Layer 1 (Consensus)
         │
    ┌────┴────┐
    │ Aura +  │  ← Include commitment in block
    │Coherence│
    └────┬────┘
         │
     Layer 0 (Entropy)
         │
    ┌────┴────┐
    │   QKD   │  ← Generate quantum random bits
    └─────────┘
```

### Spiral Path (3D View)
```
                      ╭─── Block N+2 ───╮
                     ↗                    ↖
                   ↗        Finalize        ↖
                 ↗         entropy           ↖
               ↗                              ↖
             ╭─── Block N+1 ───╮               ╰→ RPC
            ↗                   ↖                  ↓
          ↗      Reveal          ↖               Apps
        ↗       entropy            ↖
      ↗                             ↖
    ╭─── Block N ───╮                ╰→ SPHINCS+
   ↗                 ↖                     ↓
  ↗     Commit        ↖                 Signing
 ↗     entropy         ↖
╰─────────────────────→ Triple Ratchet
         ↓                     ↓
       QUIC              Key Rotation
         ↓                     ↓
    Gossip to peers ←─── Consensus
         ↓                     ↓
    [Toroidal wrap-around: Block N+3 connects back to cycle]
```

---

## 5. Toroidal Mesh Visualization (3D Donut)

### Traditional View (Flat 2D Grid)
```
Node 0 ←→ Node 1 ←→ Node 2
  ↑↓        ↑↓        ↑↓
Node 3 ←→ Node 4 ←→ Node 5
  ↑↓        ↑↓        ↑↓
Node 6 ←→ Node 7 ←→ Node 8

Problem: Edges don't connect (Node 2 doesn't link to Node 0)
```

### Toroidal View (3D Donut - Wrap Around)
```
       ╭─────────────╮
      ↗               ↖
    ↗   Node 2 → Node 0  ↖   ← Wraps horizontally
   ↗    ↑↓       ↑↓      ↖
  │     Node 5 → Node 3   │  ← AND vertically
  │     ↑↓       ↑↓       │
  ↖     Node 8 → Node 6  ↗   ← All nodes connect!
   ↖                    ↗
    ↖                  ↗
     ╰────────────────╯

Advantage: Max path length = √N (not N)
For 512 nodes: 22 hops (not 512!)
```

### Ternary Encoding on Torus
```
Node ID: 341 (decimal)
    ↓
Ternary: 110201₃
    ↓
3D coordinates: (X=1, Y=1, Z=0, W=2, U=0, V=1)
    ↓
Toroidal position: Layer 2, Segment 15, Validator 7
```

---

## 6. Interactive Wallet Architecture (Self-Documenting)

### Concept: Wallet AS Documentation

**Traditional wallets:**
- UI separate from docs
- Users don't understand what's happening
- Runtime upgrades are hidden admin operations

**QuantumHarmony wallet:**
- **Visual 3D spiral** shows where transactions flow
- **Hover over layer** to see documentation
- **Click component** to drill into technical details
- **Runtime upgrade UI** shows exactly what changes

### Wallet UI Layout (3D Spiral View)

```
┌──────────────────────────────────────────────────────┐
│                 QuantumHarmony Wallet                │
├──────────────────────────────────────────────────────┤
│                                                      │
│          ╭──────────── RPC Layer ────────────╮      │
│         ↗         [Your Balance]              ↖     │
│       ↗          500,000 QHP                   ↖    │
│     ↗                                            ↖   │
│   ╭────── SPHINCS+ Signature Layer ──────╮       │  │
│  │  [Sign Transaction] [Verify Block]     │       │ │
│  ╰──────────────────────────────────────╯        │ │
│       ↗                                    ↖      │ │
│     ╭────── Triple Ratchet Key Layer ──────╮     │ │
│    │  Session: #12,345  [Re-key Now]      │     │ │
│    ╰──────────────────────────────────────╯      │ │
│         ↗                          ↖             │ │
│       ╭────── QUIC Network Layer ──────╮         │ │
│      │  Peers: 47  Latency: 23ms       │        │ │
│      ╰──────────────────────────────────╯        │ │
│           ↗                      ↖               │ │
│         ╭────── Consensus Layer ──────╮          │ │
│        │  Block: #45,678               │         │ │
│        │  Finality: 1.5s               │         │ │
│        │  Validators: 3/3 online       │         │ │
│        ╰──────────────────────────────╯          │ │
│             ↗                  ↖                 │ │
│           ╭────── Entropy Layer ──────╮          │ │
│          │  QKD: 2 devices active     │         │ │
│          │  Quality: 99.7% (QBER<2%)  │         │ │
│          ╰──────────────────────────────╯         │ │
│                                                   │ │
│  [Rotate View] [Zoom In/Out] [Show Data Flow]   │ │
│                                                   │ │
│  ┌─────────────────────────────────────────────┐ │ │
│  │ Click any layer to view documentation      │ │ │
│  │ Drag to rotate • Scroll to zoom           │ │ │
│  └─────────────────────────────────────────────┘ │ │
└──────────────────────────────────────────────────┘ │
```

### Runtime Upgrade UI (Spiral Diff View)

When sudo initiates runtime upgrade:

```
┌──────────────────────────────────────────────────────┐
│            Runtime Upgrade: v1.0 → v1.1              │
├──────────────────────────────────────────────────────┤
│                                                      │
│  ╭────── Layer 5: Application ──────╮               │
│  │  + Added: QSBR batch RPC         │  [NEW]        │
│  │  ~ Modified: Ternary encoding    │  [CHANGED]    │
│  ╰──────────────────────────────────╯               │
│         ↓                                            │
│  ╭────── Layer 4: Signatures ──────╮                │
│  │  ✓ No changes                   │  [SAFE]        │
│  ╰──────────────────────────────────╯               │
│         ↓                                            │
│  ╭────── Layer 3: Key Management ──────╮            │
│  │  + Added: Emergency rekey protocol  │  [NEW]     │
│  ╰──────────────────────────────────────╯           │
│         ↓                                            │
│  ╭────── Layer 2: Network ──────╮                   │
│  │  ✓ No changes               │  [SAFE]            │
│  ╰──────────────────────────────╯                   │
│         ↓                                            │
│  ╭────── Layer 1: Consensus ──────╮                 │
│  │  ~ Modified: Coherence voting  │  [CHANGED]      │
│  │    - Old: 2/3 threshold         │                │
│  │    + New: 68% threshold (BFT)   │                │
│  ╰──────────────────────────────────╯               │
│                                                      │
│  Impact Analysis:                                   │
│  • State migration: Required (auto-handled)         │
│  • Downtime: None (forkless upgrade)               │
│  • Validator action: None (automatic)              │
│                                                      │
│  [Approve Upgrade] [Reject] [View Full Diff]       │
└──────────────────────────────────────────────────────┘
```

---

## 7. Technical Implementation: Wallet Stack

### Rust Dependencies
```toml
[package]
name = "quantumharmony-wallet"
version = "0.1.0"
edition = "2021"

[dependencies]
# Core Substrate
sp-core = { workspace = true }
sp-runtime = { workspace = true }
sp-keyring = { workspace = true }
sc-rpc-api = { workspace = true }

# RPC client
jsonrpsee = { workspace = true, features = ["ws-client", "http-client"] }

# 3D rendering
bevy = "0.12"  # Game engine for 3D visualization
bevy_egui = "0.23"  # UI overlay
bevy_fly_camera = "0.11"  # Camera controls

# SPHINCS+ signatures
sp-core = { workspace = true, features = ["full_crypto"] }

# Terminal UI (fallback if no graphics)
ratatui = "0.25"  # TUI framework
crossterm = "0.27"  # Terminal control

# Documentation embedding
include_dir = "0.7"  # Embed docs/ in binary
markdown = "0.3"  # Render markdown as HTML

[features]
default = ["gui"]
gui = ["bevy", "bevy_egui", "bevy_fly_camera"]
tui = ["ratatui", "crossterm"]
```

### Wallet Module Structure
```
wallet/
├── src/
│   ├── main.rs                    # Entry point (choose GUI/TUI)
│   ├── lib.rs                     # Core wallet logic
│   │
│   ├── gui/                       # 3D GUI wallet
│   │   ├── mod.rs
│   │   ├── spiral_renderer.rs    # 3D spiral visualization
│   │   ├── layer_components.rs   # Interactive layer UI
│   │   ├── upgrade_viewer.rs     # Runtime upgrade diff
│   │   └── camera_controls.rs    # Orbit/zoom controls
│   │
│   ├── tui/                       # Terminal wallet (fallback)
│   │   ├── mod.rs
│   │   ├── spiral_ascii.rs       # ASCII art spiral
│   │   └── layer_tabs.rs         # Tab-based navigation
│   │
│   ├── core/                      # Wallet business logic
│   │   ├── rpc_client.rs         # Connect to node RPC
│   │   ├── keystore.rs           # SPHINCS+ key management
│   │   ├── transaction.rs        # Build/sign transactions
│   │   ├── balance.rs            # Query balances
│   │   └── upgrade.rs            # Runtime upgrade logic
│   │
│   ├── docs/                      # Embedded documentation
│   │   ├── layer_0_entropy.md
│   │   ├── layer_1_consensus.md
│   │   ├── layer_2_network.md
│   │   ├── layer_3_keys.md
│   │   ├── layer_4_signatures.md
│   │   └── layer_5_application.md
│   │
│   └── assets/                    # 3D models, textures
│       ├── spiral_mesh.glb       # 3D spiral model
│       ├── layer_icons/          # UI icons
│       └── quantum_particles.png # Visual effects
│
├── Cargo.toml
└── README.md
```

---

## 8. GUI Implementation: Bevy 3D Spiral

### Spiral Renderer (Pseudo-Code)
```rust
use bevy::prelude::*;

#[derive(Component)]
struct LayerComponent {
    z_index: f32,  // 0.0 (entropy) to 5.0 (application)
    radius: f32,   // Distance from center
    angle: f32,    // Angular position (radians)
    label: String,
    docs_path: String,
}

fn setup_spiral(
    mut commands: Commands,
    mut meshes: ResMut<Assets<Mesh>>,
    mut materials: ResMut<Assets<StandardMaterial>>,
) {
    // Create spiral path
    let layers = vec![
        ("Entropy (QKD)", 0.0, Color::PURPLE),
        ("Consensus (Aura)", 1.0, Color::BLUE),
        ("Network (QUIC)", 2.0, Color::GREEN),
        ("Key Mgmt (Ratchet)", 3.0, Color::YELLOW),
        ("Signatures (SPHINCS+)", 4.0, Color::ORANGE),
        ("Application (RPC)", 5.0, Color::RED),
    ];

    for (i, (label, z, color)) in layers.iter().enumerate() {
        let angle = (i as f32) * (2.0 * PI / 5.0);  // Pentagon distribution
        let radius = 3.0 + (z * 0.5);  // Spiral outward as we go up

        // Create sphere for layer
        commands.spawn((
            PbrBundle {
                mesh: meshes.add(Sphere::new(0.3).mesh()),
                material: materials.add(StandardMaterial {
                    base_color: *color,
                    emissive: *color * 0.5,
                    ..default()
                }),
                transform: Transform::from_xyz(
                    radius * angle.cos(),
                    *z * 2.0,  // Vertical spacing
                    radius * angle.sin(),
                ),
                ..default()
            },
            LayerComponent {
                z_index: *z,
                radius,
                angle,
                label: label.to_string(),
                docs_path: format!("docs/layer_{}_*.md", z as u32),
            },
        ));

        // Create connecting helix line
        if i > 0 {
            // Draw line from previous layer to this one
            // (Bevy line rendering code here)
        }
    }

    // Add camera
    commands.spawn(Camera3dBundle {
        transform: Transform::from_xyz(10.0, 10.0, 10.0)
            .looking_at(Vec3::new(0.0, 5.0, 0.0), Vec3::Y),
        ..default()
    });

    // Add lighting
    commands.spawn(DirectionalLightBundle {
        transform: Transform::from_rotation(Quat::from_euler(
            EulerRot::XYZ, -PI / 4.0, PI / 4.0, 0.0
        )),
        ..default()
    });
}

fn handle_layer_click(
    mouse_button: Res<Input<MouseButton>>,
    camera_query: Query<(&Camera, &GlobalTransform)>,
    layer_query: Query<(&LayerComponent, &Transform)>,
    mut ui_state: ResMut<UiState>,
) {
    if mouse_button.just_pressed(MouseButton::Left) {
        // Raycast from camera to clicked position
        // Find intersected layer
        // Open documentation panel

        for (layer, transform) in layer_query.iter() {
            if is_clicked(transform.translation, &camera_query) {
                ui_state.show_docs(&layer.docs_path);
            }
        }
    }
}

fn animate_data_flow(
    time: Res<Time>,
    mut particle_query: Query<&mut Transform, With<DataParticle>>,
) {
    // Animate particles flowing through spiral
    for mut transform in particle_query.iter_mut() {
        // Move along spiral path
        let progress = (time.elapsed_seconds() % 5.0) / 5.0;
        let z = progress * 10.0;  // Move up layers
        let angle = progress * 2.0 * PI * 3.0;  // 3 full rotations
        let radius = 3.0 + (z * 0.5);

        transform.translation = Vec3::new(
            radius * angle.cos(),
            z,
            radius * angle.sin(),
        );
    }
}
```

---

## 9. Runtime Upgrade Workflow (Wallet POV)

### Step 1: Detect Pending Upgrade
```rust
// Poll RPC for runtime version
let current_version = rpc_client.runtime_version().await?;
let pending_upgrade = rpc_client.check_pending_upgrade().await?;

if let Some(upgrade) = pending_upgrade {
    // Show upgrade UI
    wallet_ui.show_upgrade_dialog(upgrade);
}
```

### Step 2: Fetch Upgrade Diff
```rust
struct UpgradeDiff {
    from_version: RuntimeVersion,
    to_version: RuntimeVersion,
    wasm_diff: WasmDiff,
    pallet_changes: Vec<PalletChange>,
}

enum PalletChange {
    Added { name: String, description: String },
    Removed { name: String, reason: String },
    Modified {
        name: String,
        old_spec: String,
        new_spec: String,
        breaking: bool,
    },
}

// Visualize in spiral: highlight changed layers
for change in upgrade_diff.pallet_changes {
    let layer = determine_layer(&change.name);
    spiral_renderer.highlight_layer(layer, change.breaking);
}
```

### Step 3: Sudo Approval (If User Has Sudo Key)
```rust
if wallet.has_sudo_key() {
    let approve_button = ui.button("Approve Upgrade");

    if approve_button.clicked() {
        let sudo_call = sudo::set_code(upgrade_diff.to_version.wasm);
        let signed_tx = wallet.sign_transaction(sudo_call)?;
        rpc_client.submit_transaction(signed_tx).await?;

        // Monitor upgrade progress
        wallet_ui.show_upgrade_progress();
    }
}
```

### Step 4: Monitor Upgrade Execution
```rust
loop {
    let current_version = rpc_client.runtime_version().await?;

    if current_version == upgrade_diff.to_version {
        wallet_ui.show_success("Upgrade complete!");
        break;
    }

    // Show progress in spiral (animate layers updating)
    spiral_renderer.update_layer_version(
        current_layer,
        current_version,
    );

    tokio::time::sleep(Duration::from_secs(6)).await;  // Poll every block
}
```

---

## 10. Documentation Embedding Strategy

### Embedded Markdown Files
```rust
use include_dir::{include_dir, Dir};

static DOCS_DIR: Dir = include_dir!("$CARGO_MANIFEST_DIR/src/docs");

fn load_layer_docs(layer_index: u32) -> Result<String, Error> {
    let file_path = format!("layer_{}_*.md", layer_index);
    let file = DOCS_DIR.get_file(&file_path)
        .ok_or(Error::DocsNotFound)?;

    let markdown = file.contents_utf8()
        .ok_or(Error::InvalidUtf8)?;

    // Convert markdown to HTML for display
    let html = markdown::to_html(markdown);
    Ok(html)
}
```

### Layer Documentation Files (Examples)

**src/docs/layer_0_entropy.md:**
```markdown
# Layer 0: Entropy Foundation

## What is this layer?
The quantum entropy layer provides **true random numbers** from QKD devices.

## Why is it important?
Traditional blockchains use pseudo-random hashes (deterministic).
QuantumHarmony uses **quantum physics** (non-deterministic).

## How does it work?
1. QKD device emits photons
2. Measure polarization (quantum superposition)
3. Store bits in priority queue (sorted by QBER quality)
4. Validators consume best entropy first

## Visual: Entropy Flow
[Interactive diagram showing QKD → Priority Queue → Shamir Shares]

## Runtime Parameters
- `qkd_device_count`: 2 per validator
- `priority_queue_size`: 1000 samples
- `qber_threshold`: 5% (reject worse)

## Related Code
- `node/src/threshold_qrng.rs`
- `pallets/qkd-client/src/lib.rs`
```

**src/docs/layer_1_consensus.md:**
```markdown
# Layer 1: Consensus & Toroidal Mesh

## What is this layer?
Byzantine fault-tolerant consensus with **toroidal parallelization**.

## Components
1. **Aura**: Block authoring (6-second rounds)
2. **GRANDPA**: Finality gadget (finalize 100+ blocks)
3. **Coherence**: Byzantine voting (2f+1 threshold)

## Toroidal Mesh Advantage
Traditional: O(N) message complexity
Toroidal: O(√N) message complexity

For 512 validators:
- Linear: 512 hops max
- Toroidal: 22 hops max (23× faster!)

## Visual: 3D Torus
[Interactive 3D donut showing wrap-around connections]

## Runtime Parameters
- `validator_count`: 3 (testnet), 50k (mainnet)
- `block_time`: 6 seconds
- `finality_lag`: 1-3 blocks

## Related Code
- `node/src/coherence_gadget.rs`
- `pallets/runtime-segmentation/src/lib.rs`
```

---

## 11. Next Steps: Wallet Development Plan

### Phase 1: Core RPC Client (Week 1)
- [ ] Implement `wallet/src/core/rpc_client.rs`
- [ ] Test connection to local node
- [ ] Query balance, block height, runtime version
- [ ] Submit signed transactions

### Phase 2: SPHINCS+ Key Management (Week 1)
- [ ] Implement `wallet/src/core/keystore.rs`
- [ ] Generate SPHINCS+ keypairs
- [ ] Store keys securely (encrypted file)
- [ ] Sign transactions with SPHINCS+

### Phase 3: TUI (Terminal) Wallet (Week 2)
- [ ] ASCII art spiral visualization
- [ ] Tab-based layer navigation
- [ ] Transaction submission
- [ ] Balance display
- [ ] Runtime upgrade monitoring

### Phase 4: GUI (3D) Wallet (Week 3-4)
- [ ] Bevy 3D spiral rendering
- [ ] Interactive layer components
- [ ] Documentation panel (click layers)
- [ ] Runtime upgrade diff viewer
- [ ] Animated data flow particles

### Phase 5: Runtime Upgrade UI (Week 4)
- [ ] Detect pending upgrades
- [ ] Parse WASM diff
- [ ] Visualize changed layers
- [ ] Sudo approval workflow
- [ ] Monitor upgrade progress

---

## 12. File Structure: Complete Wallet

```
quantumharmony/
├── wallet/                           # NEW: Wallet implementation
│   ├── Cargo.toml
│   ├── README.md
│   ├── src/
│   │   ├── main.rs                  # Choose GUI/TUI mode
│   │   ├── lib.rs
│   │   │
│   │   ├── gui/                     # 3D wallet
│   │   │   ├── mod.rs
│   │   │   ├── spiral_renderer.rs  # Bevy 3D spiral
│   │   │   ├── layer_components.rs # Interactive layers
│   │   │   ├── upgrade_viewer.rs   # Runtime upgrade UI
│   │   │   └── camera_controls.rs
│   │   │
│   │   ├── tui/                     # Terminal wallet
│   │   │   ├── mod.rs
│   │   │   ├── spiral_ascii.rs
│   │   │   └── layer_tabs.rs
│   │   │
│   │   ├── core/                    # Business logic
│   │   │   ├── rpc_client.rs
│   │   │   ├── keystore.rs
│   │   │   ├── transaction.rs
│   │   │   ├── balance.rs
│   │   │   └── upgrade.rs
│   │   │
│   │   ├── docs/                    # Embedded docs
│   │   │   ├── layer_0_entropy.md
│   │   │   ├── layer_1_consensus.md
│   │   │   ├── layer_2_network.md
│   │   │   ├── layer_3_keys.md
│   │   │   ├── layer_4_signatures.md
│   │   │   └── layer_5_application.md
│   │   │
│   │   └── assets/
│   │       ├── spiral_mesh.glb
│   │       └── layer_icons/
│   │
│   └── tests/
│       ├── rpc_tests.rs
│       └── keystore_tests.rs
│
├── docs/
│   └── UNIFIED_ARCHITECTURE_DIAGRAM.md  # THIS FILE
│
└── [existing project structure]
```

---

## 13. Summary: Why This Approach is Revolutionary

### Traditional Documentation Problems
- ❌ Separate from code (gets outdated)
- ❌ Linear/hierarchical (doesn't show relationships)
- ❌ Static diagrams (can't explore interactively)
- ❌ Technical jargon (inaccessible to non-experts)

### QuantumHarmony Wallet Solution
- ✅ **Embedded in binary** (always up-to-date)
- ✅ **3D spiral visualization** (shows relationships naturally)
- ✅ **Interactive exploration** (click to learn)
- ✅ **Self-documenting** (UI explains architecture)
- ✅ **Runtime upgrades visualized** (users see what changes)

### Nokia Pitch
> "Our wallet isn't just a transaction tool—it's an **interactive architecture diagram**. Click any component to see how it works. Runtime upgrades show exactly what changes in each layer. No separate docs needed—the wallet **is** the documentation."

---

**Next Action:** Shall I create the initial wallet implementation (`wallet/src/main.rs` and `wallet/src/core/rpc_client.rs`) to get started?
