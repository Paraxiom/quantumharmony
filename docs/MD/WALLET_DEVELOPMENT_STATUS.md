# QuantumHarmony Self-Documenting Wallet: Development Status

**Date:** October 28, 2025
**Purpose:** Track progress on 3D spiral self-documenting wallet
**Vision:** Wallet AS documentation - interactive architecture explorer

---

## Current Status

### ✅ Completed (Today)

1. **Unified Architecture Document**
   - Created `UNIFIED_ARCHITECTURE_DIAGRAM.md`
   - 3D double helix spiral concept
   - 5-layer coordinate system (Z, R, θ axes)
   - Toroidal mesh visualization
   - Triple Ratchet integration (not "double ratchet" - corrected)

2. **Core Wallet Modules** (Created in `wallet/src/core/`)
   - `mod.rs` - Layer definitions and coordinate system
   - `rpc_client.rs` - RPC connection to blockchain node
   - `keystore.rs` - SPHINCS+ key management
   - `transaction.rs` - Transaction building (stub)
   - `balance.rs` - Balance queries
   - `upgrade.rs` - Runtime upgrade monitoring

3. **Documentation Structure**
   - `NOKIA_PRESENTATION_READY.md` - 95% completion status
   - `TODO_NOKIA_FOCUSED.md` - Prioritized roadmap
   - `DOCUMENTATION_CLEANUP_SUMMARY.md` - File consolidation

### 🔄 Existing Wallet Components (Already in Codebase)

The wallet already has:
- ✅ `quantum_tunnel.rs` - Tunnel integration
- ✅ `docker.rs` - Docker deployment support
- ✅ `types.rs` - Type definitions
- ✅ `bin/quantum_wallet_web.rs` - Web wallet server
- ✅ `bin/simple_web_wallet.rs` - Simple web interface
- ✅ `qrng_client.rs` - QRNG client
- ✅ `tui/frictionless_tui.rs` - Existing TUI implementation

---

## Architecture Integration Plan

### Phase 1: Enhance Existing TUI with Spiral Visualization

Instead of creating from scratch, **enhance the existing TUI** with:

1. **ASCII Spiral Art** (`wallet/src/tui/spiral_ascii.rs`)
   ```
         ╭─── App (RPC) ───╮
        ↗                   ↖
      ↗   Signatures         ↖
    ↗     (SPHINCS+)           ↖
   ╭─── Keys (Triple Ratchet) ───╮
  │                               │
  ↖       Network (QUIC)        ↗
   ↖                           ↗
    ↖    Consensus (Aura)    ↗
     ↖                      ↗
      ╰─── Entropy (QKD) ──╯
   ```

2. **Tab-Based Layer Navigation**
   - Press `0-5` to jump to layer
   - Arrow keys to move between layers
   - `Enter` to view layer documentation
   - `U` to check for runtime upgrades

3. **Embedded Documentation Display**
   - Markdown files in `wallet/src/docs/`
   - Rendered in TUI panel when layer selected
   - Real-time metrics overlay

### Phase 2: Add Runtime Upgrade UI

Integrate into existing TUI:

1. **Upgrade Detection**
   - Poll RPC every 6 seconds
   - Show notification when upgrade pending
   - Press `U` to view upgrade details

2. **Upgrade Diff Viewer**
   ```
   ┌─────────────────────────────────────┐
   │ Runtime Upgrade: v1.0 → v1.1        │
   ├─────────────────────────────────────┤
   │ Layer 5 (Application)               │
   │  + Added: QSBR batch RPC      [NEW] │
   │  ~ Modified: Ternary encoding [CHG] │
   │                                     │
   │ Layer 4 (Signatures)                │
   │  ✓ No changes                 [SAFE]│
   │                                     │
   │ Layer 3 (Key Management)            │
   │  + Added: Emergency rekey     [NEW] │
   │                                     │
   │ [Approve] [Reject] [Details]        │
   └─────────────────────────────────────┘
   ```

3. **Sudo Integration**
   - If user has sudo key in keystore
   - Allow `sudo.set_code()` submission
   - Monitor execution progress

### Phase 3: 3D GUI (Future - Using Bevy)

**After TUI is complete**, add optional 3D mode:

1. **Bevy 3D Engine**
   - Feature flag: `--features gui`
   - Renders actual 3D spiral
   - Camera orbits around architecture
   - Click spheres to see layer docs

2. **WebGL Export (Optional)**
   - Compile to WASM
   - Run in browser
   - Same 3D visualization
   - No installation required

---

## Files Created Today

```
wallet/src/
├── core/                           (NEW - Core business logic)
│   ├── mod.rs                     ✅ Layer definitions, coordinate system
│   ├── rpc_client.rs              ✅ RPC connection & queries
│   ├── keystore.rs                ✅ SPHINCS+ key management
│   ├── transaction.rs             ✅ Transaction building (stub)
│   ├── balance.rs                 ✅ Balance queries
│   └── upgrade.rs                 ✅ Runtime upgrade monitoring
│
├── main.rs                        ✅ Entry point with CLI args
│
└── (docs/, gui/, assets/ created but empty)

docs/
├── UNIFIED_ARCHITECTURE_DIAGRAM.md     ✅ Complete 3D spiral spec
├── NOKIA_PRESENTATION_READY.md         ✅ Status for Nokia
├── TODO_NOKIA_FOCUSED.md               ✅ Prioritized roadmap
└── DOCUMENTATION_CLEANUP_SUMMARY.md    ✅ File consolidation

```

---

## Next Steps (Priority Order)

### Week 1: Minimal Viable Wallet (TUI)

**Day 1-2: Enhance Existing TUI**
- [ ] Read existing `wallet/src/tui/frictionless_tui.rs`
- [ ] Add spiral ASCII art visualization
- [ ] Implement layer navigation (0-5 keys)
- [ ] Test with running node

**Day 3: Embedded Documentation**
- [ ] Create `wallet/src/docs/layer_*.md` files
- [ ] Implement markdown rendering in TUI
- [ ] Add documentation panel

**Day 4-5: Runtime Upgrade UI**
- [ ] Integrate `core/upgrade.rs` with TUI
- [ ] Create upgrade diff viewer
- [ ] Test sudo approval workflow

### Week 2: Testing & Nokia Demo

**Day 6-7: Integration Testing**
- [ ] Test against 3-validator testnet
- [ ] Test key generation/signing
- [ ] Test runtime upgrade flow

**Day 8-9: Documentation**
- [ ] Complete all 6 layer markdown files
- [ ] Add inline help (`?` key)
- [ ] Create wallet user guide

**Day 10: Nokia Demo Preparation**
- [ ] Record demo video
- [ ] Prepare live demo script
- [ ] Test on fresh machine

### Week 3-4: 3D GUI (Optional)

**If time permits:**
- [ ] Integrate Bevy engine
- [ ] Render 3D spiral mesh
- [ ] Add camera controls
- [ ] Port documentation display to GUI

---

## Integration with Existing Wallet

### Leverage What's Already There

**Keep:**
- `bin/quantum_wallet_web.rs` - Web interface
- `bin/simple_web_wallet.rs` - Simple web UI
- `qrng_client.rs` - QRNG integration
- `tui/frictionless_tui.rs` - Existing TUI

**Enhance:**
- Add spiral visualization to TUI
- Add layer navigation
- Add embedded docs
- Add runtime upgrade UI

**Merge:**
- Use existing RPC client if better
- Use existing keystore if available
- Consolidate type definitions

---

## Key Design Decisions

### 1. TUI First, GUI Later

**Rationale:**
- TUI works everywhere (SSH, terminals, low-end machines)
- Faster to implement and test
- Nokia can demo immediately
- 3D GUI is "wow factor" but not essential

### 2. Embedded Documentation

**Rationale:**
- Docs always up-to-date with code
- No separate website/wiki to maintain
- Users explore by clicking/pressing keys
- Self-documenting = game changer

### 3. Runtime Upgrade Transparency

**Rationale:**
- Users see exactly what changes
- Layer-by-layer diff view
- Sudo approval workflow
- Builds trust in governance

### 4. Triple Ratchet (Not Double)

**Correction:**
- UNIFIED_ARCHITECTURE_DIAGRAM.md mentioned "double ratchet"
- QuantumHarmony uses **Sparse Triple Ratchet** (Signal's protocol extended)
- Document updated to reflect this

---

## Questions for Next Session

1. **Should we enhance existing TUI or start fresh?**
   - Existing TUI has infrastructure
   - New TUI has clean architecture
   - Recommendation: **Enhance existing**

2. **Priority: Wallet or Nokia docs?**
   - Wallet shows off architecture interactively
   - Docs are needed for meeting
   - Recommendation: **Both in parallel** (wallet IS the docs)

3. **3D GUI timeline?**
   - After TUI complete?
   - For Nokia demo?
   - Recommendation: **Post-Nokia** (TUI sufficient for demo)

---

## Success Criteria

### Minimal Viable Wallet (Week 1)

- ✅ Connects to node RPC
- ✅ Displays 5-layer spiral (ASCII art)
- ✅ Navigate layers with keyboard
- ✅ View embedded documentation
- ✅ Check runtime upgrade status
- ✅ Display real-time metrics

### Nokia Demo Ready (Week 2)

- ✅ Generate SPHINCS+ keys
- ✅ Sign transactions
- ✅ Submit runtime upgrade (sudo)
- ✅ Monitor upgrade execution
- ✅ Complete layer documentation
- ✅ Smooth demo workflow

### Production Ready (Week 3-4)

- ✅ 3D GUI mode (optional)
- ✅ WebGL browser export
- ✅ Comprehensive tests
- ✅ User guide
- ✅ Video tutorials

---

## Technical Debt & Future Work

### Known Issues

1. **Keystore encryption**
   - Currently saves keys UNENCRYPTED
   - TODO: Add AES-256-GCM encryption
   - Priority: HIGH (before production)

2. **Transaction encoding**
   - Stub implementation in `transaction.rs`
   - TODO: Proper SCALE codec encoding
   - Priority: MEDIUM (needed for transfers)

3. **Error handling**
   - Many TODOs use `anyhow::bail!`
   - TODO: Structured error types
   - Priority: LOW (works for now)

### Future Enhancements

1. **Hardware wallet support**
   - Ledger/Trezor integration
   - SPHINCS+ via hardware device
   - Priority: POST-LAUNCH

2. **Multi-sig wallets**
   - M-of-N SPHINCS+ signatures
   - Governance integration
   - Priority: POST-LAUNCH

3. **Light client mode**
   - Don't trust RPC node
   - Verify finality proofs
   - Priority: POST-LAUNCH

---

## Conclusion

We've laid the groundwork for a **revolutionary self-documenting wallet** that:

- **IS the documentation** (not just a transaction tool)
- **Visualizes architecture** (3D spiral, layer navigation)
- **Enables runtime upgrades** (with full transparency)
- **Uses post-quantum crypto** (SPHINCS+, Triple Ratchet)
- **Works everywhere** (TUI first, GUI optional)

**Next immediate action:** Enhance existing TUI with spiral visualization and layer navigation.

---

**Status:** Foundation complete, ready for TUI integration
**Timeline:** 2-4 weeks to production-ready
**Nokia Demo:** Week 2 (TUI with embedded docs)
**Full 3D GUI:** Week 3-4 (optional enhancement)
