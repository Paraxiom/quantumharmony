//! Genesis Config Presets for QuantumHarmony Runtime
//!
//! NOTE: Runtime genesis presets are currently disabled because ECDSA key derivation
//! (from_string) doesn't work in WASM/no_std environment. Genesis configuration is
//! handled by the node's chain_spec.rs instead, which runs in native code where
//! key derivation works correctly.

use sp_genesis_builder::PresetId;

/// Provides the JSON representation of predefined genesis config for given `id`.
/// Currently returns None to use chain_spec genesis configuration instead.
pub fn get_preset(_id: &PresetId) -> Option<sp_std::vec::Vec<u8>> {
    // Return None to signal that genesis config should come from chain_spec.rs
    // This avoids WASM compatibility issues with ECDSA key derivation
    None
}

/// List of supported presets.
/// Currently returns empty list since we're using chain_spec genesis config.
pub fn preset_names() -> sp_std::vec::Vec<PresetId> {
    sp_std::vec![]
}
