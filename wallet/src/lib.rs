//! QuantumHarmony QPP Wallet
//!
//! Implements Quantum Preservation Pattern (QPP) to enforce quantum physics laws
//! at compile time using Rust's type system.

#![cfg_attr(not(feature = "std"), no_std)]

// For no_std environments, we need alloc for Vec and other heap types
#[cfg(not(feature = "std"))]
extern crate alloc;

// Core modules
pub mod no_clone;
pub mod quantum_state;
pub mod wallet;
pub mod light_client;
pub mod types;
pub mod qpp_enforcement;
pub mod qpp_sync_context;

// Additional modules
// pub mod bridge; // TODO: Implement bridge module
// pub mod quantum_ops; // TODO: Implement quantum operations
// FIXME: quantum_tunnel and tunnel_integration have compilation errors
// pub mod quantum_tunnel;
// pub mod tunnel_integration;

// RPC-based wallet for production
#[cfg(feature = "std")]
pub mod rpc_wallet;

// QPP-enforced RPC wallet
#[cfg(feature = "std")]
pub mod qpp_rpc_wallet;

// QRNG client for quantum entropy
#[cfg(feature = "std")]
pub mod qrng_client;

// QKD-based key derivation
#[cfg(feature = "std")]
pub mod qkd_key_derivation;

// Docker management for web wallet
#[cfg(feature = "std")]
pub mod docker;

// Re-exports
pub use no_clone::NoClone;
pub use quantum_state::{QuantumState, QuantumKey};
pub use wallet::{QPPWallet, WalletState};
pub use light_client::QPPLightClient;
// FIXME: Commented out until quantum_tunnel and tunnel_integration are fixed
// pub use quantum_tunnel::{QuantumTunnel, TunnelConfig};
// pub use tunnel_integration::TunneledWallet;
pub use qpp_enforcement::{
    QuantumEntropy, QuantumKeyGenerator, QuantumSigner,
    QuantumTransactionBuilder, QuantumTransaction,
    QuantumAccountCreator, QuantumSignature
};
pub use qpp_sync_context::{
    SyncQuantumContext, QuantumSignature as SyncQuantumSignature,
    SignatureType, MetaAwareScheduler
};

// #[cfg(feature = "wasm")]
// pub mod wasm_bindings;
