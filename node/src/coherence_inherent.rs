//! Coherence Finality Checkpoint Storage
//!
//! This module provides a simple shared storage for finality certificates
//! that need to be included on-chain at checkpoint blocks.
//!
//! Phase 6B: For now, this is just shared state. In Phase 7, we'll add
//! proper inherent data provider integration with Substrate's inherent system.

use pallet_proof_of_coherence::types::FinalityCertificate;
use sp_core::H256;
use std::sync::{Arc, Mutex};

/// Shared checkpoint provider for the node
///
/// This is shared between:
/// - Coherence gadget (generates certificates at checkpoint blocks)
/// - Block authoring (includes them in blocks - Phase 7)
pub type SharedCheckpointProvider = Arc<Mutex<Option<FinalityCertificate<
    sp_core::sphincs::Public,
    u32,
    H256,
>>>>;

/// Create a shared checkpoint provider
pub fn create_shared_checkpoint_provider() -> SharedCheckpointProvider {
    Arc::new(Mutex::new(None))
}

/// Get the pending checkpoint certificate if any
pub fn get_pending_checkpoint(
    provider: &SharedCheckpointProvider,
) -> Option<FinalityCertificate<sp_core::sphincs::Public, u32, H256>> {
    provider.lock().unwrap().clone()
}

/// Set a checkpoint certificate to be included
pub fn set_pending_checkpoint(
    provider: &SharedCheckpointProvider,
    cert: FinalityCertificate<sp_core::sphincs::Public, u32, H256>,
) {
    let mut lock = provider.lock().unwrap();
    *lock = Some(cert);
}

/// Clear the pending checkpoint after inclusion
pub fn clear_pending_checkpoint(provider: &SharedCheckpointProvider) {
    let mut lock = provider.lock().unwrap();
    *lock = None;
}
