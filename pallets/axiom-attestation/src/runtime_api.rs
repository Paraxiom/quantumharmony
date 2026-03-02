//! Runtime API for Axiom Attestation pallet
//!
//! Provides RPC-accessible methods to query task attestations,
//! verify tasks by hash, and retrieve account attestation history.

use sp_runtime::codec::Codec;
use sp_std::vec::Vec;

sp_api::decl_runtime_apis! {
    /// Runtime API for querying Axiom attestation storage
    pub trait AxiomAttestationApi<AccountId>
    where
        AccountId: Codec,
    {
        /// Get attestation by ID
        /// Returns: (id, task_hash, description_hash, step_count, fingerprint, provider, attester_bytes, anchored_at, revoked)
        fn get_attestation(id: u64) -> Option<(u64, [u8; 32], [u8; 32], u32, Vec<u8>, Vec<u8>, u32, bool)>;

        /// Verify a task exists on-chain by its hash
        /// Returns: (attestation_id, anchored_at_block, step_count)
        fn verify_task(task_hash: [u8; 32]) -> Option<(u64, u32, u32)>;

        /// Get all attestation IDs for an account
        fn get_attestations_by_account(account: AccountId) -> Vec<u64>;

        /// Get total number of attestations
        fn total_attestations() -> u64;
    }
}
