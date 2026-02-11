//! Runtime API for Notarial pallet
//!
//! Provides RPC-accessible methods to query attestations, verify documents,
//! and retrieve certificates from on-chain storage.

use sp_runtime::codec::Codec;
use sp_std::vec::Vec;

sp_api::decl_runtime_apis! {
    /// Runtime API for querying notarial storage
    pub trait NotarialRuntimeApi<AccountId>
    where
        AccountId: Codec,
    {
        /// Get attestation by ID
        /// Returns: (id, document_hash, category, description, attester, attested_at, expires_at, status, witness_count, certified)
        fn get_attestation(id: u64) -> Option<(u64, [u8; 32], u8, Vec<u8>, AccountId, u32, Option<u32>, u8, u32, bool)>;

        /// Verify a document hash exists on-chain
        /// Returns: (attestation_id, attested_at, status, certified, witness_count)
        fn verify_document(hash: [u8; 32]) -> Option<(u64, u32, u8, bool, u32)>;

        /// Get all attestation IDs for an owner
        fn get_attestations_by_owner(account: AccountId) -> Vec<u64>;

        /// Get certificate by ID
        /// Returns: (id, attestation_id, generated_at, certificate_hash, issuer)
        fn get_certificate(id: u64) -> Option<(u64, u64, u32, [u8; 32], AccountId)>;
    }
}
