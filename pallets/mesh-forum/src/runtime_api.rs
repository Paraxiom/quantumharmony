//! Runtime API for MeshForum pallet
//!
//! Provides RPC-accessible methods to query forum messages.

use sp_runtime::codec::Codec;
use sp_std::vec::Vec;

sp_api::decl_runtime_apis! {
    /// Runtime API for querying forum messages
    pub trait MeshForumApi<AccountId>
    where
        AccountId: Codec,
    {
        /// Get all messages with pagination
        /// Returns: Vec of (message_id, sender, block_number, content)
        fn get_messages(limit: u32, offset: u32) -> Vec<(u32, AccountId, u32, Vec<u8>)>;

        /// Get total message count
        fn message_count() -> u32;
    }
}
