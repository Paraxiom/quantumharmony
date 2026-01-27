//! Runtime API for Devonomics pallet
//!
//! Provides RPC-accessible methods to query quest completion and scores.

use sp_runtime::codec::Codec;
use sp_std::vec::Vec;

sp_api::decl_runtime_apis! {
    /// Runtime API for querying devonomics quest and score data
    pub trait DevonomicsApi<AccountId>
    where
        AccountId: Codec,
    {
        /// Get the devonomics score for an account
        fn get_score(account: AccountId) -> u32;

        /// Get completed quests for an account
        /// Returns: Vec of (quest_id_bytes, block_number)
        fn get_completed_quests(account: AccountId) -> Vec<(Vec<u8>, u32)>;

        /// Get the highest tier unlocked for an account
        fn get_tier(account: AccountId) -> u8;

        /// Get leaderboard sorted by score descending
        /// Returns: Vec of (account, score), limited to `limit` entries
        fn get_leaderboard(limit: u32) -> Vec<(AccountId, u32)>;
    }
}
