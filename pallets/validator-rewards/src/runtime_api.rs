//! Runtime API for ValidatorRewards pallet
//!
//! Provides RPC-accessible methods to query validator staking and rewards data.

use sp_runtime::codec::Codec;
use sp_std::vec::Vec;

sp_api::decl_runtime_apis! {
    /// Runtime API for querying validator rewards information
    pub trait ValidatorRewardsApi<AccountId, Balance>
    where
        AccountId: Codec,
        Balance: Codec,
    {
        /// Get the staked amount for a validator
        fn validator_stake(account: AccountId) -> Balance;

        /// Get pending rewards for a validator
        fn pending_rewards(account: AccountId) -> Balance;

        /// Get certification level for a validator (0=Uncertified, 1=KYC, 2=Agent)
        fn certification_level(account: AccountId) -> u8;

        /// Get all staked validators with their stakes
        fn all_validators() -> Vec<(AccountId, Balance)>;

        /// Get the minimum stake requirement
        fn min_stake() -> Balance;

        /// Get the block reward amount
        fn block_reward() -> Balance;

        /// Get total staked across all validators
        fn total_staked() -> Balance;
    }
}
