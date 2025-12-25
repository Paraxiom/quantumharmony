//! Wallet API for querying balances and account information
//! Provides simple RPC methods for wallets to query blockchain state

#![cfg_attr(not(feature = "std"), no_std)]

use scale_codec::Codec;

sp_api::decl_runtime_apis! {
    /// Wallet API for balance queries
    pub trait WalletApi<AccountId, Balance> where
        AccountId: Codec,
        Balance: Codec,
    {
        /// Get the free balance of an account
        fn get_balance(account: AccountId) -> Balance;
    }
}
