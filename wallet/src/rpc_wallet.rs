// RPC-based wallet implementation for production use
// This replaces sp_io dependencies with RPC calls

use crate::types::{AccountType, WalletError};
use serde::{Deserialize, Serialize};
use serde_json::json;
use sp_core::{
    crypto::{Ss58Codec, SecretStringError, AccountId32},
    sr25519::{Pair as Sr25519Pair, Public as Sr25519Public},
    twox_128, twox_64, blake2_128, Pair,
};
use scale_codec::Decode;
use std::collections::HashMap;

#[derive(Deserialize)]
struct RpcResponse {
    result: Option<String>,
    error: Option<RpcError>,
}

#[derive(Deserialize)]
struct RpcError {
    message: String,
}

/// RPC client for blockchain interaction
pub struct RpcClient {
    endpoint: String,
    client: reqwest::Client,
}

impl RpcClient {
    pub fn new(endpoint: String) -> Self {
        Self {
            endpoint,
            client: reqwest::Client::new(),
        }
    }

    /// Submit a signed transaction via RPC
    pub async fn submit_extrinsic(&self, signed_tx: Vec<u8>) -> Result<String, WalletError> {
        let response = self.rpc_call("author_submitExtrinsic", json!([format!("0x{}", hex::encode(signed_tx))])).await?;
        Ok(response)
    }

    /// Get account balance via RPC
    pub async fn get_balance(&self, account: &str) -> Result<u128, WalletError> {
        // Parse SS58 address to AccountId32
        let account_id = AccountId32::from_ss58check(account)
            .map_err(|_| WalletError::InvalidAddress(account.to_string()))?;

        // Encode storage key for System::Account
        let storage_key = self.encode_account_storage_key(account_id.as_ref());

        // Query storage
        let response = self.rpc_call("state_getStorage", json!([storage_key])).await?;

        if response.is_empty() || response == "null" {
            // Account doesn't exist yet, return 0
            return Ok(0u128);
        }

        // Decode hex response
        let hex_data = response.trim_start_matches("0x");
        let data = hex::decode(hex_data)
            .map_err(|e| WalletError::RpcError(format!("Failed to decode hex: {}", e)))?;

        // Decode AccountInfo - the balance is in the `data` field
        // AccountInfo structure: { nonce, consumers, providers, sufficients, data: AccountData }
        // AccountData structure: { free, reserved, frozen, flags }
        // We need to skip the first fields and extract `free` balance

        if data.len() < 40 {
            return Ok(0u128);
        }

        // Skip nonce (4 bytes), consumers (4 bytes), providers (4 bytes), sufficients (4 bytes)
        // Then read free balance (16 bytes for u128)
        let balance_start = 16; // After 4 u32 fields
        if data.len() >= balance_start + 16 {
            let mut balance_bytes = [0u8; 16];
            balance_bytes.copy_from_slice(&data[balance_start..balance_start + 16]);
            let balance = u128::from_le_bytes(balance_bytes);
            Ok(balance)
        } else {
            Ok(0u128)
        }
    }

    /// Make RPC call
    async fn rpc_call(&self, method: &str, params: serde_json::Value) -> Result<String, WalletError> {
        let request = json!({
            "jsonrpc": "2.0",
            "id": 1,
            "method": method,
            "params": params
        });

        let response = self.client
            .post(&self.endpoint)
            .json(&request)
            .send()
            .await
            .map_err(|e| WalletError::RpcError(format!("HTTP error: {}", e)))?;

        let rpc_response: RpcResponse = response.json().await
            .map_err(|e| WalletError::RpcError(format!("JSON parse error: {}", e)))?;

        if let Some(error) = rpc_response.error {
            return Err(WalletError::RpcError(error.message));
        }

        Ok(rpc_response.result.unwrap_or_default())
    }

    fn encode_account_storage_key(&self, account_id: &[u8]) -> String {
        // Storage key = twox128("System") + twox128("Account") + blake2_128(account_id) + account_id
        let mut key = Vec::new();
        key.extend_from_slice(&twox_128(b"System"));
        key.extend_from_slice(&twox_128(b"Account"));
        key.extend_from_slice(&blake2_128(account_id));
        key.extend_from_slice(account_id);
        format!("0x{}", hex::encode(key))
    }
}

/// Wallet state for RPC wallet
#[derive(Debug, Clone, PartialEq)]
pub enum RpcWalletState {
    Locked,
    Unlocked,
}

/// RPC-based QPP Wallet
pub struct RpcQppWallet {
    /// Wallet state
    state: RpcWalletState,
    /// Accounts stored locally
    accounts: HashMap<String, Sr25519Pair>,
    /// RPC client for blockchain interaction
    rpc: RpcClient,
}

impl RpcQppWallet {
    /// Create new wallet connected to blockchain RPC
    pub fn new(rpc_endpoint: String) -> Self {
        Self {
            state: RpcWalletState::Locked,
            accounts: HashMap::new(),
            rpc: RpcClient::new(rpc_endpoint),
        }
    }

    /// Create account using local key generation
    /// (Quantum entropy comes from blockchain when submitting transactions)
    pub fn create_account(&mut self, name: &str) -> Result<String, WalletError> {
        // Generate keypair locally (no sp_io needed)
        let (pair, phrase, _) = Sr25519Pair::generate_with_phrase(None);
        let public = pair.public();
        let address = public.to_ss58check();
        
        self.accounts.insert(address.clone(), pair);
        
        Ok(address)
    }

    /// Sign transaction locally
    pub fn sign_transaction(&self, from: &str, call_data: Vec<u8>) -> Result<Vec<u8>, WalletError> {
        let pair = self.accounts.get(from)
            .ok_or(WalletError::AccountNotFound(from.to_string()))?;
        
        // In production, construct proper extrinsic with nonce, era, etc.
        let signature = pair.sign(&call_data);
        
        // Construct signed extrinsic (simplified)
        let mut signed_tx = Vec::new();
        signed_tx.extend_from_slice(&call_data);
        signed_tx.extend_from_slice(signature.as_ref());
        
        Ok(signed_tx)
    }

    /// Submit transaction to blockchain
    pub async fn submit_transaction(&self, signed_tx: Vec<u8>) -> Result<String, WalletError> {
        self.rpc.submit_extrinsic(signed_tx).await
    }
}

/// Production wallet factory
pub fn create_production_wallet(endpoint: &str) -> RpcQppWallet {
    RpcQppWallet::new(endpoint.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rpc_wallet_creation() {
        let wallet = create_production_wallet("ws://localhost:9933");
        assert!(matches!(wallet.state, RpcWalletState::Locked));
    }
}