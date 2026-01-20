//! Test Account Setup for Canary Network Testing
//!
//! This module provides utilities for creating and managing SPHINCS+ test accounts
//! for network integration testing. Unlike the genesis accounts in `test_accounts.rs`,
//! these are dynamically generated accounts for test scenarios.
//!
//! ## Usage
//!
//! ```rust,ignore
//! use quantumharmony_node::test_account_setup::{generate_test_account, save_test_accounts};
//!
//! // Generate test accounts
//! let accounts = vec![
//!     generate_test_account("test_sender"),
//!     generate_test_account("test_receiver"),
//! ];
//!
//! // Save for later use
//! save_test_accounts(&accounts, "tests/test_accounts.json").unwrap();
//! ```
//!
//! ## Security Note
//!
//! Test accounts are generated with full keypairs (public + secret keys).
//! The secret keys are saved to the JSON file for test automation.
//! **NEVER use these accounts in production environments.**

use serde::{Deserialize, Serialize};
use sp_core::crypto::Ss58Codec;
use sp_runtime::traits::IdentifyAccount;
use sp_runtime::MultiSigner;
use pqcrypto_sphincsplus::sphincsshake256ssimple as sphincs;
use pqcrypto_traits::sign::{PublicKey, SecretKey};
use sp_core::{Blake2Hasher, Hasher};

/// A test account with SPHINCS+ keypair
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TestAccount {
    /// Human-readable name for the account
    pub name: String,
    /// SPHINCS+ public key (hex encoded)
    pub public_key: String,
    /// SPHINCS+ secret key (hex encoded) - for signing test transactions
    pub secret_key: String,
    /// Account ID (32-byte hash, hex encoded)
    pub account_id: String,
    /// SS58 encoded address (for RPC calls)
    pub ss58_address: String,
    /// Creation timestamp
    pub created_at: u64,
}

impl TestAccount {
    /// Get the raw public key bytes
    pub fn public_key_bytes(&self) -> Result<Vec<u8>, hex::FromHexError> {
        hex::decode(&self.public_key)
    }

    /// Get the raw secret key bytes
    pub fn secret_key_bytes(&self) -> Result<Vec<u8>, hex::FromHexError> {
        hex::decode(&self.secret_key)
    }

    /// Get the account ID as bytes
    pub fn account_id_bytes(&self) -> Result<[u8; 32], String> {
        let bytes = hex::decode(&self.account_id)
            .map_err(|e| format!("Invalid account_id hex: {}", e))?;
        bytes.try_into()
            .map_err(|_| "Account ID must be 32 bytes".to_string())
    }
}

/// Generate a new SPHINCS+ test account
///
/// Creates a new keypair using SPHINCS+-SHAKE-256s-simple (64-byte public key)
/// and derives the AccountId using Keccak-256 (matching chain_spec.rs).
///
/// # Arguments
/// * `name` - Human-readable name for the account
///
/// # Returns
/// A `TestAccount` with all key material and derived addresses
pub fn generate_test_account(name: &str) -> TestAccount {
    // Generate SPHINCS+ keypair
    let (public_key, secret_key) = sphincs::keypair();

    let public_key_bytes = public_key.as_bytes();
    let secret_key_bytes = secret_key.as_bytes();

    // For SPHINCS+ accounts, we need to derive AccountId from the public key
    // Using the first 64 bytes (which is our SPHINCS+ public key size for the simple variant)
    // and hashing with Blake2-256 to get a 32-byte AccountId
    let pk_64: [u8; 64] = public_key_bytes[..64]
        .try_into()
        .expect("SPHINCS+ public key should be at least 64 bytes");

    // Create sp_core::sphincs::Public from the 64-byte public key
    let sphincs_public = sp_core::sphincs::Public::from_raw(pk_64);

    // Convert to MultiSigner and then to AccountId (uses Keccak-256 internally)
    let signer = MultiSigner::from(sphincs_public);
    let account_id = signer.into_account();

    // Get SS58 address
    let ss58_address = account_id.to_ss58check();

    let timestamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_millis() as u64)
        .unwrap_or(0);

    // Get the account ID bytes explicitly
    let account_id_bytes: &[u8; 32] = account_id.as_ref();

    TestAccount {
        name: name.to_string(),
        public_key: hex::encode(public_key_bytes),
        secret_key: hex::encode(secret_key_bytes),
        account_id: hex::encode(account_id_bytes),
        ss58_address,
        created_at: timestamp,
    }
}

/// Save test accounts to a JSON file
///
/// # Arguments
/// * `accounts` - Slice of test accounts to save
/// * `path` - File path to save to
///
/// # Returns
/// Result indicating success or IO error
pub fn save_test_accounts(accounts: &[TestAccount], path: &str) -> std::io::Result<()> {
    let json = serde_json::to_string_pretty(accounts)
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
    std::fs::write(path, json)
}

/// Load test accounts from a JSON file
///
/// # Arguments
/// * `path` - File path to load from
///
/// # Returns
/// Vector of test accounts or IO error
pub fn load_test_accounts(path: &str) -> std::io::Result<Vec<TestAccount>> {
    let json = std::fs::read_to_string(path)?;
    serde_json::from_str(&json)
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))
}

/// Funding transaction builder for test accounts
pub mod funding {
    use super::*;
    use scale_codec::Encode;

    /// Amount in QMHY (18 decimals)
    pub const QMHY_DECIMALS: u128 = 1_000_000_000_000_000_000;

    /// Default funding amount for test accounts (10,000 QMHY)
    pub const DEFAULT_FUNDING_AMOUNT: u128 = 10_000 * QMHY_DECIMALS;

    /// Funding request for display/manual execution
    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub struct FundingRequest {
        /// Recipient SS58 address
        pub recipient: String,
        /// Amount in raw units (18 decimals)
        pub amount_raw: u128,
        /// Amount in QMHY (human readable)
        pub amount_qmhy: f64,
        /// Suggested priority queue priority
        pub priority: i32,
    }

    /// Create funding requests for a list of test accounts
    ///
    /// # Arguments
    /// * `accounts` - Test accounts to fund
    /// * `amount_qmhy` - Amount in QMHY (will be converted to raw units)
    ///
    /// # Returns
    /// Vector of funding requests
    pub fn create_funding_requests(
        accounts: &[TestAccount],
        amount_qmhy: f64,
    ) -> Vec<FundingRequest> {
        let amount_raw = (amount_qmhy * QMHY_DECIMALS as f64) as u128;

        accounts
            .iter()
            .map(|acc| FundingRequest {
                recipient: acc.ss58_address.clone(),
                amount_raw,
                amount_qmhy,
                priority: 100, // High priority for test account funding
            })
            .collect()
    }

    /// Print funding instructions for manual execution via Polkadot.js Apps
    pub fn print_funding_instructions(accounts: &[TestAccount]) {
        println!("\n=== Fund Test Accounts via Polkadot.js Apps ===\n");
        println!("1. Connect to: wss://51.79.26.123:9944 (Alice - Sudo)");
        println!("2. Go to: Developer > Extrinsics");
        println!("3. Select account: Alice (has sudo privileges)");
        println!("4. For each account below, submit:");
        println!("   sudo > sudo > balances > transferAllowDeath\n");

        for acc in accounts {
            println!("Account: {}", acc.name);
            println!("  SS58 Address: {}", acc.ss58_address);
            println!("  Amount: {} (= 10,000 QMHY)", DEFAULT_FUNDING_AMOUNT);
            println!();
        }

        println!("After funding, verify with:");
        println!("  cargo test test_accounts_funded -- --ignored --nocapture\n");
    }
}

/// Batch operations for test accounts
pub mod batch {
    use super::*;

    /// Standard test account set for network testing
    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub struct StandardTestSet {
        /// Account for sending transactions
        pub sender: TestAccount,
        /// Account for receiving transactions
        pub receiver: TestAccount,
        /// Account for validator staking tests
        pub validator_candidate: TestAccount,
        /// Additional general purpose accounts
        pub extra: Vec<TestAccount>,
    }

    /// Generate the standard test account set
    pub fn generate_standard_test_set() -> StandardTestSet {
        StandardTestSet {
            sender: generate_test_account("test_sender"),
            receiver: generate_test_account("test_receiver"),
            validator_candidate: generate_test_account("test_validator_candidate"),
            extra: vec![
                generate_test_account("test_extra_1"),
                generate_test_account("test_extra_2"),
            ],
        }
    }

    /// Get all accounts from a standard test set as a flat vector
    pub fn flatten_test_set(set: &StandardTestSet) -> Vec<&TestAccount> {
        let mut accounts = vec![&set.sender, &set.receiver, &set.validator_candidate];
        accounts.extend(set.extra.iter());
        accounts
    }

    /// Save standard test set to file
    pub fn save_standard_test_set(set: &StandardTestSet, path: &str) -> std::io::Result<()> {
        let json = serde_json::to_string_pretty(set)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
        std::fs::write(path, json)
    }

    /// Load standard test set from file
    pub fn load_standard_test_set(path: &str) -> std::io::Result<StandardTestSet> {
        let json = std::fs::read_to_string(path)?;
        serde_json::from_str(&json)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))
    }
}

/// RPC helpers for interacting with test accounts
pub mod rpc_helpers {
    use super::*;

    /// Build a JSON-RPC request for balance query
    pub fn build_balance_request(ss58_address: &str) -> serde_json::Value {
        serde_json::json!({
            "jsonrpc": "2.0",
            "id": 1,
            "method": "gateway_balance",
            "params": [ss58_address]
        })
    }

    /// Build a JSON-RPC request for submitting a transaction
    pub fn build_submit_request(tx_hex: &str) -> serde_json::Value {
        serde_json::json!({
            "jsonrpc": "2.0",
            "id": 1,
            "method": "gateway_submit",
            "params": [tx_hex]
        })
    }

    /// Build a JSON-RPC request for getting current block number
    pub fn build_block_number_request() -> serde_json::Value {
        serde_json::json!({
            "jsonrpc": "2.0",
            "id": 1,
            "method": "chain_getHeader",
            "params": []
        })
    }

    /// Parse balance from RPC response
    pub fn parse_balance_response(response: &serde_json::Value) -> Option<u128> {
        response["result"].as_str()
            .and_then(|s| s.parse().ok())
            .or_else(|| response["result"].as_u64().map(|n| n as u128))
    }

    /// Parse block number from header response
    pub fn parse_block_number(response: &serde_json::Value) -> Option<u64> {
        response["result"]["number"]
            .as_str()
            .and_then(|s| {
                // Block number is hex encoded with 0x prefix
                let s = s.trim_start_matches("0x");
                u64::from_str_radix(s, 16).ok()
            })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_generate_account() {
        let account = generate_test_account("test_user");

        // Verify name
        assert_eq!(account.name, "test_user");

        // Verify public key is valid hex (SPHINCS+ public keys are large)
        assert!(!account.public_key.is_empty());
        let pk_bytes = hex::decode(&account.public_key).unwrap();
        assert!(pk_bytes.len() >= 64, "Public key should be at least 64 bytes");

        // Verify secret key is valid hex
        assert!(!account.secret_key.is_empty());
        let sk_bytes = hex::decode(&account.secret_key).unwrap();
        assert!(sk_bytes.len() > 0, "Secret key should not be empty");

        // Verify account ID is 32 bytes
        let account_id_bytes = hex::decode(&account.account_id).unwrap();
        assert_eq!(account_id_bytes.len(), 32, "Account ID should be 32 bytes");

        // Verify SS58 address starts with expected prefix
        assert!(account.ss58_address.starts_with("5"), "SS58 should start with '5'");

        // Verify timestamp is set
        assert!(account.created_at > 0);
    }

    #[test]
    fn test_account_deterministic_derivation() {
        // Generate two accounts with different names
        let account1 = generate_test_account("alice_test");
        let account2 = generate_test_account("bob_test");

        // They should have different keys and addresses
        assert_ne!(account1.public_key, account2.public_key);
        assert_ne!(account1.account_id, account2.account_id);
        assert_ne!(account1.ss58_address, account2.ss58_address);
    }

    #[test]
    fn test_account_serialization() {
        let account = generate_test_account("serialization_test");

        // Serialize to JSON
        let json = serde_json::to_string(&account).unwrap();

        // Deserialize back
        let deserialized: TestAccount = serde_json::from_str(&json).unwrap();

        // Verify all fields match
        assert_eq!(account.name, deserialized.name);
        assert_eq!(account.public_key, deserialized.public_key);
        assert_eq!(account.secret_key, deserialized.secret_key);
        assert_eq!(account.account_id, deserialized.account_id);
        assert_eq!(account.ss58_address, deserialized.ss58_address);
    }

    #[test]
    fn test_funding_request_creation() {
        let accounts = vec![
            generate_test_account("fund_test_1"),
            generate_test_account("fund_test_2"),
        ];

        let requests = funding::create_funding_requests(&accounts, 100.0);

        assert_eq!(requests.len(), 2);
        assert_eq!(requests[0].recipient, accounts[0].ss58_address);
        assert_eq!(requests[0].amount_qmhy, 100.0);
        assert_eq!(requests[0].amount_raw, 100 * funding::QMHY_DECIMALS);
    }

    #[test]
    fn test_standard_test_set() {
        let set = batch::generate_standard_test_set();

        // Verify all accounts are present
        assert_eq!(set.sender.name, "test_sender");
        assert_eq!(set.receiver.name, "test_receiver");
        assert_eq!(set.validator_candidate.name, "test_validator_candidate");
        assert_eq!(set.extra.len(), 2);

        // Verify all accounts have unique addresses
        let flattened = batch::flatten_test_set(&set);
        let addresses: Vec<_> = flattened.iter().map(|a| &a.ss58_address).collect();
        let unique_count = addresses.iter().collect::<std::collections::HashSet<_>>().len();
        assert_eq!(unique_count, flattened.len(), "All accounts should have unique addresses");
    }

    #[test]
    fn test_rpc_helpers() {
        let balance_req = rpc_helpers::build_balance_request("5GrwvaEF5zXb26Fz9rcQpDWS57CtERHpNehXCPcNoHGKutQY");
        assert_eq!(balance_req["method"], "gateway_balance");

        let block_req = rpc_helpers::build_block_number_request();
        assert_eq!(block_req["method"], "chain_getHeader");

        // Test parsing
        let balance_response = serde_json::json!({
            "result": "1000000000000000000000"
        });
        let balance = rpc_helpers::parse_balance_response(&balance_response);
        assert!(balance.is_some());

        let block_response = serde_json::json!({
            "result": {
                "number": "0x1234"
            }
        });
        let block_num = rpc_helpers::parse_block_number(&block_response);
        assert_eq!(block_num, Some(0x1234));
    }
}
