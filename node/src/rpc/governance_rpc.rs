//! Governance & Rewards RPC
//!
//! Provides RPC methods for dashboard integration with validator governance and rewards pallets.
//!
//! Methods:
//! - `quantumharmony_submitSignedExtrinsic` - Submit any SPHINCS+ signed extrinsic
//! - `quantumharmony_getGovernanceStats` - Get governance proposal statistics
//! - `quantumharmony_getProposals` - Get active proposals
//! - `quantumharmony_getRewardsInfo` - Get rewards and staking info
//! - `quantumharmony_getValidatorSet` - Get current validator set

use jsonrpsee::{
    core::{async_trait, RpcResult},
    proc_macros::rpc,
    types::error::{ErrorCode, ErrorObject},
};
use scale_codec::{Encode, Decode, Compact};
use sp_core::{
    sphincs::{Pair as SphincsPair, SignatureWithPublic},
    Pair,
    H256,
};
use sp_runtime::{
    generic::Era,
    traits::{Block as BlockT, IdentifyAccount},
    AccountId32,
    transaction_validity::TransactionSource,
    MultiSignature,
};
use sc_transaction_pool_api::TransactionPool;
use sp_api::{ProvideRuntimeApi, Core};
use sp_blockchain::HeaderBackend;
use std::sync::Arc;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use frame_system_rpc_runtime_api::AccountNonceApi;
use substrate_frame_rpc_system::AccountNonceApi as SystemAccountNonceApi;

/// Generic signed extrinsic request
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SignedExtrinsicRequest {
    /// Encoded call data (hex with 0x prefix)
    /// Format: pallet_index (1 byte) + call_index (1 byte) + encoded_args
    #[serde(rename = "callData")]
    pub call_data: String,
    /// SPHINCS+ signer's 128-byte secret key (hex with 0x prefix)
    /// For dev mode, can use 48-byte seed for test accounts
    #[serde(rename = "signerKey")]
    pub signer_key: String,
    /// Transaction nonce (if not provided, will query from chain)
    pub nonce: Option<u32>,
}

/// Governance statistics response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GovernanceStats {
    pub active_proposals: u32,
    pub total_proposals: u32,
    pub voting_period: u32,
    pub min_votes_required: u32,
}

/// Proposal info
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProposalInfo {
    pub id: u32,
    pub proposer: String,
    pub proposed_validator: String,
    pub votes_for: u32,
    pub votes_against: u32,
    pub block_number: u32,
    pub status: String,
}

/// Rewards info response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RewardsInfo {
    pub pending_rewards: String,
    pub total_staked: String,
    pub certification_level: String,
    pub reward_multiplier: String,
}

/// Validator info
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ValidatorInfo {
    pub account: String,
    pub is_active: bool,
    pub session_key: Option<String>,
}

/// Governance & Rewards RPC interface
#[rpc(client, server)]
pub trait GovernanceApi<BlockHash> {
    /// Submit a SPHINCS+ signed extrinsic
    ///
    /// This is a generic method that can submit any extrinsic:
    /// - Governance: propose, vote, finalize
    /// - Rewards: stake, unstake, claim
    /// - Any other pallet call
    #[method(name = "quantumharmony_submitSignedExtrinsic")]
    async fn submit_signed_extrinsic(&self, request: Value) -> RpcResult<Value>;

    /// Get governance statistics
    #[method(name = "quantumharmony_getGovernanceStats")]
    async fn get_governance_stats(&self) -> RpcResult<GovernanceStats>;

    /// Get active proposals
    #[method(name = "quantumharmony_getProposals")]
    async fn get_proposals(&self) -> RpcResult<Vec<ProposalInfo>>;

    /// Get rewards info for an account
    #[method(name = "quantumharmony_getRewardsInfo")]
    async fn get_rewards_info(&self, account: String) -> RpcResult<RewardsInfo>;

    /// Get current validator set
    #[method(name = "quantumharmony_getValidatorSet")]
    async fn get_validator_set(&self) -> RpcResult<Vec<ValidatorInfo>>;
}

/// Governance RPC implementation
pub struct GovernanceRpc<C, P, Block> {
    client: Arc<C>,
    pool: Arc<P>,
    _phantom: std::marker::PhantomData<Block>,
}

impl<C, P, Block> GovernanceRpc<C, P, Block>
where
    Block: BlockT,
    C: ProvideRuntimeApi<Block>,
{
    pub fn new(client: Arc<C>, pool: Arc<P>) -> Self {
        Self {
            client,
            pool,
            _phantom: std::marker::PhantomData,
        }
    }

    /// Get SPHINCS+ keypair from secret key
    ///
    /// Accepts ONLY the full 128-byte SPHINCS+ secret key.
    /// The 48-byte seed format is deprecated and no longer supported.
    fn get_keypair(&self, secret_key: &str) -> Result<SphincsPair, String> {
        let key_bytes = hex::decode(secret_key.trim_start_matches("0x"))
            .map_err(|e| format!("Invalid secret key hex: {}", e))?;

        match key_bytes.len() {
            // Full 128-byte secret key (PRODUCTION)
            128 => {
                log::info!("   GOVERNANCE RPC: Using full 128-byte SPHINCS+ secret key");
                let secret: [u8; 128] = key_bytes.try_into()
                    .map_err(|_| "Failed to convert secret key to fixed array")?;
                Ok(SphincsPair::from_secret(secret))
            },

            // 48-byte seed is DEPRECATED - no longer supported
            48 => {
                Err("48-byte seed format is deprecated. Please use the full 128-byte SPHINCS+ secret key (secret_hex from your validator config).".to_string())
            },

            other => Err(format!(
                "Invalid key size: {} bytes. Expected 128-byte SPHINCS+ secret key.",
                other
            )),
        }
    }
}

#[async_trait]
impl<C, P, Block> GovernanceApiServer<Block::Hash> for GovernanceRpc<C, P, Block>
where
    Block: BlockT,
    C: Send + Sync + 'static + HeaderBackend<Block> + ProvideRuntimeApi<Block>,
    C::Api: sp_block_builder::BlockBuilder<Block>
        + sp_api::Core<Block>
        + substrate_frame_rpc_system::AccountNonceApi<Block, AccountId32, u32>
        + frame_system_rpc_runtime_api::AccountNonceApi<Block, AccountId32, u32>,
    P: TransactionPool<Block = Block> + 'static,
{
    async fn submit_signed_extrinsic(&self, request: Value) -> RpcResult<Value> {
        // Parse request - supports both JSON object and positional array formats
        let req: SignedExtrinsicRequest = if request.is_array() {
            // Positional format: [callData, signerKey] or [callData, signerKey, nonce]
            let arr = request.as_array().unwrap();
            if arr.len() < 2 {
                return Err(ErrorObject::owned(
                    ErrorCode::InvalidParams.code(),
                    "Expected [callData, signerKey] or [callData, signerKey, nonce]",
                    None::<()>
                ));
            }
            SignedExtrinsicRequest {
                call_data: arr[0].as_str().unwrap_or("").to_string(),
                signer_key: arr[1].as_str().unwrap_or("").to_string(),
                nonce: arr.get(2).and_then(|v| v.as_u64()).map(|n| n as u32),
            }
        } else {
            // JSON object format: { callData, signerKey, nonce? }
            serde_json::from_value(request)
                .map_err(|e| ErrorObject::owned(
                    ErrorCode::InvalidParams.code(),
                    format!("Invalid request: {}", e),
                    None::<()>
                ))?
        };

        log::info!("🏛️ Governance RPC: Submitting signed extrinsic");
        log::info!("   Call data: {}...", &req.call_data[..std::cmp::min(40, req.call_data.len())]);

        // Get keypair
        let keypair = self.get_keypair(&req.signer_key)
            .map_err(|e| ErrorObject::owned(
                ErrorCode::InternalError.code(),
                format!("Failed to get keypair: {}", e),
                None::<()>
            ))?;

        // Derive signer account
        use sp_runtime::MultiSigner;
        let keypair_public = keypair.public();
        let signer_account = MultiSigner::from(keypair_public.clone()).into_account();

        log::info!("   Signer account: {:?}", signer_account);

        // Decode call data
        let call_bytes = hex::decode(req.call_data.trim_start_matches("0x"))
            .map_err(|e| ErrorObject::owned(
                ErrorCode::InvalidParams.code(),
                format!("Invalid call data hex: {}", e),
                None::<()>
            ))?;

        // Decode as RuntimeCall
        use quantumharmony_runtime::RuntimeCall;
        let call = RuntimeCall::decode(&mut &call_bytes[..])
            .map_err(|e| ErrorObject::owned(
                ErrorCode::InvalidParams.code(),
                format!("Failed to decode call: {}", e),
                None::<()>
            ))?;

        log::info!("   Decoded call successfully");

        // Get nonce
        let best_hash = self.client.info().best_hash;
        let nonce = if let Some(n) = req.nonce {
            n
        } else {
            self.client.runtime_api()
                .account_nonce(best_hash, signer_account.clone())
                .map_err(|e| ErrorObject::owned(
                    ErrorCode::InternalError.code(),
                    format!("Failed to get nonce: {}", e),
                    None::<()>
                ))?
        };

        log::info!("   Nonce: {}", nonce);

        // Get runtime version and genesis hash
        let genesis_hash = sp_core::H256::from_slice(self.client.info().genesis_hash.as_ref());
        let runtime_version = self.client.runtime_api()
            .version(best_hash)
            .map_err(|e| ErrorObject::owned(
                ErrorCode::InternalError.code(),
                format!("Failed to get runtime version: {}", e),
                None::<()>
            ))?;

        // Build signed extra
        let extra: quantumharmony_runtime::SignedExtra = (
            frame_system::CheckNonZeroSender::<quantumharmony_runtime::Runtime>::new(),
            frame_system::CheckSpecVersion::<quantumharmony_runtime::Runtime>::new(),
            frame_system::CheckTxVersion::<quantumharmony_runtime::Runtime>::new(),
            frame_system::CheckGenesis::<quantumharmony_runtime::Runtime>::new(),
            frame_system::CheckEra::<quantumharmony_runtime::Runtime>::from(Era::Immortal),
            frame_system::CheckNonce::<quantumharmony_runtime::Runtime>::from(nonce),
            frame_system::CheckWeight::<quantumharmony_runtime::Runtime>::new(),
            pallet_transaction_payment::ChargeTransactionPayment::<quantumharmony_runtime::Runtime>::from(0),
        );

        // Create signed payload
        use quantumharmony_runtime::SignedPayload;
        let raw_payload = SignedPayload::from_raw(
            call.clone(),
            extra.clone(),
            (
                (),
                runtime_version.spec_version,
                runtime_version.transaction_version,
                genesis_hash,
                genesis_hash,
                (),
                (),
                (),
            ),
        );

        // Sign with SPHINCS+
        let signature = raw_payload.using_encoded(|payload| keypair.sign(payload));
        let sig_with_pub = SignatureWithPublic::new(signature, keypair.public());
        let sphincs_signature = MultiSignature::SphincsPlus(sig_with_pub);

        // Build extrinsic
        use quantumharmony_runtime::UncheckedExtrinsic;
        let extrinsic = UncheckedExtrinsic::new_signed(
            call,
            sp_runtime::MultiAddress::Id(signer_account.clone()),
            sphincs_signature,
            extra,
        );

        // Submit to pool
        let encoded_extrinsic = extrinsic.encode();
        let block_extrinsic = Block::Extrinsic::decode(&mut &encoded_extrinsic[..])
            .map_err(|e| ErrorObject::owned(
                ErrorCode::InternalError.code(),
                format!("Failed to decode extrinsic: {}", e),
                None::<()>
            ))?;

        let tx_hash = self.pool
            .submit_one(best_hash, TransactionSource::Local, block_extrinsic)
            .await
            .map_err(|e| ErrorObject::owned(
                ErrorCode::InternalError.code(),
                format!("Failed to submit: {}", e),
                None::<()>
            ))?;

        log::info!("✅ Governance extrinsic submitted: {:?}", tx_hash);

        Ok(serde_json::json!({
            "success": true,
            "hash": format!("{:?}", tx_hash),
            "status": "pending",
            "signer": format!("{:?}", signer_account),
            "nonce": nonce
        }))
    }

    async fn get_governance_stats(&self) -> RpcResult<GovernanceStats> {
        log::info!("🏛️ Governance RPC: Getting governance stats");

        // Query NextProposalId storage
        // Storage key: twox128("ValidatorGovernance") + twox128("NextProposalId")
        let best_hash = self.client.info().best_hash;

        // For now, return placeholder data
        // Full implementation would query runtime storage
        Ok(GovernanceStats {
            active_proposals: 0,
            total_proposals: 0,
            voting_period: 10,
            min_votes_required: 1,
        })
    }

    async fn get_proposals(&self) -> RpcResult<Vec<ProposalInfo>> {
        log::info!("🏛️ Governance RPC: Getting proposals");

        // For now, return empty list
        // Full implementation would iterate over Proposals storage map
        Ok(vec![])
    }

    async fn get_rewards_info(&self, account: String) -> RpcResult<RewardsInfo> {
        log::info!("🏛️ Governance RPC: Getting rewards for {}", account);

        // For now, return placeholder data
        // Full implementation would query ValidatorRewards storage
        Ok(RewardsInfo {
            pending_rewards: "0 QHM".to_string(),
            total_staked: "0 QHM".to_string(),
            certification_level: "Uncertified".to_string(),
            reward_multiplier: "70%".to_string(),
        })
    }

    async fn get_validator_set(&self) -> RpcResult<Vec<ValidatorInfo>> {
        log::info!("🏛️ Governance RPC: Getting validator set");

        // For now, return the known validators
        Ok(vec![
            ValidatorInfo {
                account: "Alice".to_string(),
                is_active: true,
                session_key: None,
            },
            ValidatorInfo {
                account: "Bob".to_string(),
                is_active: true,
                session_key: None,
            },
            ValidatorInfo {
                account: "Charlie".to_string(),
                is_active: true,
                session_key: None,
            },
        ])
    }
}
