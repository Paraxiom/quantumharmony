//! MeshForum RPC
//!
//! Provides RPC methods for on-chain forum messaging between validators.
//!
//! Methods:
//! - `forum_postMessage` - Post a message to the on-chain forum
//! - `forum_getMessages` - Get all forum messages
//! - `forum_getMessageCount` - Get total message count

use jsonrpsee::{
    core::{async_trait, RpcResult},
    proc_macros::rpc,
    types::error::{ErrorCode, ErrorObject},
};
use scale_codec::{Encode, Decode};
use sp_core::{
    sphincs::{Pair as SphincsPair, SignatureWithPublic},
    Pair,
};
use sp_runtime::{
    generic::Era,
    traits::{Block as BlockT, IdentifyAccount},
    AccountId32,
    transaction_validity::TransactionSource,
    MultiSignature, MultiSigner,
};
use sc_transaction_pool_api::TransactionPool;
use sp_api::{ProvideRuntimeApi, Core};
use sp_blockchain::HeaderBackend;
use std::sync::Arc;
use serde::{Deserialize, Serialize};
use frame_system_rpc_runtime_api::AccountNonceApi;
use pallet_mesh_forum::runtime_api::MeshForumApi as MeshForumRuntimeApi;

/// Post message request
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PostMessageRequest {
    /// Message content (max 1024 chars)
    pub content: String,
    /// SPHINCS+ signer key (128 bytes hex) - optional, uses default if not provided
    #[serde(rename = "signerKey")]
    pub signer_key: Option<String>,
}

/// Forum message response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ForumMessage {
    pub id: u32,
    pub sender: String,
    pub content: String,
    pub block: u32,
    pub timestamp: u64,
}

/// Post message response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PostMessageResponse {
    pub success: bool,
    #[serde(rename = "txHash")]
    pub tx_hash: String,
    pub content: String,
    pub sender: String,
    pub status: String,
}

/// RPC trait for MeshForum
#[rpc(server, client)]
pub trait MeshForumApi<BlockHash> {
    /// Post a message to the on-chain forum
    #[method(name = "forum_postMessage")]
    async fn post_message(&self, request: PostMessageRequest) -> RpcResult<PostMessageResponse>;

    /// Get all forum messages
    #[method(name = "forum_getMessages")]
    async fn get_messages(&self, limit: Option<u32>, offset: Option<u32>) -> RpcResult<Vec<ForumMessage>>;

    /// Get total message count
    #[method(name = "forum_getMessageCount")]
    async fn get_message_count(&self) -> RpcResult<u32>;
}

/// MeshForum RPC implementation
pub struct MeshForumRpc<C, P, Block> {
    client: Arc<C>,
    pool: Arc<P>,
    _marker: std::marker::PhantomData<Block>,
}

impl<C, P, Block> MeshForumRpc<C, P, Block>
where
    Block: BlockT,
    C: ProvideRuntimeApi<Block>,
{
    pub fn new(client: Arc<C>, pool: Arc<P>) -> Self {
        Self {
            client,
            pool,
            _marker: std::marker::PhantomData,
        }
    }

    fn get_keypair(&self, secret_key: &str) -> Result<SphincsPair, String> {
        let key_bytes = hex::decode(secret_key.trim_start_matches("0x"))
            .map_err(|e| format!("Invalid secret key hex: {}", e))?;

        match key_bytes.len() {
            128 => {
                let secret: [u8; 128] = key_bytes.try_into()
                    .map_err(|_| "Failed to convert secret key")?;
                Ok(SphincsPair::from_secret(secret))
            },
            other => Err(format!(
                "Invalid key size: {} bytes. Expected 128-byte SPHINCS+ secret key.",
                other
            )),
        }
    }
}

// Default dev key for forum posting
const DEV_FORUM_SEED: &str = "//ForumDev";

#[async_trait]
impl<C, P, Block> MeshForumApiServer<Block::Hash> for MeshForumRpc<C, P, Block>
where
    Block: BlockT,
    C: Send + Sync + 'static + HeaderBackend<Block> + ProvideRuntimeApi<Block>,
    C::Api: sp_block_builder::BlockBuilder<Block>
        + Core<Block>
        + substrate_frame_rpc_system::AccountNonceApi<Block, AccountId32, u32>
        + frame_system_rpc_runtime_api::AccountNonceApi<Block, AccountId32, u32>
        + MeshForumRuntimeApi<Block, AccountId32>,
    P: TransactionPool<Block = Block> + 'static,
{
    async fn post_message(&self, request: PostMessageRequest) -> RpcResult<PostMessageResponse> {
        log::info!("📝 MeshForum RPC: Posting message");

        // Validate content
        if request.content.is_empty() {
            return Err(ErrorObject::owned(
                ErrorCode::InvalidParams.code(),
                "Message content cannot be empty",
                None::<()>,
            ));
        }

        if request.content.len() > 1024 {
            return Err(ErrorObject::owned(
                ErrorCode::InvalidParams.code(),
                "Message too long (max 1024 characters)",
                None::<()>,
            ));
        }

        // Get or create signing keypair
        let keypair = if let Some(ref key_hex) = request.signer_key {
            self.get_keypair(key_hex)
                .map_err(|e| ErrorObject::owned(
                    ErrorCode::InvalidParams.code(),
                    e,
                    None::<()>,
                ))?
        } else {
            // Use dev key
            SphincsPair::from_string(DEV_FORUM_SEED, None)
                .map_err(|_| ErrorObject::owned(
                    ErrorCode::InternalError.code(),
                    "Failed to derive dev key",
                    None::<()>,
                ))?
        };

        // Derive signer account
        let signer_account = MultiSigner::from(keypair.public()).into_account();

        log::info!("   Sender: {:?}", signer_account);
        log::info!("   Content: {}...", &request.content[..std::cmp::min(50, request.content.len())]);

        // Build call for MeshForum::post_message
        use quantumharmony_runtime::RuntimeCall;
        let content_bytes = request.content.as_bytes().to_vec();
        let call = RuntimeCall::MeshForum(pallet_mesh_forum::Call::post_message {
            content: content_bytes,
        });

        // Get nonce
        let best_hash = self.client.info().best_hash;
        let nonce = self.client.runtime_api()
            .account_nonce(best_hash, signer_account.clone())
            .map_err(|e| ErrorObject::owned(
                ErrorCode::InternalError.code(),
                format!("Failed to get nonce: {}", e),
                None::<()>,
            ))?;

        // Get runtime version and genesis hash
        let genesis_hash = sp_core::H256::from_slice(self.client.info().genesis_hash.as_ref());
        let runtime_version = self.client.runtime_api()
            .version(best_hash)
            .map_err(|e| ErrorObject::owned(
                ErrorCode::InternalError.code(),
                format!("Failed to get runtime version: {}", e),
                None::<()>,
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
                None::<()>,
            ))?;

        let tx_hash = self.pool
            .submit_one(best_hash, TransactionSource::Local, block_extrinsic)
            .await
            .map_err(|e| ErrorObject::owned(
                ErrorCode::InternalError.code(),
                format!("Failed to submit: {}", e),
                None::<()>,
            ))?;

        log::info!("✅ Forum message submitted: {:?}", tx_hash);

        Ok(PostMessageResponse {
            success: true,
            tx_hash: format!("{:?}", tx_hash),
            content: request.content,
            sender: format!("{}", signer_account),
            status: "pending".to_string(),
        })
    }

    async fn get_messages(&self, limit: Option<u32>, offset: Option<u32>) -> RpcResult<Vec<ForumMessage>> {
        let limit = limit.unwrap_or(50);
        let offset = offset.unwrap_or(0);
        let best_hash = self.client.info().best_hash;

        let messages = self.client.runtime_api()
            .get_messages(best_hash, limit, offset)
            .map_err(|e| ErrorObject::owned(
                ErrorCode::InternalError.code(),
                format!("Failed to get messages: {}", e),
                None::<()>,
            ))?;

        Ok(messages
            .into_iter()
            .map(|(id, sender, block, content)| {
                ForumMessage {
                    id,
                    sender: format!("{}", sender),
                    content: String::from_utf8_lossy(&content).to_string(),
                    block,
                    timestamp: 0, // Block time not available in storage
                }
            })
            .collect())
    }

    async fn get_message_count(&self) -> RpcResult<u32> {
        let best_hash = self.client.info().best_hash;

        self.client.runtime_api()
            .message_count(best_hash)
            .map_err(|e| ErrorObject::owned(
                ErrorCode::InternalError.code(),
                format!("Failed to get message count: {}", e),
                None::<()>,
            ))
    }
}
