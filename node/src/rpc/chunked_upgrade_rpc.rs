//! Chunked Runtime Upgrade RPC
//!
//! RPC interface for uploading runtime upgrades in chunks to bypass BlockLength limits.
//!
//! ## Flow
//! 1. Client calls `initiate_chunked_upgrade` with WASM hash and chunk count
//! 2. Client uploads each chunk via `upload_chunk` (each chunk signed with SPHINCS+)
//! 3. Client calls `finalize_chunked_upgrade` to assemble and apply the upgrade
//!
//! Each chunk transaction is ~115KB (64KB data + 50KB SPHINCS+ signature + overhead),
//! well under the 256KB BlockLength limit.

use jsonrpsee::{
    core::{async_trait, RpcResult},
    proc_macros::rpc,
    types::error::ErrorObject,
};
use jsonrpsee_types::ErrorObjectOwned;
use sp_api::{Core, ProvideRuntimeApi};
use sp_blockchain::HeaderBackend;
use sp_runtime::traits::Block as BlockT;
use quantumharmony_runtime::{RuntimeCall, Runtime, SignedExtra, SignedPayload, UncheckedExtrinsic};
use sc_transaction_pool_api::{TransactionPool, TransactionSource};
use scale_codec::{Encode, Decode};
use std::sync::Arc;
use log;
use hex;

use sp_core::{Pair, sphincs::Pair as SphincsPair, sphincs::SignatureWithPublic, H256};
use sp_core::crypto::AccountId32;
use frame_system_rpc_runtime_api::AccountNonceApi;
use sp_runtime::{generic::Era, MultiAddress, MultiSignature};

use pallet_runtime_segmentation::chunked_upgrade::{MAX_CHUNK_SIZE, MAX_CHUNKS};

/// Chunked upgrade status
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct ChunkedUpgradeStatus {
    pub upgrade_id: String,
    pub chunks_received: u8,
    pub total_chunks: u8,
    pub expected_size: u32,
    pub ready_to_finalize: bool,
}

#[rpc(client, server)]
pub trait ChunkedUpgradeApi {
    /// Initiate a chunked runtime upgrade
    ///
    /// # Parameters
    /// - `wasm_hex`: Complete WASM blob (hex encoded) - will be split into chunks
    /// - `secret_key`: SPHINCS+ 128-byte secret key (hex encoded)
    ///
    /// # Returns
    /// Upgrade ID and number of chunks to upload
    #[method(name = "chunkedUpgrade_initiate")]
    async fn initiate_chunked_upgrade(
        &self,
        wasm_hex: String,
        secret_key: String,
    ) -> RpcResult<ChunkedUpgradeStatus>;

    /// Upload a single chunk
    ///
    /// # Parameters
    /// - `chunk_index`: 0-based index of this chunk
    /// - `chunk_hex`: Chunk data (hex encoded)
    /// - `secret_key`: SPHINCS+ 128-byte secret key (hex encoded)
    ///
    /// # Returns
    /// Transaction hash
    #[method(name = "chunkedUpgrade_uploadChunk")]
    async fn upload_chunk(
        &self,
        chunk_index: u8,
        chunk_hex: String,
        secret_key: String,
    ) -> RpcResult<String>;

    /// Finalize the chunked upgrade
    ///
    /// # Parameters
    /// - `secret_key`: SPHINCS+ 128-byte secret key (hex encoded)
    ///
    /// # Returns
    /// Transaction hash
    #[method(name = "chunkedUpgrade_finalize")]
    async fn finalize_chunked_upgrade(
        &self,
        secret_key: String,
    ) -> RpcResult<String>;

    /// Get current upgrade status
    #[method(name = "chunkedUpgrade_status")]
    async fn get_status(&self) -> RpcResult<Option<ChunkedUpgradeStatus>>;

    /// Cancel pending upgrade
    #[method(name = "chunkedUpgrade_cancel")]
    async fn cancel_upgrade(
        &self,
        secret_key: String,
    ) -> RpcResult<String>;

    /// Calculate how many chunks are needed for a WASM of given size
    #[method(name = "chunkedUpgrade_calculateChunks")]
    async fn calculate_chunks(&self, wasm_size: u32) -> RpcResult<u8>;
}

use std::sync::atomic::{AtomicU32, Ordering};

pub struct ChunkedUpgradeRpc<C, P, Block> {
    client: Arc<C>,
    pool: Arc<P>,
    /// Track pending nonce adjustments for transactions not yet in blocks
    pending_nonce_offset: AtomicU32,
    _phantom: std::marker::PhantomData<Block>,
}

impl<C, P, Block> ChunkedUpgradeRpc<C, P, Block> {
    pub fn new(client: Arc<C>, pool: Arc<P>) -> Self {
        Self {
            client,
            pool,
            pending_nonce_offset: AtomicU32::new(0),
            _phantom: std::marker::PhantomData,
        }
    }

    /// Reset the pending nonce offset (call when starting a new upgrade session)
    fn reset_nonce_offset(&self) {
        self.pending_nonce_offset.store(0, Ordering::SeqCst);
    }

    /// Get the next nonce offset and increment it
    fn get_and_increment_nonce_offset(&self) -> u32 {
        self.pending_nonce_offset.fetch_add(1, Ordering::SeqCst)
    }
}

#[async_trait]
impl<C, P, Block> ChunkedUpgradeApiServer for ChunkedUpgradeRpc<C, P, Block>
where
    Block: BlockT,
    C: Send + Sync + 'static + ProvideRuntimeApi<Block> + HeaderBackend<Block>,
    C::Api: AccountNonceApi<Block, AccountId32, u32> + Core<Block>,
    P: Send + Sync + 'static + TransactionPool<Block = Block>,
{
    async fn initiate_chunked_upgrade(
        &self,
        wasm_hex: String,
        secret_key: String,
    ) -> RpcResult<ChunkedUpgradeStatus> {
        log::info!("🔄 Chunked upgrade initiation requested");

        // Reset nonce offset for new upgrade session
        self.reset_nonce_offset();

        // Decode WASM
        let wasm_code = hex::decode(wasm_hex.trim_start_matches("0x"))
            .map_err(|e| error_object(-32602, format!("Invalid WASM hex: {}", e)))?;

        let wasm_size = wasm_code.len() as u32;
        log::info!("   WASM size: {} bytes ({} KB)", wasm_size, wasm_size / 1024);

        // Calculate chunks needed
        let total_chunks = ((wasm_size + MAX_CHUNK_SIZE - 1) / MAX_CHUNK_SIZE) as u8;
        if total_chunks > MAX_CHUNKS as u8 {
            return Err(error_object(-32602, format!(
                "WASM too large: {} bytes requires {} chunks, max is {}",
                wasm_size, total_chunks, MAX_CHUNKS
            )));
        }

        log::info!("   Will split into {} chunks of max {}KB each", total_chunks, MAX_CHUNK_SIZE / 1024);

        // Calculate WASM hash
        let wasm_hash = sp_core::hashing::blake2_256(&wasm_code);
        let wasm_hash_h256 = H256::from_slice(&wasm_hash);

        log::info!("   WASM hash: 0x{}", hex::encode(&wasm_hash));

        // Load keypair
        let keypair = load_sphincs_keypair(&secret_key)?;
        log::info!("   SPHINCS+ keypair loaded");

        // Build the initiate_chunked_upgrade call
        // ChunkedUpgrade::initiate_chunked_upgrade(total_chunks, expected_size, wasm_hash, chunk_hashes, chunk_sizes)
        let call = RuntimeCall::ChunkedUpgrade(
            pallet_runtime_segmentation::chunked_upgrade::pallet::Call::initiate_chunked_upgrade {
                total_chunks,
                expected_size: wasm_size,
                wasm_hash: wasm_hash_h256,
                chunk_hashes: None,  // Optional: will be verified if provided
                chunk_sizes: None,   // Optional: will be verified if provided
            }
        );

        // Submit transaction
        let tx_hash = self.submit_sudo_call(call, &keypair).await?;

        log::info!("✅ Chunked upgrade initiated: {}", tx_hash);

        Ok(ChunkedUpgradeStatus {
            upgrade_id: format!("0x{}", hex::encode(&wasm_hash)),
            chunks_received: 0,
            total_chunks,
            expected_size: wasm_size,
            ready_to_finalize: false,
        })
    }

    async fn upload_chunk(
        &self,
        chunk_index: u8,
        chunk_hex: String,
        secret_key: String,
    ) -> RpcResult<String> {
        log::info!("📦 Uploading chunk {}", chunk_index);

        // Decode chunk data
        let chunk_data = hex::decode(chunk_hex.trim_start_matches("0x"))
            .map_err(|e| error_object(-32602, format!("Invalid chunk hex: {}", e)))?;

        if chunk_data.len() > MAX_CHUNK_SIZE as usize {
            return Err(error_object(-32602, format!(
                "Chunk too large: {} bytes, max is {}",
                chunk_data.len(), MAX_CHUNK_SIZE
            )));
        }

        log::info!("   Chunk {} size: {} bytes", chunk_index, chunk_data.len());

        // Load keypair
        let keypair = load_sphincs_keypair(&secret_key)?;

        // Build the upload_chunk call
        let call = RuntimeCall::ChunkedUpgrade(
            pallet_runtime_segmentation::chunked_upgrade::pallet::Call::upload_chunk {
                chunk_index,
                chunk_data,
            }
        );

        // Submit transaction
        let tx_hash = self.submit_sudo_call(call, &keypair).await?;

        log::info!("✅ Chunk {} uploaded: {}", chunk_index, tx_hash);

        Ok(tx_hash)
    }

    async fn finalize_chunked_upgrade(
        &self,
        secret_key: String,
    ) -> RpcResult<String> {
        log::info!("🚀 Finalizing chunked upgrade");

        // Load keypair
        let keypair = load_sphincs_keypair(&secret_key)?;

        // Build the finalize_chunked_upgrade call
        let call = RuntimeCall::ChunkedUpgrade(
            pallet_runtime_segmentation::chunked_upgrade::pallet::Call::finalize_chunked_upgrade {}
        );

        // Submit transaction
        let tx_hash = self.submit_sudo_call(call, &keypair).await?;

        log::info!("✅ Chunked upgrade finalized: {}", tx_hash);

        Ok(tx_hash)
    }

    async fn get_status(&self) -> RpcResult<Option<ChunkedUpgradeStatus>> {
        // NOTE: Returns None; runtime state query requires ChunkedUpgrade pallet storage reader
        // Placeholder until pallet integration complete
        Ok(None)
    }

    async fn cancel_upgrade(
        &self,
        secret_key: String,
    ) -> RpcResult<String> {
        log::info!("❌ Cancelling chunked upgrade");

        // Reset nonce offset
        self.reset_nonce_offset();

        // Load keypair
        let keypair = load_sphincs_keypair(&secret_key)?;

        // Build the cancel call
        let call = RuntimeCall::ChunkedUpgrade(
            pallet_runtime_segmentation::chunked_upgrade::pallet::Call::cancel_chunked_upgrade {}
        );

        // Submit transaction
        let tx_hash = self.submit_sudo_call(call, &keypair).await?;

        log::info!("✅ Chunked upgrade cancelled: {}", tx_hash);

        Ok(tx_hash)
    }

    async fn calculate_chunks(&self, wasm_size: u32) -> RpcResult<u8> {
        let chunks = ((wasm_size + MAX_CHUNK_SIZE - 1) / MAX_CHUNK_SIZE) as u8;
        Ok(chunks)
    }
}

impl<C, P, Block> ChunkedUpgradeRpc<C, P, Block>
where
    Block: BlockT,
    C: Send + Sync + 'static + ProvideRuntimeApi<Block> + HeaderBackend<Block>,
    C::Api: AccountNonceApi<Block, AccountId32, u32> + Core<Block>,
    P: Send + Sync + 'static + TransactionPool<Block = Block>,
{
    /// Submit a sudo-wrapped call with SPHINCS+ signature
    async fn submit_sudo_call(
        &self,
        inner_call: RuntimeCall,
        keypair: &SphincsPair,
    ) -> RpcResult<String> {
        use frame_support::weights::Weight;
        use quantumharmony_runtime::SudoCall;

        // Wrap in sudo.sudoUncheckedWeight
        let call = RuntimeCall::Sudo(
            SudoCall::sudo_unchecked_weight {
                call: Box::new(inner_call),
                weight: Weight::from_parts(0, 0),
            }
        );

        // Get signer account
        use sp_runtime::traits::IdentifyAccount;
        use sp_runtime::MultiSigner;
        let public_key = keypair.public();
        log::info!("   DEBUG: Public key (first 16 bytes): {:02x?}", &public_key.as_ref()[..16]);
        log::info!("   DEBUG: Public key (full): 0x{}", hex::encode(public_key.as_ref()));
        let signer_account = MultiSigner::from(public_key).into_account();
        log::info!("   DEBUG: Signer AccountId: 0x{}", hex::encode(AsRef::<[u8; 32]>::as_ref(&signer_account)));

        // Get nonce from chain + pending offset
        let best_hash = self.client.info().best_hash;
        let on_chain_nonce = self.client
            .runtime_api()
            .account_nonce(best_hash, signer_account.clone())
            .map_err(|e| error_object(-32603, format!("Failed to get nonce: {}", e)))?;

        // Add offset for pending transactions
        let nonce_offset = self.get_and_increment_nonce_offset();
        let nonce = on_chain_nonce + nonce_offset;
        log::info!("   Using nonce {} (on-chain: {}, offset: {})", nonce, on_chain_nonce, nonce_offset);

        // Get genesis hash
        let genesis_hash = {
            let hash = self.client.info().genesis_hash;
            sp_core::H256::from_slice(hash.as_ref())
        };

        // Get runtime version
        let runtime_version = self.client
            .runtime_api()
            .version(best_hash)
            .map_err(|e| error_object(-32603, format!("Failed to get runtime version: {}", e)))?;

        let spec_version = runtime_version.spec_version;
        let transaction_version = runtime_version.transaction_version;

        // Build SignedExtra
        let extra: SignedExtra = (
            frame_system::CheckNonZeroSender::<Runtime>::new(),
            frame_system::CheckSpecVersion::<Runtime>::new(),
            frame_system::CheckTxVersion::<Runtime>::new(),
            frame_system::CheckGenesis::<Runtime>::new(),
            frame_system::CheckEra::<Runtime>::from(Era::Immortal),
            frame_system::CheckNonce::<Runtime>::from(nonce),
            frame_system::CheckWeight::<Runtime>::new(),
            pallet_transaction_payment::ChargeTransactionPayment::<Runtime>::from(0),
        );

        // Create signed payload
        let raw_payload = SignedPayload::from_raw(
            call.clone(),
            extra.clone(),
            (
                (),
                spec_version,
                transaction_version,
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
        let extrinsic = UncheckedExtrinsic::new_signed(
            call,
            MultiAddress::Id(signer_account),
            sphincs_signature,
            extra,
        );

        // Encode and submit
        let encoded = extrinsic.encode();
        log::info!("   Extrinsic size: {} bytes", encoded.len());

        let block_extrinsic = Block::Extrinsic::decode(&mut &encoded[..])
            .map_err(|e| error_object(-32603, format!("Failed to decode extrinsic: {}", e)))?;

        let xt_hash = self.pool
            .submit_one(
                best_hash,
                TransactionSource::Local,
                block_extrinsic,
            )
            .await
            .map_err(|e| error_object(-32603, format!("Failed to submit transaction: {}", e)))?;

        Ok(format!("{:?}", xt_hash))
    }
}

/// Load SPHINCS+ keypair from hex-encoded 128-byte secret key
fn load_sphincs_keypair(secret_key: &str) -> RpcResult<SphincsPair> {
    let key_bytes = hex::decode(secret_key.trim_start_matches("0x"))
        .map_err(|e| error_object(-32602, format!("Invalid secret key hex: {}", e)))?;

    if key_bytes.len() != 128 {
        return Err(error_object(-32602, format!(
            "Invalid SPHINCS+ key size: {} bytes. Expected 128 bytes.",
            key_bytes.len()
        )));
    }

    let secret: [u8; 128] = key_bytes.try_into()
        .map_err(|_| error_object(-32602, "Failed to convert secret key to array".to_string()))?;

    Ok(SphincsPair::from_secret(secret))
}

/// Helper to create error objects
fn error_object(code: i32, message: String) -> ErrorObjectOwned {
    ErrorObjectOwned::owned(code, message, None::<()>)
}
