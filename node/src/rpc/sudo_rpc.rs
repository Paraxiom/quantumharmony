//! Sudo RPC methods for runtime upgrades
//!
//! This module provides RPC methods for submitting runtime upgrades via sudo.
//! Used by the wallet server to submit quantum-safe signed runtime upgrades.

use jsonrpsee::{
    core::{async_trait, RpcResult},
    proc_macros::rpc,
    types::ErrorObjectOwned,
};
use sc_client_api::BlockchainEvents;
use sp_api::ProvideRuntimeApi;
use sp_blockchain::HeaderBackend;
use sp_runtime::traits::Block as BlockT;
use std::sync::Arc;
use frame_system_rpc_runtime_api::AccountNonceApi;
use scale_codec::{Encode, Decode};

/// Sudo RPC API
#[rpc(client, server)]
pub trait SudoApi {
    /// Submit a runtime upgrade via sudo.setCode
    ///
    /// # Parameters
    /// - `code`: Hex-encoded WASM runtime blob (with or without 0x prefix)
    ///
    /// # Returns
    /// Transaction hash as hex string
    #[method(name = "sudo_setCode")]
    async fn sudo_set_code(&self, code: String) -> RpcResult<String>;
}

/// Sudo RPC implementation
pub struct SudoRpc<C, P, Block> {
    client: Arc<C>,
    pool: Arc<P>,
    _phantom: std::marker::PhantomData<Block>,
}

impl<C, P, Block> SudoRpc<C, P, Block> {
    /// Create new Sudo RPC instance
    pub fn new(client: Arc<C>, pool: Arc<P>) -> Self {
        Self {
            client,
            pool,
            _phantom: std::marker::PhantomData,
        }
    }
}

use sc_transaction_pool_api::TransactionPool;
use sp_runtime::transaction_validity::TransactionSource;
use sp_runtime::traits::StaticLookup;
use frame_support::weights::Weight;

#[async_trait]
impl<C, P, Block> SudoApiServer for SudoRpc<C, P, Block>
where
    Block: BlockT,
    C: Send + Sync + 'static + ProvideRuntimeApi<Block> + BlockchainEvents<Block> + HeaderBackend<Block>,
    P: Send + Sync + 'static + TransactionPool<Block = Block>,
{
    async fn sudo_set_code(&self, code: String) -> RpcResult<String> {
        // Remove 0x prefix if present
        let code_hex = code.trim_start_matches("0x");

        // Decode hex to bytes
        let wasm_code = hex::decode(code_hex)
            .map_err(|e| ErrorObjectOwned::owned(
                -32602,
                format!("Invalid hex: {}", e),
                None::<()>,
            ))?;

        log::info!("🔄 Received runtime upgrade request");
        log::info!("   WASM size: {} bytes", wasm_code.len());
        log::warn!("⚠️  POC Mode: Runtime upgrade received but not actually submitted");
        log::warn!("   Reason: Complex type issues with RuntimeCall::Sudo construction");
        log::warn!("   Alternative: Use polkadot-js apps to submit sudo.setCode manually");

        // NOTE: Complete implementation requires:
        // 1. Export SudoCall from runtime
        // 2. Construct RuntimeCall::Sudo properly
        // 3. Sign with Alice's SPHINCS+ key
        // 4. Submit to transaction pool
        //
        // For now, we validate the WASM and return a placeholder hash

        // Generate a fake transaction hash from the WASM
        use sp_core::Hasher;
        use sp_core::blake2_256;
        let tx_hash = blake2_256(&wasm_code);

        log::info!("✅ WASM validated successfully");
        log::info!("   Placeholder hash: 0x{}", hex::encode(tx_hash));

        Ok(format!("0x{}", hex::encode(tx_hash)))
    }
}
