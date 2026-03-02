// Axiom Task Attestation RPC with SPHINCS+ Signing
//
// Accepts attestation fields + SPHINCS+ secret key, builds and submits a
// pallet_axiom_attestation::anchor_attestation extrinsic — same signing
// infrastructure as quantumharmony_submitRuntimeUpgrade.
//
// The Axiom agent calls this after every completed task.

use jsonrpsee::{
    core::{async_trait, RpcResult},
    proc_macros::rpc,
};
use jsonrpsee_types::ErrorObjectOwned;
use sp_api::{Core, ProvideRuntimeApi};
use sp_blockchain::HeaderBackend;
use sp_runtime::{
    generic::Era,
    traits::Block as BlockT,
    MultiAddress, MultiSignature,
};
use quantumharmony_runtime::{
    UncheckedExtrinsic, RuntimeCall, SignedExtra, Runtime, SignedPayload,
};
use frame_system;
use pallet_transaction_payment;
use sc_transaction_pool_api::{TransactionPool, TransactionSource};
use scale_codec::{Encode, Decode};
use std::sync::Arc;
use log;
use hex;

use sp_core::{Pair, sphincs::Pair as SphincsPair, sphincs::SignatureWithPublic};
use sp_core::crypto::AccountId32;
use frame_system_rpc_runtime_api::AccountNonceApi;

#[rpc(client, server)]
pub trait AxiomAttestationRpcApi {
    /// Anchor a completed Axiom task attestation on-chain.
    ///
    /// Builds and submits a `pallet_axiom_attestation::anchor_attestation`
    /// extrinsic signed with the provided SPHINCS+ key.
    ///
    /// # Parameters
    /// - `task_hash_hex`:        SHA-256(task_id|step_count|provider), hex-encoded
    /// - `description_hash_hex`: SHA-256(task description), hex-encoded
    /// - `step_count`:           Number of tool invocations
    /// - `signer_fingerprint`:   Falcon public key fingerprint string
    /// - `signature_hex`:        Falcon-512 signature over attestation data, hex-encoded
    /// - `audit_chain_hash_hex`: SHA-256 of final audit chain entry, hex-encoded
    /// - `provider`:             LLM provider name ("claude-code" or "anthropic")
    /// - `secret_key`:           SPHINCS+ 128-byte secret key, hex-encoded
    ///
    /// # Returns
    /// Transaction hash (hex string with 0x prefix)
    #[method(name = "quantumharmony_submitTaskAttestation")]
    async fn submit_task_attestation(
        &self,
        task_hash_hex: String,
        description_hash_hex: String,
        step_count: u32,
        signer_fingerprint: String,
        signature_hex: String,
        audit_chain_hash_hex: String,
        provider: String,
        secret_key: String,
    ) -> RpcResult<String>;
}

pub struct AxiomAttestationRpc<C, P, Block> {
    client: Arc<C>,
    pool: Arc<P>,
    _phantom: std::marker::PhantomData<Block>,
}

impl<C, P, Block> AxiomAttestationRpc<C, P, Block> {
    pub fn new(client: Arc<C>, pool: Arc<P>) -> Self {
        Self {
            client,
            pool,
            _phantom: std::marker::PhantomData,
        }
    }
}

#[async_trait]
impl<C, P, Block> AxiomAttestationRpcApiServer for AxiomAttestationRpc<C, P, Block>
where
    Block: BlockT,
    C: Send + Sync + 'static + ProvideRuntimeApi<Block> + HeaderBackend<Block>,
    C::Api: AccountNonceApi<Block, AccountId32, u32>,
    P: Send + Sync + 'static + TransactionPool<Block = Block>,
{
    async fn submit_task_attestation(
        &self,
        task_hash_hex: String,
        description_hash_hex: String,
        step_count: u32,
        signer_fingerprint: String,
        signature_hex: String,
        audit_chain_hash_hex: String,
        provider: String,
        secret_key: String,
    ) -> RpcResult<String> {
        log::info!("📋 Axiom task attestation request received");

        // 1. Decode attestation fields
        let task_hash: [u8; 32] = hex::decode(task_hash_hex.trim_start_matches("0x"))
            .map_err(|e| error_object(-32602, format!("Invalid task_hash hex: {e}")))?
            .try_into()
            .map_err(|_| error_object(-32602, "task_hash must be 32 bytes".into()))?;

        let description_hash: [u8; 32] = hex::decode(description_hash_hex.trim_start_matches("0x"))
            .map_err(|e| error_object(-32602, format!("Invalid description_hash hex: {e}")))?
            .try_into()
            .map_err(|_| error_object(-32602, "description_hash must be 32 bytes".into()))?;

        let signature_bytes = hex::decode(signature_hex.trim_start_matches("0x"))
            .map_err(|e| error_object(-32602, format!("Invalid signature hex: {e}")))?;

        if signature_bytes.is_empty() {
            return Err(error_object(-32602, "signature must not be empty".into()));
        }

        let fingerprint_bytes = signer_fingerprint.as_bytes().to_vec();
        if fingerprint_bytes.is_empty() {
            return Err(error_object(-32602, "signer_fingerprint must not be empty".into()));
        }
        if fingerprint_bytes.len() > 48 {
            return Err(error_object(-32602, format!(
                "signer_fingerprint too long: {} bytes (max 48)", fingerprint_bytes.len()
            )));
        }

        let provider_bytes = provider.as_bytes().to_vec();
        if provider_bytes.len() > 32 {
            return Err(error_object(-32602, format!(
                "provider too long: {} bytes (max 32)", provider_bytes.len()
            )));
        }
        if signature_bytes.len() > 1400 {
            return Err(error_object(-32602, format!(
                "signature too long: {} bytes (max 1400)", signature_bytes.len()
            )));
        }

        let audit_chain_hash: [u8; 32] = hex::decode(audit_chain_hash_hex.trim_start_matches("0x"))
            .map_err(|e| error_object(-32602, format!("Invalid audit_chain_hash hex: {e}")))?
            .try_into()
            .map_err(|_| error_object(-32602, "audit_chain_hash must be 32 bytes".into()))?;

        log::info!(
            "   task_hash: {}, steps: {}, provider: {}",
            hex::encode(&task_hash[..4]),
            step_count,
            provider,
        );

        // 2. Load SPHINCS+ keypair (128-byte secret key)
        let key_bytes = hex::decode(secret_key.trim_start_matches("0x"))
            .map_err(|e| error_object(-32602, format!("Invalid secret key hex: {e}")))?;

        if key_bytes.len() != 128 {
            return Err(error_object(-32602, format!(
                "Invalid SPHINCS+ key size: {} bytes. Expected 128-byte secret key.",
                key_bytes.len()
            )));
        }
        let secret: [u8; 128] = key_bytes.try_into()
            .map_err(|_| error_object(-32602, "Failed to convert secret key".into()))?;
        let keypair = SphincsPair::from_secret(secret);

        log::info!("   SPHINCS+ keypair loaded");

        // 3. Build pallet_axiom_attestation::anchor_attestation call
        let call = RuntimeCall::AxiomAttestation(
            pallet_axiom_attestation::Call::anchor_attestation {
                task_hash,
                description_hash,
                step_count,
                signer_fingerprint: fingerprint_bytes,
                signature: signature_bytes,
                audit_chain_hash,
                provider: provider_bytes,
            }
        );

        log::info!("   RuntimeCall::AxiomAttestation built");

        // 4. Get nonce for signer account
        use sp_runtime::traits::IdentifyAccount;
        use sp_runtime::MultiSigner;
        let signer_account = MultiSigner::from(keypair.public()).into_account();

        let best_hash = self.client.info().best_hash;
        let nonce = self.client
            .runtime_api()
            .account_nonce(best_hash, signer_account.clone())
            .map_err(|e| error_object(-32603, format!("Failed to get nonce: {e}")))?;

        log::info!("   Signer nonce: {nonce}");

        // 5. Runtime metadata for signing
        let genesis_hash = {
            let hash = self.client.info().genesis_hash;
            sp_core::H256::from_slice(hash.as_ref())
        };
        let runtime_version = self.client
            .runtime_api()
            .version(best_hash)
            .map_err(|e| error_object(-32603, format!("Failed to get runtime version: {e}")))?;

        // 6. Build SignedExtra
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

        // 7. Sign payload
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

        let signature = raw_payload.using_encoded(|payload| keypair.sign(payload));
        let sig_with_pub = SignatureWithPublic::new(signature, keypair.public());
        let sphincs_signature = MultiSignature::SphincsPlus(sig_with_pub);

        // 8. Build and submit extrinsic
        let extrinsic = UncheckedExtrinsic::new_signed(
            call,
            MultiAddress::Id(signer_account),
            sphincs_signature,
            extra,
        );

        let encoded = extrinsic.encode();
        let block_extrinsic = Block::Extrinsic::decode(&mut &encoded[..])
            .map_err(|e| error_object(-32603, format!("Failed to decode extrinsic: {e}")))?;

        let xt_hash = self.pool
            .submit_one(best_hash, TransactionSource::Local, block_extrinsic)
            .await
            .map_err(|e| error_object(-32603, format!("Failed to submit transaction: {e}")))?;

        log::info!("✅ Axiom attestation submitted: {:?}", xt_hash);

        Ok(format!("{:?}", xt_hash))
    }
}

fn error_object(code: i32, message: String) -> ErrorObjectOwned {
    ErrorObjectOwned::owned(code, message, None::<()>)
}
