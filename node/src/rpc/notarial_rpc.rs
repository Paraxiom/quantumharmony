//! Notarial RPC
//!
//! Provides RPC methods for document attestation and verification.
//!
//! Methods:
//! - `notarial_attestDocument` - Attest a document hash on-chain
//! - `notarial_witnessAttestation` - Witness an existing attestation
//! - `notarial_getAttestation` - Get attestation by ID
//! - `notarial_verifyDocument` - Verify a document hash exists on-chain
//! - `notarial_generateCertificate` - Generate certificate for certified attestation

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
use pallet_notarial::runtime_api::NotarialRuntimeApi as NotarialStorageApi;

/// Document attestation request
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AttestDocumentRequest {
    /// Document hash (32 bytes, hex with 0x prefix)
    #[serde(rename = "documentHash")]
    pub document_hash: String,
    /// Category: 0=Academic, 1=Legal, 2=Contract, 3=IP, 4=Identity, 5=Financial, 6=Medical, 7=Other
    pub category: u8,
    /// Description (max 512 chars)
    pub description: String,
    /// Validity in blocks (optional, 0 = permanent)
    #[serde(rename = "validityBlocks")]
    pub validity_blocks: Option<u32>,
    /// SPHINCS+ signer key (128 bytes hex)
    #[serde(rename = "signerKey")]
    pub signer_key: String,
}

/// Witness attestation request
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WitnessRequest {
    /// Attestation ID to witness
    #[serde(rename = "attestationId")]
    pub attestation_id: u64,
    /// Optional note hash (32 bytes hex)
    #[serde(rename = "noteHash")]
    pub note_hash: Option<String>,
    /// SPHINCS+ signer key
    #[serde(rename = "signerKey")]
    pub signer_key: String,
}

/// Attestation info response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AttestationInfo {
    pub id: u64,
    #[serde(rename = "documentHash")]
    pub document_hash: String,
    pub category: String,
    pub description: String,
    pub attester: String,
    #[serde(rename = "attestedAt")]
    pub attested_at: u32,
    #[serde(rename = "expiresAt")]
    pub expires_at: Option<u32>,
    pub status: String,
    #[serde(rename = "witnessCount")]
    pub witness_count: u32,
    pub certified: bool,
}

/// Verification response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerificationResult {
    pub exists: bool,
    #[serde(rename = "attestationId")]
    pub attestation_id: Option<u64>,
    #[serde(rename = "attestedAt")]
    pub attested_at: Option<u32>,
    pub status: Option<String>,
    pub certified: Option<bool>,
    #[serde(rename = "witnessCount")]
    pub witness_count: Option<u32>,
}

/// Certificate info
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CertificateInfo {
    pub id: u64,
    #[serde(rename = "attestationId")]
    pub attestation_id: u64,
    #[serde(rename = "generatedAt")]
    pub generated_at: u32,
    #[serde(rename = "certificateHash")]
    pub certificate_hash: String,
    pub issuer: String,
}

/// Notarial RPC interface
#[rpc(client, server)]
pub trait NotarialApi<BlockHash> {
    /// Attest a document's existence on-chain
    ///
    /// Creates an immutable timestamp proof for the document hash.
    #[method(name = "notarial_attestDocument")]
    async fn attest_document(&self, request: AttestDocumentRequest) -> RpcResult<Value>;

    /// Witness an existing attestation
    ///
    /// Adds your signature as a witness to an attestation.
    #[method(name = "notarial_witnessAttestation")]
    async fn witness_attestation(&self, request: WitnessRequest) -> RpcResult<Value>;

    /// Get attestation details by ID
    #[method(name = "notarial_getAttestation")]
    async fn get_attestation(&self, attestation_id: u64) -> RpcResult<Option<AttestationInfo>>;

    /// Verify a document hash exists on-chain
    ///
    /// Returns attestation info if the document has been attested.
    #[method(name = "notarial_verifyDocument")]
    async fn verify_document(&self, document_hash: String) -> RpcResult<VerificationResult>;

    /// Generate certificate for a certified attestation
    #[method(name = "notarial_generateCertificate")]
    async fn generate_certificate(&self, attestation_id: u64, signer_key: String) -> RpcResult<Value>;

    /// Get certificate by ID
    #[method(name = "notarial_getCertificate")]
    async fn get_certificate(&self, certificate_id: u64) -> RpcResult<Option<CertificateInfo>>;

    /// Get all attestations for an account
    #[method(name = "notarial_getAttestationsByOwner")]
    async fn get_attestations_by_owner(&self, account: String) -> RpcResult<Vec<u64>>;
}

/// Notarial RPC implementation
pub struct NotarialRpc<C, P, Block> {
    client: Arc<C>,
    pool: Arc<P>,
    _phantom: std::marker::PhantomData<Block>,
}

impl<C, P, Block> NotarialRpc<C, P, Block>
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

    fn parse_document_hash(&self, hash_str: &str) -> Result<[u8; 32], String> {
        let bytes = hex::decode(hash_str.trim_start_matches("0x"))
            .map_err(|e| format!("Invalid document hash hex: {}", e))?;

        if bytes.len() != 32 {
            return Err(format!("Document hash must be 32 bytes, got {}", bytes.len()));
        }

        let mut hash = [0u8; 32];
        hash.copy_from_slice(&bytes);
        Ok(hash)
    }

    fn category_name(&self, category: u8) -> String {
        match category {
            0 => "Academic Credential",
            1 => "Legal Document",
            2 => "Contract",
            3 => "Intellectual Property",
            4 => "Identity",
            5 => "Financial",
            6 => "Medical",
            _ => "Other",
        }.to_string()
    }

    fn status_name(&self, status: u8) -> String {
        match status {
            0 => "Active",
            1 => "Revoked",
            2 => "Expired",
            3 => "Certified",
            _ => "Unknown",
        }.to_string()
    }
}

#[async_trait]
impl<C, P, Block> NotarialApiServer<Block::Hash> for NotarialRpc<C, P, Block>
where
    Block: BlockT,
    C: Send + Sync + 'static + HeaderBackend<Block> + ProvideRuntimeApi<Block>,
    C::Api: sp_block_builder::BlockBuilder<Block>
        + sp_api::Core<Block>
        + substrate_frame_rpc_system::AccountNonceApi<Block, AccountId32, u32>
        + frame_system_rpc_runtime_api::AccountNonceApi<Block, AccountId32, u32>
        + NotarialStorageApi<Block, AccountId32>,
    P: TransactionPool<Block = Block> + 'static,
{
    async fn attest_document(&self, request: AttestDocumentRequest) -> RpcResult<Value> {
        log::info!("📜 Notarial RPC: Attesting document");
        log::info!("   Hash: {}...", &request.document_hash[..std::cmp::min(20, request.document_hash.len())]);

        // Parse document hash
        let document_hash = self.parse_document_hash(&request.document_hash)
            .map_err(|e| ErrorObject::owned(
                ErrorCode::InvalidParams.code(),
                e,
                None::<()>
            ))?;

        // Get keypair
        let keypair = self.get_keypair(&request.signer_key)
            .map_err(|e| ErrorObject::owned(
                ErrorCode::InvalidParams.code(),
                e,
                None::<()>
            ))?;

        // Derive signer account
        use sp_runtime::MultiSigner;
        let signer_account = MultiSigner::from(keypair.public()).into_account();

        log::info!("   Attester: {:?}", signer_account);

        // Build call data for attest_document
        // Call: Notarial::attest_document(document_hash, category, description, validity_blocks, contract_id, academic_id)
        let description_bytes = request.description.as_bytes().to_vec();
        let validity: Option<u32> = request.validity_blocks;
        let contract_id: Option<u32> = None;
        let academic_id: Option<u32> = None;

        // Encode the call
        use quantumharmony_runtime::RuntimeCall;
        let call = RuntimeCall::Notarial(pallet_notarial::Call::attest_document {
            document_hash,
            category_id: request.category,
            description: description_bytes,
            validity_blocks: validity.map(|v| v.into()),
            contract_id,
            academic_id,
        });

        // Get nonce
        let best_hash = self.client.info().best_hash;
        let nonce = self.client.runtime_api()
            .account_nonce(best_hash, signer_account.clone())
            .map_err(|e| ErrorObject::owned(
                ErrorCode::InternalError.code(),
                format!("Failed to get nonce: {}", e),
                None::<()>
            ))?;

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

        log::info!("✅ Document attestation submitted: {:?}", tx_hash);

        Ok(serde_json::json!({
            "success": true,
            "txHash": format!("{:?}", tx_hash),
            "documentHash": request.document_hash,
            "attester": format!("{}", signer_account),
            "category": self.category_name(request.category),
            "status": "pending"
        }))
    }

    async fn witness_attestation(&self, request: WitnessRequest) -> RpcResult<Value> {
        log::info!("📜 Notarial RPC: Witnessing attestation {}", request.attestation_id);

        // Get keypair
        let keypair = self.get_keypair(&request.signer_key)
            .map_err(|e| ErrorObject::owned(
                ErrorCode::InvalidParams.code(),
                e,
                None::<()>
            ))?;

        use sp_runtime::MultiSigner;
        let signer_account = MultiSigner::from(keypair.public()).into_account();

        // Parse optional note hash
        let note_hash: Option<[u8; 32]> = if let Some(ref hash_str) = request.note_hash {
            Some(self.parse_document_hash(hash_str)
                .map_err(|e| ErrorObject::owned(
                    ErrorCode::InvalidParams.code(),
                    e,
                    None::<()>
                ))?)
        } else {
            None
        };

        // Build call
        use quantumharmony_runtime::RuntimeCall;
        let call = RuntimeCall::Notarial(pallet_notarial::Call::witness_attestation {
            attestation_id: request.attestation_id,
            note_hash,
        });

        // Get nonce and sign (same pattern as attest_document)
        let best_hash = self.client.info().best_hash;
        let nonce = self.client.runtime_api()
            .account_nonce(best_hash, signer_account.clone())
            .map_err(|e| ErrorObject::owned(
                ErrorCode::InternalError.code(),
                format!("Failed to get nonce: {}", e),
                None::<()>
            ))?;

        let genesis_hash = sp_core::H256::from_slice(self.client.info().genesis_hash.as_ref());
        let runtime_version = self.client.runtime_api()
            .version(best_hash)
            .map_err(|e| ErrorObject::owned(
                ErrorCode::InternalError.code(),
                format!("Failed to get runtime version: {}", e),
                None::<()>
            ))?;

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

        use quantumharmony_runtime::SignedPayload;
        let raw_payload = SignedPayload::from_raw(
            call.clone(),
            extra.clone(),
            ((), runtime_version.spec_version, runtime_version.transaction_version, genesis_hash, genesis_hash, (), (), ()),
        );

        let signature = raw_payload.using_encoded(|payload| keypair.sign(payload));
        let sig_with_pub = SignatureWithPublic::new(signature, keypair.public());
        let sphincs_signature = MultiSignature::SphincsPlus(sig_with_pub);

        use quantumharmony_runtime::UncheckedExtrinsic;
        let extrinsic = UncheckedExtrinsic::new_signed(
            call,
            sp_runtime::MultiAddress::Id(signer_account.clone()),
            sphincs_signature,
            extra,
        );

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

        log::info!("✅ Witness submitted: {:?}", tx_hash);

        Ok(serde_json::json!({
            "success": true,
            "txHash": format!("{:?}", tx_hash),
            "attestationId": request.attestation_id,
            "witness": format!("{}", signer_account),
            "status": "pending"
        }))
    }

    async fn get_attestation(&self, attestation_id: u64) -> RpcResult<Option<AttestationInfo>> {
        log::info!("📜 Notarial RPC: Getting attestation {}", attestation_id);

        let best_hash = self.client.info().best_hash;
        match self.client.runtime_api().get_attestation(best_hash, attestation_id) {
            Ok(Some((id, doc_hash, category, description, attester, attested_at, expires_at, status, witness_count, certified))) => {
                Ok(Some(AttestationInfo {
                    id,
                    document_hash: format!("0x{}", hex::encode(doc_hash)),
                    category: self.category_name(category),
                    description: String::from_utf8_lossy(&description).to_string(),
                    attester: format!("{}", attester),
                    attested_at,
                    expires_at,
                    status: self.status_name(status),
                    witness_count,
                    certified,
                }))
            }
            Ok(None) => Ok(None),
            Err(_) => {
                log::warn!("Notarial runtime API not available - runtime upgrade required");
                Ok(None)
            }
        }
    }

    async fn verify_document(&self, document_hash: String) -> RpcResult<VerificationResult> {
        log::info!("📜 Notarial RPC: Verifying document {}", &document_hash[..std::cmp::min(20, document_hash.len())]);

        let hash = self.parse_document_hash(&document_hash)
            .map_err(|e| ErrorObject::owned(
                ErrorCode::InvalidParams.code(),
                e,
                None::<()>
            ))?;

        let best_hash = self.client.info().best_hash;
        match self.client.runtime_api().verify_document(best_hash, hash) {
            Ok(Some((attestation_id, attested_at, status, certified, witness_count))) => {
                Ok(VerificationResult {
                    exists: true,
                    attestation_id: Some(attestation_id),
                    attested_at: Some(attested_at),
                    status: Some(self.status_name(status)),
                    certified: Some(certified),
                    witness_count: Some(witness_count),
                })
            }
            Ok(None) => {
                Ok(VerificationResult {
                    exists: false,
                    attestation_id: None,
                    attested_at: None,
                    status: None,
                    certified: None,
                    witness_count: None,
                })
            }
            Err(_) => {
                log::warn!("Notarial runtime API not available - runtime upgrade required");
                Ok(VerificationResult {
                    exists: false,
                    attestation_id: None,
                    attested_at: None,
                    status: None,
                    certified: None,
                    witness_count: None,
                })
            }
        }
    }

    async fn generate_certificate(&self, attestation_id: u64, signer_key: String) -> RpcResult<Value> {
        log::info!("📜 Notarial RPC: Generating certificate for attestation {}", attestation_id);

        let keypair = self.get_keypair(&signer_key)
            .map_err(|e| ErrorObject::owned(
                ErrorCode::InvalidParams.code(),
                e,
                None::<()>
            ))?;

        use sp_runtime::MultiSigner;
        let signer_account = MultiSigner::from(keypair.public()).into_account();

        use quantumharmony_runtime::RuntimeCall;
        let call = RuntimeCall::Notarial(pallet_notarial::Call::generate_certificate {
            attestation_id,
        });

        let best_hash = self.client.info().best_hash;
        let nonce = self.client.runtime_api()
            .account_nonce(best_hash, signer_account.clone())
            .map_err(|e| ErrorObject::owned(
                ErrorCode::InternalError.code(),
                format!("Failed to get nonce: {}", e),
                None::<()>
            ))?;

        let genesis_hash = sp_core::H256::from_slice(self.client.info().genesis_hash.as_ref());
        let runtime_version = self.client.runtime_api()
            .version(best_hash)
            .map_err(|e| ErrorObject::owned(
                ErrorCode::InternalError.code(),
                format!("Failed to get runtime version: {}", e),
                None::<()>
            ))?;

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

        use quantumharmony_runtime::SignedPayload;
        let raw_payload = SignedPayload::from_raw(
            call.clone(),
            extra.clone(),
            ((), runtime_version.spec_version, runtime_version.transaction_version, genesis_hash, genesis_hash, (), (), ()),
        );

        let signature = raw_payload.using_encoded(|payload| keypair.sign(payload));
        let sig_with_pub = SignatureWithPublic::new(signature, keypair.public());
        let sphincs_signature = MultiSignature::SphincsPlus(sig_with_pub);

        use quantumharmony_runtime::UncheckedExtrinsic;
        let extrinsic = UncheckedExtrinsic::new_signed(
            call,
            sp_runtime::MultiAddress::Id(signer_account.clone()),
            sphincs_signature,
            extra,
        );

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

        log::info!("✅ Certificate generation submitted: {:?}", tx_hash);

        Ok(serde_json::json!({
            "success": true,
            "txHash": format!("{:?}", tx_hash),
            "attestationId": attestation_id,
            "issuer": format!("{}", signer_account),
            "status": "pending"
        }))
    }

    async fn get_certificate(&self, certificate_id: u64) -> RpcResult<Option<CertificateInfo>> {
        log::info!("📜 Notarial RPC: Getting certificate {}", certificate_id);

        let best_hash = self.client.info().best_hash;
        match self.client.runtime_api().get_certificate(best_hash, certificate_id) {
            Ok(Some((id, attestation_id, generated_at, cert_hash, issuer))) => {
                Ok(Some(CertificateInfo {
                    id,
                    attestation_id,
                    generated_at,
                    certificate_hash: format!("0x{}", hex::encode(cert_hash)),
                    issuer: format!("{}", issuer),
                }))
            }
            Ok(None) => Ok(None),
            Err(_) => {
                log::warn!("Notarial runtime API not available - runtime upgrade required");
                Ok(None)
            }
        }
    }

    async fn get_attestations_by_owner(&self, account: String) -> RpcResult<Vec<u64>> {
        log::info!("📜 Notarial RPC: Getting attestations for {}", account);

        let account_id: AccountId32 = account.parse()
            .map_err(|_| ErrorObject::owned(
                ErrorCode::InvalidParams.code(),
                "Invalid SS58 account address",
                None::<()>
            ))?;

        let best_hash = self.client.info().best_hash;
        match self.client.runtime_api().get_attestations_by_owner(best_hash, account_id) {
            Ok(ids) => Ok(ids),
            Err(_) => {
                log::warn!("Notarial runtime API not available - runtime upgrade required");
                Ok(vec![])
            }
        }
    }
}
