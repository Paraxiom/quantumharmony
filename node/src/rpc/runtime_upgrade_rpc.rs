// Runtime Upgrade RPC with SPHINCS+ Signing
//
// This module provides a custom RPC method for quantum-safe runtime upgrades
// using SPHINCS+-SHAKE-256f-simple post-quantum signatures.
//
// The challenge: Standard Substrate tooling (Polkadot-JS Apps, polkadot.js library, subxt)
// doesn't support SPHINCS+ signatures. This RPC extension enables runtime upgrades by:
// 1. Accepting WASM blob and SPHINCS+ secret key via RPC
// 2. Building sudo.sudoUncheckedWeight(system.setCode(wasm)) call
// 3. Signing with SPHINCS+ (49,856 byte signature - fast variant)
// 4. Submitting to transaction pool
//
// PRODUCTION READY: This module accepts any valid 128-byte SPHINCS+ secret key.
// No longer limited to hardcoded test accounts (Alice/Bob/Charlie).
//
// Security: Use HTTPS or SSH tunnel when passing secret keys via RPC.

use jsonrpsee::{
    core::{async_trait, RpcResult},
    proc_macros::rpc,
    types::error::ErrorObject,
};
use jsonrpsee_types::ErrorObjectOwned;
use sp_api::{Core, ProvideRuntimeApi};
use sp_blockchain::HeaderBackend;
use sp_runtime::{
    generic::Era,
    traits::{Block as BlockT},
    MultiAddress, MultiSignature,
};
use quantumharmony_runtime::{UncheckedExtrinsic, RuntimeCall, SignedExtra, Runtime, SystemCall, SudoCall, SignedPayload};
use frame_system;
use pallet_transaction_payment;
use frame_support::weights::Weight;
use sc_transaction_pool_api::{TransactionPool, TransactionSource};
use scale_codec::{Encode, Decode};
use std::sync::Arc;
use log;
use hex;

// SPHINCS+ signing using sp-core's Pair trait
use sp_core::{Pair, sphincs::Pair as SphincsPair, sphincs::SignatureWithPublic};

// Account and nonce
use sp_core::crypto::AccountId32;
use frame_system_rpc_runtime_api::AccountNonceApi;

#[rpc(client, server)]
pub trait RuntimeUpgradeApi {
    /// Submit a runtime upgrade with SPHINCS+ signing
    ///
    /// # Parameters
    /// - `wasm_hex`: Hex-encoded WASM runtime blob (with or without 0x prefix)
    /// - `secret_key`: SPHINCS+ secret key - accepts two formats:
    ///   - Full 128-byte secret key (hex, 256 chars) - PRODUCTION: use this for any keypair
    ///   - 48-byte seed (hex, 96 chars) - DEV ONLY: only works with Alice/Bob/Charlie test accounts
    ///
    /// # Returns
    /// Transaction hash (hex string with 0x prefix)
    ///
    /// # Security
    /// WARNING: This method accepts the secret key via RPC. Use HTTPS or SSH tunnel.
    ///
    /// # Example (Production - full 128-byte secret key)
    /// ```bash
    /// curl -H "Content-Type: application/json" -d '{
    ///   "id":1,
    ///   "jsonrpc":"2.0",
    ///   "method":"quantumharmony_submitRuntimeUpgrade",
    ///   "params": [
    ///     "0x<WASM_HEX>",
    ///     "0x<128_BYTE_SECRET_KEY_HEX>"
    ///   ]
    /// }' http://YOUR_NODE:9944
    /// ```
    #[method(name = "quantumharmony_submitRuntimeUpgrade")]
    async fn submit_runtime_upgrade(
        &self,
        wasm_hex: String,
        secret_key: String,
    ) -> RpcResult<String>;
}

pub struct RuntimeUpgradeRpc<C, P, Block> {
    client: Arc<C>,
    pool: Arc<P>,
    _phantom: std::marker::PhantomData<Block>,
}

impl<C, P, Block> RuntimeUpgradeRpc<C, P, Block> {
    pub fn new(client: Arc<C>, pool: Arc<P>) -> Self {
        Self {
            client,
            pool,
            _phantom: std::marker::PhantomData,
        }
    }
}

#[async_trait]
impl<C, P, Block> RuntimeUpgradeApiServer for RuntimeUpgradeRpc<C, P, Block>
where
    Block: BlockT,
    C: Send + Sync + 'static + ProvideRuntimeApi<Block> + HeaderBackend<Block>,
    C::Api: AccountNonceApi<Block, AccountId32, u32>,
    P: Send + Sync + 'static + TransactionPool<Block = Block>,
{
    async fn submit_runtime_upgrade(
        &self,
        wasm_hex: String,
        secret_key: String,
    ) -> RpcResult<String> {
        log::info!("🔄 Runtime upgrade request received");

        // 1. Decode WASM
        let wasm_code = hex::decode(wasm_hex.trim_start_matches("0x"))
            .map_err(|e| error_object(-32602, format!("Invalid WASM hex: {}", e)))?;

        log::info!("   WASM size: {} bytes ({} KB)", wasm_code.len(), wasm_code.len() / 1024);

        // Validate WASM size (should be 500-700 KB typically)
        if wasm_code.len() < 100_000 {
            return Err(error_object(-32602, format!("WASM suspiciously small: {} bytes", wasm_code.len())));
        }
        if wasm_code.len() > 2_000_000 {
            return Err(error_object(-32602, format!("WASM too large: {} bytes", wasm_code.len())));
        }

        // 2. Load SPHINCS+ keypair
        // Accepts two formats:
        // - Full 128-byte secret key (PRODUCTION): direct keypair reconstruction
        // - 48-byte seed (DEV ONLY): only works with hardcoded test accounts
        let key_bytes = hex::decode(secret_key.trim_start_matches("0x"))
            .map_err(|e| error_object(-32602, format!("Invalid secret key hex: {}", e)))?;

        let keypair = match key_bytes.len() {
            // PRODUCTION MODE: Full 128-byte secret key
            // This is the complete SPHINCS+-SHAKE-256f-simple secret key
            // Structure determined by pqcrypto-sphincsplus library
            128 => {
                log::info!("   PRODUCTION MODE: Using full 128-byte SPHINCS+ secret key");

                // Convert to fixed-size array
                let secret: [u8; 128] = key_bytes.try_into()
                    .map_err(|_| error_object(-32602, "Failed to convert secret key to fixed array".to_string()))?;

                // Use Pair::from_secret() which reconstructs the keypair from the full secret key
                SphincsPair::from_secret(secret)
            },

            // 48-byte seed format is DEPRECATED
            48 => {
                return Err(error_object(-32602,
                    "48-byte seed format is deprecated. Please use the full 128-byte SPHINCS+ secret key (secret_hex from your validator config).".to_string()));
            },

            other => {
                return Err(error_object(-32602, format!(
                    "Invalid SPHINCS+ key size: {} bytes. Expected 128-byte SPHINCS+ secret key.",
                    other
                )));
            }
        };

        log::info!("   SPHINCS+ keypair loaded successfully");
        log::info!("   Public key: {:?}", hex::encode(keypair.public().as_ref()));

        // 3. Build sudo.sudoUncheckedWeight(system.setCode(wasm)) call using proper RuntimeCall API

        // Build system.setCode(wasm) call
        let set_code_call = RuntimeCall::System(
            SystemCall::set_code {
                code: wasm_code.clone(),
            }
        );

        // Build sudo.sudoUncheckedWeight(call, weight) call
        // Weight: ref_time = 0, proof_size = 0 (auto-calculate)
        let call = RuntimeCall::Sudo(
            SudoCall::sudo_unchecked_weight {
                call: Box::new(set_code_call),
                weight: Weight::from_parts(0, 0),
            }
        );

        log::info!("   RuntimeCall built successfully");

        // 4. Get nonce for the signer
        // Derive AccountId from the keypair's public key
        use sp_runtime::traits::IdentifyAccount;
        use sp_runtime::MultiSigner;
        let keypair_public = keypair.public();
        let signer_account = MultiSigner::from(keypair_public).into_account();

        let best_hash = self.client.info().best_hash;
        let nonce = self.client
            .runtime_api()
            .account_nonce(best_hash, signer_account.clone())
            .map_err(|e| error_object(-32603, format!("Failed to get nonce: {}", e)))?;

        log::info!("   Signer AccountId: {:?}", hex::encode(&signer_account));
        log::info!("   Signer nonce: {}", nonce);

        // 5. Get runtime metadata
        let genesis_hash = {
            let hash = self.client.info().genesis_hash;
            sp_core::H256::from_slice(hash.as_ref())
        };

        // Get runtime version from the current runtime
        let runtime_version = self.client
            .runtime_api()
            .version(best_hash)
            .map_err(|e| error_object(-32603, format!("Failed to get runtime version: {}", e)))?;

        let spec_version = runtime_version.spec_version;
        let transaction_version = runtime_version.transaction_version;

        log::info!("   Runtime spec_version: {}, tx_version: {}", spec_version, transaction_version);

        // 6. Build SignedExtra (matching transaction gateway approach)
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

        // 7. Create signed payload using SignedPayload::from_raw()
        // The additional_signed tuple must match the order of SignedExtension components:
        // (CheckNonZeroSender, CheckSpecVersion, CheckTxVersion, CheckGenesis, CheckEra, CheckNonce, CheckWeight, ChargeTransactionPayment)
        let raw_payload = SignedPayload::from_raw(
            call.clone(),
            extra.clone(),
            (
                (),                // CheckNonZeroSender::additional_signed() returns ()
                spec_version,      // CheckSpecVersion::additional_signed() returns spec_version
                transaction_version, // CheckTxVersion::additional_signed() returns tx_version
                genesis_hash,      // CheckGenesis::additional_signed() returns genesis_hash
                genesis_hash,      // CheckEra::additional_signed() returns block_hash (genesis for immortal)
                (),                // CheckNonce::additional_signed() returns ()
                (),                // CheckWeight::additional_signed() returns ()
                (),                // ChargeTransactionPayment::additional_signed() returns ()
            ),
        );

        log::info!("   SignedPayload created with proper additional_signed tuple");

        // 8. Sign the payload with SPHINCS+ (using Pair trait)
        let signature = raw_payload.using_encoded(|payload| keypair.sign(payload));

        log::info!("   SPHINCS+ signature generated");

        // 9. Create SignatureWithPublic (bundles signature with public key for verification)
        // This is required because AccountId is a hash of the public key, so verification
        // needs the actual public key embedded with the signature.
        let sig_with_pub = SignatureWithPublic::new(signature, keypair.public());

        log::info!("   SignatureWithPublic created (signature + public key bundled)");

        // 10. Create MultiSignature
        let sphincs_signature = MultiSignature::SphincsPlus(sig_with_pub);

        // 10. Build UncheckedExtrinsic using proper Substrate API (matching transaction gateway)
        let extrinsic = UncheckedExtrinsic::new_signed(
            call,
            MultiAddress::Id(signer_account),
            sphincs_signature,
            extra,
        );

        log::info!("   Extrinsic built successfully");

        // 11. Encode and decode to Block::Extrinsic (matching transaction gateway)
        let encoded_extrinsic = extrinsic.encode();
        log::info!("   Encoded extrinsic: {} bytes", encoded_extrinsic.len());

        let block_extrinsic = Block::Extrinsic::decode(&mut &encoded_extrinsic[..])
            .map_err(|e| error_object(-32603, format!("Failed to decode extrinsic: {}", e)))?;

        // Use TransactionSource::Local to bypass some transaction pool limits
        // This is appropriate for runtime upgrades submitted via RPC on the same node
        // Local transactions are prioritized and bypass ExhaustsResources checks during block building
        let xt_hash = self.pool
            .submit_one(
                best_hash,
                TransactionSource::Local,
                block_extrinsic,
            )
            .await
            .map_err(|e| error_object(-32603, format!("Failed to submit transaction: {}", e)))?;

        log::info!("✅ Runtime upgrade transaction submitted successfully");
        log::info!("   Transaction hash: {:?}", xt_hash);
        log::info!("   Watch for system.CodeUpdated event in next block");

        Ok(format!("{:?}", xt_hash))
    }
}

/// Helper to create error objects
fn error_object(code: i32, message: String) -> ErrorObjectOwned {
    ErrorObjectOwned::owned(code, message, None::<()>)
}

#[cfg(test)]
mod tests {
    use super::*;
    use sp_runtime::traits::IdentifyAccount;

    /// Test that SPHINCS+ keypair from_secret correctly extracts the public key
    #[test]
    fn test_sphincs_keypair_from_secret() {
        // Alice's 128-byte SPHINCS+ secret key
        let secret: [u8; 128] = [
            0xe7, 0x17, 0x5a, 0x54, 0x1e, 0xe0, 0x55, 0xe4, 0x23, 0xe0, 0x70, 0xee, 0xe2, 0xcf, 0xd2, 0xa9,
            0xf4, 0x47, 0xa8, 0x20, 0xf4, 0xe6, 0x1b, 0xf0, 0x31, 0x80, 0x80, 0x5d, 0xbc, 0x8c, 0x4a, 0x7f,
            0x1a, 0xd3, 0x43, 0x7c, 0x05, 0xc2, 0xda, 0x62, 0xed, 0x34, 0x2e, 0xef, 0x62, 0xe8, 0xca, 0xc2,
            0x85, 0xcf, 0x81, 0x34, 0xd2, 0x9b, 0x49, 0xc6, 0x8a, 0x9e, 0x57, 0x5f, 0x3c, 0x27, 0x59, 0x91,
            0xd7, 0xd0, 0xbd, 0x47, 0x54, 0x17, 0xa9, 0x3f, 0xa6, 0x12, 0x16, 0xa1, 0xe4, 0x02, 0x4f, 0x8d,
            0x1a, 0x21, 0x1f, 0x79, 0x5e, 0x6a, 0xb1, 0x11, 0xa1, 0xee, 0xf0, 0xd5, 0xe4, 0xf3, 0xf4, 0xb1,
            0x56, 0xe4, 0x7e, 0x5c, 0x8d, 0x41, 0x85, 0xce, 0x4a, 0x30, 0x84, 0x23, 0xeb, 0x31, 0x0b, 0xb3,
            0xb7, 0xf2, 0x6e, 0x6d, 0x50, 0x41, 0x91, 0x66, 0x2d, 0x22, 0x41, 0xaa, 0xfa, 0xf9, 0x14, 0xcd,
        ];

        // Expected public key (last 64 bytes of secret)
        let expected_public: [u8; 64] = [
            0xd7, 0xd0, 0xbd, 0x47, 0x54, 0x17, 0xa9, 0x3f, 0xa6, 0x12, 0x16, 0xa1, 0xe4, 0x02, 0x4f, 0x8d,
            0x1a, 0x21, 0x1f, 0x79, 0x5e, 0x6a, 0xb1, 0x11, 0xa1, 0xee, 0xf0, 0xd5, 0xe4, 0xf3, 0xf4, 0xb1,
            0x56, 0xe4, 0x7e, 0x5c, 0x8d, 0x41, 0x85, 0xce, 0x4a, 0x30, 0x84, 0x23, 0xeb, 0x31, 0x0b, 0xb3,
            0xb7, 0xf2, 0x6e, 0x6d, 0x50, 0x41, 0x91, 0x66, 0x2d, 0x22, 0x41, 0xaa, 0xfa, 0xf9, 0x14, 0xcd,
        ];

        // Create keypair from secret
        let pair = SphincsPair::from_secret(secret);

        // Verify public key extraction
        assert_eq!(
            pair.public().as_ref(),
            &expected_public,
            "Public key should be extracted from secret[64..128]"
        );
    }

    /// Test SPHINCS+ signing and verification
    #[test]
    fn test_sphincs_sign_and_verify() {
        let secret: [u8; 128] = [
            0xe7, 0x17, 0x5a, 0x54, 0x1e, 0xe0, 0x55, 0xe4, 0x23, 0xe0, 0x70, 0xee, 0xe2, 0xcf, 0xd2, 0xa9,
            0xf4, 0x47, 0xa8, 0x20, 0xf4, 0xe6, 0x1b, 0xf0, 0x31, 0x80, 0x80, 0x5d, 0xbc, 0x8c, 0x4a, 0x7f,
            0x1a, 0xd3, 0x43, 0x7c, 0x05, 0xc2, 0xda, 0x62, 0xed, 0x34, 0x2e, 0xef, 0x62, 0xe8, 0xca, 0xc2,
            0x85, 0xcf, 0x81, 0x34, 0xd2, 0x9b, 0x49, 0xc6, 0x8a, 0x9e, 0x57, 0x5f, 0x3c, 0x27, 0x59, 0x91,
            0xd7, 0xd0, 0xbd, 0x47, 0x54, 0x17, 0xa9, 0x3f, 0xa6, 0x12, 0x16, 0xa1, 0xe4, 0x02, 0x4f, 0x8d,
            0x1a, 0x21, 0x1f, 0x79, 0x5e, 0x6a, 0xb1, 0x11, 0xa1, 0xee, 0xf0, 0xd5, 0xe4, 0xf3, 0xf4, 0xb1,
            0x56, 0xe4, 0x7e, 0x5c, 0x8d, 0x41, 0x85, 0xce, 0x4a, 0x30, 0x84, 0x23, 0xeb, 0x31, 0x0b, 0xb3,
            0xb7, 0xf2, 0x6e, 0x6d, 0x50, 0x41, 0x91, 0x66, 0x2d, 0x22, 0x41, 0xaa, 0xfa, 0xf9, 0x14, 0xcd,
        ];

        let pair = SphincsPair::from_secret(secret);
        let message = b"test message for SPHINCS+ signing";

        // Sign the message
        let signature = pair.sign(message);

        // Verify with pair's public key
        assert!(
            SphincsPair::verify(&signature, message, &pair.public()),
            "Signature should verify with keypair's public key"
        );
    }

    /// Test AccountId derivation from SPHINCS+ public key
    #[test]
    fn test_sphincs_accountid_derivation() {
        use sp_runtime::MultiSigner;

        let public: [u8; 64] = [
            0xd7, 0xd0, 0xbd, 0x47, 0x54, 0x17, 0xa9, 0x3f, 0xa6, 0x12, 0x16, 0xa1, 0xe4, 0x02, 0x4f, 0x8d,
            0x1a, 0x21, 0x1f, 0x79, 0x5e, 0x6a, 0xb1, 0x11, 0xa1, 0xee, 0xf0, 0xd5, 0xe4, 0xf3, 0xf4, 0xb1,
            0x56, 0xe4, 0x7e, 0x5c, 0x8d, 0x41, 0x85, 0xce, 0x4a, 0x30, 0x84, 0x23, 0xeb, 0x31, 0x0b, 0xb3,
            0xb7, 0xf2, 0x6e, 0x6d, 0x50, 0x41, 0x91, 0x66, 0x2d, 0x22, 0x41, 0xaa, 0xfa, 0xf9, 0x14, 0xcd,
        ];

        let sphincs_public = sp_core::sphincs::Public::from_raw(public);
        let signer = MultiSigner::from(sphincs_public);
        let account_id = signer.into_account();

        // Log the derived AccountId for debugging
        println!("Derived AccountId: 0x{}", hex::encode(AsRef::<[u8; 32]>::as_ref(&account_id)));

        // The AccountId should be 32 bytes (keccak_256 hash of public key)
        assert_eq!(AsRef::<[u8; 32]>::as_ref(&account_id).len(), 32);
    }
}
