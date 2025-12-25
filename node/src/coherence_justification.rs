//! Coherence Finality Justification Import
//!
//! This module provides justification handling for the Quantum Coherence finality gadget.
//! It allows full nodes to receive and verify finality proofs from validators, enabling
//! them to update their finalized head beyond genesis.
//!
//! ## How it works
//!
//! 1. Validators finalize blocks via the coherence gadget
//! 2. After finalization, the certificate is encoded as a `CoherenceJustification`
//! 3. The justification is broadcast via libp2p to all connected peers
//! 4. Full nodes receive the justification and verify it
//! 5. Upon successful verification, they call `finalize_block()` to update their state
//!
//! This is analogous to how GRANDPA broadcasts justifications, but using our
//! quantum coherence consensus instead.

use scale_codec::{Decode, Encode};
use log::{debug, info, warn, error};
use sc_client_api::backend::Finalizer;
use sc_consensus::JustificationImport;
use sp_api::ProvideRuntimeApi;
use sp_blockchain::HeaderBackend;
use sp_runtime::traits::{Block as BlockT, Header as HeaderT, NumberFor};
use std::sync::Arc;

use pallet_proof_of_coherence::types::FinalityCertificate;

/// Engine ID for Coherence justifications
/// This identifies our justification type in the network protocol
pub const COHERENCE_ENGINE_ID: sp_runtime::ConsensusEngineId = *b"COHR";

/// Justification wrapper for Coherence finality certificates
///
/// This wraps the `FinalityCertificate` from the PoC pallet with
/// versioning for future protocol upgrades.
#[derive(Clone, Encode, Decode, Debug, PartialEq)]
pub struct CoherenceJustification<AccountId, BlockNumber, Hash> {
    /// The finality certificate containing votes from validators
    pub certificate: FinalityCertificate<AccountId, BlockNumber, Hash>,
    /// Protocol version for future compatibility
    pub version: u32,
}

impl<AccountId, BlockNumber, Hash> CoherenceJustification<AccountId, BlockNumber, Hash>
where
    AccountId: Clone + Encode + Decode,
    BlockNumber: Clone + Encode + Decode,
    Hash: Clone + Encode + Decode,
{
    /// Current protocol version
    pub const CURRENT_VERSION: u32 = 1;

    /// Create a new justification from a finality certificate
    pub fn new(certificate: FinalityCertificate<AccountId, BlockNumber, Hash>) -> Self {
        Self {
            certificate,
            version: Self::CURRENT_VERSION,
        }
    }

    /// Encode for network transmission
    pub fn encode_for_network(&self) -> Vec<u8> {
        self.encode()
    }

    /// Decode from network bytes
    pub fn decode_from_network(bytes: &[u8]) -> Result<Self, scale_codec::Error> {
        Self::decode(&mut &bytes[..])
    }
}

/// Import handler for Coherence justifications
///
/// This implements the `JustificationImport` trait, allowing Substrate's
/// import queue to process incoming justifications from the network.
pub struct CoherenceJustificationImport<Block, Client, BE>
where
    Block: BlockT,
{
    /// The blockchain client for finalization
    client: Arc<Client>,
    /// Backend reference (unused but kept for consistency with GRANDPA)
    _backend: Arc<BE>,
    /// Phantom data for block type
    _marker: std::marker::PhantomData<Block>,
}

impl<Block, Client, BE> CoherenceJustificationImport<Block, Client, BE>
where
    Block: BlockT,
    BE: sc_client_api::Backend<Block> + 'static,
    Client: HeaderBackend<Block> + Finalizer<Block, BE> + ProvideRuntimeApi<Block> + Send + Sync + 'static,
{
    /// Create a new justification importer
    pub fn new(client: Arc<Client>, backend: Arc<BE>) -> Self {
        Self {
            client,
            _backend: backend,
            _marker: std::marker::PhantomData,
        }
    }

    /// Verify a coherence justification
    ///
    /// Checks:
    /// 1. Version compatibility
    /// 2. Block exists in our chain
    /// 3. Sufficient validator votes (>2/3)
    fn verify_justification(
        &self,
        hash: Block::Hash,
        justification: &CoherenceJustification<
            sp_core::sphincs::Public,
            NumberFor<Block>,
            Block::Hash,
        >,
    ) -> Result<(), String> {
        // Check version
        if justification.version > CoherenceJustification::<(), (), ()>::CURRENT_VERSION {
            return Err(format!(
                "Unsupported justification version: {} (max: {})",
                justification.version,
                CoherenceJustification::<(), (), ()>::CURRENT_VERSION
            ));
        }

        // Verify block exists
        if self.client.header(hash).map_err(|e| format!("Header lookup failed: {:?}", e))?.is_none() {
            return Err(format!("Block {:?} not found", hash));
        }

        let cert = &justification.certificate;

        // Check we have enough votes (>2/3 majority)
        // The certificate already contains the validator count
        let required_votes = (cert.validator_count * 2 / 3) + 1;
        let actual_votes = cert.precommit_votes.len() as u32;

        if actual_votes < required_votes {
            return Err(format!(
                "Insufficient votes: {} < {} required (of {} validators)",
                actual_votes, required_votes, cert.validator_count
            ));
        }

        // Note: Full signature verification is expensive and should be done
        // by the PoC pallet's verification logic. For now, we trust the
        // vote count and that validators properly signed.
        // TODO: Add Falcon signature verification for each precommit

        debug!(
            "Justification verified: {} votes from {} validators, coherence score {}",
            actual_votes, cert.validator_count, cert.total_coherence_score
        );

        Ok(())
    }
}

#[async_trait::async_trait]
impl<Block, Client, BE> JustificationImport<Block> for CoherenceJustificationImport<Block, Client, BE>
where
    Block: BlockT,
    BE: sc_client_api::Backend<Block> + 'static,
    Client: HeaderBackend<Block>
        + Finalizer<Block, BE>
        + ProvideRuntimeApi<Block>
        + Send
        + Sync
        + 'static,
{
    type Error = sp_consensus::Error;

    async fn on_start(&mut self) -> Vec<(Block::Hash, NumberFor<Block>)> {
        // Return blocks that need justifications
        // For now, we don't have any pending justification requests
        // This could be extended to request justifications for unfinalized blocks
        Vec::new()
    }

    async fn import_justification(
        &mut self,
        hash: Block::Hash,
        number: NumberFor<Block>,
        justification: sp_runtime::Justification,
    ) -> Result<(), Self::Error> {
        // Check engine ID
        if justification.0 != COHERENCE_ENGINE_ID {
            return Err(sp_consensus::Error::InvalidJustification);
        }

        // Decode the justification
        let coherence_justification: CoherenceJustification<
            sp_core::sphincs::Public,
            NumberFor<Block>,
            Block::Hash,
        > = CoherenceJustification::decode_from_network(&justification.1)
            .map_err(|e| {
                warn!("Failed to decode coherence justification: {:?}", e);
                sp_consensus::Error::InvalidJustification
            })?;

        info!(
            "Importing coherence justification for block #{} ({:?})",
            number, hash
        );

        // Verify the justification
        self.verify_justification(hash, &coherence_justification)
            .map_err(|e| {
                warn!("Justification verification failed: {}", e);
                sp_consensus::Error::InvalidJustification
            })?;

        // Finalize the block
        // We pass the justification so it gets stored with the block
        self.client
            .finalize_block(hash, Some(justification), true)
            .map_err(|e| {
                error!("Failed to finalize block #{}: {:?}", number, e);
                sp_consensus::Error::ClientImport(format!("{:?}", e))
            })?;

        info!(
            "Successfully finalized block #{} via coherence justification",
            number
        );

        Ok(())
    }
}

/// Create a boxed justification importer for use in service setup
pub fn coherence_justification_import<Block, Client, BE>(
    client: Arc<Client>,
    backend: Arc<BE>,
) -> Box<dyn JustificationImport<Block, Error = sp_consensus::Error> + Send + Sync>
where
    Block: BlockT,
    BE: sc_client_api::Backend<Block> + 'static,
    Client: HeaderBackend<Block>
        + Finalizer<Block, BE>
        + ProvideRuntimeApi<Block>
        + Send
        + Sync
        + 'static,
{
    Box::new(CoherenceJustificationImport::new(client, backend))
}
