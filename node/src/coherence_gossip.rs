//! Quantum Coherence Vote Gossip Protocol
//!
//! This module implements P2P gossip for CoherenceVote messages, enabling
//! real multi-validator Byzantine consensus (like GRANDPA's vote gossip).
//!
//! ## Architecture
//!
//! - Uses Substrate's notification protocol (sc-network)
//! - Broadcasts CoherenceVotes to all connected validators
//! - Receives votes from other validators
//! - Validates votes before forwarding (prevents spam)
//!
//! ## Protocol Flow
//!
//! 1. Validator creates vote for block
//! 2. Vote broadcast to all peers via gossip
//! 3. Peers receive, validate, and re-broadcast
//! 4. Votes collected until supermajority reached
//! 5. Finality certificate generated

use scale_codec::{Decode, Encode};
use sc_network::{
    config::{NonDefaultSetConfig, SetConfig, NonReservedPeerMode},
    service::traits::NotificationService,
    ProtocolName,
};
use sp_runtime::traits::{Block as BlockT, NumberFor};

/// Protocol name for coherence vote gossip
pub const COHERENCE_PROTOCOL_NAME: &str = "/quantumharmony/coherence/1";

/// Gossip message for coherence votes
///
/// ## PQ-MonadBFT Hybrid Consensus (Phase 1)
///
/// Linear O(n) voting architecture:
/// - Validators send votes ONLY to the current leader
/// - Leader aggregates votes and broadcasts certificate
/// - Total messages: 3N instead of O(N log N) gossip
///
/// ## QPP Phase 4: Triple Ratchet Integration (Future Enhancement)
///
/// **INTEGRATION POINT FOR TRIPLE RATCHET ENCRYPTION**
///
/// The QPP Triple Ratchet infrastructure is fully implemented and ready to use
/// (see `qpp_integration::ValidatorMessaging`). To integrate encrypted vote gossip:
///
/// 1. Add new enum variant:
///    ```ignore
///    EncryptedVote {
///        recipient_id: ValidatorId,
///        ciphertext: Vec<u8>,
///        message_counter: u64,
///    }
///    ```
///
/// 2. Initialize Triple Ratchet in `CoherenceGadget`:
///    ```ignore
///    let mut validator_messaging = ValidatorMessaging::new();
///    validator_messaging.initialize_from_falcon(falcon_sk, falcon_pk)?;
///    ```
///
/// 3. Encrypt votes before gossiping:
///    ```ignore
///    let vote_bytes = vote.encode();
///    let ciphertext = validator_messaging.encrypt_message(&vote_bytes)?;
///    ```
///
/// 4. Decrypt votes on reception:
///    ```ignore
///    let plaintext = validator_messaging.decrypt_message(&ciphertext)?;
///    let vote = CoherenceVote::decode(&mut &plaintext[..])?;
///    ```
///
/// 5. Check for rekeying periodically:
///    ```ignore
///    if validator_messaging.needs_rekey(1000, 3600) {
///        validator_messaging.rekey()?;
///    }
///    ```
///
/// **Benefits**: Forward secrecy, post-compromise security, per-message key rotation
///
/// **Implementation Status**: Infrastructure ready, integration pending (LOW RISK)
#[derive(Clone, Encode, Decode, Debug)]
pub enum GossipMessage<Block: BlockT> {
    /// A vote for a block (legacy gossip - kept for backwards compatibility)
    Vote(pallet_proof_of_coherence::types::CoherenceVote<sp_core::sr25519::Public, NumberFor<Block>, Block::Hash>),

    /// Request votes for a specific block
    VoteRequest(Block::Hash),

    /// A finality justification for a block
    /// This contains the full CoherenceJustification that allows full nodes
    /// to verify and finalize the block without being validators
    Justification {
        /// Block hash being justified
        block_hash: Block::Hash,
        /// Block number being justified
        block_number: NumberFor<Block>,
        /// Encoded justification (CoherenceJustification struct)
        encoded_justification: Vec<u8>,
    },

    /// PQ-MonadBFT Phase 1: Direct vote to leader (O(n) complexity)
    /// Validators send their vote directly to the elected leader only,
    /// instead of gossiping to all peers
    VoteToLeader {
        /// The vote itself
        vote: pallet_proof_of_coherence::types::CoherenceVote<sp_core::sr25519::Public, NumberFor<Block>, Block::Hash>,
        /// QBER measurement from validator's QKD channel (basis points, 0-10000)
        qber_measurement: u16,
        /// QKD channel ID measured
        qkd_channel_id: u32,
    },

    /// PQ-MonadBFT Phase 1: Finality certificate broadcast from leader
    /// After collecting 2/3+ votes, leader creates and broadcasts certificate
    FinalityCertificateBroadcast {
        /// Block hash finalized
        block_hash: Block::Hash,
        /// Block number finalized
        block_number: NumberFor<Block>,
        /// Aggregated QBER from all votes (weighted average, basis points)
        aggregated_qber: u16,
        /// Number of validators with QBER < threshold (11%)
        healthy_channels: u32,
        /// Total validators who voted
        validator_count: u32,
        /// Encoded finality certificate
        encoded_certificate: Vec<u8>,
    },
}

/// Create coherence gossip protocol configuration (like GRANDPA's grandpa_peers_set_config)
///
/// Returns a tuple of:
/// - NonDefaultSetConfig to add to network
/// - NotificationService for receiving messages
pub fn coherence_peers_set_config(
) -> (
    NonDefaultSetConfig,
    Box<dyn NotificationService>,
) {
    NonDefaultSetConfig::new(
        ProtocolName::from(COHERENCE_PROTOCOL_NAME),
        Vec::new(), // fallback names
        1024 * 1024, // max notification size: 1 MB
        None, // handshake
        SetConfig {
            in_peers: 25,
            out_peers: 25,
            reserved_nodes: Vec::new(),
            non_reserved_mode: NonReservedPeerMode::Accept,
        },
    )
}
