//! Double Ratchet protocol implementation.
//!
//! Provides forward secrecy and post-compromise security through
//! continuous key rotation using DH ratcheting and symmetric ratcheting.
//!
//! ## Ratchet Structure
//!
//! ```text
//! Root Key (RK)
//!     │
//!     ├── DH Ratchet (on each direction change)
//!     │   └── New RK, Chain Key
//!     │
//!     └── Chain Key (CK)
//!         │
//!         ├── Symmetric Ratchet (each message)
//!         │   └── New CK, Message Key
//!         │
//!         └── Message Key (MK)
//!             └── Encrypt/Decrypt message
//! ```

use rand::RngCore;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use zeroize::{Zeroize, ZeroizeOnDrop};

use crate::crypto::{
    self, aead_decrypt, aead_encrypt, generate_nonce, kdf_ck, kdf_rk,
    AEAD_KEY_SIZE, AEAD_NONCE_SIZE, CHAIN_KEY_SIZE, ROOT_KEY_SIZE,
};
use crate::error::{Error, Result};
use crate::keys::X25519_PUBLIC_KEY_SIZE;
use crate::{MAX_MESSAGE_SIZE, PROTOCOL_VERSION};

/// Maximum number of skipped messages to store (prevent DoS)
const MAX_SKIP: u32 = 1000;

/// Header prepended to each encrypted message.
#[derive(Clone, Serialize, Deserialize)]
pub struct MessageHeader {
    /// Protocol version
    pub version: u8,
    /// Sender's current ratchet public key
    pub ratchet_key: [u8; X25519_PUBLIC_KEY_SIZE],
    /// Previous chain length (for skipped messages)
    pub previous_chain_length: u32,
    /// Message number in current chain
    pub message_number: u32,
}

impl MessageHeader {
    fn to_bytes(&self) -> Vec<u8> {
        bincode::serialize(self).expect("header serialization should not fail")
    }

    fn from_bytes(bytes: &[u8]) -> Result<Self> {
        bincode::deserialize(bytes).map_err(|e| Error::Serialization(e.to_string()))
    }
}

/// Complete encrypted message including header.
#[derive(Clone, Serialize, Deserialize)]
pub struct RatchetMessage {
    /// Encrypted header (authenticated but visible)
    pub header: MessageHeader,
    /// Encrypted payload
    pub ciphertext: Vec<u8>,
}

impl RatchetMessage {
    /// Serialize to bytes.
    pub fn to_bytes(&self) -> Vec<u8> {
        bincode::serialize(self).expect("message serialization should not fail")
    }

    /// Deserialize from bytes.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
        bincode::deserialize(bytes).map_err(|e| Error::Serialization(e.to_string()))
    }
}

/// State for a single receive chain (from a specific ratchet key).
#[derive(Clone, Zeroize, ZeroizeOnDrop)]
struct ChainState {
    /// Current chain key
    chain_key: [u8; CHAIN_KEY_SIZE],
    /// Number of messages received on this chain
    #[zeroize(skip)]
    message_number: u32,
}

/// Skipped message key (for out-of-order delivery).
#[derive(Clone, Hash, Eq, PartialEq)]
struct SkippedKey {
    /// Ratchet public key
    ratchet_key: [u8; X25519_PUBLIC_KEY_SIZE],
    /// Message number
    message_number: u32,
}

/// Double Ratchet state machine.
pub struct RatchetState {
    /// Current root key
    root_key: [u8; ROOT_KEY_SIZE],

    /// Our current ratchet keypair (secret)
    our_ratchet_secret: [u8; 32],
    /// Our current ratchet public key
    our_ratchet_public: [u8; X25519_PUBLIC_KEY_SIZE],

    /// Their current ratchet public key
    their_ratchet_public: Option<[u8; X25519_PUBLIC_KEY_SIZE]>,

    /// Sending chain key
    sending_chain: Option<ChainState>,
    /// Receiving chain key
    receiving_chain: Option<ChainState>,

    /// Number of messages sent on current sending chain
    send_message_number: u32,
    /// Previous sending chain length
    previous_chain_length: u32,

    /// Skipped message keys (for out-of-order delivery)
    skipped_keys: HashMap<SkippedKey, [u8; AEAD_KEY_SIZE]>,
}

impl RatchetState {
    /// Create new ratchet state for the session initiator (Alice).
    pub fn new_initiator(
        root_key: [u8; ROOT_KEY_SIZE],
        their_ratchet_public: [u8; X25519_PUBLIC_KEY_SIZE],
    ) -> Result<Self> {
        let mut rng = rand::thread_rng();

        // Generate our first ratchet keypair
        let mut our_ratchet_secret = [0u8; 32];
        rng.fill_bytes(&mut our_ratchet_secret);
        let our_static = x25519_dalek::StaticSecret::from(our_ratchet_secret);
        let our_ratchet_public = *x25519_dalek::PublicKey::from(&our_static).as_bytes();

        // Perform initial DH ratchet
        let dh_output = crypto::x25519_dh(&our_ratchet_secret, &their_ratchet_public);
        let (new_root, sending_chain_key) = kdf_rk(&root_key, &dh_output);

        Ok(Self {
            root_key: new_root,
            our_ratchet_secret,
            our_ratchet_public,
            their_ratchet_public: Some(their_ratchet_public),
            sending_chain: Some(ChainState {
                chain_key: sending_chain_key,
                message_number: 0,
            }),
            receiving_chain: None,
            send_message_number: 0,
            previous_chain_length: 0,
            skipped_keys: HashMap::new(),
        })
    }

    /// Create new ratchet state for the session responder (Bob).
    pub fn new_responder(
        root_key: [u8; ROOT_KEY_SIZE],
        our_ratchet_secret: [u8; 32],
    ) -> Result<Self> {
        let our_static = x25519_dalek::StaticSecret::from(our_ratchet_secret);
        let our_ratchet_public = *x25519_dalek::PublicKey::from(&our_static).as_bytes();

        Ok(Self {
            root_key,
            our_ratchet_secret,
            our_ratchet_public,
            their_ratchet_public: None,
            sending_chain: None,
            receiving_chain: None,
            send_message_number: 0,
            previous_chain_length: 0,
            skipped_keys: HashMap::new(),
        })
    }

    /// Encrypt a message.
    pub fn encrypt(&mut self, plaintext: &[u8]) -> Result<Vec<u8>> {
        if plaintext.len() > MAX_MESSAGE_SIZE {
            return Err(Error::MessageTooLarge {
                size: plaintext.len(),
                max: MAX_MESSAGE_SIZE,
            });
        }

        // Ensure we have a sending chain
        if self.sending_chain.is_none() {
            return Err(Error::SessionNotEstablished);
        }

        let sending_chain = self.sending_chain.as_mut().unwrap();

        // Derive message key
        let (new_chain_key, message_key) = kdf_ck(&sending_chain.chain_key);
        sending_chain.chain_key = new_chain_key;

        let header = MessageHeader {
            version: PROTOCOL_VERSION,
            ratchet_key: self.our_ratchet_public,
            previous_chain_length: self.previous_chain_length,
            message_number: self.send_message_number,
        };

        let header_bytes = header.to_bytes();
        // Nonce is derived from message number only (no direction flag needed
        // since each chain has unique keys)
        let nonce = generate_nonce(self.send_message_number as u64, true);

        // Encrypt plaintext with header as AAD
        let ciphertext = aead_encrypt(&message_key, &nonce, plaintext, &header_bytes)?;

        self.send_message_number += 1;

        let message = RatchetMessage { header, ciphertext };
        Ok(message.to_bytes())
    }

    /// Decrypt a message.
    pub fn decrypt(&mut self, message_bytes: &[u8]) -> Result<Vec<u8>> {
        let message = RatchetMessage::from_bytes(message_bytes)?;

        // Check version
        if message.header.version != PROTOCOL_VERSION {
            return Err(Error::InvalidVersion {
                got: message.header.version,
                expected: PROTOCOL_VERSION,
            });
        }

        // Try to decrypt with skipped keys first
        let skipped_key = SkippedKey {
            ratchet_key: message.header.ratchet_key,
            message_number: message.header.message_number,
        };

        if let Some(message_key) = self.skipped_keys.remove(&skipped_key) {
            let header_bytes = message.header.to_bytes();
            // Use same nonce as sender
            let nonce = generate_nonce(message.header.message_number as u64, true);
            return aead_decrypt(&message_key, &nonce, &message.ciphertext, &header_bytes);
        }

        // Check if we need to perform a DH ratchet
        let their_key = message.header.ratchet_key;
        if self.their_ratchet_public.as_ref() != Some(&their_key) {
            self.dh_ratchet(&their_key, &message.header)?;
        }

        // Skip any missed messages
        self.skip_messages(message.header.message_number)?;

        // Decrypt with current receiving chain
        let receiving_chain = self.receiving_chain.as_mut()
            .ok_or_else(|| Error::RatchetState("no receiving chain".into()))?;

        let (new_chain_key, message_key) = kdf_ck(&receiving_chain.chain_key);
        receiving_chain.chain_key = new_chain_key;
        receiving_chain.message_number += 1;

        let header_bytes = message.header.to_bytes();
        // Use same nonce derivation as sender (is_sender=true means "this was sent")
        let nonce = generate_nonce(message.header.message_number as u64, true);

        aead_decrypt(&message_key, &nonce, &message.ciphertext, &header_bytes)
    }

    /// Perform DH ratchet step (when receiving from a new ratchet key).
    fn dh_ratchet(&mut self, their_new_key: &[u8; X25519_PUBLIC_KEY_SIZE], header: &MessageHeader) -> Result<()> {
        // Store previous chain length
        self.previous_chain_length = self.send_message_number;
        self.send_message_number = 0;

        // Skip any remaining messages from previous receiving chain
        if self.receiving_chain.is_some() && self.their_ratchet_public.is_some() {
            self.skip_messages(header.previous_chain_length)?;
        }

        self.their_ratchet_public = Some(*their_new_key);

        // DH with their new key and our current secret
        let dh_output = crypto::x25519_dh(&self.our_ratchet_secret, their_new_key);
        let (new_root, receiving_chain_key) = kdf_rk(&self.root_key, &dh_output);
        self.root_key = new_root;

        self.receiving_chain = Some(ChainState {
            chain_key: receiving_chain_key,
            message_number: 0,
        });

        // Generate new ratchet keypair for sending
        let mut rng = rand::thread_rng();
        let mut new_secret = [0u8; 32];
        rng.fill_bytes(&mut new_secret);
        let new_static = x25519_dalek::StaticSecret::from(new_secret);
        let new_public = *x25519_dalek::PublicKey::from(&new_static).as_bytes();

        self.our_ratchet_secret = new_secret;
        self.our_ratchet_public = new_public;

        // DH with their key and our new secret
        let dh_output = crypto::x25519_dh(&self.our_ratchet_secret, their_new_key);
        let (new_root, sending_chain_key) = kdf_rk(&self.root_key, &dh_output);
        self.root_key = new_root;

        self.sending_chain = Some(ChainState {
            chain_key: sending_chain_key,
            message_number: 0,
        });

        Ok(())
    }

    /// Skip messages and store their keys for later decryption.
    fn skip_messages(&mut self, until: u32) -> Result<()> {
        let receiving_chain = match self.receiving_chain.as_mut() {
            Some(c) => c,
            None => return Ok(()),
        };

        let their_key = match self.their_ratchet_public {
            Some(k) => k,
            None => return Ok(()),
        };

        if until < receiving_chain.message_number {
            return Ok(()); // No messages to skip
        }

        let skip_count = until - receiving_chain.message_number;
        if skip_count > MAX_SKIP {
            return Err(Error::RatchetState(format!(
                "too many skipped messages: {} (max {})",
                skip_count, MAX_SKIP
            )));
        }

        while receiving_chain.message_number < until {
            let (new_chain_key, message_key) = kdf_ck(&receiving_chain.chain_key);
            receiving_chain.chain_key = new_chain_key;

            let skipped = SkippedKey {
                ratchet_key: their_key,
                message_number: receiving_chain.message_number,
            };
            self.skipped_keys.insert(skipped, message_key);

            receiving_chain.message_number += 1;
        }

        // Limit skipped keys storage
        while self.skipped_keys.len() > MAX_SKIP as usize {
            if let Some(key) = self.skipped_keys.keys().next().cloned() {
                self.skipped_keys.remove(&key);
            }
        }

        Ok(())
    }
}

impl Drop for RatchetState {
    fn drop(&mut self) {
        self.root_key.zeroize();
        self.our_ratchet_secret.zeroize();
        if let Some(ref mut chain) = self.sending_chain {
            chain.chain_key.zeroize();
        }
        if let Some(ref mut chain) = self.receiving_chain {
            chain.chain_key.zeroize();
        }
        for (_, key) in self.skipped_keys.iter_mut() {
            key.zeroize();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn create_test_sessions() -> (RatchetState, RatchetState) {
        let root_key = [0x42u8; ROOT_KEY_SIZE];

        // Bob's initial ratchet keypair
        let bob_secret = [0x43u8; 32];
        let bob_static = x25519_dalek::StaticSecret::from(bob_secret);
        let bob_public = *x25519_dalek::PublicKey::from(&bob_static).as_bytes();

        let alice = RatchetState::new_initiator(root_key, bob_public).unwrap();
        let bob = RatchetState::new_responder(root_key, bob_secret).unwrap();

        (alice, bob)
    }

    #[test]
    fn test_basic_message_exchange() {
        let (mut alice, mut bob) = create_test_sessions();

        // Alice sends to Bob
        let plaintext = b"Hello Bob!";
        let ciphertext = alice.encrypt(plaintext).unwrap();
        let decrypted = bob.decrypt(&ciphertext).unwrap();
        assert_eq!(plaintext.as_slice(), decrypted.as_slice());

        // Bob sends to Alice
        let response = b"Hello Alice!";
        let ciphertext2 = bob.encrypt(response).unwrap();
        let decrypted2 = alice.decrypt(&ciphertext2).unwrap();
        assert_eq!(response.as_slice(), decrypted2.as_slice());
    }

    #[test]
    fn test_multiple_messages_same_direction() {
        let (mut alice, mut bob) = create_test_sessions();

        // Alice sends multiple messages
        for i in 0..10 {
            let msg = format!("Message {}", i);
            let ct = alice.encrypt(msg.as_bytes()).unwrap();
            let pt = bob.decrypt(&ct).unwrap();
            assert_eq!(msg.as_bytes(), pt.as_slice());
        }
    }

    #[test]
    fn test_out_of_order_delivery() {
        let (mut alice, mut bob) = create_test_sessions();

        // Alice sends 3 messages
        let ct1 = alice.encrypt(b"Message 1").unwrap();
        let ct2 = alice.encrypt(b"Message 2").unwrap();
        let ct3 = alice.encrypt(b"Message 3").unwrap();

        // Bob receives out of order
        let pt3 = bob.decrypt(&ct3).unwrap();
        assert_eq!(b"Message 3".as_slice(), pt3.as_slice());

        let pt1 = bob.decrypt(&ct1).unwrap();
        assert_eq!(b"Message 1".as_slice(), pt1.as_slice());

        let pt2 = bob.decrypt(&ct2).unwrap();
        assert_eq!(b"Message 2".as_slice(), pt2.as_slice());
    }

    #[test]
    fn test_forward_secrecy() {
        let (mut alice, mut bob) = create_test_sessions();

        // Exchange messages
        let ct1 = alice.encrypt(b"Secret 1").unwrap();
        bob.decrypt(&ct1).unwrap();

        let ct2 = bob.encrypt(b"Secret 2").unwrap();
        alice.decrypt(&ct2).unwrap();

        // Save Alice's current keys
        let old_root = alice.root_key;

        // Exchange more messages (causes ratchet)
        let ct3 = alice.encrypt(b"Secret 3").unwrap();
        bob.decrypt(&ct3).unwrap();

        let ct4 = bob.encrypt(b"Secret 4").unwrap();
        alice.decrypt(&ct4).unwrap();

        // Keys should have changed
        assert_ne!(old_root, alice.root_key);
    }

    #[test]
    fn test_replay_detection() {
        let (mut alice, mut bob) = create_test_sessions();

        let ct = alice.encrypt(b"Test message").unwrap();

        // First decryption succeeds
        bob.decrypt(&ct).unwrap();

        // Replay attempt fails (message key was consumed)
        let result = bob.decrypt(&ct);
        assert!(result.is_err());
    }
}
