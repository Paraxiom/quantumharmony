//! Post-Quantum Extended Triple Diffie-Hellman (PQ-X3DH) key exchange.
//!
//! Combines classical X25519 DH with ML-KEM-768 post-quantum KEM for
//! defense-in-depth: an attacker must break BOTH to compromise the session.
//!
//! ## Protocol Flow
//!
//! ```text
//! Alice (initiator)                          Bob (responder)
//! ─────────────────                          ───────────────
//!
//! 1. Fetch Bob's PreKeyBundle
//!    (IK_B, SPK_B, OPK_B?, signature)
//!
//! 2. Generate ephemeral keys:
//!    - EK_x25519 (classical)
//!    - EK_mlkem (post-quantum)
//!
//! 3. Compute shared secrets:
//!    DH1 = X25519(IK_A, SPK_B)              // Identity -> SignedPreKey
//!    DH2 = X25519(EK_A, IK_B)               // Ephemeral -> Identity
//!    DH3 = X25519(EK_A, SPK_B)              // Ephemeral -> SignedPreKey
//!    DH4 = X25519(EK_A, OPK_B)              // Ephemeral -> OneTimePreKey (if used)
//!    KEM = ML-KEM-768.Encaps(SPK_B_mlkem)   // Post-quantum KEM
//!
//! 4. Derive master secret:
//!    MS = HKDF(DH1 || DH2 || DH3 || DH4 || KEM_SS)
//!
//! 5. Send initial message:                  6. Receive and process:
//!    - IK_A, EK_A, OPK_B_id?, KEM_CT           - Verify IK_A
//!    - Encrypted payload                       - Compute same DH values
//!                                              - Decapsulate KEM
//!                                              - Derive same MS
//!                                              - Decrypt payload
//! ```

use serde::{Deserialize, Serialize};
use zeroize::{Zeroize, ZeroizeOnDrop};

use crate::crypto::{self, hkdf_derive, ROOT_KEY_SIZE};
use crate::error::{Error, Result};
use crate::keys::{
    IdentityKeyPair, IdentityPublicKey, OneTimePreKey, OneTimePreKeySecret,
    PreKeyBundle, SignedPreKeySecret, X25519_PUBLIC_KEY_SIZE,
};
use crate::ratchet::RatchetState;

/// Initial message sent by Alice to establish a session.
#[derive(Clone, Serialize, Deserialize)]
pub struct X3DHInitMessage {
    /// Alice's identity public key
    pub identity_key: IdentityPublicKey,
    /// Alice's ephemeral X25519 public key
    pub ephemeral_x25519: [u8; X25519_PUBLIC_KEY_SIZE],
    /// Alice's ephemeral ML-KEM public key
    pub ephemeral_mlkem: Vec<u8>,
    /// ML-KEM ciphertext
    pub mlkem_ciphertext: Vec<u8>,
    /// ID of the one-time prekey used (if any)
    pub one_time_prekey_id: Option<u32>,
    /// ID of the signed prekey used
    pub signed_prekey_id: u32,
}

/// Result of X3DH key exchange on the initiator side.
#[derive(Zeroize, ZeroizeOnDrop)]
pub struct X3DHInitResult {
    /// Shared root key for Double Ratchet
    pub root_key: [u8; ROOT_KEY_SIZE],
    /// The initial message to send
    #[zeroize(skip)]
    pub init_message: X3DHInitMessage,
}

/// Result of X3DH key exchange on the responder side.
#[derive(Zeroize, ZeroizeOnDrop)]
pub struct X3DHResponseResult {
    /// Shared root key for Double Ratchet
    pub root_key: [u8; ROOT_KEY_SIZE],
    /// Initiator's identity public key
    #[zeroize(skip)]
    pub peer_identity: IdentityPublicKey,
}

/// Active session between two parties.
pub struct X3DHSession {
    /// Our identity keypair
    identity: IdentityKeyPair,
    /// Peer's identity public key
    peer_identity: IdentityPublicKey,
    /// Double Ratchet state
    pub(crate) ratchet: RatchetState,
}

impl X3DHSession {
    /// Initiate a session with a peer using their prekey bundle.
    ///
    /// This is called by Alice to start a session with Bob.
    pub fn initiate(
        our_identity: IdentityKeyPair,
        peer_bundle: &PreKeyBundle,
    ) -> Result<(Self, X3DHInitMessage)> {
        // Verify the prekey bundle signature
        peer_bundle.verify()?;

        let mut rng = rand::thread_rng();

        // Generate ephemeral X25519 keypair
        let mut ephemeral_x25519_secret = [0u8; 32];
        rand::RngCore::fill_bytes(&mut rng, &mut ephemeral_x25519_secret);
        let ephemeral_x25519_static = x25519_dalek::StaticSecret::from(ephemeral_x25519_secret);
        let ephemeral_x25519_public = *x25519_dalek::PublicKey::from(&ephemeral_x25519_static).as_bytes();

        // Generate ephemeral ML-KEM keypair
        use ml_kem::{EncodedSizeUser, KemCore, MlKem768};
        let (_eph_mlkem_dk, eph_mlkem_ek) = MlKem768::generate(&mut rng);
        let ephemeral_mlkem_public = EncodedSizeUser::as_bytes(&eph_mlkem_ek).to_vec();

        // Perform X25519 DH operations
        // DH1 = X25519(IK_A_secret, SPK_B_public)
        let dh1 = crypto::x25519_dh(&our_identity.x25519_secret, &peer_bundle.signed_prekey.x25519_public);

        // DH2 = X25519(EK_A_secret, IK_B_public)
        let dh2 = crypto::x25519_dh(&ephemeral_x25519_secret, &peer_bundle.identity.x25519);

        // DH3 = X25519(EK_A_secret, SPK_B_public)
        let dh3 = crypto::x25519_dh(&ephemeral_x25519_secret, &peer_bundle.signed_prekey.x25519_public);

        // DH4 = X25519(EK_A_secret, OPK_B_public) if one-time prekey available
        let (dh4, one_time_prekey_id) = if let Some(otpk) = peer_bundle.one_time_prekeys.first() {
            let dh = crypto::x25519_dh(&ephemeral_x25519_secret, &otpk.x25519_public);
            (Some(dh), Some(otpk.id))
        } else {
            (None, None)
        };

        // Perform ML-KEM encapsulation
        let (kem_shared_secret, mlkem_ciphertext) =
            crypto::mlkem_encapsulate(&peer_bundle.signed_prekey.mlkem_public)?;

        // Combine all secrets: DH1 || DH2 || DH3 || [DH4] || KEM_SS
        let mut combined_secret = Vec::new();
        combined_secret.extend_from_slice(&dh1);
        combined_secret.extend_from_slice(&dh2);
        combined_secret.extend_from_slice(&dh3);
        if let Some(ref dh4_bytes) = dh4 {
            combined_secret.extend_from_slice(dh4_bytes);
        }
        combined_secret.extend_from_slice(&kem_shared_secret);

        // Derive root key using HKDF
        let mut root_key = [0u8; ROOT_KEY_SIZE];
        hkdf_derive(
            &combined_secret,
            None, // No salt for X3DH
            b"QuantumHarmony_X3DH_RootKey",
            &mut root_key,
        )?;

        // Zeroize sensitive data
        combined_secret.zeroize();
        ephemeral_x25519_secret.zeroize();

        let init_message = X3DHInitMessage {
            identity_key: our_identity.public_key(),
            ephemeral_x25519: ephemeral_x25519_public,
            ephemeral_mlkem: ephemeral_mlkem_public,
            mlkem_ciphertext,
            one_time_prekey_id,
            signed_prekey_id: peer_bundle.signed_prekey.id,
        };

        // Create ratchet state (Alice is sender)
        let ratchet = RatchetState::new_initiator(
            root_key,
            peer_bundle.signed_prekey.x25519_public,
        )?;

        let session = Self {
            identity: our_identity,
            peer_identity: peer_bundle.identity.clone(),
            ratchet,
        };

        Ok((session, init_message))
    }

    /// Respond to a session initiation.
    ///
    /// This is called by Bob when receiving Alice's initial message.
    pub fn respond(
        our_identity: IdentityKeyPair,
        signed_prekey_secret: &SignedPreKeySecret,
        one_time_prekey_secret: Option<&OneTimePreKeySecret>,
        init_message: &X3DHInitMessage,
    ) -> Result<Self> {
        // DH1 = X25519(SPK_B_secret, IK_A_public)
        let dh1 = crypto::x25519_dh(
            &signed_prekey_secret.x25519_secret,
            &init_message.identity_key.x25519,
        );

        // DH2 = X25519(IK_B_secret, EK_A_public)
        let dh2 = crypto::x25519_dh(
            &our_identity.x25519_secret,
            &init_message.ephemeral_x25519,
        );

        // DH3 = X25519(SPK_B_secret, EK_A_public)
        let dh3 = crypto::x25519_dh(
            &signed_prekey_secret.x25519_secret,
            &init_message.ephemeral_x25519,
        );

        // DH4 = X25519(OPK_B_secret, EK_A_public) if one-time prekey was used
        let dh4 = if let Some(otpk_secret) = one_time_prekey_secret {
            if init_message.one_time_prekey_id == Some(otpk_secret.id) {
                Some(crypto::x25519_dh(
                    &otpk_secret.x25519_secret,
                    &init_message.ephemeral_x25519,
                ))
            } else {
                return Err(Error::InvalidPreKeyBundle(
                    "one-time prekey ID mismatch".into(),
                ));
            }
        } else {
            if init_message.one_time_prekey_id.is_some() {
                return Err(Error::InvalidPreKeyBundle(
                    "one-time prekey expected but not provided".into(),
                ));
            }
            None
        };

        // Decapsulate ML-KEM
        let kem_shared_secret = crypto::mlkem_decapsulate(
            &signed_prekey_secret.mlkem_secret,
            &init_message.mlkem_ciphertext,
        )?;

        // Combine all secrets (same order as initiator)
        let mut combined_secret = Vec::new();
        combined_secret.extend_from_slice(&dh1);
        combined_secret.extend_from_slice(&dh2);
        combined_secret.extend_from_slice(&dh3);
        if let Some(ref dh4_bytes) = dh4 {
            combined_secret.extend_from_slice(dh4_bytes);
        }
        combined_secret.extend_from_slice(&kem_shared_secret);

        // Derive root key using HKDF
        let mut root_key = [0u8; ROOT_KEY_SIZE];
        hkdf_derive(
            &combined_secret,
            None,
            b"QuantumHarmony_X3DH_RootKey",
            &mut root_key,
        )?;

        // Zeroize sensitive data
        combined_secret.zeroize();

        // Create ratchet state (Bob is responder)
        let ratchet = RatchetState::new_responder(
            root_key,
            signed_prekey_secret.x25519_secret,
        )?;

        Ok(Self {
            identity: our_identity,
            peer_identity: init_message.identity_key.clone(),
            ratchet,
        })
    }

    /// Get our identity public key.
    pub fn our_identity(&self) -> IdentityPublicKey {
        self.identity.public_key()
    }

    /// Get the peer's identity public key.
    pub fn peer_identity(&self) -> &IdentityPublicKey {
        &self.peer_identity
    }

    /// Encrypt a message for the peer.
    pub fn encrypt(&mut self, plaintext: &[u8]) -> Result<Vec<u8>> {
        self.ratchet.encrypt(plaintext)
    }

    /// Decrypt a message from the peer.
    pub fn decrypt(&mut self, ciphertext: &[u8]) -> Result<Vec<u8>> {
        self.ratchet.decrypt(ciphertext)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::keys::{generate_one_time_prekey, generate_signed_prekey};

    #[test]
    fn test_x3dh_full_flow() {
        // Setup: Bob generates keys and publishes prekey bundle
        let bob_identity = IdentityKeyPair::generate().unwrap();
        let (bob_signed_pk, bob_signed_sk) = generate_signed_prekey(&bob_identity, 1).unwrap();
        let (bob_otpk, bob_otpk_secret) = generate_one_time_prekey(1).unwrap();

        let bob_bundle = PreKeyBundle {
            identity: bob_identity.public_key(),
            signed_prekey: bob_signed_pk,
            one_time_prekeys: vec![bob_otpk],
        };

        // Alice initiates session
        let alice_identity = IdentityKeyPair::generate().unwrap();
        let (mut alice_session, init_message) =
            X3DHSession::initiate(alice_identity, &bob_bundle).unwrap();

        // Bob responds
        let mut bob_session = X3DHSession::respond(
            bob_identity,
            &bob_signed_sk,
            Some(&bob_otpk_secret),
            &init_message,
        ).unwrap();

        // Test message exchange
        let plaintext = b"Hello, post-quantum world!";
        let ciphertext = alice_session.encrypt(plaintext).unwrap();
        let decrypted = bob_session.decrypt(&ciphertext).unwrap();

        assert_eq!(plaintext.as_slice(), decrypted.as_slice());

        // Test reverse direction
        let response = b"Hello from Bob!";
        let ciphertext2 = bob_session.encrypt(response).unwrap();
        let decrypted2 = alice_session.decrypt(&ciphertext2).unwrap();

        assert_eq!(response.as_slice(), decrypted2.as_slice());
    }

    #[test]
    fn test_x3dh_without_one_time_prekey() {
        // Setup: Bob generates keys without one-time prekeys
        let bob_identity = IdentityKeyPair::generate().unwrap();
        let (bob_signed_pk, bob_signed_sk) = generate_signed_prekey(&bob_identity, 1).unwrap();

        let bob_bundle = PreKeyBundle {
            identity: bob_identity.public_key(),
            signed_prekey: bob_signed_pk,
            one_time_prekeys: vec![], // No one-time prekeys
        };

        // Alice initiates session
        let alice_identity = IdentityKeyPair::generate().unwrap();
        let (mut alice_session, init_message) =
            X3DHSession::initiate(alice_identity, &bob_bundle).unwrap();

        assert!(init_message.one_time_prekey_id.is_none());

        // Bob responds
        let mut bob_session = X3DHSession::respond(
            bob_identity,
            &bob_signed_sk,
            None, // No one-time prekey
            &init_message,
        ).unwrap();

        // Test message exchange still works
        let plaintext = b"Hello without one-time prekey!";
        let ciphertext = alice_session.encrypt(plaintext).unwrap();
        let decrypted = bob_session.decrypt(&ciphertext).unwrap();

        assert_eq!(plaintext.as_slice(), decrypted.as_slice());
    }
}
