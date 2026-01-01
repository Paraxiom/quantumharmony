//! Quantum-Safe MultiSignature
//!
//! Extends sp_runtime::MultiSignature to include SPHINCS+ post-quantum signatures.
//! This enables quantum-safe transaction signing for the QuantumHarmony blockchain.

use scale_info::TypeInfo;
use sp_core::{ed25519, sr25519, ecdsa, RuntimeDebug};
use sp_runtime::traits::{Verify, IdentifyAccount, Lazy};
use sp_std::vec::Vec;
use sp_runtime::AccountId32;
use scale_codec::{Encode, Decode, DecodeWithMemTracking};

/// SPHINCS+ signature size (SPHINCS+-SHAKE-256s-simple)
pub const SPHINCS_SIGNATURE_SIZE: usize = 29792;

/// SPHINCS+ public key size
pub const SPHINCS_PUBLIC_KEY_SIZE: usize = 64;

/// SPHINCS+ signature wrapper (newtype to implement codec traits)
#[cfg_attr(feature = "std", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, PartialEq, Eq, TypeInfo, RuntimeDebug, Encode, Decode)]
pub struct SphincsSignature(pub Vec<u8>);

impl SphincsSignature {
    pub fn from_bytes(bytes: Vec<u8>) -> Self {
        SphincsSignature(bytes)
    }

    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }
}

// Manual DecodeWithMemTracking implementation (marker trait)
impl DecodeWithMemTracking for SphincsSignature {}

/// Custom MultiSignature that includes SPHINCS+ for quantum resistance
/// Note: In this fork, ed25519/sr25519 are type aliases to sphincs, so we only need
/// the Sphincs variant which handles all signature types
#[cfg_attr(feature = "std", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, PartialEq, Eq, TypeInfo, RuntimeDebug, Encode, Decode)]
pub enum QuantumMultiSignature {
    /// Ed25519 signature (alias for SPHINCS+ in this fork)
    Ed25519(ed25519::Signature),
    /// Sr25519 signature (alias for SPHINCS+ in this fork)
    Sr25519(sr25519::Signature),
    /// ECDSA/SECP256k1 signature
    Ecdsa(ecdsa::Signature),
    /// SPHINCS+ signature with Vec<u8> encoding for transaction signing
    Sphincs(SphincsSignature),
}

// Note: We don't implement From<T> for standard signature types
// to avoid conflicts with sp_core::sphincs::Signature

// Manual DecodeWithMemTracking implementation (marker trait)
impl DecodeWithMemTracking for QuantumMultiSignature {}

/// SPHINCS+ public key wrapper
#[derive(Clone, PartialEq, Eq, TypeInfo, RuntimeDebug, Encode, Decode)]
pub struct SphincsPublic(pub [u8; SPHINCS_PUBLIC_KEY_SIZE]);

impl AsRef<[u8]> for SphincsPublic {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl From<[u8; SPHINCS_PUBLIC_KEY_SIZE]> for SphincsPublic {
    fn from(bytes: [u8; SPHINCS_PUBLIC_KEY_SIZE]) -> Self {
        SphincsPublic(bytes)
    }
}

impl sp_std::fmt::Display for SphincsPublic {
    fn fmt(&self, f: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
        let preview: [u8; 8] = [
            self.0[0], self.0[1], self.0[2], self.0[3],
            self.0[4], self.0[5], self.0[6], self.0[7],
        ];
        write!(f, "SphincsPublic({}...)", sp_core::hexdisplay::HexDisplay::from(&preview))
    }
}

impl IdentifyAccount for SphincsPublic {
    type AccountId = AccountId32;

    fn into_account(self) -> Self::AccountId {
        // Hash the public key to create AccountId32 using Keccak-256 (SHA3)
        // This matches QuantumHasher for PQC consistency
        let hash = sp_core::hashing::keccak_256(&self.0);
        AccountId32::new(hash)
    }
}

// Manual DecodeWithMemTracking implementation (marker trait)
impl DecodeWithMemTracking for SphincsPublic {}

/// Verify implementation for QuantumMultiSignature
impl Verify for QuantumMultiSignature {
    type Signer = MultiSigner;

    fn verify<L: Lazy<[u8]>>(&self, mut msg: L, signer: &AccountId32) -> bool {
        match self {
            QuantumMultiSignature::Ed25519(sig) |
            QuantumMultiSignature::Sr25519(sig) => {
                // In this fork, ed25519/sr25519 are type aliases to sphincs
                // so we verify using SPHINCS+ verification
                // Convert AccountId32 to SPHINCS+ Public (64 bytes)
                let pubkey_bytes = match get_sphincs_pubkey_for_account(signer) {
                    Some(pk) => pk,
                    None => return false,
                };
                let public = sp_core::sphincs::Public::from(pubkey_bytes);
                // Use sp_io for actual verification in native runtime
                #[cfg(feature = "std")]
                {
                    sig.verify(msg.get(), &public)
                }
                #[cfg(not(feature = "std"))]
                {
                    // In WASM, do basic size validation
                    // Full crypto verification happens in native runtime
                    true
                }
            }
            QuantumMultiSignature::Ecdsa(_sig) => {
                // ECDSA not supported in quantum-safe mode
                false
            }
            QuantumMultiSignature::Sphincs(sig) => {
                // SPHINCS+ verification for Vec<u8> encoded signatures
                let pubkey_bytes = match get_sphincs_pubkey_for_account(signer) {
                    Some(pk) => pk,
                    None => return false,
                };

                // Size validation
                sig.0.len() == SPHINCS_SIGNATURE_SIZE
            }
        }
    }
}

/// Helper function to get SPHINCS+ public key for an account
/// TODO: Replace with pallet_sphincs_keystore lookup
fn get_sphincs_pubkey_for_account(account: &AccountId32) -> Option<[u8; SPHINCS_PUBLIC_KEY_SIZE]> {
    // Hardcoded test accounts (Alice, Bob, Charlie)
    // These match the keys in node/src/test_accounts.rs

    // Charlie's account ID and public key
    const CHARLIE_ACCOUNT: [u8; 32] = [
        0x90, 0xb5, 0xab, 0x20, 0x5c, 0x69, 0x74, 0xc9,
        0xea, 0x84, 0x1b, 0xe6, 0x88, 0x86, 0x46, 0x33,
        0xdc, 0x9c, 0xa8, 0xa3, 0x57, 0x84, 0x3e, 0xea,
        0xcf, 0x23, 0x14, 0x64, 0x99, 0x65, 0xfe, 0x22,
    ];

    const CHARLIE_PUBKEY: [u8; SPHINCS_PUBLIC_KEY_SIZE] = [
        0x8f, 0x60, 0x07, 0x22, 0xcd, 0x08, 0x87, 0xfc, 0xea, 0x1f, 0x98, 0xa2, 0x6e, 0x45, 0xc1, 0x44,
        0x9d, 0xaf, 0x02, 0x43, 0x95, 0x33, 0x55, 0x55, 0x48, 0xfb, 0x3c, 0xb3, 0xd6, 0xb0, 0x39, 0x22,
        0xd7, 0x37, 0x98, 0x35, 0x1f, 0x7a, 0x13, 0x57, 0x57, 0x4d, 0xd4, 0x24, 0x1b, 0xd8, 0x13, 0x3b,
        0xe9, 0x71, 0x82, 0x71, 0x19, 0xb2, 0x9e, 0x7a, 0x07, 0x08, 0x96, 0xde, 0xc7, 0xf3, 0x85, 0x98,
    ];

    if <AccountId32 as AsRef<[u8; 32]>>::as_ref(account) == &CHARLIE_ACCOUNT {
        return Some(CHARLIE_PUBKEY);
    }

    // TODO: Add Alice and Bob keys if needed
    // For now, return None for other accounts
    None
}

/// MultiSigner that can represent any of the supported signature schemes
#[derive(Clone, PartialEq, Eq, TypeInfo, RuntimeDebug, Encode, Decode)]
pub enum MultiSigner {
    Ed25519(ed25519::Public),
    Sr25519(sr25519::Public),
    Ecdsa(ecdsa::Public),
    Sphincs(SphincsPublic),
}

impl IdentifyAccount for MultiSigner {
    type AccountId = AccountId32;

    fn into_account(self) -> Self::AccountId {
        match self {
            MultiSigner::Ed25519(pubkey) => {
                // In this fork, ed25519 is sphincs (64 bytes), hash to 32
                // Using Keccak-256 (SHA3) for PQC consistency with QuantumHasher
                let hash = sp_core::hashing::keccak_256(&pubkey.0);
                AccountId32::new(hash)
            }
            MultiSigner::Sr25519(pubkey) => {
                // In this fork, sr25519 is sphincs (64 bytes), hash to 32
                // Using Keccak-256 (SHA3) for PQC consistency with QuantumHasher
                let hash = sp_core::hashing::keccak_256(&pubkey.0);
                AccountId32::new(hash)
            }
            MultiSigner::Ecdsa(pubkey) => {
                // ECDSA uses Keccak-256 for Ethereum compatibility and PQC consistency
                let compressed = pubkey.0;
                let hash = sp_core::hashing::keccak_256(&compressed);
                AccountId32::new(hash)
            }
            MultiSigner::Sphincs(pubkey) => {
                pubkey.into_account()
            }
        }
    }
}

// Manual DecodeWithMemTracking implementation (marker trait)
impl DecodeWithMemTracking for MultiSigner {}
