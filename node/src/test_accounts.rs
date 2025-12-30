//! SPHINCS+ Public Keys for QuantumHarmony Genesis
//!
//! This file contains ONLY PUBLIC KEYS for the genesis validators.
//! SECRET KEYS are NOT stored in source code for security reasons.
//!
//! For validators:
//! - Keys are stored securely in the keystore directory
//! - Use VALIDATOR_KEY_FILE environment variable for production
//! - Never commit secret keys to version control
//!
//! SECURITY NOTE:
//! The production network was launched with unique SPHINCS+ keys.
//! Secret keys are stored securely on validator servers, NOT in this repository.

use sp_core::sphincs::Public as SphincPublic;
use sp_runtime::traits::IdentifyAccount;
use sp_runtime::MultiSigner;
use quantumharmony_runtime::AccountId;

// =============================================================================
// GENESIS VALIDATOR PUBLIC KEYS
// =============================================================================
// These public keys are embedded in the genesis block and are safe to publish.
// The corresponding secret keys are stored securely on validator servers.

// Alice (Validator 1 - Montreal)
pub const ALICE_SPHINCS_PUBLIC: [u8; 64] = [
    0xd7, 0xd0, 0xbd, 0x47, 0x54, 0x17, 0xa9, 0x3f, 0xa6, 0x12, 0x16, 0xa1, 0xe4, 0x02, 0x4f, 0x8d,
    0x1a, 0x21, 0x1f, 0x79, 0x5e, 0x6a, 0xb1, 0x11, 0xa1, 0xee, 0xf0, 0xd5, 0xe4, 0xf3, 0xf4, 0xb1,
    0x56, 0xe4, 0x7e, 0x5c, 0x8d, 0x41, 0x85, 0xce, 0x4a, 0x30, 0x84, 0x23, 0xeb, 0x31, 0x0b, 0xb3,
    0xb7, 0xf2, 0x6e, 0x6d, 0x50, 0x41, 0x91, 0x66, 0x2d, 0x22, 0x41, 0xaa, 0xfa, 0xf9, 0x14, 0xcd,
];

// Bob (Validator 2 - Beauharnois)
pub const BOB_SPHINCS_PUBLIC: [u8; 64] = [
    0x12, 0xf6, 0x88, 0xd8, 0x90, 0x5b, 0x2b, 0x67, 0xc0, 0xfe, 0x33, 0x27, 0x24, 0xa5, 0xa4, 0x44,
    0xb6, 0x1d, 0xc9, 0x49, 0xe8, 0x5f, 0x51, 0xf8, 0x50, 0x30, 0xb9, 0xc3, 0xf4, 0x1e, 0xe6, 0x61,
    0xea, 0xc6, 0x64, 0x30, 0x0e, 0x9a, 0xfc, 0x55, 0xbf, 0x15, 0x15, 0xdf, 0x53, 0x82, 0x7d, 0x28,
    0x1c, 0xe2, 0xce, 0x29, 0x5e, 0x18, 0xc2, 0x98, 0xe4, 0x89, 0x65, 0xff, 0x9e, 0xf3, 0xf0, 0x79,
];

// Charlie (Validator 3 - Frankfurt)
pub const CHARLIE_SPHINCS_PUBLIC: [u8; 64] = [
    0x8f, 0x60, 0x07, 0x22, 0xcd, 0x08, 0x87, 0xfc, 0xea, 0x1f, 0x98, 0xa2, 0x6e, 0x45, 0xc1, 0x44,
    0x9d, 0xaf, 0x02, 0x43, 0x95, 0x33, 0x55, 0x55, 0x48, 0xfb, 0x3c, 0xb3, 0xd6, 0xb0, 0x39, 0x22,
    0xd7, 0x37, 0x98, 0x35, 0x1f, 0x7a, 0x13, 0x57, 0x57, 0x4d, 0xd4, 0x24, 0x1b, 0xd8, 0x13, 0x3b,
    0xe9, 0x71, 0x82, 0x71, 0x19, 0xb2, 0x9e, 0x7a, 0x07, 0x08, 0x96, 0xde, 0xc7, 0xf3, 0x85, 0x98,
];

// Dave (Additional account for testing)
pub const DAVE_SPHINCS_PUBLIC: [u8; 64] = [
    0xc8, 0xf8, 0xb3, 0x39, 0xd1, 0xe3, 0xb7, 0x56, 0xfd, 0xdd, 0xae, 0xa1, 0xa6, 0x2f, 0x2e, 0x2f,
    0xda, 0x9b, 0xcd, 0x35, 0xc9, 0xb1, 0x71, 0xc4, 0x86, 0xff, 0xda, 0xb2, 0x98, 0xd6, 0x78, 0xdd,
    0x7b, 0x46, 0xec, 0x0e, 0x0e, 0x8a, 0x55, 0x53, 0x99, 0x41, 0x72, 0xb1, 0xbf, 0xca, 0xce, 0x8d,
    0x46, 0xeb, 0x51, 0xe7, 0xcb, 0x3b, 0xfc, 0x2c, 0xd8, 0xf9, 0xc6, 0x0c, 0xaf, 0x8f, 0x7c, 0xaf,
];

// Eve (Additional account for testing)
pub const EVE_SPHINCS_PUBLIC: [u8; 64] = [
    0x6f, 0xa0, 0x94, 0xd2, 0x5f, 0x65, 0xeb, 0x49, 0x9f, 0xbb, 0xf1, 0xf5, 0x02, 0x41, 0x2f, 0xea,
    0xde, 0x20, 0x9f, 0x9c, 0x4c, 0x50, 0xf3, 0x6f, 0x58, 0xd9, 0xab, 0x3a, 0x46, 0xeb, 0xce, 0x90,
    0xf8, 0x32, 0x2e, 0x64, 0x96, 0xce, 0xd0, 0xb4, 0x88, 0xad, 0xe8, 0x2b, 0xe3, 0xb6, 0xba, 0x57,
    0xc9, 0xdc, 0x9e, 0xfa, 0x7e, 0xf8, 0x97, 0xb3, 0x5c, 0x94, 0xa9, 0xa7, 0x32, 0x27, 0xd6, 0x43,
];

// Ferdie (Additional account for testing)
pub const FERDIE_SPHINCS_PUBLIC: [u8; 64] = [
    0x36, 0xb2, 0x6c, 0x68, 0xf7, 0xd9, 0xfc, 0xfc, 0xc2, 0x3e, 0x60, 0x51, 0xde, 0x34, 0x48, 0x69,
    0x94, 0xee, 0x1f, 0xe7, 0x79, 0x99, 0xc7, 0x24, 0xe2, 0xf5, 0x6e, 0x93, 0x58, 0x4d, 0xd4, 0xfa,
    0x3d, 0xeb, 0xb7, 0x6a, 0x8b, 0x29, 0x83, 0x11, 0x16, 0x0b, 0xd5, 0x6b, 0xaf, 0xa2, 0xfe, 0xc7,
    0x0d, 0xca, 0x6b, 0xb5, 0xaa, 0x87, 0xc1, 0x41, 0xc8, 0x7c, 0xb4, 0x8a, 0x10, 0x1b, 0xa4, 0x21,
];

// =============================================================================
// PUBLIC KEY ACCESS FUNCTIONS
// =============================================================================

/// Get SPHINCS+ public key for genesis account
pub fn get_test_public(name: &str) -> SphincPublic {
    match name {
        "Alice" => SphincPublic::from_raw(ALICE_SPHINCS_PUBLIC),
        "Bob" => SphincPublic::from_raw(BOB_SPHINCS_PUBLIC),
        "Charlie" => SphincPublic::from_raw(CHARLIE_SPHINCS_PUBLIC),
        "Dave" => SphincPublic::from_raw(DAVE_SPHINCS_PUBLIC),
        "Eve" => SphincPublic::from_raw(EVE_SPHINCS_PUBLIC),
        "Ferdie" => SphincPublic::from_raw(FERDIE_SPHINCS_PUBLIC),
        _ => panic!("Unknown genesis account: {}", name),
    }
}

/// Get AccountId for genesis account (using SHA3/Keccak-256)
pub fn get_test_account_id(name: &str) -> AccountId {
    let public = get_test_public(name);
    let signer = MultiSigner::from(public);
    signer.into_account()
}

/// Get SS58 address for genesis account
pub fn get_test_ss58(name: &str) -> String {
    use sp_core::crypto::Ss58Codec;
    get_test_account_id(name).to_ss58check()
}

/// Get Aura AuthorityId for genesis account
pub fn get_test_aura_key(name: &str) -> sp_consensus_aura::sphincs::AuthorityId {
    use sp_core::crypto::ByteArray;
    let public = get_test_public(name);
    sp_consensus_aura::sphincs::AuthorityId::from_slice(public.as_slice())
        .expect("SPHINCS+ public key should convert to AuraId")
}

// =============================================================================
// DEPRECATED FUNCTIONS - SECRET KEYS REMOVED FOR SECURITY
// =============================================================================
// These functions previously returned secret keys but are now removed.
// For production, use VALIDATOR_KEY_FILE or keystore.

/// DEPRECATED: Secret keys are no longer stored in source code.
/// Use VALIDATOR_KEY_FILE environment variable or keystore instead.
#[deprecated(note = "Secret keys removed from source code for security. Use VALIDATOR_KEY_FILE or keystore.")]
pub fn get_test_seed(_name: &str) -> [u8; 48] {
    panic!(
        "Secret keys are no longer stored in source code for security. \
        For production validators, use VALIDATOR_KEY_FILE environment variable \
        or inject keys directly into the keystore directory."
    );
}

/// DEPRECATED: Secret keys are no longer stored in source code.
/// Use VALIDATOR_KEY_FILE environment variable or keystore instead.
#[deprecated(note = "Secret keys removed from source code for security. Use VALIDATOR_KEY_FILE or keystore.")]
pub fn get_test_secret(_name: &str) -> [u8; 128] {
    panic!(
        "Secret keys are no longer stored in source code for security. \
        For production validators, use VALIDATOR_KEY_FILE environment variable \
        or inject keys directly into the keystore directory."
    );
}

/// DEPRECATED: Keypair generation requires secret keys which are not in source.
/// Use VALIDATOR_KEY_FILE environment variable or keystore instead.
#[deprecated(note = "Secret keys removed from source code for security. Use VALIDATOR_KEY_FILE or keystore.")]
pub fn get_test_keypair(_name: &str) -> sp_core::sphincs::Pair {
    panic!(
        "Keypair generation requires secret keys which are no longer stored in source code. \
        For production validators, use VALIDATOR_KEY_FILE environment variable \
        or inject keys directly into the keystore directory."
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_public_keys_valid() {
        // Verify all public keys are valid 64-byte arrays
        let names = ["Alice", "Bob", "Charlie", "Dave", "Eve", "Ferdie"];
        for name in names {
            let public = get_test_public(name);
            assert_eq!(public.as_ref().len(), 64, "{} public key should be 64 bytes", name);
        }
    }

    #[test]
    fn test_account_ids_deterministic() {
        // Verify account IDs are consistently derived from public keys
        let alice_ss58 = get_test_ss58("Alice");
        let bob_ss58 = get_test_ss58("Bob");

        // Verify SS58 addresses are valid and consistent
        // (addresses depend on the public keys in this file)
        assert!(alice_ss58.starts_with("5"), "Alice SS58 should start with 5");
        assert!(bob_ss58.starts_with("5"), "Bob SS58 should start with 5");
        assert_ne!(alice_ss58, bob_ss58, "Alice and Bob should have different addresses");
    }

    #[test]
    fn test_aura_keys_valid() {
        use sp_core::crypto::ByteArray;
        let alice_aura = get_test_aura_key("Alice");
        assert_eq!(alice_aura.as_slice().len(), 64, "Aura key should be 64 bytes");
    }
}
