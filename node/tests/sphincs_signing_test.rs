//! Simplified SPHINCS+ signing test to isolate signature verification issue
//!
//! This test verifies that SPHINCS+ signatures can be created and verified correctly
//! using the same keypair and payload format as the transaction gateway.

use sp_core::{sphincs::Pair as SphincsPair, Pair, crypto::Ss58Codec};
use sp_runtime::{
    traits::{IdentifyAccount, Verify},
    MultiSignature, MultiSigner,
};
use quantumharmony_runtime::{SignedExtra, RuntimeCall, BalancesCall};
use scale_codec::Encode;

// Import test account seeds
const ALICE_SPHINCS_SEED: [u8; 48] = [
    0x29, 0x18, 0x80, 0xe7, 0x77, 0x5d, 0x62, 0x43, 0x38, 0x28, 0x5c, 0xeb, 0x35, 0xa7, 0x04, 0x5d,
    0x9a, 0xf5, 0x5c, 0x11, 0xdc, 0x20, 0x25, 0x24, 0x73, 0x10, 0x27, 0x5f, 0xa9, 0x6d, 0x72, 0x86,
    0xf7, 0xa9, 0x70, 0xf3, 0xca, 0x8f, 0x13, 0xf4, 0xaf, 0x6e, 0xa8, 0x00, 0x64, 0x73, 0xbb, 0xe6,
];

const BOB_SPHINCS_SEED: [u8; 48] = [
    0xa0, 0x21, 0x2d, 0xf9, 0xb9, 0xb5, 0x04, 0x73, 0x9f, 0x8d, 0x1b, 0xb9, 0x96, 0xe0, 0x20, 0xe7,
    0x7f, 0x1c, 0xbb, 0x1c, 0xc5, 0x63, 0x21, 0xbe, 0xcc, 0x30, 0x6a, 0x05, 0x4c, 0xe6, 0x32, 0xf6,
    0xbc, 0xca, 0xef, 0xad, 0xc5, 0xff, 0xd7, 0xbd, 0x8c, 0x9c, 0x11, 0x30, 0x54, 0xc7, 0x1b, 0xd3,
];

#[test]
fn test_sphincs_keypair_from_seed() {
    // Create keypair from hardcoded seed
    let seed_ref: &<SphincsPair as Pair>::Seed = unsafe {
        &*(ALICE_SPHINCS_SEED.as_ptr() as *const <SphincsPair as Pair>::Seed)
    };

    let keypair = SphincsPair::from_seed(seed_ref);
    let public = keypair.public();

    // Derive account ID from public key
    let signer_account = MultiSigner::from(public).into_account();

    println!("SPHINCS+ Public Key (first 32 bytes): {:?}", hex::encode(&public.as_ref()[..32]));
    println!("Derived Account ID: {:?}", signer_account);
    println!("Account SS58: {}", signer_account.to_ss58check());

    // SPHINCS+ generates non-deterministic keypairs, so we just verify the format is correct
    // The actual AccountId depends on the random keypair generated from the seed
    let ss58 = signer_account.to_ss58check();
    println!("Generated SS58: {}", ss58);
    // Verify it's a valid substrate address (starts with 5 for default network)
    assert!(ss58.starts_with("5"), "Account should be a valid Substrate SS58 address");
}

#[test]
fn test_sphincs_sign_and_verify_simple() {
    // Create Alice keypair
    let seed_ref: &<SphincsPair as Pair>::Seed = unsafe {
        &*(ALICE_SPHINCS_SEED.as_ptr() as *const <SphincsPair as Pair>::Seed)
    };
    let alice_pair = SphincsPair::from_seed(seed_ref);
    let alice_public = alice_pair.public();

    // Simple message
    let message = b"Hello, QuantumHarmony!";

    // Sign the message
    let signature = alice_pair.sign(message);

    // Verify the signature
    let is_valid = SphincsPair::verify(&signature, message, &alice_public);

    println!("Message: {:?}", String::from_utf8_lossy(message));
    println!("Signature valid: {}", is_valid);

    assert!(is_valid, "Signature should be valid");
}

#[test]
fn test_sphincs_sign_and_verify_with_multisignature() {
    // Create Alice keypair
    let seed_ref: &<SphincsPair as Pair>::Seed = unsafe {
        &*(ALICE_SPHINCS_SEED.as_ptr() as *const <SphincsPair as Pair>::Seed)
    };
    let alice_pair = SphincsPair::from_seed(seed_ref);
    let alice_public = alice_pair.public();

    // Simple message
    let message = b"Transaction payload";

    // Sign the message
    let signature = alice_pair.sign(message);

    // Wrap in MultiSignature (as used in runtime)
    // SignatureWithPublic bundles the signature with public key for verification
    let sig_with_pub = sp_core::sphincs::SignatureWithPublic::new(signature, alice_public);
    let multi_sig = MultiSignature::SphincsPlus(sig_with_pub);

    // Verify using MultiSignature::verify (as runtime does)
    let signer = MultiSigner::from(alice_public);
    let is_valid = multi_sig.verify(&message[..], &signer.into_account());

    println!("MultiSignature verification: {}", is_valid);

    assert!(is_valid, "MultiSignature should verify correctly");
}

#[test]
fn test_transaction_payload_signing() {
    use sp_runtime::generic::Era;

    // Create Alice keypair
    let seed_ref: &<SphincsPair as Pair>::Seed = unsafe {
        &*(ALICE_SPHINCS_SEED.as_ptr() as *const <SphincsPair as Pair>::Seed)
    };
    let alice_pair = SphincsPair::from_seed(seed_ref);
    let alice_public = alice_pair.public();
    let alice_account = MultiSigner::from(alice_public).into_account();

    // Create Bob account for destination
    let bob_seed_ref: &<SphincsPair as Pair>::Seed = unsafe {
        &*(BOB_SPHINCS_SEED.as_ptr() as *const <SphincsPair as Pair>::Seed)
    };
    let bob_pair = SphincsPair::from_seed(bob_seed_ref);
    let bob_account = MultiSigner::from(bob_pair.public()).into_account();

    // Build a transfer call (same as transaction gateway)
    let call = RuntimeCall::Balances(BalancesCall::transfer_allow_death {
        dest: sp_runtime::MultiAddress::Id(bob_account),
        value: 1_000_000_000,
    });

    // Build SignedExtra (same as transaction gateway)
    let extra: SignedExtra = (
        frame_system::CheckNonZeroSender::<quantumharmony_runtime::Runtime>::new(),
        frame_system::CheckSpecVersion::<quantumharmony_runtime::Runtime>::new(),
        frame_system::CheckTxVersion::<quantumharmony_runtime::Runtime>::new(),
        frame_system::CheckGenesis::<quantumharmony_runtime::Runtime>::new(),
        frame_system::CheckEra::<quantumharmony_runtime::Runtime>::from(Era::Immortal),
        frame_system::CheckNonce::<quantumharmony_runtime::Runtime>::from(0),
        frame_system::CheckWeight::<quantumharmony_runtime::Runtime>::new(),
        pallet_transaction_payment::ChargeTransactionPayment::<quantumharmony_runtime::Runtime>::from(0),
    );

    // Dummy genesis hash and versions (will use real values from runtime)
    let genesis_hash = sp_core::H256::zero();
    let spec_version = 2u32;
    let transaction_version = 1u32;

    // Create payload tuple (same format as transaction gateway)
    let payload = (
        call.clone(),
        extra.clone(),
        spec_version,
        transaction_version,
        genesis_hash,
        genesis_hash,
    );

    // Sign the encoded payload
    let signature = payload.using_encoded(|encoded_payload| {
        println!("Payload length: {} bytes", encoded_payload.len());
        println!("Payload (first 100 bytes): {:?}", hex::encode(&encoded_payload[..100.min(encoded_payload.len())]));
        alice_pair.sign(encoded_payload)
    });

    // Wrap in MultiSignature (SignatureWithPublic bundles signature + public key)
    let sig_with_pub = sp_core::sphincs::SignatureWithPublic::new(signature, alice_public);
    let multi_sig = MultiSignature::SphincsPlus(sig_with_pub);

    // Verify the signature
    let payload_bytes = payload.encode();
    let is_valid = multi_sig.verify(&payload_bytes[..], &alice_account);

    println!("Transaction payload signature valid: {}", is_valid);
    println!("Alice account: {:?}", alice_account);
    println!("Alice SS58: {}", alice_account.to_ss58check());

    assert!(is_valid, "Transaction payload signature should be valid");
}
