use std::{collections::BTreeMap, str::FromStr};

use hex as hex_crate;
use hex_literal::hex;
// Substrate
use sc_chain_spec::{ChainType, Properties};
use sp_consensus_aura::sphincs::AuthorityId as AuraId;
#[allow(unused_imports)]
use sp_core::ecdsa;
use sp_core::{Pair, Public, H160, U256};
use sp_runtime::traits::{IdentifyAccount, Verify};

// FRONTIER REMOVED: governance-only node
// // Frontier
use quantumharmony_runtime::{
    opaque::SessionKeys, AccountId, Balance, RuntimeGenesisConfig, SS58Prefix, Signature,
    WASM_BINARY,
};

// Hardcoded SPHINCS+ test accounts
use crate::test_accounts;

// The URL for the telemetry server.
// const STAGING_TELEMETRY_URL: &str = "wss://telemetry.polkadot.io/submit/";

/// Specialized `ChainSpec`. This is a specialization of the general Substrate ChainSpec type.
pub type ChainSpec = sc_chain_spec::GenericChainSpec;

const PROTOCOL_ID: &str = "quantumharmony";
const TOKEN_SYMBOL: &str = "QMHY";

/// Generate a crypto pair from seed.
/// For SPHINCS+, we use from_string which provides consistent keys in native code.
/// NOTE: SPHINCS+ key generation is inherently non-deterministic for security.
/// We use from_string for development/testing as it provides stable keys in std environments.
pub fn get_from_seed<TPublic: Public>(seed: &str) -> <TPublic::Pair as Pair>::Public {
    // Use from_string for SPHINCS+ - provides stable keys in native/std code
    TPublic::Pair::from_string(&format!("//{}", seed), None)
        .expect("from_string should work for SPHINCS+ in native code")
        .public()
}

#[allow(dead_code)]
type AccountPublic = <Signature as Verify>::Signer;

/// Generate an account ID from seed.
/// For use with `AccountId32`, `dead_code` if `AccountId20`.
#[allow(dead_code)]
pub fn get_account_id_from_seed<TPublic: Public>(seed: &str) -> AccountId
where
    AccountPublic: From<<TPublic::Pair as Pair>::Public>,
{
    AccountPublic::from(get_from_seed::<TPublic>(seed)).into_account()
}


/// Get authority keys for SPHINCS+ Aura
pub fn authority_keys_from_seed_aura(s: &str) -> (AccountId, AuraId) {
    // CRITICAL FIX FOR SPHINCS+ NON-DETERMINISM:
    //
    // SPHINCS+ key generation from seeds is NON-DETERMINISTIC - each call to
    // from_seed_slice() produces DIFFERENT public keys even with the same seed!
    //
    // This was causing a mismatch:
    // - Chain spec generation: Calls from_seed_slice() -> gets public key A
    // - Service.rs keystore insertion: Calls from_seed_slice() -> gets public key B
    // - Aura consensus: Looks for key A, finds key B, rejects it!
    //
    // SOLUTION: Use the pre-generated hardcoded public keys from test_accounts.rs
    // These keys were generated ONCE and stored. We'll use them consistently in both
    // the chain spec AND the keystore insertion (service.rs will be updated too).

    use sp_core::crypto::ByteArray;
    use sp_runtime::traits::IdentifyAccount;
    use sp_runtime::MultiSigner;

    // Get the pre-generated SPHINCS+ public key (this is deterministic!)
    let public = test_accounts::get_test_public(s);

    // Derive AccountId from public key using MultiSigner
    let signer = MultiSigner::from(public.clone());
    let account_id = signer.into_account();

    // Create Aura AuthorityId from public key
    let aura_key = sp_consensus_aura::sphincs::AuthorityId::from_slice(public.as_slice())
        .expect("SPHINCS+ public key should convert to AuraId");

    (account_id, aura_key)
}

pub fn authority_keys_from_seed(
    s: &str,
    a: AccountId,
) -> (AccountId, AuraId) {
    (
        a,
        get_from_seed::<AuraId>(s),
    )
}

pub fn session_keys_from_seed(s: &str) -> SessionKeys {
    SessionKeys {
        aura: get_from_seed::<AuraId>(s),
    }
}

/// Get SPHINCS+ account ID from seed for dev/testing
/// SPHINCS+ public keys are 64 bytes, we take first 32 for AccountId32
pub fn get_sphincs_account_id_from_seed(seed: &str) -> AccountId {
    use sp_core::{sphincs::Pair as SphincsPair, Pair};

    let pair = SphincsPair::from_string(seed, None)
        .expect("static values are valid; qed");
    let public_key = pair.public();

    // SPHINCS+ public key is 64 bytes, AccountId32 is 32 bytes
    // Take first 32 bytes of SPHINCS+ public key
    let mut account_bytes = [0u8; 32];
    account_bytes.copy_from_slice(&public_key.0[..32]);
    AccountId::from(account_bytes)
}

fn properties() -> Properties {
    let mut properties = Properties::new();
    // FRONTIER REMOVED: governance-only node
    // properties.insert("isEthereum".into(), true.into());
    properties.insert("tokenDecimals".into(), 18.into());
    properties.insert("ss58Format".into(), SS58Prefix::get().into());
    properties.insert("tokenSymbol".to_string(), TOKEN_SYMBOL.into());
    properties
}

const UNITS: Balance = 1_000_000_000_000_000_000;

pub fn development_config(_enable_manual_seal: bool) -> ChainSpec {
    // Use from_string to generate keys - this matches what --alice flag generates
    let (alice, alice_public) = authority_keys_from_seed_aura("Alice");
    let (bob, _) = authority_keys_from_seed_aura("Bob");

    ChainSpec::builder(
        WASM_BINARY.expect("WASM not available"),
        Default::default(),
    )
    .with_name("Development")
    .with_id("dev")
    .with_chain_type(ChainType::Development)
    .with_properties(properties())
    .with_genesis_config_patch(testnet_genesis(
        // Sudo account (Alice) - using SPHINCS+ (post-quantum)
        alice.clone(),
        // Pre-funded accounts
        vec![
            alice.clone(),
            bob,
        ],
        vec![
            (
                alice,
                alice_public,
            ),
        ],
    ))
    .with_protocol_id(PROTOCOL_ID)
    .build()
}

/// QuantumHarmony Testnet - Production testnet with 2 validators
/// Uses ChainType::Live for proper peer discovery and networking
pub fn testnet_config() -> ChainSpec {
    let (alice, alice_public) = authority_keys_from_seed_aura("Alice");
    let (bob, bob_public) = authority_keys_from_seed_aura("Bob");
    let (charlie, _) = authority_keys_from_seed_aura("Charlie");
    let (dave, _) = authority_keys_from_seed_aura("Dave");
    let (eve, _) = authority_keys_from_seed_aura("Eve");
    let (ferdie, _) = authority_keys_from_seed_aura("Ferdie");

    ChainSpec::builder(WASM_BINARY.expect("WASM not available"), None)
        .with_name("QuantumHarmony Testnet")
        .with_id("quantumharmony_testnet")
        .with_chain_type(ChainType::Live)
        .with_properties(properties())
        .with_genesis_config_patch(testnet_genesis(
            // Sudo account (Alice) - using SPHINCS+ (post-quantum)
            alice.clone(),
            // Pre-funded accounts
            vec![
                alice.clone(),
                bob.clone(),
                charlie,
                dave,
                eve,
                ferdie,
            ],
            // 2 validators: Alice and Bob
            vec![
                (alice, alice_public),
                (bob, bob_public),
            ],
        ))
        .with_protocol_id(PROTOCOL_ID)
        .build()
}

pub fn local_testnet_config() -> ChainSpec {
    // Use from_string to generate keys - this matches what --alice/--bob flags generate
    // UPDATED: Changed from 3 validators (Alice, Bob, Charlie) to 2 validators (Alice, Bob)
    // This matches our actual network deployment
    let (alice, alice_public) = authority_keys_from_seed_aura("Alice");
    let (bob, bob_public) = authority_keys_from_seed_aura("Bob");
    let (charlie, _) = authority_keys_from_seed_aura("Charlie");
    let (dave, _) = authority_keys_from_seed_aura("Dave");
    let (eve, _) = authority_keys_from_seed_aura("Eve");
    let (ferdie, _) = authority_keys_from_seed_aura("Ferdie");

    ChainSpec::builder(WASM_BINARY.expect("WASM not available"), None)
        .with_name("Local Testnet")
        .with_id("local_testnet")
        .with_chain_type(ChainType::Local)
        .with_properties(properties())
        .with_genesis_config_patch(testnet_genesis(
            // Sudo account (Alice) - using SPHINCS+ (post-quantum)
            alice.clone(),
            // Pre-funded accounts
            vec![
                alice.clone(),
                bob.clone(),
                charlie,
                dave,
                eve,
                ferdie,
            ],
            // UPDATED: Only 2 validators instead of 3
            vec![
                (alice, alice_public),
                (bob, bob_public),
            ],
        ))
        .with_protocol_id(PROTOCOL_ID)
        .build()
}

/// 3-validator development network - combines Development chainType with 3 validators
/// This avoids --chain local issues while having multiple validators on same chain
pub fn dev_3validators_config() -> ChainSpec {
    let (alice, alice_public) = authority_keys_from_seed_aura("Alice");
    let (bob, bob_public) = authority_keys_from_seed_aura("Bob");
    let (charlie, charlie_public) = authority_keys_from_seed_aura("Charlie");

    ChainSpec::builder(
        WASM_BINARY.expect("WASM not available"),
        Default::default(),
    )
    .with_name("Development 3-Validator Network")
    .with_id("dev3")
    .with_chain_type(ChainType::Development)
    .with_properties(properties())
    .with_genesis_config_patch(testnet_genesis(
        // Sudo account (Alice)
        alice.clone(),
        // Pre-funded accounts
        vec![
            alice.clone(),
            bob.clone(),
            charlie.clone(),
        ],
        // All 3 validators in genesis
        vec![
            (alice, alice_public),
            (bob, bob_public),
            (charlie, charlie_public),
        ],
    ))
    .with_protocol_id(PROTOCOL_ID)
    .build()
}

/// Production 3-validator network with custom SPHINCS+ keys
///
/// This creates a chain spec using actual production keys (not test accounts).
/// Keys are generated on each validator machine and passed as hex strings.
///
/// # Arguments
/// * `validator1_public_hex` - 64-byte SPHINCS+ public key as hex (128 chars)
/// * `validator2_public_hex` - 64-byte SPHINCS+ public key as hex (128 chars)
/// * `validator3_public_hex` - 64-byte SPHINCS+ public key as hex (128 chars)
pub fn production_3validators_config(
    validator1_public_hex: &str,
    validator2_public_hex: &str,
    validator3_public_hex: &str,
) -> ChainSpec {
    use sp_core::{sphincs::Public as SphincsPublic, crypto::ByteArray};
    use sp_runtime::{traits::IdentifyAccount, MultiSigner};

    // Parse public keys from hex
    let v1_bytes = hex_crate::decode(validator1_public_hex).expect("Invalid validator1 hex");
    let v2_bytes = hex_crate::decode(validator2_public_hex).expect("Invalid validator2 hex");
    let v3_bytes = hex_crate::decode(validator3_public_hex).expect("Invalid validator3 hex");

    // Convert to SPHINCS+ public keys
    let v1_public = SphincsPublic::from_slice(&v1_bytes).expect("Invalid validator1 public key length");
    let v2_public = SphincsPublic::from_slice(&v2_bytes).expect("Invalid validator2 public key length");
    let v3_public = SphincsPublic::from_slice(&v3_bytes).expect("Invalid validator3 public key length");

    // Derive AccountIds from public keys using Keccak-256
    let v1_account: AccountId = MultiSigner::from(v1_public.clone()).into_account();
    let v2_account: AccountId = MultiSigner::from(v2_public.clone()).into_account();
    let v3_account: AccountId = MultiSigner::from(v3_public.clone()).into_account();

    // Convert to AuraId
    let v1_aura = AuraId::from_slice(v1_public.as_slice()).expect("Invalid AuraId");
    let v2_aura = AuraId::from_slice(v2_public.as_slice()).expect("Invalid AuraId");
    let v3_aura = AuraId::from_slice(v3_public.as_slice()).expect("Invalid AuraId");

    ChainSpec::builder(
        WASM_BINARY.expect("WASM not available"),
        Default::default(),
    )
    .with_name("QuantumHarmony Production Network")
    .with_id("quantumharmony_prod")
    .with_chain_type(ChainType::Live)
    .with_properties(properties())
    .with_genesis_config_patch(testnet_genesis(
        // Sudo account (validator1)
        v1_account.clone(),
        // Pre-funded accounts (all validators)
        vec![
            v1_account.clone(),
            v2_account.clone(),
            v3_account.clone(),
        ],
        // All 3 validators with their actual keys
        vec![
            (v1_account, v1_aura),
            (v2_account, v2_aura),
            (v3_account, v3_aura),
        ],
    ))
    .with_protocol_id(PROTOCOL_ID)
    .build()
}

/// Configure initial storage state for FRAME modules.
fn testnet_genesis(
    sudo_key: AccountId,
    endowed_accounts: Vec<AccountId>,
    initial_authorities: Vec<(AccountId, AuraId)>,
) -> serde_json::Value {
    // FRONTIER REMOVED: governance-only node
    // let evm_accounts = {
    //     let mut map = BTreeMap::new();
    //     map.insert(
    //         // H160 address of Alice dev account
    //         // Derived from SS58 (42 prefix) address
    //         // SS58: 5GrwvaEF5zXb26Fz9rcQpDWS57CtERHpNehXCPcNoHGKutQY
    //         // hex: 0xd43593c715fdd31c61141abd04a99fd6822c8558854ccde39a5684e7a56da27d
    //         // Using the full hex key, truncating to the first 20 bytes (the first 40 hex chars)
    //         H160::from_str("d43593c715fdd31c61141abd04a99fd6822c8558")
    //             .expect("internal H160 is valid; qed"),
    //         fp_evm::GenesisAccount {
    //             balance: U256::from_str("0xffffffffffffffffffffffffffffffff")
    //                 .expect("internal U256 is valid; qed"),
    //             code: Default::default(),
    //             nonce: Default::default(),
    //             storage: Default::default(),
    //         },
    //     );
    //     map.insert(
    //         // H160 address of CI test runner account
    //         H160::from_str("6be02d1d3665660d22ff9624b7be0551ee1ac91b")
    //             .expect("internal H160 is valid; qed"),
    //         fp_evm::GenesisAccount {
    //             balance: U256::from_str("0xffffffffffffffffffffffffffffffff")
    //                 .expect("internal U256 is valid; qed"),
    //             code: Default::default(),
    //             nonce: Default::default(),
    //             storage: Default::default(),
    //         },
    //     );
    //     map.insert(
    //         // H160 address for benchmark usage
    //         H160::from_str("1000000000000000000000000000000000000001")
    //             .expect("internal H160 is valid; qed"),
    //         fp_evm::GenesisAccount {
    //             nonce: U256::from(1),
    //             balance: U256::from(1_000_000_000_000_000_000_000_000u128),
    //             storage: Default::default(),
    //             code: vec![0x00],
    //         },
    //     );
    //     map
    // };

    let session_keys: Vec<_> = initial_authorities
        .iter()
        .map(|(acc, aura)| {
            (
                acc.clone(),
                acc.clone(),
                SessionKeys { aura: aura.clone() },
            )
        })
        .collect();

    // Pre-populate SPHINCS+ keystore with test account mappings
    // This allows the runtime to verify signatures without padding issues
    //
    // Now that we generate keys dynamically from seeds (not hardcoded),
    // we need to convert the AuraId back to the SPHINCS+ public key format.
    let sphincs_keys: Vec<_> = initial_authorities
        .iter()
        .map(|(account_id, aura_id)| {
            // AuraId IS a SPHINCS+ public key, just convert it
            use sp_core::{sphincs::Public as SphincPublic, crypto::ByteArray};
            let public_key = SphincPublic::from_slice(aura_id.as_ref())
                .expect("AuraId should be valid SPHINCS+ public key");

            (account_id.clone(), public_key)
        })
        .collect();

    // Pre-stake validators for reward distribution
    // Stake amount: 10,000 QMHY (with 18 decimals)
    let validator_stake = 10_000 * UNITS;
    let initial_validator_stakes: Vec<_> = initial_authorities
        .iter()
        .map(|(account, _)| (account.clone(), validator_stake))
        .collect();

    serde_json::json!({
        "sudo": { "key": sudo_key },
        "balances": {
            "balances": endowed_accounts
                .iter()
                .cloned()
                .map(|k| (k, 1_000_000 * UNITS))
                .collect::<Vec<_>>()
        },
        "session": { "keys": session_keys },
        // Note: Aura authorities are set via Session pallet, not directly
        // Setting them here would cause "Authorities are already initialized!" panic
        "sphincsKeystore": {
            "keys": sphincs_keys
        },
        // Validator rewards configuration with pre-staked validators
        "validatorRewards": {
            "blockReward": UNITS,  // 1 QMHY per block
            "minStake": 1_000 * UNITS,  // 1000 QMHY minimum stake
            "initialValidators": initial_validator_stakes
        },
        // SubstrateValidatorSet - include all validators for leader rotation
        "validatorSet": {
            "initialValidators": initial_authorities
                .iter()
                .map(|(account, _)| account.clone())
                .collect::<Vec<_>>()
        }
        // NOTE: Council and TechnicalCommittee removed - not in runtime
        // ConsensusLevel pallet uses defaults (genesis config not registered)
        // Democracy, Scheduler, and Preimage use defaults
    })
}
