#![cfg_attr(not(feature = "std"), no_std)]
// `construct_runtime!` does a lot of recursion and requires us to increase the limits.
#![recursion_limit = "1024"]

// Make the WASM binary available.
#[cfg(feature = "std")]
include!(concat!(env!("OUT_DIR"), "/wasm_binary.rs"));

// Quantum-resistant hasher module (Keccak-256 with QRNG entropy pool support)
pub mod quantum_hasher;
use quantum_hasher::QuantumHasher;

// Quantum configuration (randomness source)
pub mod quantum_config;

// Genesis config presets
pub mod genesis_config_presets;

// Wallet API for balance queries
pub mod wallet_api;

// Using fork's sp_runtime::MultiSignature which already supports SPHINCS+ only

// GRANDPA removed - quantum-vulnerable (uses Ed25519/BLS)
// Finality provided by Proof of Coherence consensus
use sp_api::impl_runtime_apis;
use sp_consensus_aura::sphincs::AuthorityId as AuraId;  // Fork uses SPHINCS+ instead of sr25519
use sp_core::{crypto::KeyTypeId, OpaqueMetadata};
use sp_runtime::{
    create_runtime_str, generic, impl_opaque_keys,
    traits::{
        AccountIdLookup, Block as BlockT, Hash as HashT, IdentifyAccount, NumberFor, One, Verify,
    },
    transaction_validity::{TransactionSource, TransactionValidity},
    ApplyExtrinsicResult,
};
use sp_std::prelude::*;
extern crate alloc;
use alloc::string::String;
#[cfg(feature = "std")]
use sp_version::NativeVersion;
use sp_version::RuntimeVersion;

// Genesis builder helpers
use frame_support::genesis_builder_helper::{build_state, get_preset};

// A few exports that help ease life for downstream crates.
pub use frame_support::{
    construct_runtime, parameter_types,
    traits::{
        ConstBool, ConstU128, ConstU32, ConstU64, ConstU8, EqualPrivilegeOnly, KeyOwnerProofSystem,
        Randomness, StorageInfo,
    },
    weights::{
        constants::{
            BlockExecutionWeight, ExtrinsicBaseWeight, RocksDbWeight, WEIGHT_REF_TIME_PER_SECOND,
        },
        IdentityFee, Weight,
    },
    PalletId, StorageValue,
};
pub use frame_system::Call as SystemCall;
pub use pallet_balances::Call as BalancesCall;
pub use pallet_timestamp::Call as TimestampCall;
pub use pallet_sudo::Call as SudoCall;
use pallet_transaction_payment::{ConstFeeMultiplier, CurrencyAdapter};
#[cfg(any(feature = "std", test))]
pub use sp_runtime::BuildStorage;
pub use sp_runtime::{Perbill, Permill};

// Additional imports for governance
use frame_support::{
    traits::EitherOfDiverse,
    dispatch::DispatchClass,
};
use frame_system::EnsureRoot;

/// Import the quantum configuration - temporarily disabled for incremental build
// TODO: Re-enable after fixing fork API incompatibilities (ConstU32 TypeInfo, BoundedVec conversion)
// pub mod quantum_config;

/// Alias to quantum-safe signature type (fork's MultiSignature supports SPHINCS+ only)
pub type Signature = sp_runtime::MultiSignature;

/// Some way of identifying an account on the chain. We intentionally make it equivalent
/// to the public key of our transaction signing scheme.
pub type AccountId = <<Signature as Verify>::Signer as IdentifyAccount>::AccountId;

/// Balance of an account.
pub type Balance = u128;

/// Index of a transaction in the chain.
pub type Index = u32;

/// Nonce type alias for Index (for node compatibility)
pub type Nonce = Index;

/// A hash of some data used by the chain.
pub type Hash = sp_core::H256;

/// Opaque types. These are used by the CLI to instantiate machinery that don't need to know
/// the specifics of the runtime. They can then be made to be agnostic over specific formats
/// of data like extrinsics, allowing for them to continue syncing the network through upgrades
/// to even the core data structures.
pub mod opaque {
    use super::*;

    pub use sp_runtime::OpaqueExtrinsic as UncheckedExtrinsic;

    /// Opaque block header type (using quantum-resistant QuantumHasher with QRNG support).
    pub type Header = generic::Header<BlockNumber, QuantumHasher>;
    /// Opaque block type.
    pub type Block = generic::Block<Header, UncheckedExtrinsic>;
    /// Opaque block identifier type.
    pub type BlockId = generic::BlockId<Block>;

    impl_opaque_keys! {
        pub struct SessionKeys {
            pub aura: Aura,
            // GRANDPA removed - using Proof of Coherence for finality
        }
    }
}

// To learn more about runtime versioning, see:
// https://docs.substrate.io/main-docs/build/upgrade#runtime-versioning
#[sp_version::runtime_version]
pub const VERSION: RuntimeVersion = RuntimeVersion {
    spec_name: create_runtime_str!("quantumharmony"),
    impl_name: create_runtime_str!("quantumharmony"),
    authoring_version: 1,
    spec_version: 22,  // v22: Add MeshForum runtime API for reading messages
    impl_version: 1,
    apis: RUNTIME_API_VERSIONS,
    transaction_version: 1,
    system_version: 1,
};

/// The version information used to identify this runtime when compiled natively.
#[cfg(feature = "std")]
pub fn native_version() -> NativeVersion {
    NativeVersion { runtime_version: VERSION, can_author_with: Default::default() }
}

const NORMAL_DISPATCH_RATIO: Perbill = Perbill::from_percent(75);

parameter_types! {
    pub const BlockHashCount: BlockNumber = 2400;
    pub const Version: RuntimeVersion = VERSION;
    /// We allow for 2 seconds of compute with a 3 second average block time.
    pub BlockWeights: frame_system::limits::BlockWeights =
        frame_system::limits::BlockWeights::with_sensible_defaults(
            Weight::from_parts(2u64 * WEIGHT_REF_TIME_PER_SECOND, u64::MAX),
            NORMAL_DISPATCH_RATIO,
        );
    // Increased to 2MB to accommodate large runtime upgrade extrinsics
    // Runtime upgrade = 598KB WASM + 50KB SPHINCS+ signature ≈ 650KB
    // Using 2MB provides headroom for future larger runtimes
    pub BlockLength: frame_system::limits::BlockLength = frame_system::limits::BlockLength
        ::max_with_normal_ratio(2 * 1024 * 1024, NORMAL_DISPATCH_RATIO);
    pub const SS58Prefix: u8 = 42;
}

// Configure FRAME pallets to include in runtime.

impl frame_system::Config for Runtime {
    /// The basic call filter to use in dispatchable.
    type BaseCallFilter = frame_support::traits::Everything;
    /// Block & extrinsics weights: base values and limits.
    type BlockWeights = BlockWeights;
    /// The maximum length of a block (in bytes).
    type BlockLength = BlockLength;
    /// The identifier used to distinguish between accounts.
    type AccountId = AccountId;
    /// The aggregated dispatch type that is available for extrinsics.
    type RuntimeCall = RuntimeCall;
    /// The lookup mechanism to get account ID from whatever is passed in dispatchers.
    type Lookup = AccountIdLookup<AccountId, ()>;
    /// The type for hashing blocks and tries.
    type Hash = Hash;
    /// The hashing algorithm used (quantum-resistant hasher with QRNG entropy pool support).
    type Hashing = QuantumHasher;
    /// The ubiquitous event type.
    type RuntimeEvent = RuntimeEvent;
    /// The ubiquitous origin type.
    type RuntimeOrigin = RuntimeOrigin;
    /// Maximum number of block number to block hash mappings to keep (oldest pruned first).
    type BlockHashCount = BlockHashCount;
    /// The weight of database operations that the runtime can invoke.
    type DbWeight = RocksDbWeight;
    /// Version of the runtime.
    type Version = Version;
    /// Converts a module to the index of the module in `construct_runtime!`.
    type PalletInfo = PalletInfo;
    /// What to do if a new account is created.
    type OnNewAccount = ();
    /// What to do if an account is fully reaped from the system.
    type OnKilledAccount = ();
    /// The data to be stored in an account.
    type AccountData = pallet_balances::AccountData<Balance>;
    /// Weight information for the extrinsics of this pallet.
    type SystemWeightInfo = ();
    /// This is used as an identifier of the chain. 42 is the generic substrate prefix.
    type SS58Prefix = SS58Prefix;
    /// The set code logic, just the default since we're not a parachain.
    type OnSetCode = ();
    type MaxConsumers = frame_support::traits::ConstU32<16>;
    type MultiBlockMigrator = ();
    type PreInherents = ();
    type PostInherents = ();
    type PostTransactions = ();
    type RuntimeTask = ();
    type Nonce = Index;
    type Block = Block;
    type ExtensionsWeightInfo = ();
    type SingleBlockMigrations = ();
}

impl pallet_aura::Config for Runtime {
    type AuthorityId = AuraId;
    type DisabledValidators = ();
    type MaxAuthorities = ConstU32<32>;
    type AllowMultipleBlocksPerSlot = ConstBool<false>;
    type SlotDuration = ConstU64<SLOT_DURATION>;
}

parameter_types! {
    pub const Period: u32 = 6 * HOURS;
    pub const Offset: u32 = 0;
}

impl pallet_session::Config for Runtime {
    type RuntimeEvent = RuntimeEvent;
    type ValidatorId = AccountId;
    type ValidatorIdOf = sp_runtime::traits::ConvertInto;
    type ShouldEndSession = pallet_session::PeriodicSessions<Period, Offset>;
    type NextSessionRotation = pallet_session::PeriodicSessions<Period, Offset>;
    type SessionManager = ();
    type SessionHandler = <opaque::SessionKeys as sp_runtime::traits::OpaqueKeys>::KeyTypeIdProviders;
    type Keys = opaque::SessionKeys;
    type WeightInfo = ();
    type Currency = Balances;
    type KeyDeposit = ConstU128<0>;
    type DisablingStrategy = ();
}

impl pallet_authorship::Config for Runtime {
    type FindAuthor = pallet_session::FindAccountFromAuthorIndex<Self, Aura>;
    type EventHandler = ValidatorRewards;
}

// GRANDPA Config removed - quantum-vulnerable finality gadget
// Using Proof of Coherence for quantum-safe consensus

impl pallet_timestamp::Config for Runtime {
    /// A timestamp: milliseconds since the unix epoch.
    type Moment = u64;
    type OnTimestampSet = Aura;
    type MinimumPeriod = ConstU64<{ SLOT_DURATION / 2 }>;
    type WeightInfo = ();
}

/// Existential deposit.
pub const EXISTENTIAL_DEPOSIT: u128 = 500;

impl pallet_balances::Config for Runtime {
    type MaxLocks = ConstU32<50>;
    type MaxReserves = ();
    type ReserveIdentifier = [u8; 8];
    /// The type for recording an account's balance.
    type Balance = Balance;
    /// The ubiquitous event type.
    type RuntimeEvent = RuntimeEvent;
    type DustRemoval = ();
    type ExistentialDeposit = ConstU128<EXISTENTIAL_DEPOSIT>;
    type AccountStore = System;
    type WeightInfo = pallet_balances::weights::SubstrateWeight<Runtime>;
    type FreezeIdentifier = ();
    type MaxFreezes = ();
    type RuntimeHoldReason = RuntimeHoldReason;
    type RuntimeFreezeReason = ();
    type DoneSlashHandler = ();
}

impl pallet_transaction_payment::Config for Runtime {
    type RuntimeEvent = RuntimeEvent;
    type OnChargeTransaction = CurrencyAdapter<Balances, ()>;
    type OperationalFeeMultiplier = ConstU8<5>;
    type WeightToFee = IdentityFee<Balance>;
    type LengthToFee = IdentityFee<Balance>;
    type FeeMultiplierUpdate = ();
    type WeightInfo = ();
}

impl pallet_sudo::Config for Runtime {
    type RuntimeEvent = RuntimeEvent;
    type RuntimeCall = RuntimeCall;
    type WeightInfo = ();
}

// Simple randomness provider for quantum crypto initialization
// This provides basic randomness until quantum entropy pool is populated
pub struct TimestampRandomness;
impl frame_support::traits::Randomness<Hash, BlockNumber> for TimestampRandomness {
    fn random(subject: &[u8]) -> (Hash, BlockNumber) {
        let block_number = frame_system::Pallet::<Runtime>::block_number();
        let block_hash = frame_system::Pallet::<Runtime>::block_hash(block_number);

        // Mix timestamp, block hash, and subject
        let timestamp = pallet_timestamp::Pallet::<Runtime>::get();
        let mut data = Vec::new();
        data.extend_from_slice(block_hash.as_ref());
        data.extend_from_slice(&timestamp.to_le_bytes());
        data.extend_from_slice(subject);

        let randomness = <Runtime as frame_system::Config>::Hashing::hash(&data);
        (randomness, block_number)
    }
}

// Quantum pallet configs moved to quantum_config.rs to avoid duplication

impl pallet_runtime_segmentation::Config for Runtime {
    type RuntimeEvent = RuntimeEvent;
    type MyRandomness = quantum_config::QuantumRandomness;
}

// Configure ChunkedUpgrade pallet (for runtime upgrades larger than BlockLength)
impl pallet_runtime_segmentation::chunked_upgrade::pallet::Config for Runtime {
    type RuntimeEvent = RuntimeEvent;
}

// Configure SphincsKeystore pallet
impl pallet_sphincs_keystore::Config for Runtime {}

// Configure ValidatorEntropy pallet
parameter_types! {
    pub const MaxDevices: u32 = 10;
    pub const MaxValidators: u32 = 1000;
}

impl pallet_validator_entropy::Config for Runtime {
    type RuntimeEvent = RuntimeEvent;
    type MaxDevices = MaxDevices;
    type MaxValidators = MaxValidators;
    type WeightInfo = pallet_validator_entropy::weights::SubstrateWeight<Runtime>;
}

// Configure RelayCoordination pallet
pub const UNITS: Balance = 1_000_000_000_000_000_000; // 1 QMHY = 10^18 base units

parameter_types! {
    pub const MinRelayStake: Balance = 100 * UNITS;
    pub const RelayElectionInterval: BlockNumber = 100;
    pub const MaxRelayCandidates: u32 = 100;
    pub const MaxElectedRelaysPerRegion: u32 = 10;
    pub const MinUptimePercentage: u8 = 80;
    pub const SlashPercentage: Perbill = Perbill::from_percent(10);
}

impl pallet_relay_coordination::Config for Runtime {
    type RuntimeEvent = RuntimeEvent;
    type Currency = Balances;
    type MinRelayStake = MinRelayStake;
    type RelayElectionInterval = RelayElectionInterval;
    type MaxRelayCandidates = MaxRelayCandidates;
    type MaxElectedRelaysPerRegion = MaxElectedRelaysPerRegion;
    type MinUptimePercentage = MinUptimePercentage;
    type SlashPercentage = SlashPercentage;
    type WeightInfo = pallet_relay_coordination::weights::SubstrateWeight<Runtime>;
    type ValidatorSet = Session;
}

// Dev Governance pallet configuration
parameter_types! {
    /// Minimum deposit to create a proposal (10 UNITS)
    pub const MinProposalDeposit: Balance = 10 * UNITS;
    /// Minimum stake to vote (1 UNIT)
    pub const MinVoteStake: Balance = 1 * UNITS;
    /// Default voting period (7 days in blocks)
    pub const DefaultVotingPeriod: BlockNumber = 7 * DAYS;
}

impl pallet_dev_governance::Config for Runtime {
    type RuntimeEvent = RuntimeEvent;
    type Currency = Balances;
    type MinProposalDeposit = MinProposalDeposit;
    type MinVoteStake = MinVoteStake;
    type DefaultVotingPeriod = DefaultVotingPeriod;
    type AdminOrigin = EnsureRoot<AccountId>;
}

// Validator Rewards pallet configuration
impl pallet_validator_rewards::Config for Runtime {
    type RuntimeEvent = RuntimeEvent;
    type Currency = Balances;
    type SlashOrigin = EnsureRoot<AccountId>;
    type RewardOrigin = EnsureRoot<AccountId>;
}

// Substrate Validator Set pallet configuration
parameter_types! {
    pub const MinAuthorities: u32 = 1;
    pub const ValidatorSetMaxValidators: u32 = 100;
}

impl substrate_validator_set::Config for Runtime {
    type RuntimeEvent = RuntimeEvent;
    type AddRemoveOrigin = EnsureRoot<AccountId>;
    type MinAuthorities = MinAuthorities;
    type MaxValidators = ValidatorSetMaxValidators;
    type WeightInfo = substrate_validator_set::weights::SubstrateWeight<Runtime>;
    type ValidatorIdToAccountId = sp_runtime::traits::ConvertInto;
    type AccountIdToValidatorId = sp_runtime::traits::ConvertInto;
    type Lookup = AccountIdLookup<AccountId, ()>;
    type EVMAddress = sp_core::H160;
    type Randomness = quantum_config::QuantumRandomness;
}

// Validator Governance pallet configuration (short voting period for testing)
parameter_types! {
    pub const ValidatorVotingPeriod: BlockNumber = 10; // ~1 minute for testing
    pub const MinimumVotes: u32 = 1; // Low threshold for testing
}

impl pallet_validator_governance::Config for Runtime {
    type RuntimeEvent = RuntimeEvent;
    type VotingPeriod = ValidatorVotingPeriod;
    type MinimumVotes = MinimumVotes;
}

// Academic Vouching pallet configuration
parameter_types! {
    pub const RequiredVouches: u32 = 2; // Vouches needed for program acceptance
    pub const AcademicVotingPeriod: BlockNumber = 100; // ~10 minutes for academic registration voting
    pub const MinimumAcademicApprovals: u32 = 1; // Low for testing
}

impl pallet_academic_vouch::Config for Runtime {
    type RuntimeEvent = RuntimeEvent;
    type RequiredVouches = RequiredVouches;
    type AcademicVotingPeriod = AcademicVotingPeriod;
    type MinimumAcademicApprovals = MinimumAcademicApprovals;
}

// Ricardian Contracts pallet configuration
parameter_types! {
    pub const MinContractDuration: BlockNumber = 10; // Minimum blocks before contract can expire
}

impl pallet_ricardian_contracts::Config for Runtime {
    type RuntimeEvent = RuntimeEvent;
    type MinContractDuration = MinContractDuration;
}

// Notarial pallet configuration
parameter_types! {
    pub const MinWitnesses: u32 = 2; // Witnesses needed for certification
    pub const DefaultValidityPeriod: BlockNumber = 0; // 0 = permanent attestations by default
}

impl pallet_notarial::Config for Runtime {
    type RuntimeEvent = RuntimeEvent;
    type MinWitnesses = MinWitnesses;
    type DefaultValidityPeriod = DefaultValidityPeriod;
}

// Mesh Forum pallet configuration
parameter_types! {
    pub const MaxMessageLength: u32 = 512;
    pub const MaxMessages: u32 = 1000;
}

impl pallet_mesh_forum::Config for Runtime {
    type RuntimeEvent = RuntimeEvent;
    type MaxMessageLength = MaxMessageLength;
    type MaxMessages = MaxMessages;
}

parameter_types! {
    // Minimum 1 day before trigger (at 3s blocks = 28,800 blocks)
    pub const MinTrustDuration: BlockNumber = 28_800;
    // Maximum 10 years (at 3s blocks = ~105,120,000 blocks)
    pub const MaxTrustDuration: BlockNumber = 105_120_000;
    // Minimum 1 QMHY deposit (18 decimals)
    pub const MinTrustDeposit: Balance = 1_000_000_000_000_000_000;
}

impl pallet_fideicommis::Config for Runtime {
    type RuntimeEvent = RuntimeEvent;
    type Currency = Balances;
    type MinTrustDuration = MinTrustDuration;
    type MaxTrustDuration = MaxTrustDuration;
    type MinDeposit = MinTrustDeposit;
    type ForceOrigin = EnsureRoot<AccountId>;
}

// QCAD Stablecoin pallet configuration
parameter_types! {
    // 150% minimum collateral ratio (1_500_000 = 150%)
    pub const MinCollateralRatio: u32 = 1_500_000;
    // 120% liquidation threshold
    pub const LiquidationRatio: u32 = 1_200_000;
    // 13% liquidation penalty
    pub const LiquidationPenalty: u32 = 130_000;
    // 2% annual stability fee
    pub const StabilityFeeRate: u32 = 20_000;
    // Minimum 100 QCAD debt per vault (18 decimals)
    pub const MinVaultDebt: Balance = 100_000_000_000_000_000_000;
    // Oracle price valid for 1 hour (at 3s blocks = 1200 blocks)
    pub const OracleValidityPeriod: BlockNumber = 1200;
}

impl pallet_stablecoin::Config for Runtime {
    type RuntimeEvent = RuntimeEvent;
    type Currency = Balances;
    type MinCollateralRatio = MinCollateralRatio;
    type LiquidationRatio = LiquidationRatio;
    type LiquidationPenalty = LiquidationPenalty;
    type StabilityFeeRate = StabilityFeeRate;
    type MinVaultDebt = MinVaultDebt;
    type OracleValidityPeriod = OracleValidityPeriod;
    type OracleOrigin = EnsureRoot<AccountId>;
    type ForceOrigin = EnsureRoot<AccountId>;
}

// Consensus Level pallet configuration
impl pallet_consensus_level::Config for Runtime {
    type RuntimeEvent = RuntimeEvent;
}

// Governance parameters
parameter_types! {
    pub const LaunchPeriod: BlockNumber = 7 * DAYS;
    pub const VotingPeriod: BlockNumber = 7 * DAYS;
    pub const FastTrackVotingPeriod: BlockNumber = 3 * HOURS;
    pub const MinimumDeposit: Balance = 100 * EXISTENTIAL_DEPOSIT;
    pub const EnactmentPeriod: BlockNumber = 1 * DAYS;
    pub const CooloffPeriod: BlockNumber = 7 * DAYS;
    pub const InstantAllowed: bool = true;
    pub const MaxVotes: u32 = 100;
    pub const MaxProposals: u32 = 100;
}

// Council collective instance (must be defined before democracy config)
type CouncilCollective = pallet_collective::Instance1;

parameter_types! {
    pub const CouncilMotionDuration: BlockNumber = 3 * DAYS;
    pub const CouncilMaxProposals: u32 = 100;
    pub const CouncilMaxMembers: u32 = 100;
    pub const TechnicalMotionDuration: BlockNumber = 3 * DAYS;
    pub const TechnicalMaxProposals: u32 = 100;
    pub const TechnicalMaxMembers: u32 = 100;
    pub MaxCollectivesProposalWeight: Weight = Perbill::from_percent(50) *
        BlockWeights::get().max_block;
}

impl pallet_collective::Config<CouncilCollective> for Runtime {
    type RuntimeOrigin = RuntimeOrigin;
    type Proposal = RuntimeCall;
    type RuntimeEvent = RuntimeEvent;
    type MotionDuration = CouncilMotionDuration;
    type MaxProposals = CouncilMaxProposals;
    type MaxMembers = CouncilMaxMembers;
    type DefaultVote = pallet_collective::PrimeDefaultVote;
    type WeightInfo = pallet_collective::weights::SubstrateWeight<Runtime>;
    type SetMembersOrigin = EnsureRoot<Self::AccountId>;
    type MaxProposalWeight = MaxCollectivesProposalWeight;
    type DisapproveOrigin = EnsureRoot<AccountId>;
    type KillOrigin = EnsureRoot<AccountId>;
    type Consideration = ();
}

// Technical collective instance
type TechnicalCollective = pallet_collective::Instance2;
impl pallet_collective::Config<TechnicalCollective> for Runtime {
    type RuntimeOrigin = RuntimeOrigin;
    type Proposal = RuntimeCall;
    type RuntimeEvent = RuntimeEvent;
    type MotionDuration = TechnicalMotionDuration;
    type MaxProposals = TechnicalMaxProposals;
    type MaxMembers = TechnicalMaxMembers;
    type DefaultVote = pallet_collective::PrimeDefaultVote;
    type WeightInfo = pallet_collective::weights::SubstrateWeight<Runtime>;
    type SetMembersOrigin = EnsureRoot<Self::AccountId>;
    type MaxProposalWeight = MaxCollectivesProposalWeight;
    type DisapproveOrigin = EnsureRoot<AccountId>;
    type KillOrigin = EnsureRoot<AccountId>;
    type Consideration = ();
}

// Scheduler configuration (must be before democracy)
parameter_types! {
    pub MaximumSchedulerWeight: Weight = Perbill::from_percent(80) *
        BlockWeights::get().max_block;
}

impl pallet_scheduler::Config for Runtime {
    type RuntimeEvent = RuntimeEvent;
    type RuntimeOrigin = RuntimeOrigin;
    type PalletsOrigin = OriginCaller;
    type RuntimeCall = RuntimeCall;
    type MaximumWeight = MaximumSchedulerWeight;
    type ScheduleOrigin = EnsureRoot<AccountId>;
    type MaxScheduledPerBlock = ConstU32<50>;
    type WeightInfo = pallet_scheduler::weights::SubstrateWeight<Runtime>;
    type OriginPrivilegeCmp = EqualPrivilegeOnly;
    type Preimages = Preimage;
    type BlockNumberProvider = frame_system::Pallet<Runtime>;
}

// Preimage configuration (must be before democracy)
parameter_types! {
    pub const PreimageBaseDeposit: Balance = EXISTENTIAL_DEPOSIT;
    pub const PreimageByteDeposit: Balance = EXISTENTIAL_DEPOSIT / 100;
}

impl pallet_preimage::Config for Runtime {
    type RuntimeEvent = RuntimeEvent;
    type WeightInfo = pallet_preimage::weights::SubstrateWeight<Runtime>;
    type Currency = Balances;
    type ManagerOrigin = EnsureRoot<AccountId>;
    type Consideration = ();
}

impl pallet_democracy::Config for Runtime {
    type RuntimeEvent = RuntimeEvent;
    type Currency = Balances;
    type EnactmentPeriod = EnactmentPeriod;
    type LaunchPeriod = LaunchPeriod;
    type VotingPeriod = VotingPeriod;
    type VoteLockingPeriod = EnactmentPeriod;
    type MinimumDeposit = MinimumDeposit;
    type ExternalOrigin = EnsureRoot<AccountId>;
    type ExternalMajorityOrigin = EnsureRoot<AccountId>;
    type ExternalDefaultOrigin = EnsureRoot<AccountId>;
    type FastTrackOrigin = EnsureRoot<AccountId>;
    type InstantOrigin = EnsureRoot<AccountId>;
    type InstantAllowed = InstantAllowed;
    type FastTrackVotingPeriod = FastTrackVotingPeriod;
    type CancellationOrigin = EnsureRoot<AccountId>;
    type BlacklistOrigin = EnsureRoot<AccountId>;
    type CancelProposalOrigin = EnsureRoot<AccountId>;
    type VetoOrigin = pallet_collective::EnsureMember<AccountId, CouncilCollective>;
    type CooloffPeriod = CooloffPeriod;
    type Slash = ();
    type Scheduler = Scheduler;
    type PalletsOrigin = OriginCaller;
    type MaxVotes = MaxVotes;
    type WeightInfo = pallet_democracy::weights::SubstrateWeight<Runtime>;
    type MaxProposals = MaxProposals;
    type Preimages = Preimage;
    type MaxDeposits = ConstU32<100>;
    type MaxBlacklisted = ConstU32<100>;
    type SubmitOrigin = frame_system::EnsureSigned<AccountId>;
}

// Treasury configuration - temporarily disabled due to Pay trait API changes in fork
// TODO: Re-enable after implementing proper Pay trait for treasury payouts
// parameter_types! {
//     pub const TreasuryPalletId: PalletId = PalletId(*b"py/trsry");
//     pub const ProposalBond: Permill = Permill::from_percent(5);
//     pub const ProposalBondMinimum: Balance = 100 * EXISTENTIAL_DEPOSIT;
//     pub const ProposalBondMaximum: Balance = 500 * EXISTENTIAL_DEPOSIT;
//     pub const SpendPeriod: BlockNumber = 24 * DAYS;
//     pub const Burn: Permill = Permill::from_percent(1);
//     pub const TreasuryMaxApprovals: u32 = 100;
//     pub const PayoutSpendPeriod: BlockNumber = 30 * DAYS;
// }

// Off-chain worker unsigned transaction support
impl<LocalCall> frame_system::offchain::CreateTransactionBase<LocalCall> for Runtime
where
    RuntimeCall: From<LocalCall>,
{
    type Extrinsic = UncheckedExtrinsic;
    type RuntimeCall = RuntimeCall;
}

impl<LocalCall> frame_system::offchain::CreateBare<LocalCall> for Runtime
where
    RuntimeCall: From<LocalCall>,
{
    fn create_bare(call: RuntimeCall) -> UncheckedExtrinsic {
        UncheckedExtrinsic::new_bare(call)
    }
}

// Create the runtime by composing the FRAME pallets that were previously configured.
construct_runtime!(
    pub struct Runtime
    where
        Block = Block,
        NodeBlock = opaque::Block,
        UncheckedExtrinsic = UncheckedExtrinsic,
    {
        System: frame_system,
        Timestamp: pallet_timestamp,
        Aura: pallet_aura,
        // Grandpa removed - quantum-vulnerable (Ed25519/BLS signatures)
        Session: pallet_session,
        Authorship: pallet_authorship,
        Balances: pallet_balances,
        TransactionPayment: pallet_transaction_payment,
        Sudo: pallet_sudo,

        // Governance pallets - enabled for decentralized runtime upgrades
        Scheduler: pallet_scheduler,
        Preimage: pallet_preimage,
        Democracy: pallet_democracy,
        Council: pallet_collective::<Instance1>,
        TechnicalCommittee: pallet_collective::<Instance2>,
        // Treasury: pallet_treasury, // Temporarily disabled - Pay trait API changes

        // Quantum pallets - providing quantum-safe consensus and entropy
        QuantumCrypto: pallet_quantum_crypto,
        ProofOfCoherence: pallet_proof_of_coherence,
        RuntimeSegmentation: pallet_runtime_segmentation,
        ChunkedUpgrade: pallet_runtime_segmentation::chunked_upgrade::pallet,
        ValidatorEntropy: pallet_validator_entropy,
        RelayCoordination: pallet_relay_coordination,
        SphincsKeystore: pallet_sphincs_keystore,

        // Dev governance pallet - tokenized voting for feature proposals
        DevGovernance: pallet_dev_governance,

        // Validator rewards pallet - economic incentives for validators
        ValidatorRewards: pallet_validator_rewards,

        // Validator set management
        ValidatorSet: substrate_validator_set,

        // Validator governance - voting on new validator additions
        ValidatorGovernance: pallet_validator_governance,

        // Academic/Legal Governance pallets
        AcademicVouch: pallet_academic_vouch,
        RicardianContracts: pallet_ricardian_contracts,
        Notarial: pallet_notarial,
		MeshForum: pallet_mesh_forum,
        Fideicommis: pallet_fideicommis,
        Stablecoin: pallet_stablecoin,

        // Adaptive consensus level tracking
        ConsensusLevel: pallet_consensus_level,
    }
);

/// The address format for describing accounts.
pub type Address = sp_runtime::MultiAddress<AccountId, ()>;
/// Block header type as expected by this runtime (using quantum-resistant QuantumHasher).
pub type Header = generic::Header<BlockNumber, QuantumHasher>;
/// Block type as expected by this runtime.
pub type Block = generic::Block<Header, UncheckedExtrinsic>;
/// The SignedExtension to the basic transaction logic.
pub type SignedExtra = (
    frame_system::CheckNonZeroSender<Runtime>,
    frame_system::CheckSpecVersion<Runtime>,
    frame_system::CheckTxVersion<Runtime>,
    frame_system::CheckGenesis<Runtime>,
    frame_system::CheckEra<Runtime>,
    frame_system::CheckNonce<Runtime>,
    frame_system::CheckWeight<Runtime>,
    pallet_transaction_payment::ChargeTransactionPayment<Runtime>,
);

/// Unchecked extrinsic type as expected by this runtime.
pub type UncheckedExtrinsic =
    generic::UncheckedExtrinsic<Address, RuntimeCall, Signature, SignedExtra>;
/// The payload being signed in transactions.
pub type SignedPayload = generic::SignedPayload<RuntimeCall, SignedExtra>;
/// Executive: handles dispatch to the various modules.
pub type Executive = frame_executive::Executive<
    Runtime,
    Block,
    frame_system::ChainContext<Runtime>,
    Runtime,
    AllPalletsWithSystem,
>;

/// The SignedExtension to the basic transaction logic.
pub type BlockNumber = u32;

/// Block time constants
pub const MILLISECS_PER_BLOCK: u64 = 3000;
pub const SLOT_DURATION: u64 = MILLISECS_PER_BLOCK;

// Time is measured by number of blocks.
pub const MINUTES: BlockNumber = 60_000 / (MILLISECS_PER_BLOCK as BlockNumber);
pub const HOURS: BlockNumber = MINUTES * 60;
pub const DAYS: BlockNumber = HOURS * 24;

impl_runtime_apis! {
    impl sp_api::Core<Block> for Runtime {
        fn version() -> RuntimeVersion {
            VERSION
        }

        fn execute_block(block: Block) {
            Executive::execute_block(block);
        }

        fn initialize_block(header: &<Block as BlockT>::Header) -> sp_runtime::ExtrinsicInclusionMode {
            Executive::initialize_block(header)
        }
    }

    impl sp_api::Metadata<Block> for Runtime {
        fn metadata() -> OpaqueMetadata {
            OpaqueMetadata::new(Runtime::metadata().into())
        }

        fn metadata_at_version(version: u32) -> Option<OpaqueMetadata> {
            Runtime::metadata_at_version(version)
        }

        fn metadata_versions() -> sp_std::vec::Vec<u32> {
            Runtime::metadata_versions()
        }
    }

    impl sp_block_builder::BlockBuilder<Block> for Runtime {
        fn apply_extrinsic(extrinsic: <Block as BlockT>::Extrinsic) -> ApplyExtrinsicResult {
            Executive::apply_extrinsic(extrinsic)
        }

        fn finalize_block() -> <Block as BlockT>::Header {
            Executive::finalize_block()
        }

        fn inherent_extrinsics(data: sp_inherents::InherentData) -> Vec<<Block as BlockT>::Extrinsic> {
            data.create_extrinsics()
        }

        fn check_inherents(
            block: Block,
            data: sp_inherents::InherentData,
        ) -> sp_inherents::CheckInherentsResult {
            data.check_extrinsics(&block)
        }
    }

    impl sp_transaction_pool::runtime_api::TaggedTransactionQueue<Block> for Runtime {
        fn validate_transaction(
            source: TransactionSource,
            tx: <Block as BlockT>::Extrinsic,
            block_hash: <Block as BlockT>::Hash,
        ) -> TransactionValidity {
            Executive::validate_transaction(source, tx, block_hash)
        }
    }

    impl sp_offchain::OffchainWorkerApi<Block> for Runtime {
        fn offchain_worker(header: &<Block as BlockT>::Header) {
            Executive::offchain_worker(header)
        }
    }

    impl sp_consensus_aura::AuraApi<Block, AuraId> for Runtime {
        fn slot_duration() -> sp_consensus_aura::SlotDuration {
            sp_consensus_aura::SlotDuration::from_millis(SLOT_DURATION)
        }

        fn authorities() -> Vec<AuraId> {
            // Fork API change: authorities() method removed, read from storage directly
            pallet_aura::Authorities::<Runtime>::get().into_inner()
        }
    }

    impl sp_session::SessionKeys<Block> for Runtime {
        fn generate_session_keys(seed: Option<Vec<u8>>) -> Vec<u8> {
            opaque::SessionKeys::generate(seed)
        }

        fn decode_session_keys(
            encoded: Vec<u8>,
        ) -> Option<Vec<(Vec<u8>, KeyTypeId)>> {
            opaque::SessionKeys::decode_into_raw_public_keys(&encoded)
        }
    }

    // GRANDPA API removed - quantum-vulnerable finality gadget
    // Finality provided by Proof of Coherence consensus

    impl frame_system_rpc_runtime_api::AccountNonceApi<Block, AccountId, Index> for Runtime {
        fn account_nonce(account: AccountId) -> Index {
            System::account_nonce(account)
        }
    }

    impl pallet_transaction_payment_rpc_runtime_api::TransactionPaymentApi<Block, Balance> for Runtime {
        fn query_info(
            uxt: <Block as BlockT>::Extrinsic,
            len: u32,
        ) -> pallet_transaction_payment_rpc_runtime_api::RuntimeDispatchInfo<Balance> {
            TransactionPayment::query_info(uxt, len)
        }
        fn query_fee_details(
            uxt: <Block as BlockT>::Extrinsic,
            len: u32,
        ) -> pallet_transaction_payment::FeeDetails<Balance> {
            TransactionPayment::query_fee_details(uxt, len)
        }
        fn query_weight_to_fee(weight: Weight) -> Balance {
            TransactionPayment::weight_to_fee(weight)
        }
        fn query_length_to_fee(length: u32) -> Balance {
            TransactionPayment::length_to_fee(length)
        }
    }

    impl sp_genesis_builder::GenesisBuilder<Block> for Runtime {
        fn build_state(config: sp_std::vec::Vec<u8>) -> sp_genesis_builder::Result {
            build_state::<RuntimeGenesisConfig>(config)
        }

        fn get_preset(id: &Option<sp_genesis_builder::PresetId>) -> Option<sp_std::vec::Vec<u8>> {
            get_preset::<RuntimeGenesisConfig>(id, &genesis_config_presets::get_preset)
        }

        fn preset_names() -> sp_std::vec::Vec<sp_genesis_builder::PresetId> {
            genesis_config_presets::preset_names()
        }
    }

    impl wallet_api::WalletApi<Block, AccountId, Balance> for Runtime {
        fn get_balance(account: AccountId) -> Balance {
            Balances::free_balance(&account)
        }
    }

    impl pallet_validator_rewards::runtime_api::ValidatorRewardsApi<Block, AccountId, Balance> for Runtime {
        fn validator_stake(account: AccountId) -> Balance {
            ValidatorRewards::validator_stake(&account)
        }

        fn pending_rewards(account: AccountId) -> Balance {
            ValidatorRewards::pending_rewards(&account)
        }

        fn certification_level(account: AccountId) -> u8 {
            match ValidatorRewards::certification(&account) {
                pallet_validator_rewards::CertificationLevel::Uncertified => 0,
                pallet_validator_rewards::CertificationLevel::KYCVerified => 1,
                pallet_validator_rewards::CertificationLevel::AgentCertified => 2,
            }
        }

        fn all_validators() -> sp_std::vec::Vec<(AccountId, Balance)> {
            pallet_validator_rewards::ValidatorStake::<Runtime>::iter().collect()
        }

        fn min_stake() -> Balance {
            ValidatorRewards::min_stake()
        }

        fn block_reward() -> Balance {
            ValidatorRewards::block_reward()
        }

        fn total_staked() -> Balance {
            ValidatorRewards::total_staked()
        }
    }

    impl pallet_mesh_forum::runtime_api::MeshForumApi<Block, AccountId> for Runtime {
        fn get_messages(limit: u32, offset: u32) -> sp_std::vec::Vec<(u32, AccountId, u32, sp_std::vec::Vec<u8>)> {
            let messages = pallet_mesh_forum::Messages::<Runtime>::get();
            let total = messages.len() as u32;

            messages
                .into_iter()
                .enumerate()
                .skip(offset as usize)
                .take(limit as usize)
                .map(|(idx, msg)| {
                    (
                        idx as u32,
                        msg.sender,
                        msg.block.try_into().unwrap_or(0u32),
                        msg.content.into_inner(),
                    )
                })
                .collect()
        }

        fn message_count() -> u32 {
            pallet_mesh_forum::MessageCount::<Runtime>::get()
        }
    }
}

#[cfg(feature = "std")]
pub fn development_genesis_config() -> RuntimeGenesisConfig {
    RuntimeGenesisConfig::default()
}

#[cfg(feature = "std")]
pub fn create_default_config<T: serde::Serialize + Default>() -> Vec<u8> {
    serde_json::to_string(&T::default())
        .expect("Genesis config must be valid")
        .into_bytes()
}

#[cfg(feature = "std")]
pub fn build_config<T: serde::de::DeserializeOwned>(json: Vec<u8>) -> sp_genesis_builder::Result {
    let _config: T = serde_json::from_slice(&json)
        .map_err(|e| format!("Invalid JSON blob: {}", e))?;
    Ok(())
}

#[cfg(feature = "runtime-benchmarks")]
mod benches {
    frame_benchmarking::define_benchmarks!(
        [frame_benchmarking, BaselineBench::<Runtime>]
        [frame_system, SystemBench::<Runtime>]
        [pallet_balances, Balances]
        [pallet_timestamp, Timestamp]
        [pallet_validator_entropy, ValidatorEntropy]
        [pallet_relay_coordination, RelayCoordination]
        // Governance pallets temporarily disabled
        // [pallet_democracy, Democracy]
        // [pallet_collective, Council]
        // [pallet_treasury, Treasury]
        // [pallet_scheduler, Scheduler]
        // [pallet_preimage, Preimage]
    );
}
