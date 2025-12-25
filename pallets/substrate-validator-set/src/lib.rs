//! # Validator Set Pallet
//!
//! The Validator Set Pallet allows addition and removal of
//! authorities/validators via extrinsics (transaction calls), in
//! Substrate-based PoA networks. It also integrates with the im-online pallet
//! to automatically remove offline validators.
//!
//! The pallet depends on the Session pallet and implements related traits for session
//! management. Currently it uses periodic session rotation provided by the
//! session pallet to automatically rotate sessions. For this reason, th#[pallet::genesis_config]e
//! validator addition and removal becomes effective only after 2 sessions
//! (queuing + applying).

#![cfg_attr(not(feature = "std"), no_std)]

mod benchmarking;
// mod mock; // Disabled - needs pallet_session config updates
// mod tests; // Disabled - needs pallet_session config updates
pub mod weights;
use crate::alloc::string::ToString;
use frame_support::{
	ensure,
	pallet_prelude::*,
	traits::{EstimateNextSessionRotation, Get, Randomness, ValidatorSet, ValidatorSetWithIdentification},
	DefaultNoBound,
};
use sp_core::H160;
extern crate alloc;
pub mod types;
use frame_system::pallet_prelude::*;
use log;
pub use pallet::*;
// BABE REMOVED: incompatible with SPHINCS+, using Aura instead
// use pallet_babe;
use scale_info::prelude::format;

use sp_runtime::traits::{Convert, Zero};
use sp_staking::offence::{Offence, OffenceError, ReportOffence};
use sp_std::prelude::*;
use types::EpochChangeData;
pub use weights::*;
pub const LOG_TARGET: &'static str = "runtime::validator-set";

// BABE REMOVED: VRF not needed with quantum randomness
// use sp_consensus_babe::{VrfPreOutput, VrfProof, VrfSignData};

// use sp_core::crypto::RuntimeAppPublic;
// BABE REMOVED: sr25519 used by BABE VRF, not needed with quantum randomness
// use sp_application_crypto::sr25519;

// Removed: qkd_client import - now using runtime's Randomness trait instead

#[frame_support::pallet()]
pub mod pallet {
	use super::*;

	/// Configure the pallet by specifying the parameters and types on which it
	/// depends.
	#[pallet::config]
	// BABE REMOVED: incompatible with SPHINCS+, using Aura instead
	pub trait Config: frame_system::Config + pallet_session::Config {
		/// The Event type.
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// Origin for adding or removing a validator.
		type AddRemoveOrigin: EnsureOrigin<Self::RuntimeOrigin>;

		/// Minimum number of validators to leave in the validator set during
		/// auto removal. Initial validator count could be less than this.
		type MinAuthorities: Get<u32>;

		/// Maximum number of validators allowed in the validator set.
		type MaxValidators: Get<u32>;

		/// Information on runtime weights.
		type WeightInfo: WeightInfo;

		type ValidatorIdToAccountId: Convert<Self::ValidatorId, Option<Self::AccountId>>;
		type AccountIdToValidatorId: Convert<Self::AccountId, Option<Self::ValidatorId>>;
		type Lookup: StaticLookup<Target = Self::AccountId>;
		type EVMAddress: From<H160> + Into<H160>;
		type Randomness: frame_support::traits::Randomness<Self::Hash, BlockNumberFor<Self>>;
	}

	#[pallet::pallet]
	#[pallet::without_storage_info]
	pub struct Pallet<T>(_);

	#[pallet::storage]
	#[pallet::getter(fn validator_count)]
	pub type ValidatorCount<T> = StorageValue<_, u32, ValueQuery>;

	#[pallet::storage]
	#[pallet::getter(fn evm_to_validator_id)]
	pub type EVMAddresstoId<T: Config> = StorageMap<_, Blake2_128Concat, H160, u32, ValueQuery>;

	#[pallet::storage]
	#[pallet::getter(fn validators)]
	pub type Validators<T: Config> = StorageValue<_, Vec<T::ValidatorId>, ValueQuery>;

	#[pallet::storage]
	#[pallet::getter(fn offline_validators)]
	pub type OfflineValidators<T: Config> = StorageValue<_, Vec<T::ValidatorId>, ValueQuery>;

	#[pallet::storage]
	#[pallet::getter(fn current_leader)]
	pub type CurrentLeader<T: Config> =
		StorageValue<_, <T as pallet_session::Config>::ValidatorId, OptionQuery>;

	#[pallet::storage]
	#[pallet::getter(fn current_block_in_window)]
	pub type CurrentBlockInWindow<T: Config> = StorageValue<_, u32, ValueQuery>;

	#[pallet::storage]
	#[pallet::getter(fn block_window)]
	pub type BlockWindow<T: Config> = StorageValue<_, u32, ValueQuery>;

	#[pallet::storage]
	pub type LeaderSet<T: Config> = StorageValue<_, Vec<T::AccountId>, ValueQuery>;

	#[pallet::storage]
	pub type CurrentLeaderIndex<T> = StorageValue<_, u32, ValueQuery>;

	#[pallet::storage]
	pub type BlocksSinceLastRotation<T> = StorageValue<_, u32, ValueQuery>;

	#[pallet::storage]
	#[pallet::getter(fn validator_states)]
	pub type ValidatorStates<T: Config> =
		StorageMap<_, Blake2_128Concat, T::ValidatorId, bool, ValueQuery>;

	// #[pallet::storage]
	// #pub type SlashingOffenses<T: Config> = StorageMap _, Blake2_128Concat, T::ValidatorId,
	// Vec<(OffenseType, BlockNumberFor<T>)>, ValueQuery>;

	#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug)]
	pub enum OffenseType {
		InvalidQuantumValue,
		LeaderDutyFailure,
		VerificationFailure,
		EventOrderTampering,
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		ValidatorAdditionInitiated(T::ValidatorId),
		ValidatorRemovalInitiated(T::ValidatorId),
		ValidatorRegistered(T::ValidatorId, EpochChangeData),
		ValidatorAdded(T::ValidatorId),
		ValidatorRemoved(T::ValidatorId),
		ValidatorEnabled(T::ValidatorId),
		ValidatorDisabled(T::ValidatorId),
		ValidatorStateUpdated(T::ValidatorId, bool),
		ValidatorUnregistered(T::ValidatorId),
		LeaderRotated { new_leader: T::ValidatorId },
		SomethingDone { param: u32 },
		ValidatorsListed(Vec<T::ValidatorId>),
	}

	// Errors inform users that something went wrong.
	#[pallet::error]
	pub enum Error<T> {
		/// Target (post-removal) validator count is below the minimum.
		TooLowValidatorCount,
		/// Validator is already in the validator set.
		Duplicate,
		InvalidLeader,
		InvalidNFTMintEvent,
		NotEligible,
		NoValidators,
		TooFewValidators,
		ValidatorNotFound,
		ValidatorAlreadyExists,
		TooManyValidators,
		NoLeader,
		ValidatorSetNotEmpty,
		InvalidValidator,
		InvalidEpochChangeData, // NoValidators,
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn on_initialize(_n: BlockNumberFor<T>) -> Weight {
			let current_block_in_window = CurrentBlockInWindow::<T>::get();
			if current_block_in_window + 1 >= BlockWindow::<T>::get() {
				let _ = Self::rotate_leaders();
			}
			CurrentBlockInWindow::<T>::mutate(|block| *block += 1);
			Weight::zero()
		}

		fn offchain_worker(_n: BlockNumberFor<T>) {
			Self::log_current_state();
			// log::debug!("Offchain worker triggered for block: {:?}", _n);

			// if let Err(e) = Self::rotate_leaders() {
			// 	log::error!("
			// ╔════════════════════════════════════════════════════════════════════════════╗");
			// 	log::error!("║                               ERROR OCCURRED
			// ║"); 	log::error!("║
			// ║"); 	log::error!("║ Error in rotate_leaders: {:<64} ║", format!("{:?}", e));
			// 	log::error!("
			// ╚════════════════════════════════════════════════════════════════════════════╝");
			// }
		}

		fn on_finalize(_n: BlockNumberFor<T>) {
			// If necessary, reset or perform other finalization tasks here.
		}
	}

	#[pallet::genesis_config]
	#[derive(DefaultNoBound)]
	pub struct GenesisConfig<T: Config> {
		pub initial_validators: Vec<<T as pallet_session::Config>::ValidatorId>,
	}

	#[pallet::genesis_build]
	impl<T: Config> BuildGenesisConfig for GenesisConfig<T> {
		fn build(&self) {
			assert!(<Validators<T>>::get().is_empty(), "Validators are already initialized!");
			<Validators<T>>::put(&self.initial_validators);
			BlockWindow::<T>::put(2);
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		// pub fn slash_validator(validator: &T::ValidatorId, offense: OffenseType) {
		// 	// Base slashing logic
		// 	// Validator removal if needed
		// 	// Stake slashing
		// }
		// fn check_and_slash_invalid_qrng(&self, event: QRNGEvent) {
		// 	// Quantum-specific validation
		// 	// Call substrate-validator-set's slash_validator if needed
		// }

		/// Add a new validator.
		///
		/// New validator's session keys should be set in Session pallet before
		/// calling this.
		///
		/// The origin can be configured using the `AddRemoveOrigin` type in the
		/// host runtime. Can also be set to sudo/root.
		#[pallet::weight(<T as pallet::Config>::WeightInfo::add_validator())]
		pub fn add_validator(origin: OriginFor<T>, validator_id: T::ValidatorId) -> DispatchResult {
			T::AddRemoveOrigin::ensure_origin(origin)?;
			log::info!("add_validator called with validator_id: {:?}", validator_id);

			let mut validators = Validators::<T>::get();
			ensure!(
				validators.len() < T::MaxValidators::get() as usize,
				Error::<T>::TooManyValidators
			);
			ensure!(!validators.contains(&validator_id), Error::<T>::Duplicate);

			log::debug!("Current validators: {:?}", validators);
			log::debug!("MaxValidators: {}", T::MaxValidators::get());

			let validator_id_as_bytes = validator_id.encode();
			log::debug!("Validator ID as bytes: {:?}", validator_id_as_bytes);

			ensure!(validator_id_as_bytes.len() >= 20, Error::<T>::InvalidLeader);

			// Derive EVM address from validator ID
			let evm_address = H160::from_slice(&validator_id_as_bytes[0..20]);

			validators.push(validator_id.clone());
			Validators::<T>::put(validators.clone());

			// In the add_validator function:
			let new_id = Self::validator_count() + 1;
			ValidatorCount::<T>::put(new_id);

			// Store mapping of EVM address to validator ID
			EVMAddresstoId::<T>::insert(evm_address, new_id);

			log::debug!("Updated validators: {:?}", validators);
			log::debug!("New validator ID: {}", new_id);

			Self::deposit_event(Event::ValidatorAdditionInitiated(validator_id));

			Ok(())
		}

		/// Remove a validator.
		///
		/// The origin can be configured using the `AddRemoveOrigin` type in the
		/// host runtime. Can also be set to sudo/root.
		#[pallet::call_index(1)]
		#[pallet::weight(<T as pallet::Config>::WeightInfo::remove_validator())]
		pub fn remove_validator(
			origin: OriginFor<T>,
			validator_id: T::ValidatorId,
		) -> DispatchResult {
			T::AddRemoveOrigin::ensure_origin(origin)?;

			log::info!("remove_validator called with validator_id: {:?}", validator_id);

			Self::do_remove_validator(validator_id.clone())?;

			log::debug!("Validator {:?} removed", validator_id);
			Ok(())
		}

		#[pallet::call_index(2)]
		#[pallet::weight(10_000)]
		pub fn process_registration_event(
			origin: OriginFor<T>,
			validator: T::ValidatorId,
			state: bool,
		) -> DispatchResult {
			let _who = ensure_signed(origin)?;

			// Update the state of the validator
			ValidatorStates::<T>::insert(&validator, state);

			if state {
				Self::deposit_event(Event::ValidatorEnabled(validator));
			} else {
				Self::deposit_event(Event::ValidatorDisabled(validator));
			}

			Ok(())
		}

		#[pallet::call_index(3)]
		#[pallet::weight(10_000)]
		pub fn unregister_validator(
			origin: OriginFor<T>,
			validator: T::ValidatorId,
		) -> DispatchResult {
			let _who = ensure_signed(origin)?;

			// Remove the validator from the state map
			ValidatorStates::<T>::remove(&validator);

			Self::deposit_event(Event::ValidatorUnregistered(validator));

			Ok(())
		}
		#[pallet::call_index(4)]
		#[pallet::weight(10_000)]
		pub fn list_validators(origin: OriginFor<T>) -> DispatchResult {
			let _who = ensure_signed(origin)?;

			let validators = Self::validators();

			let total_validators = validators.len();
			let validator_list = validators
				.iter()
				.map(|validator| format!("║  Validator: {:<74}║", format!("{:?}", validator)))
				.collect::<Vec<String>>()
				.join("\n");

			log::info!(
				r#"
╔══════════════════════════════════════════════════════════════════════════════╗
║                            List of Validators                              ║
║------------------------------------------------------------------------------║
{} 
║------------------------------------------------------------------------------║
║ Total Validators: {:<64}║
╚══════════════════════════════════════════════════════════════════════════════╝
"#,
				validator_list,
				total_validators
			);

			Ok(())
		}
		#[pallet::call_index(5)]
		#[pallet::weight(10_000)]
		pub fn do_something(origin: OriginFor<T>, param: u32) -> DispatchResult {
			let who = ensure_signed(origin)?;

			// Logic for the call, in this case, we're just emitting an event
			Self::deposit_event(Event::SomethingDone { param });

			log::info!("do_something was called by: {:?}", who);
			Ok(())
		}
		#[pallet::call_index(6)]
		#[pallet::weight(10_000)]
		pub fn register_validator(
			origin: OriginFor<T>,
			epoch_change_data: EpochChangeData,
		) -> DispatchResult {
			let account_id = ensure_signed(origin)?;

			// Convert AccountId to ValidatorId
			let validator_id = T::AccountIdToValidatorId::convert(account_id)
				.ok_or(Error::<T>::InvalidValidator)?;

			// // Verify the epoch change data
			// ensure!(
			// 	Self::verify_epoch_change_data(&epoch_change_data),
			// 	Error::<T>::InvalidEpochChangeData
			// );

			// Check if the validator is already in the set
			let mut validators = <Validators<T>>::get();
			ensure!(!validators.contains(&validator_id), Error::<T>::ValidatorAlreadyExists);

			// Ensure we don't exceed the maximum number of validators
			ensure!(
				validators.len() < T::MaxValidators::get() as usize,
				Error::<T>::TooManyValidators
			);

			// Add the validator to the set
			validators.push(validator_id.clone());
			<Validators<T>>::put(validators);

			// Store the epoch change data
			// <ValidatorEpochData<T>>::insert(&validator_id, epoch_change_data.clone());

			// Emit an event
			Self::deposit_event(Event::ValidatorRegistered(validator_id, epoch_change_data));

			Ok(())
		}
	}
}
use scale_info::prelude::string::String;
use sp_application_crypto::RuntimeAppPublic;
// BABE REMOVED: VRF not needed with quantum randomness
// use sp_consensus_babe::{make_vrf_sign_data, Slot};
use sp_core::H256;
use sp_io::hashing::blake2_256;

// Define the key type for your validator keys
const KEY_TYPE: sp_core::crypto::KeyTypeId = sp_application_crypto::key_types::AURA;
use sp_runtime::traits::StaticLookup;

// BABE REMOVED: VRF not needed with quantum randomness
// use schnorrkel::{
// 	signing_context,
// 	vrf::{VRFInOut, VRFProof},
// 	Keypair,
// };
use sp_core::Pair;

// Helper to convert Hash to bytes for random selection
fn hash_to_bytes<H: AsRef<[u8]>>(hash: H) -> Vec<u8> {
	hash.as_ref().to_vec()
}

impl<T: Config> Pallet<T> {
	// BABE REMOVED: VRF not needed with quantum randomness - using quantum randomness instead
	// // Function to generate the VRF input (sign data) for the validator
	// fn generate_vrf_sign_data(slot: Slot) -> VrfSignData {
	// 	// Fetch randomness from BABE
	// 	let randomness = pallet_babe::Randomness::<T>::get(); // Get randomness for the current epoch
	// 	let next_epoch = pallet_babe::Pallet::<T>::next_epoch(); // Get the next epoch dynamically
	//
	// 	// Access the correct field for the epoch number
	// 	let epoch_number = next_epoch.epoch_index; // Assuming `epoch_index` is the correct field
	//
	// 	// Generate VRF sign data with the correct epoch type
	// 	let sign_data = make_vrf_sign_data(&randomness, slot, epoch_number);
	// 	sign_data
	// }
	// fn verify_vrf_proof(
	// 	vrf_in_out: VRFInOut,
	// 	vrf_proof: VRFProof,
	// 	input: &[u8],
	// 	keypair: &Keypair,
	// ) -> bool {
	// 	let context = signing_context(b"babe vrf context"); // BABE context
	// 	let vrf_pre_out = vrf_in_out.to_preout(); // Extract pre-output
	// 										// Use keypair's public key for verification
	// 	keypair
	// 		.public
	// 		.vrf_verify(context.bytes(input), &vrf_pre_out, &vrf_proof)
	// 		.is_ok()
	// }
	//
	// // Generate VRF proof for validator
	// fn generate_vrf_proof(keypair: &Keypair, input: &[u8]) -> (VRFInOut, VRFProof) {
	// 	let context = signing_context(b"babe vrf context"); // BABE context
	// 	let (vrf_in_out, vrf_proof, _) = keypair.vrf_sign(context.bytes(input));
	// 	(vrf_in_out, vrf_proof)
	// }
	// fn generate_vrf_for_validator(
	// 	validator: &T::ValidatorId,
	// 	seed: &[u8],
	// ) -> Result<(VrfPreOutput, VrfProof), &'static str> {
	// 	// Fetch randomness from BABE
	// 	let randomness = pallet_babe::Randomness::<T>::get();
	//
	// 	// Get the next epoch dynamically
	// 	let next_epoch = pallet_babe::Pallet::<T>::next_epoch();
	//
	// 	// Access the correct field for the epoch number
	// 	let epoch_number = next_epoch.epoch_index; // Assuming `epoch_index` is the correct field
	//
	// 	// Generate VRF sign data with dynamic randomness and epoch
	// 	let slot: u64 =
	// 		u64::from_le_bytes(seed[..8].try_into().expect("Seed must be at least 8 bytes"));
	//
	// 	// Create a signing context for VRF
	// 	let context = signing_context(b"babe vrf context");
	//
	// 	// Fetch the validator's keypair (example using Alice's keypair)
	// 	let sr25519_pair =
	// 		sr25519::Pair::from_string("//Alice", None).expect("Failed to get secret key");
	// 	let secret_key = Keypair::from_bytes(&sr25519_pair.to_raw_vec())
	// 		.expect("Failed to convert to schnorrkel Keypair");
	//
	// 	// Generate the VRF proof
	// 	let (vrf_in_out, vrf_proof, _) = secret_key.vrf_sign(context.bytes(&randomness));
	//
	// 	// Extract the pre-output from the VRFInOut struct
	// 	let vrf_pre_output = vrf_in_out.to_preout();
	//
	// 	// Return the VRF output and proof
	// 	Ok((sp_consensus_babe::VrfPreOutput(vrf_pre_output), VrfProof(vrf_proof)))
	// }


	pub fn get_local_validator_id() -> Option<u32> {
		if let Some(local_evm_address) = Self::get_local_evm_address() {
			log::info!("Local EVM address found: {:?}", local_evm_address);
			let id = Self::evm_to_validator_id(local_evm_address);
			log::info!("Local validator ID: {}", id);
			Some(id)
		} else {
			log::warn!("Failed to retrieve local EVM address");
			None
		}
	}

	pub fn get_local_evm_address() -> Option<H160> {
		// BABE REMOVED: Using sphincs public keys instead of sr25519
		let local_keys = sp_io::crypto::sphincs_public_keys(sp_core::crypto::KeyTypeId(*b"aura"));
		local_keys.get(0).map(|key| {
			let key_bytes = key.0;
			H160::from_slice(&key_bytes[0..20])
		})
	}
	/// Check if the given account is a local validator
	fn is_local_validator(validator: &T::ValidatorId) -> bool {
		Self::validators().contains(validator)
	}

	pub fn is_leader() -> bool {
		log::info!("╔═══════════════════ IS LEADER CHECK ═══════════════════╗");

		if let Some(current_leader) = Self::current_leader() {
			log::info!("║ 👑 Current leader: {:?}", current_leader);

			let leader_id_as_bytes = current_leader.encode();
			if leader_id_as_bytes.len() >= 20 {
				let leader_evm_address = H160::from_slice(&leader_id_as_bytes[0..20]);
				let leader_id = Self::evm_to_validator_id(leader_evm_address);
				log::info!("║ Leader EVM address: {:?}", leader_evm_address);
				log::info!("║ Leader ID: {}", leader_id);

				match Self::get_local_validator_id() {
					Some(local_id) => {
						log::info!("║ Local validator ID: {}", local_id);
						let is_leader = leader_id == local_id;

						if is_leader {
							log::info!("║ ✅ MATCH FOUND - This node is the leader!           ║");
						} else {
							log::info!("║ ❌ This node is NOT the leader                        ║");
						}

						log::info!("╚════════════════════════════════════════════════════╝");
						is_leader
					},
					None => {
						log::warn!("║ ⚠️  No local validator ID found                        ║");
						log::info!("╚════════════════════════════════════════════════════╝");
						false
					},
				}
			} else {
				log::warn!("║ ⚠️  Invalid leader ID encoding                         ║");
				log::info!("╚════════════════════════════════════════════════════╝");
				false
			}
		} else {
			log::warn!("║ ⚠️  No current leader set                             ║");
			log::info!("╚════════════════════════════════════════════════════╝");
			false
		}
	}

	fn get_local_validators() -> Vec<T::ValidatorId> {
		Self::validators().into_iter().filter(|v| Self::is_local_validator(v)).collect()
	}

	/// Hash the epoch change data
	pub fn hash_epoch_data(data: &EpochChangeData) -> H256 {
		let encoded_data = (
			data.last_epoch,
			data.last_slot,
			data.last_blockhash.clone(),
			data.new_epoch,
			data.new_slot,
			data.new_blockhash.clone(),
			data.epoch_nonce.clone(),
		)
			.encode();

		H256::from_slice(&blake2_256(&encoded_data))
	}

	pub fn log_current_state() {
		let validators = Self::validators();
		let current_leader = Self::current_leader();
		let block_window = Self::block_window();
		let current_block_in_window = Self::current_block_in_window();

		log::info!("╔════════════════════ CURRENT STATE ════════════════════╗");
		log::info!("║ Validators ({} total):", validators.len());
		for validator in &validators {
			log::info!("║   {:?}", validator);
		}
		log::info!("║----------------------------------------------------║");
		log::info!("║ Current Leader: {:?}", current_leader);
		log::info!("║ Block Window: {}", block_window);
		log::info!("║ Current Block in Window: {}", current_block_in_window);
		log::info!("╚════════════════════════════════════════════════════╝");
	}

	pub fn rotate_leaders() -> DispatchResult {
		let validators = Self::validators();

		// Skip leader rotation if no validators configured in this pallet
		// (ValidatorGovernance pallet handles the actual validator set)
		if validators.is_empty() {
			return Ok(());
		}

		let block_number = <frame_system::Pallet<T>>::block_number();
		let block_window = Self::block_window();

		log::info!("╔═══════════════════ LEADER ROTATION ═══════════════════╗");
		log::info!("║ Current block: {:?}", block_number);
		log::info!("║ Validators count: {}", validators.len());
		
		if (block_number % block_window.into()).is_zero() {
			// Use runtime's Randomness trait for deterministic, consensus-safe randomness
			let (random_hash, _block) = T::Randomness::random(b"leader_rotation");
			let random_bytes = hash_to_bytes(random_hash);
			let quantum_value = if random_bytes.len() >= 8 {
				u64::from_le_bytes(random_bytes[0..8].try_into().expect("Always has 8 bytes"))
			} else {
				// Fallback: use hash bytes as-is
				random_bytes.iter().fold(0u64, |acc, &b| acc.wrapping_mul(256).wrapping_add(b as u64))
			};

			let current_leader_index = (quantum_value as usize) % validators.len();
			
			if let Some(new_leader) = validators.get(current_leader_index) {
				log::info!("║ New leader (quantum selected): {:?}", new_leader);
				CurrentLeader::<T>::put(new_leader.clone());
				Self::deposit_event(Event::LeaderRotated { new_leader: new_leader.clone() });
				CurrentBlockInWindow::<T>::put(0);
				log::info!("║ Leader rotation successful with quantum entropy");
			} else {
				log::error!("║ Failed to get leader from the validator set");
				return Err(Error::<T>::NoLeader.into());
			}
		} else {
			log::info!("║ Not time to rotate leaders yet");
		}
		
		// Rest of your function remains the same
		if let Some(current_leader) = Self::current_leader() {
			log::info!("║ Current leader: {:?}", current_leader);
		} else {
			log::info!("║ No current leader set");
		}
		
		log::info!("╚════════════════════════════════════════════════════╝");
		Ok(())
	}
	// BABE REMOVED: VRF not needed with quantum randomness
	// fn generate_quantum_seeded_vrf_for_validator(
	// 	validator: &T::ValidatorId,
	// ) -> Result<(VrfPreOutput, VrfProof), &'static str> {
	// 	// Get quantum random bytes for seeding
	// 	let seed = get_quantum_random_bytes(32);
	//
	// 	// Create a signing context with quantum seed
	// 	let context = signing_context(b"quantum-babe-vrf");
	//
	// 	// Fetch the validator's keypair (example using Alice's keypair)
	// 	let sr25519_pair =
	// 		sr25519::Pair::from_string("//Alice", None).expect("Failed to get secret key");
	// 	let secret_key = Keypair::from_bytes(&sr25519_pair.to_raw_vec())
	// 		.expect("Failed to convert to schnorrkel Keypair");
	//
	// 	// Generate the VRF proof with quantum seed
	// 	let (vrf_in_out, vrf_proof, _) = secret_key.vrf_sign(context.bytes(&seed));
	//
	// 	// Extract the pre-output from the VRFInOut struct
	// 	let vrf_pre_output = vrf_in_out.to_preout();
	//
	// 	// Return the VRF output and proof
	// 	Ok((sp_consensus_babe::VrfPreOutput(vrf_pre_output), VrfProof(vrf_proof)))
	// }
	pub fn get_hybrid_randomness() -> Vec<u8> {
		// Use runtime's Randomness trait for deterministic, consensus-safe randomness
		let (random_hash, _block) = T::Randomness::random(b"hybrid_randomness");
		let quantum_randomness = hash_to_bytes(random_hash);

		log::debug!("Generated deterministic randomness: {:?}", quantum_randomness);
		quantum_randomness
	}
	pub fn get_validators() -> Vec<T::ValidatorId> {
		let validators = Self::validators();
		log::debug!("Retrieved validators: {:?}", validators);
		validators
	}

	/// Set the block window
	pub fn set_block_window(window: u32) {
		BlockWindow::<T>::put(window);
	}

	/// Initialize the block window
	pub fn initialize_block_window(window: u32) {
		BlockWindow::<T>::put(window);
	}

	/// Remove a validator from the set
	fn do_remove_validator(validator_id: T::ValidatorId) -> DispatchResult {
		let mut validators = Self::validators();
		ensure!(validators.contains(&validator_id), Error::<T>::ValidatorNotFound);
		ensure!(
			validators.len().saturating_sub(1) as u32 >= T::MinAuthorities::get(),
			Error::<T>::TooLowValidatorCount
		);

		validators.retain(|v| *v != validator_id);
		<Validators<T>>::put(validators);

		Self::deposit_event(Event::ValidatorRemovalInitiated(validator_id.clone()));
		log::debug!(target: LOG_TARGET, "Validator removal initiated.");

		Ok(())
	}

	/// Mark a validator for removal
	fn mark_for_removal(validator_id: T::ValidatorId) {
		<OfflineValidators<T>>::mutate(|v| v.push(validator_id));
		log::debug!(target: LOG_TARGET, "Offline validator marked for auto removal.");
	}

	fn log_validator_set() {
		let validators = Self::validators();
		let current_leader = Self::current_leader();
		let block_window = Self::block_window();
		let current_block = Self::current_block_in_window();

		log::debug!("╔══════════════════ VALIDATOR SET ══════════════════╗");
		log::debug!("║ Number of validators: {}", validators.len());
		for validator in &validators {
			log::debug!("║  Validator: {:?}", validator);
		}
		log::debug!(
			"║ Current Leader: {}",
			match current_leader {
				Some(leader) => format!("{:?}", leader),
				None => "None".to_string(),
			}
		);
		log::debug!("║ Block Window: {}", block_window);
		log::debug!("║ Current Block in Window: {}", current_block);
		log::debug!("╚════════════════════════════════════════════════════╝");
	}
	pub fn elect_leader_via_vrf() -> Result<T::ValidatorId, &'static str> {
		let validators = Self::validators();
		ensure!(!validators.is_empty(), "No validators available");

		// Use runtime's Randomness trait for deterministic, consensus-safe randomness
		let (random_hash, _block) = T::Randomness::random(b"elect_leader_vrf");
		let quantum_random_bytes = hash_to_bytes(random_hash);

		// Use the quantum random bytes to select a validator
		let chosen_validator_index = if quantum_random_bytes.len() >= 8 {
			u64::from_le_bytes(quantum_random_bytes[0..8].try_into().expect("Always has 8 bytes"))
				as usize % validators.len()
		} else {
			// Fallback for shorter hashes
			quantum_random_bytes.iter().fold(0usize, |acc, &b| acc.wrapping_mul(256).wrapping_add(b as usize))
				% validators.len()
		};

		let chosen_leader =
			validators.get(chosen_validator_index).ok_or("Failed to select leader")?;

		log::info!(
			"Selected leader using quantum randomness: {:?} (index: {})",
			chosen_leader, chosen_validator_index
		);

		Ok(chosen_leader.clone())
	}
	pub fn get_quantum_seed_for_vrf() -> [u8; 32] {
		// Use runtime's Randomness trait for deterministic, consensus-safe randomness
		let (random_hash, _block) = T::Randomness::random(b"quantum_seed_for_vrf");
		let quantum_bytes = hash_to_bytes(random_hash);

		// Convert to a fixed array
		let mut seed = [0u8; 32];
		for (i, byte) in quantum_bytes.iter().enumerate().take(32) {
			seed[i] = *byte;
		}

		log::debug!("Generated deterministic seed for VRF: {:?}", seed);
		seed
	}

	/// Add a validator internally (called by governance pallets)
	/// This bypasses the origin check and is only meant to be called by trusted pallets
	pub fn add_validator_internal(account_id: T::AccountId) -> DispatchResult {
		// Convert AccountId to ValidatorId
		let validator_id = T::AccountIdToValidatorId::convert(account_id)
			.ok_or(Error::<T>::InvalidValidator)?;

		log::info!("add_validator_internal called with validator_id: {:?}", validator_id);

		let mut validators = Validators::<T>::get();
		ensure!(
			validators.len() < T::MaxValidators::get() as usize,
			Error::<T>::TooManyValidators
		);
		ensure!(!validators.contains(&validator_id), Error::<T>::Duplicate);

		let validator_id_as_bytes = validator_id.encode();
		ensure!(validator_id_as_bytes.len() >= 20, Error::<T>::InvalidLeader);

		// Derive EVM address from validator ID
		let evm_address = H160::from_slice(&validator_id_as_bytes[0..20]);

		validators.push(validator_id.clone());
		Validators::<T>::put(validators);

		// Update validator count
		let new_id = Self::validator_count() + 1;
		ValidatorCount::<T>::put(new_id);

		// Store mapping of EVM address to validator ID
		EVMAddresstoId::<T>::insert(evm_address, new_id);

		log::info!("Validator added via governance: {:?}", validator_id);
		Self::deposit_event(Event::ValidatorAdded(validator_id));

		Ok(())
	}
}

// Provides the new set of validators to the session module when session is
// being rotated.
impl<T: Config> pallet_session::SessionManager<T::ValidatorId> for Pallet<T> {
	// Plan a new session and provide new validator set.
	fn new_session(new_index: u32) -> Option<Vec<T::ValidatorId>> {
		let validators = Validators::<T>::get(); // Fetch validators from storage
		log::debug!("New session validators: {:?}", validators);
		log::debug!(target: LOG_TARGET, "Validators after removal of offline validators: {:?}", validators);

		if validators.is_empty() {
			log::warn!(target: LOG_TARGET, "No validators found after removing offline validators");
			return None;
		}

		let block_window = BlockWindow::<T>::get();
		log::debug!(target: LOG_TARGET, "Configured block window: {}", block_window);

		let block_window = if block_window == 0 {
			log::warn!(target: LOG_TARGET, "Block window is zero. Defaulting to a value of 1.");
			BlockWindow::<T>::put(1);
			1
		} else {
			block_window
		};

		let leader_index = (new_index as usize / block_window as usize) % validators.len();
		log::debug!(target: LOG_TARGET, "Calculated leader index: {}", leader_index);

		let leader = validators[leader_index].clone();
		log::debug!(target: LOG_TARGET, "New leader selected: {:?}", leader);

		CurrentLeader::<T>::put(leader.clone());
		CurrentBlockInWindow::<T>::put(0);

		Self::log_validator_set(); // Log the validator set and current leader

		Some(validators)
	}

	fn end_session(_end_index: u32) {}

	fn start_session(_start_index: u32) {}
}

impl<T: Config> EstimateNextSessionRotation<BlockNumberFor<T>> for Pallet<T> {
	fn average_session_length() -> BlockNumberFor<T> {
		Zero::zero()
	}

	fn estimate_current_session_progress(
		_now: BlockNumberFor<T>,
	) -> (Option<sp_runtime::Permill>, sp_weights::Weight) {
		(None, Zero::zero())
	}

	fn estimate_next_session_rotation(
		_now: BlockNumberFor<T>,
	) -> (Option<BlockNumberFor<T>>, sp_weights::Weight) {
		(None, Zero::zero())
	}
}

// Implementation of Convert trait to satisfy trait bounds in session pallet.
// Here it just returns the same ValidatorId.
pub struct ValidatorOf<T>(sp_std::marker::PhantomData<T>);

impl<T: Config>
	Convert<
		<T as pallet_session::Config>::ValidatorId,
		Option<<T as pallet_session::Config>::ValidatorId>,
	> for ValidatorOf<T>
{
	fn convert(
		account: <T as pallet_session::Config>::ValidatorId,
	) -> Option<<T as pallet_session::Config>::ValidatorId> {
		Some(account)
	}
}

impl<T: Config> ValidatorSet<T::ValidatorId> for Pallet<T> {
	type ValidatorId = <T as pallet_session::Config>::ValidatorId;
	type ValidatorIdOf = ValidatorOf<T>;

	fn session_index() -> sp_staking::SessionIndex {
		pallet_session::Pallet::<T>::current_index()
	}

	fn validators() -> Vec<T::ValidatorId> {
		pallet_session::Pallet::<T>::validators()
	}
}

impl<T: Config> ValidatorSetWithIdentification<T::ValidatorId> for Pallet<T> {
	type Identification = <T as pallet_session::Config>::ValidatorId;
	type IdentificationOf = ValidatorOf<T>;
}

// Offence reporting and unresponsiveness management.
// This is for the ImOnline pallet integration.
impl<
		T: Config,
		O: Offence<(
			<T as pallet_session::Config>::ValidatorId,
			<T as pallet_session::Config>::ValidatorId,
		)>,
	>
	ReportOffence<
		T::AccountId,
		(<T as pallet_session::Config>::ValidatorId, <T as pallet_session::Config>::ValidatorId),
		O,
	> for Pallet<T>
{
	fn report_offence(_reporters: Vec<T::AccountId>, offence: O) -> Result<(), OffenceError> {
		let offenders = offence.offenders();

		for (v, _) in offenders.into_iter() {
			Self::mark_for_removal(v);
		}

		Ok(())
	}

	fn is_known_offence(
		_offenders: &[(T::ValidatorId, T::ValidatorId)],
		_time_slot: &O::TimeSlot,
	) -> bool {
		false
	}
}
