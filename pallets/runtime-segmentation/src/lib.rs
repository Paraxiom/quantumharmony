//! # Runtime Segmentation Pallet
//!
//! Implements 8x8x8 toroidal mesh topology for parallel transaction processing.
//! - 512 total segments in a 3D torus
//! - Load balancing across segments
//! - Cross-segment communication
//! - **Chunked runtime upgrades** for large WASM blobs exceeding BlockLength
//!
//! Ported from quantumharmony-core for Substrate integration.

#![cfg_attr(not(feature = "std"), no_std)]

pub use pallet::*;

/// Ternary encoding module for efficient 3D coordinate representation
pub mod ternary;

/// Quaternary encoding module for quantum checksums
pub mod quaternary;

/// Chunked runtime upgrade module for bypassing BlockLength limits
pub mod chunked_upgrade;

use codec::{Encode, Decode};
use frame_support::pallet_prelude::*;
use frame_system::pallet_prelude::*;
use sp_runtime::traits::Hash;
use sp_std::prelude::*;
use frame_support::traits::Randomness;

/// Toroidal mesh dimensions (8x8x8 = 512 segments)
pub const MESH_SIZE_X: usize = 8;
pub const MESH_SIZE_Y: usize = 8;
pub const MESH_SIZE_Z: usize = 8;
pub const TOTAL_SEGMENTS: usize = MESH_SIZE_X * MESH_SIZE_Y * MESH_SIZE_Z;

/// Segment coordinates in the toroidal mesh
#[derive(Encode, Decode, TypeInfo, Clone, Copy, PartialEq, Eq, RuntimeDebug, MaxEncodedLen)]
pub struct SegmentCoordinates {
	pub x: u8,
	pub y: u8,
	pub z: u8,
}

/// Runtime segment in the toroidal mesh
#[derive(Encode, Decode, TypeInfo, Clone, PartialEq, Eq, RuntimeDebug)]
#[scale_info(skip_type_params(T))]
pub struct RuntimeSegment<T: Config> {
	pub id: u32,
	pub coordinates: SegmentCoordinates,
	pub state_root: T::Hash,
	pub transaction_count: u64,
	pub load_factor: u8, // 0-100%
	pub entangled_segments: BoundedVec<u32, ConstU32<6>>, // 6 neighbors in 3D torus
}

/// Segment load information
#[derive(Encode, Decode, TypeInfo, Clone, PartialEq, Eq, RuntimeDebug, MaxEncodedLen)]
pub struct SegmentLoad {
	pub segment_id: u32,
	pub current_load: u8,
	pub average_load: u8,
	pub peak_load: u8,
}

/// Convert 3D coordinates to segment ID
pub fn coordinates_to_id(coords: &SegmentCoordinates) -> u32 {
	(coords.z as u32 * MESH_SIZE_X as u32 * MESH_SIZE_Y as u32) +
	(coords.y as u32 * MESH_SIZE_X as u32) +
	coords.x as u32
}

/// Convert segment ID to 3D coordinates
pub fn id_to_coordinates(id: u32) -> SegmentCoordinates {
	let x = (id % MESH_SIZE_X as u32) as u8;
	let y = ((id / MESH_SIZE_X as u32) % MESH_SIZE_Y as u32) as u8;
	let z = (id / (MESH_SIZE_X as u32 * MESH_SIZE_Y as u32)) as u8;

	SegmentCoordinates { x, y, z }
}

/// Get adjacent segments in the toroidal mesh (6 neighbors in 3D)
pub fn get_adjacent_segments(coords: &SegmentCoordinates) -> Vec<SegmentCoordinates> {
	let mut neighbors = Vec::new();

	// X-axis neighbors (with toroidal wrap)
	let x_plus = (coords.x + 1) % MESH_SIZE_X as u8;
	let x_minus = if coords.x == 0 { MESH_SIZE_X as u8 - 1 } else { coords.x - 1 };

	// Y-axis neighbors (with toroidal wrap)
	let y_plus = (coords.y + 1) % MESH_SIZE_Y as u8;
	let y_minus = if coords.y == 0 { MESH_SIZE_Y as u8 - 1 } else { coords.y - 1 };

	// Z-axis neighbors (with toroidal wrap)
	let z_plus = (coords.z + 1) % MESH_SIZE_Z as u8;
	let z_minus = if coords.z == 0 { MESH_SIZE_Z as u8 - 1 } else { coords.z - 1 };

	neighbors.push(SegmentCoordinates { x: x_plus, y: coords.y, z: coords.z });
	neighbors.push(SegmentCoordinates { x: x_minus, y: coords.y, z: coords.z });
	neighbors.push(SegmentCoordinates { x: coords.x, y: y_plus, z: coords.z });
	neighbors.push(SegmentCoordinates { x: coords.x, y: y_minus, z: coords.z });
	neighbors.push(SegmentCoordinates { x: coords.x, y: coords.y, z: z_plus });
	neighbors.push(SegmentCoordinates { x: coords.x, y: coords.y, z: z_minus });

	neighbors
}

/// Calculate distance between two segments in toroidal space
pub fn toroidal_distance(a: &SegmentCoordinates, b: &SegmentCoordinates) -> u32 {
	let dx = toroidal_diff(a.x, b.x, MESH_SIZE_X as u8);
	let dy = toroidal_diff(a.y, b.y, MESH_SIZE_Y as u8);
	let dz = toroidal_diff(a.z, b.z, MESH_SIZE_Z as u8);

	(dx as u32 * dx as u32 + dy as u32 * dy as u32 + dz as u32 * dz as u32)
}

/// Calculate minimum difference in toroidal space
fn toroidal_diff(a: u8, b: u8, size: u8) -> u8 {
	let direct = if a > b { a - b } else { b - a };
	let wrapped = size - direct;
	if direct < wrapped { direct } else { wrapped }
}

#[frame_support::pallet]
pub mod pallet {
	use super::*;

	#[pallet::pallet]
	#[pallet::without_storage_info]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The overarching event type.
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// Source of randomness for quantum-secure segment selection
		type MyRandomness: Randomness<Self::Hash, BlockNumberFor<Self>>;
	}

	/// Segments storage - maps segment ID to RuntimeSegment
	#[pallet::storage]
	#[pallet::getter(fn segment)]
	pub type Segments<T: Config> = StorageMap<_, Blake2_128Concat, u32, RuntimeSegment<T>>;

	/// Current load per segment
	#[pallet::storage]
	#[pallet::getter(fn segment_load)]
	pub type SegmentLoads<T: Config> = StorageMap<_, Blake2_128Concat, u32, SegmentLoad>;

	/// Total number of initialized segments
	#[pallet::storage]
	#[pallet::getter(fn segment_count)]
	pub type SegmentCount<T: Config> = StorageValue<_, u32, ValueQuery>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// Segment initialized [segment_id]
		SegmentInitialized { segment_id: u32 },
		/// Load balancing performed [migrations_count]
		LoadBalanced { migrations: u32 },
		/// Transaction routed to segment [tx_hash, segment_id]
		TransactionRouted { segment_id: u32 },
	}

	#[pallet::error]
	pub enum Error<T> {
		/// Segment ID out of range
		InvalidSegmentId,
		/// Segment already initialized
		SegmentAlreadyExists,
		/// Segment not found
		SegmentNotFound,
	}

	#[pallet::genesis_config]
	pub struct GenesisConfig<T: Config> {
		/// Initialize all segments on genesis
		pub initialize_segments: bool,
		#[serde(skip)]
		pub _phantom: core::marker::PhantomData<T>,
	}

	impl<T: Config> Default for GenesisConfig<T> {
		fn default() -> Self {
			Self {
				initialize_segments: true, // Auto-initialize by default
				_phantom: Default::default(),
			}
		}
	}

	#[pallet::genesis_build]
	impl<T: Config> BuildGenesisConfig for GenesisConfig<T> {
		fn build(&self) {
			if self.initialize_segments {
				// Initialize all 512 segments
				let result = Pallet::<T>::initialize_all_segments();
				match result {
					Ok(count) => {
						log::info!("✅ Initialized {} runtime segments in genesis", count);
					}
					Err(e) => {
						log::error!("❌ Failed to initialize segments: {:?}", e);
					}
				}
			}
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Initialize a runtime segment
		#[pallet::call_index(0)]
		#[pallet::weight(Weight::from_parts(10_000, 0))]
		pub fn initialize_segment(origin: OriginFor<T>, segment_id: u32) -> DispatchResult {
			ensure_root(origin)?;

			ensure!(segment_id < TOTAL_SEGMENTS as u32, Error::<T>::InvalidSegmentId);
			ensure!(!Segments::<T>::contains_key(segment_id), Error::<T>::SegmentAlreadyExists);

			let coordinates = id_to_coordinates(segment_id);
			let neighbors = get_adjacent_segments(&coordinates);
			let entangled_segments: BoundedVec<u32, ConstU32<6>> = neighbors
				.iter()
				.map(|c| coordinates_to_id(c))
				.collect::<Vec<_>>()
				.try_into()
				.map_err(|_| Error::<T>::InvalidSegmentId)?;

			// Generate initial state root using block hash
			let state_root = T::Hashing::hash(&segment_id.encode());

			let segment = RuntimeSegment {
				id: segment_id,
				coordinates,
				state_root,
				transaction_count: 0,
				load_factor: 0, // Start with 0% load
				entangled_segments,
			};

			Segments::<T>::insert(segment_id, segment);
			SegmentCount::<T>::mutate(|count| *count += 1);

			Self::deposit_event(Event::SegmentInitialized { segment_id });

			Ok(())
		}
	}

	impl<T: Config> Pallet<T> {
		/// Route transaction to optimal segment using quantum randomness
		///
		/// Strategy:
		/// 1. Find N candidates with lowest load (e.g., N=5)
		/// 2. Use quantum randomness to select among candidates
		/// 3. This prevents routing attacks while maintaining load balance
		pub fn route_to_segment() -> u32 {
			const CANDIDATE_COUNT: usize = 5;

			// Collect all segments with their loads
			let mut segments_with_load: Vec<(u32, u8)> = Vec::new();
			for i in 0..TOTAL_SEGMENTS as u32 {
				if let Some(load) = SegmentLoads::<T>::get(i) {
					segments_with_load.push((i, load.current_load));
				}
			}

			// If no segments initialized, return 0
			if segments_with_load.is_empty() {
				return 0;
			}

			// Sort by load (ascending)
			segments_with_load.sort_by_key(|(_, load)| *load);

			// Take top CANDIDATE_COUNT candidates (or all if fewer)
			let candidate_count = segments_with_load.len().min(CANDIDATE_COUNT);
			let candidates = &segments_with_load[0..candidate_count];

			// Use quantum randomness to select among candidates
			let (random_hash, _) = T::MyRandomness::random(b"segment_selection");
			let random_bytes = random_hash.as_ref();
			let random_index = (random_bytes[0] as usize) % candidate_count;

			candidates[random_index].0
		}

		/// Deterministic routing (for testing and non-critical paths)
		/// Simply returns segment with lowest load
		pub fn route_to_segment_deterministic() -> u32 {
			let mut min_load = 255u8;
			let mut best_segment = 0u32;

			for i in 0..TOTAL_SEGMENTS as u32 {
				if let Some(load) = SegmentLoads::<T>::get(i) {
					if load.current_load < min_load {
						min_load = load.current_load;
						best_segment = i;
					}
				}
			}

			best_segment
		}

		/// Initialize all segments (for genesis or testing)
		pub fn initialize_all_segments() -> Result<u32, DispatchError> {
			let mut initialized = 0u32;

			for segment_id in 0..TOTAL_SEGMENTS as u32 {
				if !Segments::<T>::contains_key(segment_id) {
					let coordinates = id_to_coordinates(segment_id);
					let neighbors = get_adjacent_segments(&coordinates);
					let entangled_segments: BoundedVec<u32, ConstU32<6>> = neighbors
						.iter()
						.map(|c| coordinates_to_id(c))
						.collect::<Vec<_>>()
						.try_into()
						.map_err(|_| Error::<T>::InvalidSegmentId)?;

					let state_root = T::Hashing::hash(&segment_id.encode());

					let segment = RuntimeSegment {
						id: segment_id,
						coordinates,
						state_root,
						transaction_count: 0,
						load_factor: 0,
						entangled_segments,
					};

					Segments::<T>::insert(segment_id, segment);

					// Initialize load tracking
					let load = SegmentLoad {
						segment_id,
						current_load: 0,
						average_load: 0,
						peak_load: 0,
					};
					SegmentLoads::<T>::insert(segment_id, load);

					initialized += 1;
				}
			}

			SegmentCount::<T>::put(initialized);

			Ok(initialized)
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn test_coordinates_conversion() {
		// Test first segment
		let coords = id_to_coordinates(0);
		assert_eq!(coords.x, 0);
		assert_eq!(coords.y, 0);
		assert_eq!(coords.z, 0);
		assert_eq!(coordinates_to_id(&coords), 0);

		// Test last segment
		let coords = id_to_coordinates(511);
		assert_eq!(coords.x, 7);
		assert_eq!(coords.y, 7);
		assert_eq!(coords.z, 7);
		assert_eq!(coordinates_to_id(&coords), 511);

		// Test middle segment
		let coords = id_to_coordinates(256);
		let id = coordinates_to_id(&coords);
		assert_eq!(id, 256);
	}

	#[test]
	fn test_adjacent_segments() {
		// Test center segment
		let coords = SegmentCoordinates { x: 4, y: 4, z: 4 };
		let neighbors = get_adjacent_segments(&coords);
		assert_eq!(neighbors.len(), 6);

		// Test toroidal wrap at edge
		let coords = SegmentCoordinates { x: 0, y: 0, z: 0 };
		let neighbors = get_adjacent_segments(&coords);
		assert_eq!(neighbors.len(), 6);

		// Verify wraparound
		assert!(neighbors.contains(&SegmentCoordinates { x: 7, y: 0, z: 0 })); // x wraps
		assert!(neighbors.contains(&SegmentCoordinates { x: 0, y: 7, z: 0 })); // y wraps
		assert!(neighbors.contains(&SegmentCoordinates { x: 0, y: 0, z: 7 })); // z wraps
	}

	#[test]
	fn test_toroidal_distance() {
		let a = SegmentCoordinates { x: 0, y: 0, z: 0 };
		let b = SegmentCoordinates { x: 1, y: 0, z: 0 };
		let dist = toroidal_distance(&a, &b);
		assert_eq!(dist, 1);

		// Test wraparound distance
		let a = SegmentCoordinates { x: 0, y: 0, z: 0 };
		let b = SegmentCoordinates { x: 7, y: 0, z: 0 };
		let dist = toroidal_distance(&a, &b);
		assert_eq!(dist, 1); // Should be 1 because of toroidal wrap
	}
}
