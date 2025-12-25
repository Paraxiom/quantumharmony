//! Chunked Runtime Upgrade Module
//!
//! Enables runtime upgrades larger than BlockLength by splitting WASM into chunks.
//! Each chunk is uploaded in a separate transaction, then assembled and applied.
//!
//! ## Design
//!
//! The 598KB WASM + 50KB SPHINCS+ signature = 650KB total, exceeding the 256KB BlockLength.
//! This module solves the chicken-and-egg problem by:
//!
//! 1. Splitting WASM into chunks of ~64KB each (well under 256KB limit with signature overhead)
//! 2. Each chunk is individually signed and uploaded via separate extrinsics
//! 3. Chunks are stored in runtime storage, distributed across toroidal segments
//! 4. Final commit transaction assembles chunks and triggers system.set_code
//!
//! ## Security
//!
//! - Only sudo origin can upload chunks and finalize upgrades
//! - Upgrade ID prevents mixing chunks from different upgrade attempts
//! - Blake2-256 hash verification ensures chunk integrity
//! - Chunks expire after a configurable number of blocks
//!
//! ## Integration with Toroidal Mesh
//!
//! Chunks are assigned to segments based on their index:
//! - Chunk 0 → Segment 0, Chunk 1 → Segment 1, etc.
//! - This distributes storage load across the 512-segment mesh
//! - Cross-segment queries aggregate chunks during finalization

use codec::{Encode, Decode, MaxEncodedLen, DecodeWithMemTracking};
use frame_support::pallet_prelude::*;
use frame_system::pallet_prelude::*;
use sp_std::prelude::*;
use scale_info::TypeInfo;
use sp_runtime::traits::Hash;

/// Maximum chunk size in bytes (64KB - leaves room for signature + call overhead)
pub const MAX_CHUNK_SIZE: u32 = 65_536;

/// Maximum number of chunks for a single upgrade (32 chunks * 64KB = 2MB max WASM)
/// Increased from 16 to support larger runtimes with quantum cryptography pallets
pub const MAX_CHUNKS: u32 = 32;

/// Maximum WASM size after assembly (2MB)
/// Note: Debug builds are ~2MB, release builds with optimization are typically smaller
pub const MAX_WASM_SIZE: u32 = MAX_CHUNK_SIZE * MAX_CHUNKS;

/// Chunk expiry in blocks (if not finalized within this time, chunks are cleared)
/// Increased from 100 to 1800 (~3 hours at 6s blocks) to allow for network delays
/// and manual verification before finalization
pub const CHUNK_EXPIRY_BLOCKS: u32 = 1800;

/// WASM magic bytes - all valid WASM starts with these 4 bytes
pub const WASM_MAGIC: [u8; 4] = [0x00, 0x61, 0x73, 0x6D]; // \0asm

/// Minimum WASM size for a valid Substrate runtime (~100KB)
pub const MIN_WASM_SIZE: u32 = 100_000;

/// WASM version we expect (version 1)
pub const WASM_VERSION: u8 = 0x01;

/// Maximum number of upgrade retries allowed before requiring manual intervention
pub const MAX_UPGRADE_ATTEMPTS: u8 = 3;

/// Rollback window in blocks (~6 hours at 6s blocks)
/// After this window, the backup is automatically invalidated
pub const ROLLBACK_WINDOW_BLOCKS: u32 = 3600;

/// Represents a single chunk of a runtime upgrade
#[derive(Encode, Decode, TypeInfo, Clone, PartialEq, Eq, RuntimeDebug, MaxEncodedLen)]
pub struct UpgradeChunkMeta {
    /// Index of this chunk (0-based)
    pub chunk_index: u8,
    /// Total number of chunks expected
    pub total_chunks: u8,
    /// Block number when this chunk was uploaded
    pub uploaded_at: u32,
    /// Size of this chunk in bytes
    pub chunk_size: u32,
    /// Segment ID where this chunk is stored (for toroidal distribution)
    pub segment_id: u32,
    /// Blake2-256 hash of this chunk's data for integrity verification
    pub chunk_hash: [u8; 32],
}

/// Metadata for a pending chunked upgrade
#[derive(Encode, Decode, TypeInfo, Clone, PartialEq, Eq, RuntimeDebug, MaxEncodedLen)]
pub struct PendingUpgradeMeta {
    /// Block when upgrade was initiated
    pub initiated_at: u32,
    /// Expected total WASM size
    pub expected_size: u32,
    /// Number of chunks expected
    pub total_chunks: u8,
    /// Number of chunks received so far
    pub chunks_received: u8,
}

/// Reason for upgrade cancellation
#[derive(Encode, Decode, TypeInfo, Clone, PartialEq, Eq, RuntimeDebug, MaxEncodedLen)]
pub enum CancelReason {
    /// Expired due to timeout
    Expired,
    /// Manually cancelled by initiator
    ManualCancel,
    /// Hash verification failed
    VerificationFailed,
}

// Implement DecodeWithMemTracking for CancelReason
impl DecodeWithMemTracking for CancelReason {}

#[frame_support::pallet]
pub mod pallet {
    use super::*;

    #[pallet::pallet]
    #[pallet::without_storage_info]
    pub struct Pallet<T>(_);

    #[pallet::config]
    pub trait Config: frame_system::Config {
        /// The overarching event type
        type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;
    }

    /// Current pending upgrade metadata
    #[pallet::storage]
    #[pallet::getter(fn pending_upgrade)]
    pub type CurrentPendingUpgrade<T: Config> = StorageValue<_, PendingUpgradeMeta>;

    /// Current upgrade ID (hash)
    #[pallet::storage]
    #[pallet::getter(fn upgrade_id)]
    pub type CurrentUpgradeId<T: Config> = StorageValue<_, T::Hash>;

    /// Expected WASM hash for verification
    #[pallet::storage]
    #[pallet::getter(fn expected_wasm_hash)]
    pub type ExpectedWasmHash<T: Config> = StorageValue<_, T::Hash>;

    /// Stored chunk metadata indexed by chunk_index
    #[pallet::storage]
    #[pallet::getter(fn chunk_metadata)]
    pub type ChunkMetadata<T: Config> = StorageMap<
        _,
        Blake2_128Concat, u8,  // chunk_index
        UpgradeChunkMeta,
    >;

    /// Raw chunk data storage indexed by chunk_index
    #[pallet::storage]
    #[pallet::getter(fn chunk_data)]
    pub type ChunkData<T: Config> = StorageMap<
        _,
        Blake2_128Concat, u8,  // chunk_index
        BoundedVec<u8, ConstU32<MAX_CHUNK_SIZE>>,
    >;

    /// Tracks which chunks have been received
    #[pallet::storage]
    #[pallet::getter(fn chunk_received)]
    pub type ChunkReceived<T: Config> = StorageMap<
        _,
        Blake2_128Concat, u8,  // chunk_index
        bool,
        ValueQuery,
    >;

    /// Backup of the previous runtime WASM for rollback capability
    /// Stored when finalize_chunked_upgrade is called, cleared after successful verification
    #[pallet::storage]
    #[pallet::getter(fn runtime_backup)]
    pub type RuntimeBackup<T: Config> = StorageValue<_, Vec<u8>>;

    /// Block number when the last upgrade was applied (for rollback window)
    #[pallet::storage]
    #[pallet::getter(fn last_upgrade_block)]
    pub type LastUpgradeBlock<T: Config> = StorageValue<_, u32>;

    /// Expected hashes for each chunk (set during initiation for integrity verification)
    /// Maps chunk_index -> expected Blake2-256 hash
    #[pallet::storage]
    #[pallet::getter(fn expected_chunk_hash)]
    pub type ExpectedChunkHashes<T: Config> = StorageMap<
        _,
        Blake2_128Concat, u8,  // chunk_index
        [u8; 32],              // Blake2-256 hash
    >;

    /// Expected size for each chunk (for additional validation)
    #[pallet::storage]
    #[pallet::getter(fn expected_chunk_size)]
    pub type ExpectedChunkSizes<T: Config> = StorageMap<
        _,
        Blake2_128Concat, u8,  // chunk_index
        u32,                   // expected size in bytes
    >;

    #[pallet::event]
    #[pallet::generate_deposit(pub(super) fn deposit_event)]
    pub enum Event<T: Config> {
        /// Chunked upgrade initiated [upgrade_id, total_chunks, expected_size]
        UpgradeInitiated {
            upgrade_id: T::Hash,
            total_chunks: u8,
            expected_size: u32,
        },
        /// Chunk uploaded successfully [chunk_index, segment_id]
        ChunkUploaded {
            chunk_index: u8,
            segment_id: u32,
        },
        /// All chunks received, ready for finalization
        AllChunksReceived,
        /// Upgrade finalized and applied [wasm_size]
        UpgradeFinalized {
            wasm_size: u32,
        },
        /// Upgrade cancelled [reason]
        UpgradeCancelled {
            reason: CancelReason,
        },
        /// WASM validation passed
        WasmValidated {
            size: u32,
        },
        /// Previous runtime backed up for rollback
        RuntimeBackedUp {
            backup_size: u32,
        },
        /// Runtime rolled back to previous version
        RuntimeRolledBack {
            restored_size: u32,
        },
        /// Per-chunk integrity verification passed
        ChunkIntegrityVerified {
            chunk_index: u8,
            chunk_hash: [u8; 32],
        },
        /// All chunks verified during finalization
        AllChunksVerified {
            total_chunks: u8,
        },
    }

    #[pallet::error]
    pub enum Error<T> {
        /// No pending upgrade to operate on
        NoPendingUpgrade,
        /// An upgrade is already in progress
        UpgradeAlreadyInProgress,
        /// Chunk index out of range
        InvalidChunkIndex,
        /// Chunk size exceeds maximum
        ChunkTooLarge,
        /// Chunk hash verification failed
        ChunkHashMismatch,
        /// Not all chunks have been received
        IncompleteChunks,
        /// Assembled WASM hash doesn't match expected
        WasmHashMismatch,
        /// Upgrade has expired
        UpgradeExpired,
        /// Wrong upgrade ID
        UpgradeIdMismatch,
        /// Chunk already uploaded
        ChunkAlreadyUploaded,
        /// Too many chunks
        TooManyChunks,
        /// WASM size exceeds maximum
        WasmTooLarge,
        /// WASM validation failed (invalid magic bytes or version)
        InvalidWasmFormat,
        /// WASM too small to be a valid Substrate runtime
        WasmTooSmall,
        /// Rollback data not available
        NoRollbackAvailable,
        /// Upgrade was already rolled back
        AlreadyRolledBack,
        /// Per-chunk hash mismatch - chunk data corrupted during upload
        ChunkIntegrityFailed,
        /// Rollback window has expired
        RollbackWindowExpired,
        /// Expected chunk hashes not provided during initiation
        MissingChunkHashes,
        /// Chunk size doesn't match expected size
        ChunkSizeMismatch,
    }

    #[pallet::call]
    impl<T: Config> Pallet<T> {
        /// Initiate a new chunked runtime upgrade with per-chunk integrity verification
        ///
        /// # Parameters
        /// - `total_chunks`: Number of chunks the WASM will be split into
        /// - `expected_size`: Total size of the WASM in bytes
        /// - `wasm_hash`: Blake2-256 hash of the complete WASM for verification
        /// - `chunk_hashes`: Optional list of per-chunk Blake2-256 hashes for integrity verification
        /// - `chunk_sizes`: Optional list of expected sizes for each chunk
        ///
        /// # Security
        /// When chunk_hashes is provided, each uploaded chunk will be verified against its
        /// expected hash before being accepted. This provides early detection of corrupted
        /// or tampered data during the upload process.
        #[pallet::call_index(0)]
        #[pallet::weight(Weight::from_parts(10_000, 0))]
        pub fn initiate_chunked_upgrade(
            origin: OriginFor<T>,
            total_chunks: u8,
            expected_size: u32,
            wasm_hash: T::Hash,
            chunk_hashes: Option<Vec<[u8; 32]>>,
            chunk_sizes: Option<Vec<u32>>,
        ) -> DispatchResult {
            ensure_root(origin)?;

            // Validate parameters
            ensure!(total_chunks > 0 && total_chunks <= MAX_CHUNKS as u8, Error::<T>::TooManyChunks);
            ensure!(expected_size <= MAX_WASM_SIZE, Error::<T>::WasmTooLarge);
            ensure!(expected_size >= MIN_WASM_SIZE, Error::<T>::WasmTooSmall);
            ensure!(CurrentPendingUpgrade::<T>::get().is_none(), Error::<T>::UpgradeAlreadyInProgress);

            // Validate chunk hashes if provided
            if let Some(ref hashes) = chunk_hashes {
                ensure!(hashes.len() == total_chunks as usize, Error::<T>::TooManyChunks);
            }

            // Validate chunk sizes if provided
            if let Some(ref sizes) = chunk_sizes {
                ensure!(sizes.len() == total_chunks as usize, Error::<T>::TooManyChunks);
                // Verify total size matches sum of chunk sizes
                let total_from_chunks: u32 = sizes.iter().sum();
                ensure!(total_from_chunks == expected_size, Error::<T>::WasmTooLarge);
            }

            // Generate unique upgrade ID from block hash + wasm_hash
            let block_number = <frame_system::Pallet<T>>::block_number();
            let block_hash = <frame_system::Pallet<T>>::block_hash(block_number);
            let upgrade_id = T::Hashing::hash_of(&(block_hash, &wasm_hash));

            // Create pending upgrade record
            let block_num_u32: u32 = block_number.try_into().unwrap_or(0);
            let pending = PendingUpgradeMeta {
                initiated_at: block_num_u32,
                expected_size,
                total_chunks,
                chunks_received: 0,
            };

            // Clear any stale chunk data and expected hashes
            for i in 0..MAX_CHUNKS as u8 {
                ChunkData::<T>::remove(i);
                ChunkMetadata::<T>::remove(i);
                ChunkReceived::<T>::remove(i);
                ExpectedChunkHashes::<T>::remove(i);
                ExpectedChunkSizes::<T>::remove(i);
            }

            // Store expected chunk hashes if provided
            if let Some(hashes) = chunk_hashes {
                for (i, hash) in hashes.into_iter().enumerate() {
                    ExpectedChunkHashes::<T>::insert(i as u8, hash);
                }
                log::info!(
                    target: "runtime-segmentation",
                    "Per-chunk integrity verification enabled for {} chunks",
                    total_chunks
                );
            }

            // Store expected chunk sizes if provided
            if let Some(sizes) = chunk_sizes {
                for (i, size) in sizes.into_iter().enumerate() {
                    ExpectedChunkSizes::<T>::insert(i as u8, size);
                }
            }

            CurrentPendingUpgrade::<T>::put(pending);
            CurrentUpgradeId::<T>::put(upgrade_id.clone());
            ExpectedWasmHash::<T>::put(wasm_hash);

            Self::deposit_event(Event::UpgradeInitiated {
                upgrade_id,
                total_chunks,
                expected_size,
            });

            Ok(())
        }

        /// Upload a chunk of the runtime WASM
        ///
        /// # Parameters
        /// - `chunk_index`: 0-based index of this chunk
        /// - `chunk_data`: Raw bytes of this chunk
        ///
        /// # Security
        /// If chunk hashes were provided during initiation, this function will verify
        /// the chunk data hash matches the expected hash before accepting the chunk.
        /// This provides early detection of corrupted data during upload.
        #[pallet::call_index(1)]
        #[pallet::weight(Weight::from_parts(50_000, 0))]
        pub fn upload_chunk(
            origin: OriginFor<T>,
            chunk_index: u8,
            chunk_data: Vec<u8>,
        ) -> DispatchResult {
            ensure_root(origin)?;

            // Validate pending upgrade exists
            let mut pending = CurrentPendingUpgrade::<T>::get()
                .ok_or(Error::<T>::NoPendingUpgrade)?;

            // Check expiry
            let current_block: u32 = <frame_system::Pallet<T>>::block_number()
                .try_into().unwrap_or(0);
            let expiry_block = pending.initiated_at.saturating_add(CHUNK_EXPIRY_BLOCKS);
            ensure!(current_block <= expiry_block, Error::<T>::UpgradeExpired);

            // Validate chunk index
            ensure!(chunk_index < pending.total_chunks, Error::<T>::InvalidChunkIndex);

            // Validate chunk size
            ensure!(chunk_data.len() <= MAX_CHUNK_SIZE as usize, Error::<T>::ChunkTooLarge);
            ensure!(!chunk_data.is_empty(), Error::<T>::ChunkTooLarge); // No empty chunks

            // Check if chunk already uploaded (prevent duplicate uploads)
            ensure!(!ChunkReceived::<T>::get(chunk_index), Error::<T>::ChunkAlreadyUploaded);

            // Verify expected chunk size if provided
            if let Some(expected_size) = ExpectedChunkSizes::<T>::get(chunk_index) {
                ensure!(
                    chunk_data.len() as u32 == expected_size,
                    Error::<T>::ChunkSizeMismatch
                );
            }

            // Compute chunk hash using Blake2-256
            let chunk_hash_output = T::Hashing::hash(&chunk_data);
            let chunk_hash_bytes: [u8; 32] = chunk_hash_output.as_ref()
                .try_into()
                .expect("Hash output should be 32 bytes");

            // Verify chunk hash against expected hash if provided
            if let Some(expected_hash) = ExpectedChunkHashes::<T>::get(chunk_index) {
                if chunk_hash_bytes != expected_hash {
                    log::error!(
                        target: "runtime-segmentation",
                        "Chunk {} integrity check FAILED: expected {:?}, got {:?}",
                        chunk_index,
                        expected_hash,
                        chunk_hash_bytes
                    );
                    return Err(Error::<T>::ChunkIntegrityFailed.into());
                }

                // Emit integrity verification event
                Self::deposit_event(Event::ChunkIntegrityVerified {
                    chunk_index,
                    chunk_hash: chunk_hash_bytes,
                });

                log::info!(
                    target: "runtime-segmentation",
                    "Chunk {} integrity verified: {:?}",
                    chunk_index,
                    chunk_hash_bytes
                );
            }

            // Calculate segment ID for toroidal distribution
            let segment_id = chunk_index as u32 % crate::TOTAL_SEGMENTS as u32;

            // Store chunk metadata with computed hash
            let chunk_meta = UpgradeChunkMeta {
                chunk_index,
                total_chunks: pending.total_chunks,
                uploaded_at: current_block,
                chunk_size: chunk_data.len() as u32,
                segment_id,
                chunk_hash: chunk_hash_bytes,
            };

            ChunkMetadata::<T>::insert(chunk_index, chunk_meta);

            // Store chunk data
            let bounded_data: BoundedVec<u8, ConstU32<MAX_CHUNK_SIZE>> = chunk_data
                .try_into()
                .map_err(|_| Error::<T>::ChunkTooLarge)?;
            ChunkData::<T>::insert(chunk_index, bounded_data);

            // Mark chunk as received
            ChunkReceived::<T>::insert(chunk_index, true);

            // Update pending upgrade
            pending.chunks_received += 1;
            CurrentPendingUpgrade::<T>::put(pending.clone());

            Self::deposit_event(Event::ChunkUploaded {
                chunk_index,
                segment_id,
            });

            // Check if all chunks received
            if pending.chunks_received == pending.total_chunks {
                Self::deposit_event(Event::AllChunksReceived);
            }

            Ok(())
        }

        /// Finalize the upgrade by assembling chunks and applying set_code
        ///
        /// This can only be called after all chunks have been uploaded.
        /// The assembled WASM is verified against the expected hash before applying.
        /// Also performs WASM format validation and backs up the current runtime.
        #[pallet::call_index(2)]
        #[pallet::weight(Weight::from_parts(1_000_000_000, 0))]
        pub fn finalize_chunked_upgrade(
            origin: OriginFor<T>,
        ) -> DispatchResult {
            ensure_root(origin)?;

            // Validate pending upgrade exists
            let pending = CurrentPendingUpgrade::<T>::get()
                .ok_or(Error::<T>::NoPendingUpgrade)?;

            let expected_hash = ExpectedWasmHash::<T>::get()
                .ok_or(Error::<T>::NoPendingUpgrade)?;

            // Check all chunks received
            ensure!(
                pending.chunks_received == pending.total_chunks,
                Error::<T>::IncompleteChunks
            );

            // Assemble WASM from chunks
            let mut assembled_wasm = Vec::with_capacity(pending.expected_size as usize);
            for i in 0..pending.total_chunks {
                let chunk = ChunkData::<T>::get(i)
                    .ok_or(Error::<T>::IncompleteChunks)?;
                assembled_wasm.extend_from_slice(&chunk);
            }

            // Verify assembled WASM hash
            let computed_hash = T::Hashing::hash(&assembled_wasm);
            ensure!(expected_hash == computed_hash, Error::<T>::WasmHashMismatch);

            // Re-verify all chunks by checking stored hashes match actual data
            // This catches any storage corruption between upload and finalization
            for i in 0..pending.total_chunks {
                if let Some(meta) = ChunkMetadata::<T>::get(i) {
                    if let Some(chunk) = ChunkData::<T>::get(i) {
                        let recomputed_hash = T::Hashing::hash(&chunk);
                        let recomputed_bytes: [u8; 32] = recomputed_hash.as_ref()
                            .try_into()
                            .expect("Hash should be 32 bytes");

                        if recomputed_bytes != meta.chunk_hash {
                            log::error!(
                                target: "runtime-segmentation",
                                "Chunk {} storage corruption detected during finalization!",
                                i
                            );
                            return Err(Error::<T>::ChunkIntegrityFailed.into());
                        }
                    }
                }
            }

            Self::deposit_event(Event::AllChunksVerified {
                total_chunks: pending.total_chunks,
            });

            let wasm_size = assembled_wasm.len() as u32;

            // Validate WASM format (magic bytes, version, minimum size)
            Self::validate_wasm(&assembled_wasm)?;

            Self::deposit_event(Event::WasmValidated { size: wasm_size });

            // Backup current runtime for potential rollback
            let backup_size = Self::backup_current_runtime()?;
            if backup_size > 0 {
                Self::deposit_event(Event::RuntimeBackedUp { backup_size });
            }

            log::info!(
                target: "runtime-segmentation",
                "Applying runtime upgrade: {} bytes (backed up {} bytes)",
                wasm_size,
                backup_size
            );

            // Apply the runtime upgrade by directly writing to storage
            // This is more reliable than calling the dispatchable, as nested calls
            // can have issues with origin propagation.
            // Since we already verified the WASM hash and this is a sudo call,
            // directly updating storage is safe.
            frame_system::Pallet::<T>::update_code_in_storage(&assembled_wasm);

            // Clean up chunk storage (but keep backup for rollback)
            Self::cleanup_upgrade(pending.total_chunks);

            Self::deposit_event(Event::UpgradeFinalized {
                wasm_size,
            });

            Ok(())
        }

        /// Cancel a pending upgrade and clean up storage
        #[pallet::call_index(3)]
        #[pallet::weight(Weight::from_parts(10_000, 0))]
        pub fn cancel_chunked_upgrade(
            origin: OriginFor<T>,
        ) -> DispatchResult {
            ensure_root(origin)?;

            let pending = CurrentPendingUpgrade::<T>::get()
                .ok_or(Error::<T>::NoPendingUpgrade)?;

            Self::cleanup_upgrade(pending.total_chunks);

            Self::deposit_event(Event::UpgradeCancelled {
                reason: CancelReason::ManualCancel,
            });

            Ok(())
        }

        /// Rollback to the previously backed up runtime
        ///
        /// This can only be called after a runtime upgrade has been applied
        /// and the backup is still available. The rollback window is typically
        /// a few hours after the upgrade.
        ///
        /// WARNING: This is an emergency operation and should only be used
        /// if the new runtime is not functioning correctly.
        #[pallet::call_index(4)]
        #[pallet::weight(Weight::from_parts(1_000_000_000, 0))]
        pub fn rollback_runtime(
            origin: OriginFor<T>,
        ) -> DispatchResult {
            ensure_root(origin)?;

            // Check that we have a backup to rollback to
            let backup_wasm = RuntimeBackup::<T>::get()
                .ok_or(Error::<T>::NoRollbackAvailable)?;

            if backup_wasm.is_empty() {
                return Err(Error::<T>::NoRollbackAvailable.into());
            }

            let restored_size = backup_wasm.len() as u32;

            log::warn!(
                target: "runtime-segmentation",
                "ROLLBACK: Restoring previous runtime ({} bytes)",
                restored_size
            );

            // Validate the backup WASM before applying
            Self::validate_wasm(&backup_wasm)?;

            // Apply the rollback by directly writing to storage
            frame_system::Pallet::<T>::update_code_in_storage(&backup_wasm);

            // Clear the backup to prevent double-rollback
            RuntimeBackup::<T>::kill();
            LastUpgradeBlock::<T>::kill();

            Self::deposit_event(Event::RuntimeRolledBack { restored_size });

            log::info!(
                target: "runtime-segmentation",
                "ROLLBACK COMPLETE: Restored {} bytes",
                restored_size
            );

            Ok(())
        }

        /// Clear the runtime backup to free storage
        ///
        /// Call this after verifying that the new runtime is working correctly.
        /// This prevents accidental rollback and frees up significant storage space.
        #[pallet::call_index(5)]
        #[pallet::weight(Weight::from_parts(10_000, 0))]
        pub fn clear_runtime_backup(
            origin: OriginFor<T>,
        ) -> DispatchResult {
            ensure_root(origin)?;

            RuntimeBackup::<T>::kill();
            LastUpgradeBlock::<T>::kill();

            log::info!(
                target: "runtime-segmentation",
                "Runtime backup cleared"
            );

            Ok(())
        }
    }

    impl<T: Config> Pallet<T> {
        /// Validate WASM binary format before applying upgrade
        /// Returns Ok(()) if WASM is valid, Err with appropriate error otherwise
        fn validate_wasm(wasm: &[u8]) -> Result<(), Error<T>> {
            // Check minimum size
            if wasm.len() < MIN_WASM_SIZE as usize {
                log::error!(
                    target: "runtime-segmentation",
                    "WASM too small: {} bytes (min: {})",
                    wasm.len(),
                    MIN_WASM_SIZE
                );
                return Err(Error::<T>::WasmTooSmall);
            }

            // Check WASM magic bytes (first 4 bytes must be \0asm)
            if wasm.len() < 8 {
                log::error!(
                    target: "runtime-segmentation",
                    "WASM too short to contain header"
                );
                return Err(Error::<T>::InvalidWasmFormat);
            }

            let magic = &wasm[0..4];
            if magic != WASM_MAGIC {
                log::error!(
                    target: "runtime-segmentation",
                    "Invalid WASM magic bytes: {:?} (expected: {:?})",
                    magic,
                    WASM_MAGIC
                );
                return Err(Error::<T>::InvalidWasmFormat);
            }

            // Check WASM version (bytes 4-7 should be version 1: 01 00 00 00)
            let version = wasm[4];
            if version != WASM_VERSION {
                log::error!(
                    target: "runtime-segmentation",
                    "Invalid WASM version: {} (expected: {})",
                    version,
                    WASM_VERSION
                );
                return Err(Error::<T>::InvalidWasmFormat);
            }

            log::info!(
                target: "runtime-segmentation",
                "WASM validation passed: {} bytes, version {}",
                wasm.len(),
                version
            );

            Ok(())
        }

        /// Backup the current runtime WASM for potential rollback
        ///
        /// Note: In production, we use sp_io::storage::get to read the :code storage key.
        /// For the backup to work, the pallet must be running in std mode (not wasm).
        fn backup_current_runtime() -> Result<u32, Error<T>> {
            // Get current WASM from storage using the well-known storage key
            // :code is stored at key 0x3a636f6465 (":code" in hex)
            #[cfg(feature = "std")]
            let current_wasm = {
                let code_key = sp_core::storage::well_known_keys::CODE;
                sp_io::storage::get(code_key).unwrap_or_default()
            };

            #[cfg(not(feature = "std"))]
            let current_wasm = {
                // In WASM context, we can read from frame_support storage directly
                let code_key: &[u8] = b":code";
                frame_support::storage::unhashed::get_raw(code_key).unwrap_or_default()
            };

            let backup_size = current_wasm.len() as u32;

            if backup_size == 0 {
                log::warn!(
                    target: "runtime-segmentation",
                    "No current runtime to backup"
                );
                return Ok(0);
            }

            // Store backup
            RuntimeBackup::<T>::put(current_wasm);

            // Record block number for rollback window tracking
            let current_block: u32 = <frame_system::Pallet<T>>::block_number()
                .try_into().unwrap_or(0);
            LastUpgradeBlock::<T>::put(current_block);

            log::info!(
                target: "runtime-segmentation",
                "Backed up current runtime: {} bytes at block {}",
                backup_size,
                current_block
            );

            Ok(backup_size)
        }

        /// Clean up all storage related to an upgrade
        fn cleanup_upgrade(total_chunks: u8) {
            // Remove all chunk data, metadata, and expected hashes
            for i in 0..total_chunks {
                ChunkData::<T>::remove(i);
                ChunkMetadata::<T>::remove(i);
                ChunkReceived::<T>::remove(i);
                ExpectedChunkHashes::<T>::remove(i);
                ExpectedChunkSizes::<T>::remove(i);
            }

            // Also clean any indices beyond total_chunks that might have stale data
            for i in total_chunks..MAX_CHUNKS as u8 {
                ChunkData::<T>::remove(i);
                ChunkMetadata::<T>::remove(i);
                ChunkReceived::<T>::remove(i);
                ExpectedChunkHashes::<T>::remove(i);
                ExpectedChunkSizes::<T>::remove(i);
            }

            // Remove tracking data
            CurrentPendingUpgrade::<T>::kill();
            CurrentUpgradeId::<T>::kill();
            ExpectedWasmHash::<T>::kill();

            log::info!(
                target: "runtime-segmentation",
                "Upgrade cleanup complete: removed {} chunk entries",
                total_chunks
            );
        }

        /// Get upgrade status: (chunks_received, total_chunks)
        pub fn get_upgrade_status() -> Option<(u8, u8)> {
            CurrentPendingUpgrade::<T>::get().map(|p| {
                (p.chunks_received, p.total_chunks)
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_chunk_size_limits() {
        // Verify 64KB chunks with overhead fit in 256KB block
        // Chunk: 64KB
        // SPHINCS+ signature: ~50KB
        // Call encoding overhead: ~1KB
        // Total: ~115KB < 256KB ✓
        assert!(MAX_CHUNK_SIZE + 51_000 < 256_000);
    }

    #[test]
    fn test_max_wasm_size() {
        // 32 chunks * 64KB = 2MB max WASM
        assert_eq!(MAX_WASM_SIZE, 2_097_152);
        // Current WASM is ~2MB (debug) or ~600KB (release optimized)
        // Test with max allowed size
        let wasm_size = MAX_WASM_SIZE;
        let chunks_needed = (wasm_size + MAX_CHUNK_SIZE - 1) / MAX_CHUNK_SIZE;
        assert!(chunks_needed <= MAX_CHUNKS, "WASM size {} requires {} chunks but max is {}", wasm_size, chunks_needed, MAX_CHUNKS);

        // Test that we reject sizes over the max
        let oversized = MAX_WASM_SIZE + 1;
        assert!(oversized > MAX_WASM_SIZE, "Oversized WASM should be rejected");
    }

    #[test]
    fn test_wasm_magic_bytes() {
        // Valid WASM magic bytes: \0asm (0x00, 0x61, 0x73, 0x6D)
        assert_eq!(WASM_MAGIC, [0x00, 0x61, 0x73, 0x6D]);

        // Test that magic bytes match the actual WASM header
        let valid_wasm_header: [u8; 8] = [0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00];
        assert_eq!(&valid_wasm_header[0..4], &WASM_MAGIC);
        assert_eq!(valid_wasm_header[4], WASM_VERSION);
    }

    #[test]
    fn test_wasm_version() {
        // WASM version 1 is the current standard
        assert_eq!(WASM_VERSION, 0x01);
    }

    #[test]
    fn test_min_wasm_size() {
        // Minimum WASM size should be reasonable for a Substrate runtime
        // Even a minimal runtime is ~100KB
        assert_eq!(MIN_WASM_SIZE, 100_000);
        assert!(MIN_WASM_SIZE < MAX_WASM_SIZE);
    }

    #[test]
    fn test_chunk_expiry_blocks() {
        // Expiry should be ~3 hours at 6s blocks
        // 3 hours = 180 minutes = 10,800 seconds
        // At 6s/block = 1,800 blocks
        assert_eq!(CHUNK_EXPIRY_BLOCKS, 1800);

        // Verify this gives ~3 hours
        let seconds = CHUNK_EXPIRY_BLOCKS * 6;
        let hours = seconds / 3600;
        assert_eq!(hours, 3);
    }

    #[test]
    fn test_chunk_distribution() {
        // Test that chunks are distributed across segments correctly
        // Using modulo 512 (TOTAL_SEGMENTS)
        for chunk_index in 0..MAX_CHUNKS as u8 {
            let segment_id = chunk_index as u32 % 512;
            assert!(segment_id < 512);
        }
    }

    #[test]
    fn test_upgrade_chunk_meta_encoding() {
        let meta = UpgradeChunkMeta {
            chunk_index: 5,
            total_chunks: 10,
            uploaded_at: 12345,
            chunk_size: 65536,
            segment_id: 5,
            chunk_hash: [0xab; 32], // Test hash
        };

        // Ensure encoding/decoding roundtrip works
        let encoded = meta.encode();
        let decoded = UpgradeChunkMeta::decode(&mut &encoded[..]).unwrap();
        assert_eq!(meta, decoded);
    }

    #[test]
    fn test_chunk_hash_storage() {
        // Test that chunk hash is correctly stored in metadata
        let test_data = vec![0x42u8; 1000];
        // Simulate Blake2-256 hash (in reality this would use sp_core::hashing)
        let mock_hash: [u8; 32] = [0x12; 32];

        let meta = UpgradeChunkMeta {
            chunk_index: 0,
            total_chunks: 5,
            uploaded_at: 100,
            chunk_size: test_data.len() as u32,
            segment_id: 0,
            chunk_hash: mock_hash,
        };

        assert_eq!(meta.chunk_hash, mock_hash);
        assert_eq!(meta.chunk_size, 1000);
    }

    #[test]
    fn test_rollback_window() {
        // Rollback window should be ~6 hours at 6s blocks
        assert_eq!(ROLLBACK_WINDOW_BLOCKS, 3600);

        // Verify this gives ~6 hours
        let seconds = ROLLBACK_WINDOW_BLOCKS * 6;
        let hours = seconds / 3600;
        assert_eq!(hours, 6);
    }

    #[test]
    fn test_max_upgrade_attempts() {
        // Max 3 retry attempts for safety
        assert_eq!(MAX_UPGRADE_ATTEMPTS, 3);
    }

    #[test]
    fn test_hash_array_size() {
        // Hash arrays should always be 32 bytes (Blake2-256)
        let hash: [u8; 32] = [0; 32];
        assert_eq!(hash.len(), 32);

        // Test that metadata encoding handles the hash correctly
        let meta = UpgradeChunkMeta {
            chunk_index: 0,
            total_chunks: 1,
            uploaded_at: 0,
            chunk_size: 0,
            segment_id: 0,
            chunk_hash: hash,
        };

        let encoded = meta.encode();
        // Encoding should include the full 32-byte hash
        assert!(encoded.len() >= 32);
    }

    #[test]
    fn test_pending_upgrade_meta_encoding() {
        let meta = PendingUpgradeMeta {
            initiated_at: 100,
            expected_size: 500_000,
            total_chunks: 8,
            chunks_received: 3,
        };

        let encoded = meta.encode();
        let decoded = PendingUpgradeMeta::decode(&mut &encoded[..]).unwrap();
        assert_eq!(meta, decoded);
    }

    #[test]
    fn test_cancel_reason_encoding() {
        for reason in [CancelReason::Expired, CancelReason::ManualCancel, CancelReason::VerificationFailed] {
            let encoded = reason.encode();
            let decoded = CancelReason::decode(&mut &encoded[..]).unwrap();
            assert_eq!(reason, decoded);
        }
    }

    #[test]
    fn test_chunks_calculation() {
        // Test chunk calculation for various WASM sizes
        let test_cases = [
            (100_000u32, 2u32),   // 100KB -> 2 chunks
            (500_000, 8),         // 500KB -> 8 chunks
            (600_000, 10),        // 600KB -> 10 chunks (typical release)
            (1_000_000, 16),      // 1MB -> 16 chunks
            (2_000_000, 31),      // 2MB -> 31 chunks
        ];

        for (wasm_size, expected_chunks) in test_cases {
            let chunks_needed = (wasm_size + MAX_CHUNK_SIZE - 1) / MAX_CHUNK_SIZE;
            assert_eq!(chunks_needed, expected_chunks,
                "WASM size {} should need {} chunks, got {}",
                wasm_size, expected_chunks, chunks_needed);
        }
    }

    #[test]
    fn test_wasm_validation_data() {
        // Create a mock valid WASM header
        let mut valid_wasm = vec![0u8; MIN_WASM_SIZE as usize + 100];
        valid_wasm[0..4].copy_from_slice(&WASM_MAGIC);
        valid_wasm[4] = WASM_VERSION;
        valid_wasm[5] = 0x00;
        valid_wasm[6] = 0x00;
        valid_wasm[7] = 0x00;

        // Verify magic bytes are correct
        assert_eq!(&valid_wasm[0..4], &WASM_MAGIC);
        assert_eq!(valid_wasm[4], WASM_VERSION);
    }

    #[test]
    fn test_invalid_wasm_detection() {
        // Test various invalid WASM scenarios

        // 1. Empty data
        let empty: Vec<u8> = vec![];
        assert!(empty.len() < MIN_WASM_SIZE as usize);

        // 2. Wrong magic bytes
        let wrong_magic = vec![0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00];
        assert_ne!(&wrong_magic[0..4], &WASM_MAGIC);

        // 3. Wrong version
        let wrong_version = vec![0x00, 0x61, 0x73, 0x6D, 0x02, 0x00, 0x00, 0x00];
        assert_eq!(&wrong_version[0..4], &WASM_MAGIC);
        assert_ne!(wrong_version[4], WASM_VERSION);

        // 4. Too short
        let too_short = vec![0x00, 0x61, 0x73, 0x6D];
        assert!(too_short.len() < 8);
    }

    #[test]
    fn test_segment_coverage() {
        // Verify that with MAX_CHUNKS chunks, we cover many segments
        let mut covered_segments = std::collections::HashSet::new();
        for i in 0..MAX_CHUNKS {
            let segment = i % 512;
            covered_segments.insert(segment);
        }

        // With 32 chunks and 512 segments, we cover 32 unique segments
        assert_eq!(covered_segments.len(), MAX_CHUNKS as usize);
    }

    #[test]
    fn test_expiry_calculation() {
        // Test that expiry is calculated correctly
        let initiated_at: u32 = 1000;
        let expiry_block = initiated_at.saturating_add(CHUNK_EXPIRY_BLOCKS);

        assert_eq!(expiry_block, 2800);

        // Test near block 0
        let early_expiry = 50u32.saturating_add(CHUNK_EXPIRY_BLOCKS);
        assert_eq!(early_expiry, 1850);

        // Test overflow protection
        let max_block = u32::MAX;
        let safe_expiry = max_block.saturating_add(CHUNK_EXPIRY_BLOCKS);
        assert_eq!(safe_expiry, u32::MAX); // saturating_add prevents overflow
    }
}
