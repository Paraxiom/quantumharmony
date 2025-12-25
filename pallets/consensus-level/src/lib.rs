//! # Consensus Level Pallet
//!
//! Tracks the current consensus level for the QuantumHarmony network.
//! Provides adaptive consensus that upgrades automatically as hardware becomes available.
//!
//! ## Levels
//!
//! | Level | Name | Requirements |
//! |-------|------|--------------|
//! | 1 | Classical BFT | Base Substrate |
//! | 2 | Post-Quantum BFT | SPHINCS+ keys loaded |
//! | 3 | Coherence-Weighted | Level 2 + coherence scoring |
//! | 4 | QRNG-Enhanced | Level 3 + hardware QRNG |
//! | 5 | Full PoC | Level 4 + QKD links |

#![cfg_attr(not(feature = "std"), no_std)]

pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {
    use frame_support::pallet_prelude::*;
    use frame_system::pallet_prelude::*;
    use scale_codec::{Decode, DecodeWithMemTracking, Encode, MaxEncodedLen};
    use scale_info::TypeInfo;

    #[pallet::pallet]
    pub struct Pallet<T>(_);

    #[pallet::config]
    pub trait Config: frame_system::Config {
        type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;
    }

    /// Consensus level enumeration
    #[derive(
        Clone,
        Copy,
        Encode,
        Decode,
        TypeInfo,
        MaxEncodedLen,
        PartialEq,
        Eq,
        Debug,
        Default,
        serde::Serialize,
        serde::Deserialize,
    )]
    pub enum ConsensusLevel {
        /// Level 1: Classical BFT (base Substrate)
        ClassicalBFT = 1,
        /// Level 2: Post-Quantum BFT with SPHINCS+ signatures
        #[default]
        PostQuantumBFT = 2,
        /// Level 3: Coherence-weighted validator selection
        CoherenceWeighted = 3,
        /// Level 4: QRNG-enhanced randomness
        QRNGEnhanced = 4,
        /// Level 5: Full Proof-of-Coherence with QKD
        FullProofOfCoherence = 5,
    }

    // Implement DecodeWithMemTracking for ConsensusLevel (required for events)
    impl DecodeWithMemTracking for ConsensusLevel {}

    impl ConsensusLevel {
        /// Get display name for the current level
        pub fn display_name(&self) -> &'static str {
            match self {
                ConsensusLevel::ClassicalBFT => "BFT-Classical",
                ConsensusLevel::PostQuantumBFT => "PQ-BFT",
                ConsensusLevel::CoherenceWeighted => "PQ-BFT + Coherence",
                ConsensusLevel::QRNGEnhanced => "PQ-BFT + QRNG",
                ConsensusLevel::FullProofOfCoherence => "Proof-of-Coherence",
            }
        }

        /// Get numeric level
        pub fn level(&self) -> u8 {
            *self as u8
        }
    }

    /// Current consensus level
    #[pallet::storage]
    #[pallet::getter(fn current_level)]
    pub type CurrentLevel<T> = StorageValue<_, ConsensusLevel, ValueQuery>;

    /// Whether QRNG hardware is available
    #[pallet::storage]
    #[pallet::getter(fn qrng_available)]
    pub type QRNGAvailable<T> = StorageValue<_, bool, ValueQuery>;

    /// Number of active QKD links
    #[pallet::storage]
    #[pallet::getter(fn qkd_links_active)]
    pub type QKDLinksActive<T> = StorageValue<_, u32, ValueQuery>;

    /// Number of SPHINCS+ keys registered
    #[pallet::storage]
    #[pallet::getter(fn sphincs_keys_count)]
    pub type SPHINCSKeysCount<T> = StorageValue<_, u32, ValueQuery>;

    /// Coherence scoring enabled
    #[pallet::storage]
    #[pallet::getter(fn coherence_enabled)]
    pub type CoherenceEnabled<T> = StorageValue<_, bool, ValueQuery>;

    #[pallet::event]
    #[pallet::generate_deposit(pub(super) fn deposit_event)]
    pub enum Event<T: Config> {
        /// Consensus level changed
        LevelChanged {
            old_level: ConsensusLevel,
            new_level: ConsensusLevel,
        },
        /// QRNG hardware detected
        QRNGDetected,
        /// QRNG hardware removed
        QRNGRemoved,
        /// QKD link established
        QKDLinkEstablished {
            peer_count: u32,
        },
        /// QKD link lost
        QKDLinkLost {
            remaining: u32,
        },
        /// Coherence scoring enabled
        CoherenceEnabled,
    }

    #[pallet::error]
    pub enum Error<T> {
        /// Cannot downgrade consensus level
        CannotDowngrade,
        /// Invalid level transition
        InvalidTransition,
    }

    #[pallet::genesis_config]
    #[derive(frame_support::DefaultNoBound)]
    pub struct GenesisConfig<T: Config> {
        /// Initial consensus level
        pub initial_level: ConsensusLevel,
        /// Whether coherence is enabled at genesis
        pub coherence_enabled: bool,
        #[serde(skip)]
        pub _phantom: core::marker::PhantomData<T>,
    }

    #[pallet::genesis_build]
    impl<T: Config> BuildGenesisConfig for GenesisConfig<T> {
        fn build(&self) {
            CurrentLevel::<T>::put(self.initial_level);
            CoherenceEnabled::<T>::put(self.coherence_enabled);
        }
    }

    #[pallet::hooks]
    impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
        fn on_initialize(_n: BlockNumberFor<T>) -> Weight {
            // Auto-evaluate and upgrade consensus level each block
            Self::evaluate_and_upgrade();
            Weight::from_parts(10_000, 0)
        }
    }

    #[pallet::call]
    impl<T: Config> Pallet<T> {
        /// Register QRNG hardware availability
        ///
        /// Called by off-chain worker when QRNG hardware is detected
        #[pallet::call_index(0)]
        #[pallet::weight(Weight::from_parts(10_000, 0))]
        pub fn register_qrng(origin: OriginFor<T>, available: bool) -> DispatchResult {
            ensure_root(origin)?;

            let was_available = QRNGAvailable::<T>::get();
            QRNGAvailable::<T>::put(available);

            if available && !was_available {
                Self::deposit_event(Event::QRNGDetected);
            } else if !available && was_available {
                Self::deposit_event(Event::QRNGRemoved);
            }

            Ok(())
        }

        /// Register QKD link status
        ///
        /// Called by quantum-p2p layer when QKD sessions change
        #[pallet::call_index(1)]
        #[pallet::weight(Weight::from_parts(10_000, 0))]
        pub fn register_qkd_links(origin: OriginFor<T>, active_links: u32) -> DispatchResult {
            ensure_root(origin)?;

            let previous = QKDLinksActive::<T>::get();
            QKDLinksActive::<T>::put(active_links);

            if active_links > previous {
                Self::deposit_event(Event::QKDLinkEstablished { peer_count: active_links });
            } else if active_links < previous {
                Self::deposit_event(Event::QKDLinkLost { remaining: active_links });
            }

            Ok(())
        }

        /// Enable coherence scoring
        ///
        /// Can be called via governance to enable coherence-weighted selection
        #[pallet::call_index(2)]
        #[pallet::weight(Weight::from_parts(10_000, 0))]
        pub fn enable_coherence(origin: OriginFor<T>) -> DispatchResult {
            ensure_root(origin)?;

            CoherenceEnabled::<T>::put(true);
            Self::deposit_event(Event::CoherenceEnabled);

            Ok(())
        }

        /// Register SPHINCS+ key count
        ///
        /// Called when validators register their keys
        #[pallet::call_index(3)]
        #[pallet::weight(Weight::from_parts(10_000, 0))]
        pub fn register_sphincs_keys(origin: OriginFor<T>, count: u32) -> DispatchResult {
            ensure_root(origin)?;
            SPHINCSKeysCount::<T>::put(count);
            Ok(())
        }
    }

    impl<T: Config> Pallet<T> {
        /// Evaluate current capabilities and upgrade level if possible
        fn evaluate_and_upgrade() {
            let current = Self::current_level();
            let qrng = Self::qrng_available();
            let qkd_links = Self::qkd_links_active();
            let coherence = Self::coherence_enabled();
            let sphincs_keys = Self::sphincs_keys_count();

            // Determine the highest achievable level based on current capabilities
            let new_level = if qrng && qkd_links >= 2 {
                ConsensusLevel::FullProofOfCoherence
            } else if qrng {
                ConsensusLevel::QRNGEnhanced
            } else if coherence {
                ConsensusLevel::CoherenceWeighted
            } else if sphincs_keys > 0 {
                ConsensusLevel::PostQuantumBFT
            } else {
                ConsensusLevel::ClassicalBFT
            };

            // Only upgrade, never downgrade automatically
            if new_level.level() > current.level() {
                CurrentLevel::<T>::put(new_level);
                Self::deposit_event(Event::LevelChanged {
                    old_level: current,
                    new_level,
                });
            }
        }

        /// Get the display string for current consensus level
        ///
        /// This is called by the node's finality logging
        pub fn get_consensus_display() -> &'static str {
            Self::current_level().display_name()
        }

        /// Get numeric level code for current consensus
        pub fn get_level_code() -> u8 {
            Self::current_level().level()
        }

        /// Get requirements for next level upgrade
        pub fn get_next_upgrade_requirements() -> Option<&'static str> {
            match Self::current_level() {
                ConsensusLevel::ClassicalBFT => Some("Register SPHINCS+ validator keys"),
                ConsensusLevel::PostQuantumBFT => Some("Enable coherence scoring via governance"),
                ConsensusLevel::CoherenceWeighted => Some("Connect QRNG hardware"),
                ConsensusLevel::QRNGEnhanced => Some("Establish 2+ QKD links with peers"),
                ConsensusLevel::FullProofOfCoherence => None, // Already at max
            }
        }
    }
}

/// Consensus status for RPC responses (std only)
#[cfg(feature = "std")]
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct ConsensusStatus {
    pub level: u8,
    pub level_name: String,
    pub qrng_available: bool,
    pub qkd_links_active: u32,
    pub coherence_enabled: bool,
    pub sphincs_keys_count: u32,
    pub next_upgrade: Option<String>,
}

#[cfg(feature = "std")]
impl<T: pallet::Config> pallet::Pallet<T> {
    /// Get full status for RPC
    pub fn get_status() -> ConsensusStatus {
        let level = Self::current_level();
        ConsensusStatus {
            level: level.level(),
            level_name: level.display_name().to_string(),
            qrng_available: Self::qrng_available(),
            qkd_links_active: Self::qkd_links_active(),
            coherence_enabled: Self::coherence_enabled(),
            sphincs_keys_count: Self::sphincs_keys_count(),
            next_upgrade: Self::get_next_upgrade_requirements().map(|s| s.to_string()),
        }
    }
}
