#![cfg_attr(not(feature = "std"), no_std)]

pub use pallet::*;

pub mod runtime_api;

#[frame_support::pallet]
pub mod pallet {
    use frame_support::pallet_prelude::*;
    use frame_system::pallet_prelude::*;
    use sp_std::vec::Vec;

    /// Maximum length of a quest ID (e.g. "G001" = 4 bytes, max 8)
    pub type QuestId<T> = BoundedVec<u8, <T as Config>::MaxQuestIdLen>;

    #[pallet::pallet]
    pub struct Pallet<T>(_);

    #[pallet::config]
    pub trait Config: frame_system::Config {
        type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

        /// Origin that can admin-complete quests and override scores
        type AdminOrigin: EnsureOrigin<Self::RuntimeOrigin>;

        /// Maximum number of quests trackable per account
        #[pallet::constant]
        type MaxQuests: Get<u32>;

        /// Maximum length of a quest ID string
        #[pallet::constant]
        type MaxQuestIdLen: Get<u32>;
    }

    // ── Storage ──────────────────────────────────────────────────────

    /// When each quest was completed by an account: (AccountId, QuestId) -> BlockNumber
    #[pallet::storage]
    #[pallet::getter(fn quest_completed)]
    pub type QuestCompleted<T: Config> = StorageDoubleMap<
        _,
        Blake2_128Concat, T::AccountId,
        Blake2_128Concat, QuestId<T>,
        BlockNumberFor<T>,
        OptionQuery,
    >;

    /// Total devonomics score per account
    #[pallet::storage]
    #[pallet::getter(fn dev_score)]
    pub type DevScore<T: Config> = StorageMap<
        _,
        Blake2_128Concat, T::AccountId,
        u32,
        ValueQuery,
    >;

    /// Highest tier unlocked per account (1-4, 0 = none)
    #[pallet::storage]
    #[pallet::getter(fn tier_unlocked)]
    pub type TierUnlocked<T: Config> = StorageMap<
        _,
        Blake2_128Concat, T::AccountId,
        u8,
        ValueQuery,
    >;

    // ── Events ───────────────────────────────────────────────────────

    #[pallet::event]
    #[pallet::generate_deposit(pub(super) fn deposit_event)]
    pub enum Event<T: Config> {
        /// A quest was completed
        QuestCompleted {
            account: T::AccountId,
            quest_id: Vec<u8>,
            points: u32,
            block: BlockNumberFor<T>,
        },
        /// A new tier was unlocked
        TierUnlocked {
            account: T::AccountId,
            tier: u8,
        },
        /// Score was updated (admin override or quest completion)
        ScoreUpdated {
            account: T::AccountId,
            new_score: u32,
        },
    }

    // ── Errors ───────────────────────────────────────────────────────

    #[pallet::error]
    pub enum Error<T> {
        /// This quest has already been completed by this account
        QuestAlreadyCompleted,
        /// The quest ID is not recognized
        UnknownQuest,
        /// The quest belongs to a tier the user hasn't unlocked yet
        TierLocked,
    }

    // ── Quest Points Table ───────────────────────────────────────────

    impl<T: Config> Pallet<T> {
        /// Returns (points, required_tier) for a known quest, or None if unknown.
        /// required_tier: the tier that must already be unlocked (0 = no prerequisite).
        fn quest_info(quest_id: &[u8]) -> Option<(u32, u8)> {
            match quest_id {
                // Tier 1 - Genesis quests (G): 50 pts each, no prereq
                b"G001" => Some((50, 0)),
                b"G002" => Some((50, 0)),
                b"G003" => Some((50, 0)),
                b"G004" => Some((50, 0)),
                b"G005" => Some((50, 0)),

                // Tier 2 - Validator quests (V): variable pts, requires tier 1
                b"V001" => Some((100, 1)),
                b"V002" => Some((200, 1)),
                b"V003" => Some((150, 1)),
                b"V004" => Some((100, 1)),

                // Tier 3 - Forum/community quests (F): variable pts, requires tier 2
                b"F001" => Some((50, 2)),
                b"F002" => Some((75, 2)),
                b"F003" => Some((75, 2)),
                b"F004" => Some((50, 2)),

                // Tier 4 - Research quests (R): requires tier 3
                b"R001" => Some((200, 3)),

                _ => None,
            }
        }

        /// Returns the tier a quest belongs to (for tier-unlock checks).
        fn quest_tier(quest_id: &[u8]) -> Option<u8> {
            match quest_id {
                b"G001" | b"G002" | b"G003" | b"G004" | b"G005" => Some(1),
                b"V001" | b"V002" | b"V003" | b"V004" => Some(2),
                b"F001" | b"F002" | b"F003" | b"F004" => Some(3),
                b"R001" => Some(4),
                _ => None,
            }
        }

        /// All quest IDs belonging to a given tier.
        fn quests_in_tier(tier: u8) -> &'static [&'static [u8]] {
            match tier {
                1 => &[b"G001", b"G002", b"G003", b"G004", b"G005"],
                2 => &[b"V001", b"V002", b"V003", b"V004"],
                3 => &[b"F001", b"F002", b"F003", b"F004"],
                4 => &[b"R001"],
                _ => &[],
            }
        }

        /// Check if all quests in a tier are completed by the account.
        fn all_quests_completed_in_tier(account: &T::AccountId, tier: u8) -> bool {
            let quests = Self::quests_in_tier(tier);
            for quest_bytes in quests {
                if let Ok(bounded) = BoundedVec::<u8, T::MaxQuestIdLen>::try_from(quest_bytes.to_vec()) {
                    if QuestCompleted::<T>::get(account, &bounded).is_none() {
                        return false;
                    }
                } else {
                    return false;
                }
            }
            !quests.is_empty()
        }

        /// Internal: complete a quest for an account, awarding points and checking tier unlocks.
        fn do_complete_quest(
            account: &T::AccountId,
            quest_id_raw: Vec<u8>,
        ) -> DispatchResult {
            let bounded_id: QuestId<T> = quest_id_raw.clone()
                .try_into()
                .map_err(|_| Error::<T>::UnknownQuest)?;

            // Validate quest exists
            let (points, required_tier) = Self::quest_info(&quest_id_raw)
                .ok_or(Error::<T>::UnknownQuest)?;

            // Check not already completed
            ensure!(
                QuestCompleted::<T>::get(account, &bounded_id).is_none(),
                Error::<T>::QuestAlreadyCompleted
            );

            // Check tier prerequisite
            let current_tier = TierUnlocked::<T>::get(account);
            ensure!(current_tier >= required_tier, Error::<T>::TierLocked);

            // Record completion
            let block = <frame_system::Pallet<T>>::block_number();
            QuestCompleted::<T>::insert(account, &bounded_id, block);

            // Award points
            let old_score = DevScore::<T>::get(account);
            let new_score = old_score.saturating_add(points);
            DevScore::<T>::insert(account, new_score);

            Self::deposit_event(Event::QuestCompleted {
                account: account.clone(),
                quest_id: quest_id_raw.clone(),
                points,
                block,
            });

            Self::deposit_event(Event::ScoreUpdated {
                account: account.clone(),
                new_score,
            });

            // Check if completing this quest unlocks the next tier
            if let Some(quest_tier) = Self::quest_tier(&quest_id_raw) {
                if Self::all_quests_completed_in_tier(account, quest_tier) {
                    let new_tier = quest_tier; // completing all tier N quests unlocks tier N
                    if new_tier > current_tier {
                        TierUnlocked::<T>::insert(account, new_tier);
                        Self::deposit_event(Event::TierUnlocked {
                            account: account.clone(),
                            tier: new_tier,
                        });
                    }
                }
            }

            Ok(())
        }
    }

    // ── Extrinsics ───────────────────────────────────────────────────

    #[pallet::call]
    impl<T: Config> Pallet<T> {
        /// Self-report quest completion (signed, anyone).
        #[pallet::call_index(0)]
        #[pallet::weight(10_000)]
        pub fn complete_quest(
            origin: OriginFor<T>,
            quest_id: Vec<u8>,
        ) -> DispatchResult {
            let sender = ensure_signed(origin)?;
            Self::do_complete_quest(&sender, quest_id)
        }

        /// Admin/sudo: credit quest completion to any account.
        #[pallet::call_index(1)]
        #[pallet::weight(10_000)]
        pub fn admin_complete_quest(
            origin: OriginFor<T>,
            account: T::AccountId,
            quest_id: Vec<u8>,
        ) -> DispatchResult {
            T::AdminOrigin::ensure_origin(origin)?;
            Self::do_complete_quest(&account, quest_id)
        }

        /// Admin/sudo: override an account's score directly.
        #[pallet::call_index(2)]
        #[pallet::weight(10_000)]
        pub fn admin_set_score(
            origin: OriginFor<T>,
            account: T::AccountId,
            score: u32,
        ) -> DispatchResult {
            T::AdminOrigin::ensure_origin(origin)?;
            DevScore::<T>::insert(&account, score);

            Self::deposit_event(Event::ScoreUpdated {
                account,
                new_score: score,
            });

            Ok(())
        }
    }
}
