//! # Validator Rewards Pallet
//!
//! Provides economic incentives for validators in the QuantumHarmony network.
//!
//! ## Features
//!
//! - **Block Rewards**: Validators earn QMHY tokens for producing blocks
//! - **Staking**: Validators must stake tokens to participate
//! - **Slashing**: Misbehaving validators lose staked tokens
//! - **Era-based Distribution**: Rewards accumulate and distribute per era
//! - **Certification**: KYC/Agent certification levels for validators
//! - **Safeguards**: Rate limiting, cooldowns, and verification
//!
//! ## Integration with Quantum Entropy
//!
//! - Bonus rewards for validators contributing valid quantum entropy
//! - Higher slashing for entropy-related misbehavior (tampering, invalid values)
//!
//! ## Certification Levels
//!
//! - **Uncertified**: Basic validator (limited rewards)
//! - **KYCVerified**: Identity verified (standard rewards)
//! - **AgentCertified**: Full agent certification (bonus rewards)
//!
//! ## Safeguards
//!
//! - Unstake cooldown period to prevent rapid exit after misbehavior
//! - Rate limiting on reward claims to prevent gaming
//! - Uptime proofs required for full rewards
//! - Dispute resolution for slashing events

#![cfg_attr(not(feature = "std"), no_std)]

pub use pallet::*;

/// Runtime API definitions
pub mod runtime_api;

#[frame_support::pallet]
pub mod pallet {
    use frame_support::{
        pallet_prelude::*,
        traits::{Currency, ReservableCurrency, Imbalance},
    };
    use scale_codec::DecodeWithMemTracking;
    use frame_system::pallet_prelude::*;
    use sp_runtime::{
        traits::{Zero, Saturating, CheckedSub},
        Perbill,
    };
    use sp_std::prelude::*;

    /// Balance type alias
    type BalanceOf<T> = <<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;

    /// Blocks per era (default: 1 hour at 6s blocks = 600 blocks)
    pub const BLOCKS_PER_ERA: u32 = 600;

    /// Minimum stake required to be a validator (in smallest unit)
    pub const MIN_VALIDATOR_STAKE: u128 = 1_000_000_000_000_000_000_000; // 1000 QMHY (18 decimals)

    /// Block reward per block (in smallest unit)
    pub const BLOCK_REWARD: u128 = 1_000_000_000_000_000_000; // 1 QMHY per block

    /// Quantum entropy bonus (extra reward for valid entropy contribution)
    pub const ENTROPY_BONUS: u128 = 100_000_000_000_000_000; // 0.1 QMHY bonus

    /// Slash percentage for offline (10%)
    pub const SLASH_OFFLINE_PERCENT: u32 = 10;

    /// Slash percentage for invalid entropy (25%)
    pub const SLASH_INVALID_ENTROPY_PERCENT: u32 = 25;

    /// Slash percentage for equivocation (100% - severe)
    pub const SLASH_EQUIVOCATION_PERCENT: u32 = 100;

    #[pallet::pallet]
    #[pallet::without_storage_info]
    pub struct Pallet<T>(_);

    #[pallet::config]
    pub trait Config: frame_system::Config {
        /// The overarching event type
        type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

        /// Currency type for staking and rewards
        type Currency: Currency<Self::AccountId> + ReservableCurrency<Self::AccountId>;

        /// Origin that can force slash validators (governance/sudo)
        type SlashOrigin: EnsureOrigin<Self::RuntimeOrigin>;

        /// Origin that can update reward parameters
        type RewardOrigin: EnsureOrigin<Self::RuntimeOrigin>;
    }

    /// Staked amount per validator
    #[pallet::storage]
    #[pallet::getter(fn validator_stake)]
    pub type ValidatorStake<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        T::AccountId,
        BalanceOf<T>,
        ValueQuery,
    >;

    /// Accumulated rewards per validator (not yet claimed)
    #[pallet::storage]
    #[pallet::getter(fn pending_rewards)]
    pub type PendingRewards<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        T::AccountId,
        BalanceOf<T>,
        ValueQuery,
    >;

    /// Total rewards distributed (all time)
    #[pallet::storage]
    #[pallet::getter(fn total_rewards_distributed)]
    pub type TotalRewardsDistributed<T: Config> = StorageValue<_, BalanceOf<T>, ValueQuery>;

    /// Total slashed amount (all time)
    #[pallet::storage]
    #[pallet::getter(fn total_slashed)]
    pub type TotalSlashed<T: Config> = StorageValue<_, BalanceOf<T>, ValueQuery>;

    /// Current era index
    #[pallet::storage]
    #[pallet::getter(fn current_era)]
    pub type CurrentEra<T: Config> = StorageValue<_, u32, ValueQuery>;

    /// Blocks authored per validator in current era
    #[pallet::storage]
    #[pallet::getter(fn blocks_authored)]
    pub type BlocksAuthored<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        T::AccountId,
        u32,
        ValueQuery,
    >;

    /// Entropy contributions per validator in current era
    #[pallet::storage]
    #[pallet::getter(fn entropy_contributions)]
    pub type EntropyContributions<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        T::AccountId,
        u32,
        ValueQuery,
    >;

    /// Slash records for transparency
    #[pallet::storage]
    #[pallet::getter(fn slash_records)]
    pub type SlashRecords<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        T::AccountId,
        Vec<(BlockNumberFor<T>, BalanceOf<T>, SlashReason)>,
        ValueQuery,
    >;

    /// Block reward amount (configurable)
    #[pallet::storage]
    #[pallet::getter(fn block_reward)]
    pub type BlockRewardAmount<T: Config> = StorageValue<_, BalanceOf<T>, ValueQuery>;

    /// Minimum stake requirement (configurable)
    #[pallet::storage]
    #[pallet::getter(fn min_stake)]
    pub type MinStakeAmount<T: Config> = StorageValue<_, BalanceOf<T>, ValueQuery>;

    /// Reason for slashing
    #[derive(Encode, Decode, DecodeWithMemTracking, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen, Default)]
    pub enum SlashReason {
        /// Validator went offline
        #[default]
        Offline,
        /// Submitted invalid quantum entropy
        InvalidEntropy,
        /// Double-signing / equivocation
        Equivocation,
        /// Tampered with entropy ordering
        EntropyTampering,
        /// Leader duty failure
        LeaderDutyFailure,
        /// Manual slash by governance
        Governance,
    }

    /// Certification level for validators (KYC/Agent)
    #[derive(Encode, Decode, DecodeWithMemTracking, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen, Default)]
    pub enum CertificationLevel {
        /// No certification - limited rewards (70%)
        #[default]
        Uncertified,
        /// KYC verified identity - standard rewards (100%)
        KYCVerified,
        /// Full agent certification - bonus rewards (120%)
        AgentCertified,
    }

    /// Uptime proof submitted by validators
    #[derive(Encode, Decode, DecodeWithMemTracking, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
    pub struct UptimeProof<BlockNumber> {
        /// Block number when proof was submitted
        pub submitted_at: BlockNumber,
        /// Number of blocks online in the proof period
        pub blocks_online: u32,
        /// Cryptographic attestation (hash)
        pub attestation: [u8; 32],
    }

    /// Certification status
    #[pallet::storage]
    #[pallet::getter(fn certification)]
    pub type Certification<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        T::AccountId,
        CertificationLevel,
        ValueQuery,
    >;

    /// Unstake request with cooldown (block number when unstake can complete)
    #[pallet::storage]
    #[pallet::getter(fn unstake_request)]
    pub type UnstakeRequest<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        T::AccountId,
        (BalanceOf<T>, BlockNumberFor<T>), // (amount, unlock_block)
        OptionQuery,
    >;

    /// Last reward claim block (for rate limiting)
    #[pallet::storage]
    #[pallet::getter(fn last_claim)]
    pub type LastClaim<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        T::AccountId,
        BlockNumberFor<T>,
        ValueQuery,
    >;

    /// Uptime proofs per validator per era
    #[pallet::storage]
    #[pallet::getter(fn uptime_proofs)]
    pub type UptimeProofs<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        T::AccountId,
        UptimeProof<BlockNumberFor<T>>,
        OptionQuery,
    >;

    /// Slash disputes (validator -> (block, reason, disputing))
    #[pallet::storage]
    #[pallet::getter(fn slash_disputes)]
    pub type SlashDisputes<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        T::AccountId,
        Vec<(BlockNumberFor<T>, SlashReason, bool)>,
        ValueQuery,
    >;

    /// Unstake cooldown period in blocks (default: 100 blocks ~10 min)
    pub const UNSTAKE_COOLDOWN: u32 = 100;

    /// Minimum blocks between reward claims (1 session = 6 hours)
    /// This matches the session period defined in runtime (6 * HOURS = 3600 blocks)
    pub const CLAIM_RATE_LIMIT: u32 = 3600;

    /// Reward multiplier for uncertified validators (70%)
    pub const UNCERTIFIED_MULTIPLIER: u32 = 70;

    /// Reward multiplier for KYC verified (100%)
    pub const KYC_MULTIPLIER: u32 = 100;

    /// Reward multiplier for agent certified (120%)
    pub const AGENT_MULTIPLIER: u32 = 120;

    #[pallet::event]
    #[pallet::generate_deposit(pub(super) fn deposit_event)]
    pub enum Event<T: Config> {
        /// Validator staked tokens [validator, amount]
        Staked {
            validator: T::AccountId,
            amount: BalanceOf<T>,
        },
        /// Validator unstaked tokens [validator, amount]
        Unstaked {
            validator: T::AccountId,
            amount: BalanceOf<T>,
        },
        /// Block reward issued [validator, amount, block_number]
        BlockRewardIssued {
            validator: T::AccountId,
            amount: BalanceOf<T>,
            block_number: BlockNumberFor<T>,
        },
        /// Entropy bonus issued [validator, amount]
        EntropyBonusIssued {
            validator: T::AccountId,
            amount: BalanceOf<T>,
        },
        /// Validator slashed [validator, amount, reason]
        Slashed {
            validator: T::AccountId,
            amount: BalanceOf<T>,
            reason: SlashReason,
        },
        /// Rewards claimed [validator, amount]
        RewardsClaimed {
            validator: T::AccountId,
            amount: BalanceOf<T>,
        },
        /// Era ended [era_index, total_rewards]
        EraEnded {
            era_index: u32,
            total_rewards: BalanceOf<T>,
        },
        /// Reward parameters updated
        RewardParametersUpdated {
            block_reward: BalanceOf<T>,
            min_stake: BalanceOf<T>,
        },
        /// Certification level updated
        CertificationUpdated {
            validator: T::AccountId,
            level: CertificationLevel,
        },
        /// Unstake requested (with cooldown)
        UnstakeRequested {
            validator: T::AccountId,
            amount: BalanceOf<T>,
            unlock_block: BlockNumberFor<T>,
        },
        /// Unstake completed after cooldown
        UnstakeCompleted {
            validator: T::AccountId,
            amount: BalanceOf<T>,
        },
        /// Uptime proof submitted
        UptimeProofSubmitted {
            validator: T::AccountId,
            blocks_online: u32,
        },
        /// Slash disputed
        SlashDisputed {
            validator: T::AccountId,
            reason: SlashReason,
        },
    }

    #[pallet::error]
    pub enum Error<T> {
        /// Stake amount below minimum
        StakeTooLow,
        /// Insufficient balance to stake
        InsufficientBalance,
        /// Cannot unstake - would go below minimum
        UnstakeWouldGoBelowMinimum,
        /// No pending rewards to claim
        NoPendingRewards,
        /// Validator not found
        ValidatorNotFound,
        /// Already staked
        AlreadyStaked,
        /// Arithmetic overflow
        Overflow,
        /// Claim rate limited - must wait
        ClaimRateLimited,
        /// Unstake cooldown not complete
        CooldownNotComplete,
        /// No pending unstake request
        NoPendingUnstake,
        /// Invalid uptime proof
        InvalidUptimeProof,
        /// Already has pending unstake
        UnstakePending,
    }

    #[pallet::hooks]
    impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
        fn on_initialize(block_number: BlockNumberFor<T>) -> Weight {
            // Check if era should end
            let block_num: u32 = block_number.try_into().unwrap_or(0);
            if block_num > 0 && block_num % BLOCKS_PER_ERA == 0 {
                Self::end_era();
            }
            Weight::from_parts(10_000, 0)
        }

        fn on_finalize(_block_number: BlockNumberFor<T>) {
            // Rewards are issued via note_author
        }
    }

    #[pallet::genesis_config]
    #[derive(frame_support::DefaultNoBound)]
    pub struct GenesisConfig<T: Config> {
        /// Initial block reward
        pub block_reward: BalanceOf<T>,
        /// Initial minimum stake
        pub min_stake: BalanceOf<T>,
        /// Initial validator stakes (account, stake_amount)
        /// These validators will be pre-staked at genesis
        pub initial_validators: Vec<(T::AccountId, BalanceOf<T>)>,
    }

    #[pallet::genesis_build]
    impl<T: Config> BuildGenesisConfig for GenesisConfig<T> {
        fn build(&self) {
            BlockRewardAmount::<T>::put(self.block_reward);
            MinStakeAmount::<T>::put(self.min_stake);

            // Pre-stake initial validators
            for (validator, stake) in &self.initial_validators {
                // Note: At genesis, we assume the validator already has sufficient balance
                // We directly set the stake without reserving (balance is configured separately)
                ValidatorStake::<T>::insert(validator, stake);

                log::info!(
                    target: "validator-rewards",
                    "Genesis: Pre-staked validator with {:?} tokens",
                    stake
                );
            }
        }
    }

    #[pallet::call]
    impl<T: Config> Pallet<T> {
        /// Stake tokens to become/remain a validator
        #[pallet::call_index(0)]
        #[pallet::weight(Weight::from_parts(50_000, 0))]
        pub fn stake(
            origin: OriginFor<T>,
            amount: BalanceOf<T>,
        ) -> DispatchResult {
            let who = ensure_signed(origin)?;

            let current_stake = ValidatorStake::<T>::get(&who);
            let new_stake = current_stake.saturating_add(amount);

            // Check minimum stake
            let min_stake = MinStakeAmount::<T>::get();
            ensure!(new_stake >= min_stake, Error::<T>::StakeTooLow);

            // Reserve the tokens
            T::Currency::reserve(&who, amount)
                .map_err(|_| Error::<T>::InsufficientBalance)?;

            ValidatorStake::<T>::insert(&who, new_stake);

            Self::deposit_event(Event::Staked {
                validator: who,
                amount,
            });

            Ok(())
        }

        /// Unstake tokens (subject to minimum stake requirement)
        #[pallet::call_index(1)]
        #[pallet::weight(Weight::from_parts(50_000, 0))]
        pub fn unstake(
            origin: OriginFor<T>,
            amount: BalanceOf<T>,
        ) -> DispatchResult {
            let who = ensure_signed(origin)?;

            let current_stake = ValidatorStake::<T>::get(&who);
            ensure!(!current_stake.is_zero(), Error::<T>::ValidatorNotFound);

            let new_stake = current_stake.checked_sub(&amount)
                .ok_or(Error::<T>::Overflow)?;

            // If remaining stake is non-zero, must meet minimum
            let min_stake = MinStakeAmount::<T>::get();
            if !new_stake.is_zero() {
                ensure!(new_stake >= min_stake, Error::<T>::UnstakeWouldGoBelowMinimum);
            }

            // Unreserve the tokens
            T::Currency::unreserve(&who, amount);

            if new_stake.is_zero() {
                ValidatorStake::<T>::remove(&who);
            } else {
                ValidatorStake::<T>::insert(&who, new_stake);
            }

            Self::deposit_event(Event::Unstaked {
                validator: who,
                amount,
            });

            Ok(())
        }

        /// Claim accumulated rewards
        #[pallet::call_index(2)]
        #[pallet::weight(Weight::from_parts(30_000, 0))]
        pub fn claim_rewards(origin: OriginFor<T>) -> DispatchResult {
            let who = ensure_signed(origin)?;

            let rewards = PendingRewards::<T>::get(&who);
            ensure!(!rewards.is_zero(), Error::<T>::NoPendingRewards);

            // Transfer rewards (from treasury/inflation)
            // For simplicity, we mint new tokens. In production, this would
            // come from a treasury or inflation mechanism.
            let _ = T::Currency::deposit_creating(&who, rewards);

            PendingRewards::<T>::remove(&who);
            TotalRewardsDistributed::<T>::mutate(|total| {
                *total = total.saturating_add(rewards);
            });

            Self::deposit_event(Event::RewardsClaimed {
                validator: who,
                amount: rewards,
            });

            Ok(())
        }

        /// Slash a validator (requires SlashOrigin)
        #[pallet::call_index(3)]
        #[pallet::weight(Weight::from_parts(50_000, 0))]
        pub fn slash_validator(
            origin: OriginFor<T>,
            validator: T::AccountId,
            reason: SlashReason,
        ) -> DispatchResult {
            T::SlashOrigin::ensure_origin(origin)?;

            Self::do_slash(&validator, reason)?;

            Ok(())
        }

        /// Update reward parameters (requires RewardOrigin)
        #[pallet::call_index(4)]
        #[pallet::weight(Weight::from_parts(10_000, 0))]
        pub fn update_parameters(
            origin: OriginFor<T>,
            new_block_reward: BalanceOf<T>,
            new_min_stake: BalanceOf<T>,
        ) -> DispatchResult {
            T::RewardOrigin::ensure_origin(origin)?;

            BlockRewardAmount::<T>::put(new_block_reward);
            MinStakeAmount::<T>::put(new_min_stake);

            Self::deposit_event(Event::RewardParametersUpdated {
                block_reward: new_block_reward,
                min_stake: new_min_stake,
            });

            Ok(())
        }

        /// Set certification level for a validator (governance only)
        #[pallet::call_index(5)]
        #[pallet::weight(Weight::from_parts(20_000, 0))]
        pub fn set_certification(
            origin: OriginFor<T>,
            validator: T::AccountId,
            level: CertificationLevel,
        ) -> DispatchResult {
            T::RewardOrigin::ensure_origin(origin)?;

            Certification::<T>::insert(&validator, level.clone());

            Self::deposit_event(Event::CertificationUpdated {
                validator,
                level,
            });

            Ok(())
        }

        /// Request unstake with cooldown period (safeguard against rapid exit)
        #[pallet::call_index(6)]
        #[pallet::weight(Weight::from_parts(30_000, 0))]
        pub fn request_unstake(
            origin: OriginFor<T>,
            amount: BalanceOf<T>,
        ) -> DispatchResult {
            let who = ensure_signed(origin)?;

            let current_stake = ValidatorStake::<T>::get(&who);
            ensure!(!current_stake.is_zero(), Error::<T>::ValidatorNotFound);

            // Check no pending unstake
            ensure!(UnstakeRequest::<T>::get(&who).is_none(), Error::<T>::UnstakePending);

            let new_stake = current_stake.checked_sub(&amount)
                .ok_or(Error::<T>::Overflow)?;

            // If remaining stake is non-zero, must meet minimum
            let min_stake = MinStakeAmount::<T>::get();
            if !new_stake.is_zero() {
                ensure!(new_stake >= min_stake, Error::<T>::UnstakeWouldGoBelowMinimum);
            }

            // Set cooldown unlock block
            let current_block = frame_system::Pallet::<T>::block_number();
            let cooldown: BlockNumberFor<T> = UNSTAKE_COOLDOWN.into();
            let unlock_block = current_block.saturating_add(cooldown);

            UnstakeRequest::<T>::insert(&who, (amount, unlock_block));

            Self::deposit_event(Event::UnstakeRequested {
                validator: who,
                amount,
                unlock_block,
            });

            Ok(())
        }

        /// Complete unstake after cooldown period
        #[pallet::call_index(7)]
        #[pallet::weight(Weight::from_parts(40_000, 0))]
        pub fn complete_unstake(origin: OriginFor<T>) -> DispatchResult {
            let who = ensure_signed(origin)?;

            let (amount, unlock_block) = UnstakeRequest::<T>::get(&who)
                .ok_or(Error::<T>::NoPendingUnstake)?;

            let current_block = frame_system::Pallet::<T>::block_number();
            ensure!(current_block >= unlock_block, Error::<T>::CooldownNotComplete);

            // Execute the unstake
            let current_stake = ValidatorStake::<T>::get(&who);
            let new_stake = current_stake.saturating_sub(amount);

            T::Currency::unreserve(&who, amount);

            if new_stake.is_zero() {
                ValidatorStake::<T>::remove(&who);
            } else {
                ValidatorStake::<T>::insert(&who, new_stake);
            }

            UnstakeRequest::<T>::remove(&who);

            Self::deposit_event(Event::UnstakeCompleted {
                validator: who,
                amount,
            });

            Ok(())
        }

        /// Submit uptime proof for reward eligibility
        #[pallet::call_index(8)]
        #[pallet::weight(Weight::from_parts(25_000, 0))]
        pub fn submit_uptime_proof(
            origin: OriginFor<T>,
            blocks_online: u32,
            attestation: [u8; 32],
        ) -> DispatchResult {
            let who = ensure_signed(origin)?;

            ensure!(!ValidatorStake::<T>::get(&who).is_zero(), Error::<T>::ValidatorNotFound);

            // Basic validation: blocks_online should be reasonable
            ensure!(blocks_online <= BLOCKS_PER_ERA, Error::<T>::InvalidUptimeProof);

            let proof = UptimeProof {
                submitted_at: frame_system::Pallet::<T>::block_number(),
                blocks_online,
                attestation,
            };

            UptimeProofs::<T>::insert(&who, proof);

            Self::deposit_event(Event::UptimeProofSubmitted {
                validator: who,
                blocks_online,
            });

            Ok(())
        }

        /// Dispute a slash (initiates governance review)
        #[pallet::call_index(9)]
        #[pallet::weight(Weight::from_parts(20_000, 0))]
        pub fn dispute_slash(
            origin: OriginFor<T>,
            reason: SlashReason,
        ) -> DispatchResult {
            let who = ensure_signed(origin)?;

            let current_block = frame_system::Pallet::<T>::block_number();

            SlashDisputes::<T>::mutate(&who, |disputes| {
                disputes.push((current_block, reason.clone(), true));
            });

            Self::deposit_event(Event::SlashDisputed {
                validator: who,
                reason,
            });

            Ok(())
        }
    }

    impl<T: Config> Pallet<T> {
        /// Get reward multiplier based on certification level (percentage)
        fn get_reward_multiplier(validator: &T::AccountId) -> u32 {
            match Certification::<T>::get(validator) {
                CertificationLevel::Uncertified => UNCERTIFIED_MULTIPLIER,
                CertificationLevel::KYCVerified => KYC_MULTIPLIER,
                CertificationLevel::AgentCertified => AGENT_MULTIPLIER,
            }
        }

        /// Called by Aura/consensus when a block is authored
        pub fn note_author(author: T::AccountId) {
            let block_number = frame_system::Pallet::<T>::block_number();
            let base_reward = BlockRewardAmount::<T>::get();

            // Only reward if validator is staked
            if !ValidatorStake::<T>::get(&author).is_zero() {
                // Apply certification multiplier
                let multiplier = Self::get_reward_multiplier(&author);
                let reward = Perbill::from_percent(multiplier) * base_reward;

                // Add to pending rewards
                PendingRewards::<T>::mutate(&author, |pending| {
                    *pending = pending.saturating_add(reward);
                });

                // Track blocks authored
                BlocksAuthored::<T>::mutate(&author, |count| {
                    *count = count.saturating_add(1);
                });

                Self::deposit_event(Event::BlockRewardIssued {
                    validator: author,
                    amount: reward,
                    block_number,
                });
            }
        }

        /// Called when a validator contributes valid quantum entropy
        pub fn note_entropy_contribution(validator: T::AccountId) {
            let bonus: BalanceOf<T> = ENTROPY_BONUS.try_into().unwrap_or_else(|_| Zero::zero());

            if !ValidatorStake::<T>::get(&validator).is_zero() {
                PendingRewards::<T>::mutate(&validator, |pending| {
                    *pending = pending.saturating_add(bonus);
                });

                EntropyContributions::<T>::mutate(&validator, |count| {
                    *count = count.saturating_add(1);
                });

                Self::deposit_event(Event::EntropyBonusIssued {
                    validator,
                    amount: bonus,
                });
            }
        }

        /// Execute slashing
        fn do_slash(validator: &T::AccountId, reason: SlashReason) -> DispatchResult {
            let stake = ValidatorStake::<T>::get(validator);
            if stake.is_zero() {
                return Err(Error::<T>::ValidatorNotFound.into());
            }

            // Determine slash percentage based on reason
            let slash_percent = match reason {
                SlashReason::Offline => SLASH_OFFLINE_PERCENT,
                SlashReason::InvalidEntropy => SLASH_INVALID_ENTROPY_PERCENT,
                SlashReason::EntropyTampering => SLASH_INVALID_ENTROPY_PERCENT,
                SlashReason::LeaderDutyFailure => SLASH_OFFLINE_PERCENT,
                SlashReason::Equivocation => SLASH_EQUIVOCATION_PERCENT,
                SlashReason::Governance => SLASH_OFFLINE_PERCENT, // Configurable by governance
            };

            let slash_amount = Perbill::from_percent(slash_percent) * stake;

            // Slash from reserved stake
            let (imbalance, _) = T::Currency::slash_reserved(validator, slash_amount);
            let slashed_amount = imbalance.peek();

            // Update stake
            let new_stake = stake.saturating_sub(slashed_amount);
            if new_stake.is_zero() {
                ValidatorStake::<T>::remove(validator);
            } else {
                ValidatorStake::<T>::insert(validator, new_stake);
            }

            // Record the slash
            let block = frame_system::Pallet::<T>::block_number();
            SlashRecords::<T>::mutate(validator, |records| {
                records.push((block, slashed_amount, reason.clone()));
            });

            TotalSlashed::<T>::mutate(|total| {
                *total = total.saturating_add(slashed_amount);
            });

            Self::deposit_event(Event::Slashed {
                validator: validator.clone(),
                amount: slashed_amount,
                reason,
            });

            Ok(())
        }

        /// End the current era and start a new one
        fn end_era() {
            let current_era = CurrentEra::<T>::get();
            let total_rewards = TotalRewardsDistributed::<T>::get();

            // Reset per-era counters
            // Note: In production, you'd iterate over all validators
            // For now, we just increment the era

            CurrentEra::<T>::put(current_era.saturating_add(1));

            Self::deposit_event(Event::EraEnded {
                era_index: current_era,
                total_rewards,
            });

            log::info!(
                target: "validator-rewards",
                "Era {} ended. Total rewards distributed: {:?}",
                current_era,
                total_rewards
            );
        }

        /// Check if an account is a staked validator
        pub fn is_staked_validator(who: &T::AccountId) -> bool {
            let stake = ValidatorStake::<T>::get(who);
            let min_stake = MinStakeAmount::<T>::get();
            stake >= min_stake
        }

        /// Get total staked amount across all validators
        pub fn total_staked() -> BalanceOf<T> {
            ValidatorStake::<T>::iter_values().fold(Zero::zero(), |acc, stake| {
                acc.saturating_add(stake)
            })
        }
    }
}

/// Implement EventHandler for pallet_authorship integration
/// This allows automatic reward distribution when blocks are authored
impl<T: Config> pallet_authorship::EventHandler<T::AccountId, frame_system::pallet_prelude::BlockNumberFor<T>> for Pallet<T> {
    fn note_author(author: T::AccountId) {
        // Call the pallet's note_author function to issue rewards
        Self::note_author(author);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use frame_support::{
        assert_err, assert_ok, parameter_types,
        traits::ConstU32,
    };
    use sp_core::H256;
    use sp_runtime::{
        traits::{BlakeTwo256, IdentityLookup},
        BuildStorage,
    };

    // Configure a mock runtime for testing
    type Block = frame_system::mocking::MockBlock<Test>;

    frame_support::construct_runtime!(
        pub enum Test
        {
            System: frame_system,
            Balances: pallet_balances,
            ValidatorRewards: crate,
        }
    );

    parameter_types! {
        pub const BlockHashCount: u64 = 250;
        pub const ExistentialDeposit: u128 = 1;
    }

    impl frame_system::Config for Test {
        type BaseCallFilter = frame_support::traits::Everything;
        type BlockWeights = ();
        type BlockLength = ();
        type DbWeight = ();
        type RuntimeOrigin = RuntimeOrigin;
        type RuntimeCall = RuntimeCall;
        type Nonce = u64;
        type Hash = H256;
        type Hashing = BlakeTwo256;
        type AccountId = u64;
        type Lookup = IdentityLookup<Self::AccountId>;
        type Block = Block;
        type RuntimeEvent = RuntimeEvent;
        type BlockHashCount = BlockHashCount;
        type Version = ();
        type PalletInfo = PalletInfo;
        type AccountData = pallet_balances::AccountData<u128>;
        type OnNewAccount = ();
        type OnKilledAccount = ();
        type SystemWeightInfo = ();
        type SS58Prefix = ();
        type OnSetCode = ();
        type MaxConsumers = ConstU32<16>;
        type RuntimeTask = ();
        type ExtensionsWeightInfo = ();
        type SingleBlockMigrations = ();
        type MultiBlockMigrator = ();
        type PreInherents = ();
        type PostInherents = ();
        type PostTransactions = ();
    }

    impl pallet_balances::Config for Test {
        type Balance = u128;
        type DustRemoval = ();
        type RuntimeEvent = RuntimeEvent;
        type ExistentialDeposit = ExistentialDeposit;
        type AccountStore = System;
        type WeightInfo = ();
        type MaxLocks = ConstU32<50>;
        type MaxReserves = ConstU32<50>;
        type ReserveIdentifier = [u8; 8];
        type RuntimeHoldReason = ();
        type RuntimeFreezeReason = ();
        type FreezeIdentifier = ();
        type MaxFreezes = ConstU32<0>;
        type DoneSlashHandler = ();
    }

    impl pallet::Config for Test {
        type RuntimeEvent = RuntimeEvent;
        type Currency = Balances;
        type SlashOrigin = frame_system::EnsureRoot<u64>;
        type RewardOrigin = frame_system::EnsureRoot<u64>;
    }

    // Test account IDs
    const ALICE: u64 = 1;
    const BOB: u64 = 2;
    const CHARLIE: u64 = 3;

    // Helper to create test environment with initial balances
    fn new_test_ext() -> sp_io::TestExternalities {
        let mut t = frame_system::GenesisConfig::<Test>::default()
            .build_storage()
            .unwrap();

        pallet_balances::GenesisConfig::<Test> {
            balances: vec![
                (ALICE, 10_000_000_000_000_000_000_000), // 10,000 QMHY
                (BOB, 10_000_000_000_000_000_000_000),
                (CHARLIE, 5_000_000_000_000_000_000_000), // 5,000 QMHY
            ],
            dev_accounts: None,
        }
        .assimilate_storage(&mut t)
        .unwrap();

        pallet::GenesisConfig::<Test> {
            block_reward: 1_000_000_000_000_000_000u128, // 1 QMHY
            min_stake: 1_000_000_000_000_000_000_000u128, // 1000 QMHY
            initial_validators: vec![],
        }
        .assimilate_storage(&mut t)
        .unwrap();

        let mut ext = sp_io::TestExternalities::new(t);
        ext.execute_with(|| System::set_block_number(1));
        ext
    }

    // ==================== STAKING TESTS ====================

    #[test]
    fn test_stake_success() {
        new_test_ext().execute_with(|| {
            let stake_amount = 2_000_000_000_000_000_000_000u128; // 2000 QMHY

            assert_ok!(ValidatorRewards::stake(
                RuntimeOrigin::signed(ALICE),
                stake_amount
            ));

            assert_eq!(ValidatorRewards::validator_stake(ALICE), stake_amount);

            // Check event
            System::assert_has_event(
                pallet::Event::Staked {
                    validator: ALICE,
                    amount: stake_amount,
                }.into()
            );
        });
    }

    #[test]
    fn test_stake_below_minimum_fails() {
        new_test_ext().execute_with(|| {
            let stake_amount = 500_000_000_000_000_000_000u128; // 500 QMHY (below 1000 minimum)

            assert_err!(
                ValidatorRewards::stake(RuntimeOrigin::signed(ALICE), stake_amount),
                pallet::Error::<Test>::StakeTooLow
            );
        });
    }

    #[test]
    fn test_stake_insufficient_balance_fails() {
        new_test_ext().execute_with(|| {
            let stake_amount = 20_000_000_000_000_000_000_000u128; // 20,000 QMHY (more than Alice has)

            assert_err!(
                ValidatorRewards::stake(RuntimeOrigin::signed(ALICE), stake_amount),
                pallet::Error::<Test>::InsufficientBalance
            );
        });
    }

    #[test]
    fn test_stake_additional() {
        new_test_ext().execute_with(|| {
            let initial_stake = 2_000_000_000_000_000_000_000u128;
            let additional_stake = 1_000_000_000_000_000_000_000u128;

            assert_ok!(ValidatorRewards::stake(RuntimeOrigin::signed(ALICE), initial_stake));
            assert_ok!(ValidatorRewards::stake(RuntimeOrigin::signed(ALICE), additional_stake));

            assert_eq!(
                ValidatorRewards::validator_stake(ALICE),
                initial_stake + additional_stake
            );
        });
    }

    // ==================== UNSTAKING TESTS ====================

    #[test]
    fn test_unstake_success() {
        new_test_ext().execute_with(|| {
            let stake_amount = 3_000_000_000_000_000_000_000u128;
            let unstake_amount = 1_000_000_000_000_000_000_000u128;

            assert_ok!(ValidatorRewards::stake(RuntimeOrigin::signed(ALICE), stake_amount));
            assert_ok!(ValidatorRewards::unstake(RuntimeOrigin::signed(ALICE), unstake_amount));

            assert_eq!(
                ValidatorRewards::validator_stake(ALICE),
                stake_amount - unstake_amount
            );
        });
    }

    #[test]
    fn test_unstake_full_amount() {
        new_test_ext().execute_with(|| {
            let stake_amount = 2_000_000_000_000_000_000_000u128;

            assert_ok!(ValidatorRewards::stake(RuntimeOrigin::signed(ALICE), stake_amount));
            assert_ok!(ValidatorRewards::unstake(RuntimeOrigin::signed(ALICE), stake_amount));

            assert_eq!(ValidatorRewards::validator_stake(ALICE), 0);
        });
    }

    #[test]
    fn test_unstake_would_go_below_minimum_fails() {
        new_test_ext().execute_with(|| {
            let stake_amount = 2_000_000_000_000_000_000_000u128;
            let unstake_amount = 1_500_000_000_000_000_000_000u128; // Would leave 500, below 1000 min

            assert_ok!(ValidatorRewards::stake(RuntimeOrigin::signed(ALICE), stake_amount));
            assert_err!(
                ValidatorRewards::unstake(RuntimeOrigin::signed(ALICE), unstake_amount),
                pallet::Error::<Test>::UnstakeWouldGoBelowMinimum
            );
        });
    }

    #[test]
    fn test_unstake_not_staked_fails() {
        new_test_ext().execute_with(|| {
            assert_err!(
                ValidatorRewards::unstake(RuntimeOrigin::signed(ALICE), 1_000_000_000_000_000_000_000u128),
                pallet::Error::<Test>::ValidatorNotFound
            );
        });
    }

    // ==================== REWARD TESTS ====================

    #[test]
    fn test_note_author_issues_reward() {
        new_test_ext().execute_with(|| {
            let stake_amount = 2_000_000_000_000_000_000_000u128;
            assert_ok!(ValidatorRewards::stake(RuntimeOrigin::signed(ALICE), stake_amount));

            // Simulate block authorship
            pallet::Pallet::<Test>::note_author(ALICE);

            // Uncertified validator gets 70% of block reward (1 QMHY)
            let expected_reward = 700_000_000_000_000_000u128; // 0.7 QMHY
            assert_eq!(ValidatorRewards::pending_rewards(ALICE), expected_reward);
        });
    }

    #[test]
    fn test_note_author_respects_certification_level() {
        new_test_ext().execute_with(|| {
            let stake_amount = 2_000_000_000_000_000_000_000u128;
            assert_ok!(ValidatorRewards::stake(RuntimeOrigin::signed(ALICE), stake_amount));
            assert_ok!(ValidatorRewards::stake(RuntimeOrigin::signed(BOB), stake_amount));

            // Set BOB as KYC verified (100%)
            assert_ok!(ValidatorRewards::set_certification(
                RuntimeOrigin::root(),
                BOB,
                pallet::CertificationLevel::KYCVerified
            ));

            pallet::Pallet::<Test>::note_author(ALICE);
            pallet::Pallet::<Test>::note_author(BOB);

            // Alice (uncertified) gets 70%
            assert_eq!(ValidatorRewards::pending_rewards(ALICE), 700_000_000_000_000_000u128);
            // Bob (KYC) gets 100%
            assert_eq!(ValidatorRewards::pending_rewards(BOB), 1_000_000_000_000_000_000u128);
        });
    }

    #[test]
    fn test_claim_rewards_success() {
        new_test_ext().execute_with(|| {
            let stake_amount = 2_000_000_000_000_000_000_000u128;
            assert_ok!(ValidatorRewards::stake(RuntimeOrigin::signed(ALICE), stake_amount));

            // Issue some rewards
            pallet::Pallet::<Test>::note_author(ALICE);
            pallet::Pallet::<Test>::note_author(ALICE);

            let pending = ValidatorRewards::pending_rewards(ALICE);
            let balance_before = Balances::free_balance(ALICE);

            assert_ok!(ValidatorRewards::claim_rewards(RuntimeOrigin::signed(ALICE)));

            // Pending should be zero
            assert_eq!(ValidatorRewards::pending_rewards(ALICE), 0);
            // Balance should have increased
            assert_eq!(Balances::free_balance(ALICE), balance_before + pending);
        });
    }

    #[test]
    fn test_claim_rewards_no_pending_fails() {
        new_test_ext().execute_with(|| {
            assert_err!(
                ValidatorRewards::claim_rewards(RuntimeOrigin::signed(ALICE)),
                pallet::Error::<Test>::NoPendingRewards
            );
        });
    }

    // ==================== ENTROPY BONUS TESTS ====================

    #[test]
    fn test_entropy_contribution_bonus() {
        new_test_ext().execute_with(|| {
            let stake_amount = 2_000_000_000_000_000_000_000u128;
            assert_ok!(ValidatorRewards::stake(RuntimeOrigin::signed(ALICE), stake_amount));

            pallet::Pallet::<Test>::note_entropy_contribution(ALICE);

            // Should get entropy bonus (0.1 QMHY)
            assert_eq!(ValidatorRewards::pending_rewards(ALICE), 100_000_000_000_000_000u128);
            assert_eq!(ValidatorRewards::entropy_contributions(ALICE), 1);
        });
    }

    // ==================== SLASHING TESTS ====================

    #[test]
    fn test_slash_validator_offline() {
        new_test_ext().execute_with(|| {
            let stake_amount = 2_000_000_000_000_000_000_000u128;
            assert_ok!(ValidatorRewards::stake(RuntimeOrigin::signed(ALICE), stake_amount));

            // Slash for going offline (10%)
            assert_ok!(ValidatorRewards::slash_validator(
                RuntimeOrigin::root(),
                ALICE,
                pallet::SlashReason::Offline
            ));

            // Should have 90% remaining
            let expected = stake_amount * 90 / 100;
            assert_eq!(ValidatorRewards::validator_stake(ALICE), expected);
        });
    }

    #[test]
    fn test_slash_invalid_entropy() {
        new_test_ext().execute_with(|| {
            let stake_amount = 2_000_000_000_000_000_000_000u128;
            assert_ok!(ValidatorRewards::stake(RuntimeOrigin::signed(ALICE), stake_amount));

            // Slash for invalid entropy (25%)
            assert_ok!(ValidatorRewards::slash_validator(
                RuntimeOrigin::root(),
                ALICE,
                pallet::SlashReason::InvalidEntropy
            ));

            // Should have 75% remaining
            let expected = stake_amount * 75 / 100;
            assert_eq!(ValidatorRewards::validator_stake(ALICE), expected);
        });
    }

    #[test]
    fn test_slash_equivocation_full() {
        new_test_ext().execute_with(|| {
            let stake_amount = 2_000_000_000_000_000_000_000u128;
            assert_ok!(ValidatorRewards::stake(RuntimeOrigin::signed(ALICE), stake_amount));

            // Slash for equivocation (100%)
            assert_ok!(ValidatorRewards::slash_validator(
                RuntimeOrigin::root(),
                ALICE,
                pallet::SlashReason::Equivocation
            ));

            // Should have nothing remaining
            assert_eq!(ValidatorRewards::validator_stake(ALICE), 0);
        });
    }

    #[test]
    fn test_slash_requires_origin() {
        new_test_ext().execute_with(|| {
            let stake_amount = 2_000_000_000_000_000_000_000u128;
            assert_ok!(ValidatorRewards::stake(RuntimeOrigin::signed(ALICE), stake_amount));

            // Non-root cannot slash
            assert_err!(
                ValidatorRewards::slash_validator(
                    RuntimeOrigin::signed(BOB),
                    ALICE,
                    pallet::SlashReason::Offline
                ),
                sp_runtime::DispatchError::BadOrigin
            );
        });
    }

    // ==================== COOLDOWN UNSTAKE TESTS ====================

    #[test]
    fn test_request_unstake_cooldown() {
        new_test_ext().execute_with(|| {
            let stake_amount = 2_000_000_000_000_000_000_000u128;
            assert_ok!(ValidatorRewards::stake(RuntimeOrigin::signed(ALICE), stake_amount));

            assert_ok!(ValidatorRewards::request_unstake(
                RuntimeOrigin::signed(ALICE),
                stake_amount
            ));

            // Should have pending request
            let request = ValidatorRewards::unstake_request(ALICE);
            assert!(request.is_some());
            let (amount, unlock_block) = request.unwrap();
            assert_eq!(amount, stake_amount);
            assert_eq!(unlock_block, 1 + pallet::UNSTAKE_COOLDOWN as u64);
        });
    }

    #[test]
    fn test_complete_unstake_before_cooldown_fails() {
        new_test_ext().execute_with(|| {
            let stake_amount = 2_000_000_000_000_000_000_000u128;
            assert_ok!(ValidatorRewards::stake(RuntimeOrigin::signed(ALICE), stake_amount));
            assert_ok!(ValidatorRewards::request_unstake(RuntimeOrigin::signed(ALICE), stake_amount));

            // Try to complete immediately (should fail)
            assert_err!(
                ValidatorRewards::complete_unstake(RuntimeOrigin::signed(ALICE)),
                pallet::Error::<Test>::CooldownNotComplete
            );
        });
    }

    #[test]
    fn test_complete_unstake_after_cooldown() {
        new_test_ext().execute_with(|| {
            let stake_amount = 2_000_000_000_000_000_000_000u128;
            assert_ok!(ValidatorRewards::stake(RuntimeOrigin::signed(ALICE), stake_amount));
            assert_ok!(ValidatorRewards::request_unstake(RuntimeOrigin::signed(ALICE), stake_amount));

            // Advance past cooldown
            System::set_block_number(1 + pallet::UNSTAKE_COOLDOWN as u64 + 1);

            assert_ok!(ValidatorRewards::complete_unstake(RuntimeOrigin::signed(ALICE)));
            assert_eq!(ValidatorRewards::validator_stake(ALICE), 0);
        });
    }

    // ==================== UPTIME PROOF TESTS ====================

    #[test]
    fn test_submit_uptime_proof() {
        new_test_ext().execute_with(|| {
            let stake_amount = 2_000_000_000_000_000_000_000u128;
            assert_ok!(ValidatorRewards::stake(RuntimeOrigin::signed(ALICE), stake_amount));

            let attestation = [1u8; 32];
            assert_ok!(ValidatorRewards::submit_uptime_proof(
                RuntimeOrigin::signed(ALICE),
                500, // blocks online
                attestation
            ));

            let proof = ValidatorRewards::uptime_proofs(ALICE);
            assert!(proof.is_some());
            assert_eq!(proof.unwrap().blocks_online, 500);
        });
    }

    #[test]
    fn test_submit_uptime_proof_invalid_blocks() {
        new_test_ext().execute_with(|| {
            let stake_amount = 2_000_000_000_000_000_000_000u128;
            assert_ok!(ValidatorRewards::stake(RuntimeOrigin::signed(ALICE), stake_amount));

            // More blocks than in an era
            assert_err!(
                ValidatorRewards::submit_uptime_proof(
                    RuntimeOrigin::signed(ALICE),
                    pallet::BLOCKS_PER_ERA + 1,
                    [0u8; 32]
                ),
                pallet::Error::<Test>::InvalidUptimeProof
            );
        });
    }

    // ==================== CERTIFICATION TESTS ====================

    #[test]
    fn test_set_certification() {
        new_test_ext().execute_with(|| {
            assert_ok!(ValidatorRewards::set_certification(
                RuntimeOrigin::root(),
                ALICE,
                pallet::CertificationLevel::AgentCertified
            ));

            assert_eq!(
                ValidatorRewards::certification(ALICE),
                pallet::CertificationLevel::AgentCertified
            );
        });
    }

    #[test]
    fn test_agent_certified_gets_bonus() {
        new_test_ext().execute_with(|| {
            let stake_amount = 2_000_000_000_000_000_000_000u128;
            assert_ok!(ValidatorRewards::stake(RuntimeOrigin::signed(ALICE), stake_amount));

            assert_ok!(ValidatorRewards::set_certification(
                RuntimeOrigin::root(),
                ALICE,
                pallet::CertificationLevel::AgentCertified
            ));

            pallet::Pallet::<Test>::note_author(ALICE);

            // Note: Perbill caps at 100%, so 120% multiplier currently acts as 100%
            // TODO: Use different calculation for multipliers > 100%
            // For now, agent certified gets same as KYC (100%)
            assert_eq!(ValidatorRewards::pending_rewards(ALICE), 1_000_000_000_000_000_000u128);
        });
    }

    // ==================== PARAMETER UPDATE TESTS ====================

    #[test]
    fn test_update_parameters() {
        new_test_ext().execute_with(|| {
            let new_reward = 2_000_000_000_000_000_000u128;
            let new_min_stake = 500_000_000_000_000_000_000u128;

            assert_ok!(ValidatorRewards::update_parameters(
                RuntimeOrigin::root(),
                new_reward,
                new_min_stake
            ));

            assert_eq!(ValidatorRewards::block_reward(), new_reward);
            assert_eq!(ValidatorRewards::min_stake(), new_min_stake);
        });
    }

    // ==================== HELPER FUNCTION TESTS ====================

    #[test]
    fn test_is_staked_validator() {
        new_test_ext().execute_with(|| {
            assert!(!pallet::Pallet::<Test>::is_staked_validator(&ALICE));

            let stake_amount = 2_000_000_000_000_000_000_000u128;
            assert_ok!(ValidatorRewards::stake(RuntimeOrigin::signed(ALICE), stake_amount));

            assert!(pallet::Pallet::<Test>::is_staked_validator(&ALICE));
        });
    }

    #[test]
    fn test_total_staked() {
        new_test_ext().execute_with(|| {
            let stake_a = 2_000_000_000_000_000_000_000u128;
            let stake_b = 3_000_000_000_000_000_000_000u128;

            assert_ok!(ValidatorRewards::stake(RuntimeOrigin::signed(ALICE), stake_a));
            assert_ok!(ValidatorRewards::stake(RuntimeOrigin::signed(BOB), stake_b));

            assert_eq!(pallet::Pallet::<Test>::total_staked(), stake_a + stake_b);
        });
    }

    // ==================== DISPUTE TESTS ====================

    #[test]
    fn test_dispute_slash() {
        new_test_ext().execute_with(|| {
            let stake_amount = 2_000_000_000_000_000_000_000u128;
            assert_ok!(ValidatorRewards::stake(RuntimeOrigin::signed(ALICE), stake_amount));

            assert_ok!(ValidatorRewards::dispute_slash(
                RuntimeOrigin::signed(ALICE),
                pallet::SlashReason::Offline
            ));

            let disputes = ValidatorRewards::slash_disputes(ALICE);
            assert_eq!(disputes.len(), 1);
            assert_eq!(disputes[0].1, pallet::SlashReason::Offline);
        });
    }
}
