# ISO 24643 Smart Contract Specifications

## Overview

This document provides formal specifications for QuantumHarmony pallets following ISO 24643:2023 guidelines.

**Standard:** ISO 24643:2023 - Blockchain and distributed ledger technologies — Overview of smart contracts in blockchain and DLT systems

---

## Pallet Classification

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    SMART CONTRACT CLASSIFICATION                             │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  Deterministic Execution:     YES (WASM runtime, metered execution)         │
│  State Persistence:           YES (Merkle trie storage)                     │
│  Event Emission:              YES (indexed, queryable)                      │
│  Upgrade Mechanism:           YES (forkless runtime upgrades)               │
│  Access Control:              YES (origin-based, role-based)                │
│                                                                              │
│  ISO 24643 Category:          Native Smart Contracts (Substrate Pallets)    │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Oracle Pallet Specification

### Module: `pallet_oracle`

**Purpose:** Manage external data feeds through approved reporters with stake-based accountability.

**Location:** `pallets/oracle/src/lib.rs`

---

### Extrinsic: `propose_reporter`

#### ISO 24643 Formal Specification

```
┌─────────────────────────────────────────────────────────────────────────────┐
│ FUNCTION: propose_reporter                                                   │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│ SIGNATURE:                                                                   │
│   fn propose_reporter(                                                       │
│       origin: OriginFor<T>,                                                 │
│       candidate: T::AccountId,                                              │
│       stake: BalanceOf<T>,                                                  │
│       supported_feeds: Vec<FeedId>,                                         │
│   ) -> DispatchResult                                                       │
│                                                                              │
│ PRECONDITIONS:                                                               │
│   P1: origin is signed by existing validator                                │
│   P2: candidate ∉ Reporters (not already a reporter)                        │
│   P3: candidate ∉ active ReporterProposals (no pending proposal)            │
│   P4: stake >= MinReporterStake                                             │
│   P5: |supported_feeds| >= 1 ∧ |supported_feeds| <= MaxFeedsPerReporter     │
│   P6: ∀ feed ∈ supported_feeds: feed ∈ RegisteredFeeds                      │
│                                                                              │
│ POSTCONDITIONS:                                                              │
│   Q1: ReporterProposals[next_id] = ReporterProposal {                       │
│         candidate, stake, supported_feeds, proposer: origin,                │
│         created_at: current_block, voting_ends: current_block + VotingPeriod│
│       }                                                                     │
│   Q2: NextReporterProposalId += 1                                           │
│   Q3: Event::ReporterProposed { proposal_id, candidate, stake } emitted     │
│                                                                              │
│ INVARIANTS:                                                                  │
│   I1: |Reporters| <= MaxReporters                                           │
│   I2: No duplicate proposals for same candidate                             │
│   I3: Total staked <= Total issuance                                        │
│                                                                              │
│ ERROR CONDITIONS:                                                            │
│   E1: !P1 → Error::NotValidator                                             │
│   E2: !P2 → Error::AlreadyReporter                                          │
│   E3: !P3 → Error::ProposalExists                                           │
│   E4: !P4 → Error::InsufficientStake                                        │
│   E5: !P5 → Error::InvalidFeedCount                                         │
│   E6: !P6 → Error::UnknownFeed                                              │
│                                                                              │
│ GAS/WEIGHT:                                                                  │
│   Base: 50_000_000                                                          │
│   Per feed: + 1_000_000 × |supported_feeds|                                 │
│   Storage: 1 write (proposal), 1 read (next_id)                             │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

#### Implementation Reference

```rust
/// ISO 24643 Smart Contract Specification
///
/// # Function: propose_reporter
///
/// ## Purpose
/// Allows validators to propose new oracle reporters for network approval.
///
/// ## Preconditions
/// - Caller is an existing validator (P1)
/// - Candidate is not already a reporter (P2)
/// - No pending proposal exists for candidate (P3)
/// - Stake meets minimum requirement (P4)
/// - Feed list is valid (P5, P6)
///
/// ## Postconditions
/// - ReporterProposal created with unique ID (Q1)
/// - Proposal ID counter incremented (Q2)
/// - ReporterProposed event emitted (Q3)
///
/// ## Invariants
/// - Total reporters never exceeds MaxReporters (I1)
/// - No duplicate proposals per candidate (I2)
#[pallet::call_index(0)]
#[pallet::weight(T::WeightInfo::propose_reporter(supported_feeds.len() as u32))]
pub fn propose_reporter(
    origin: OriginFor<T>,
    candidate: T::AccountId,
    stake: BalanceOf<T>,
    supported_feeds: BoundedVec<FeedId, T::MaxFeedsPerReporter>,
) -> DispatchResult {
    let proposer = ensure_signed(origin)?;

    // P1: Verify proposer is validator
    ensure!(
        T::ValidatorSet::is_validator(&proposer),
        Error::<T>::NotValidator
    );

    // P2: Check not already reporter
    ensure!(
        !Reporters::<T>::contains_key(&candidate),
        Error::<T>::AlreadyReporter
    );

    // P3: Check no pending proposal
    ensure!(
        !Self::has_pending_proposal(&candidate),
        Error::<T>::ProposalExists
    );

    // P4: Verify stake
    ensure!(
        stake >= T::MinReporterStake::get(),
        Error::<T>::InsufficientStake
    );

    // P5: Verify feed count
    ensure!(
        !supported_feeds.is_empty(),
        Error::<T>::InvalidFeedCount
    );

    // P6: Verify all feeds exist
    for feed in supported_feeds.iter() {
        ensure!(
            RegisteredFeeds::<T>::contains_key(feed),
            Error::<T>::UnknownFeed
        );
    }

    // Create proposal (Q1)
    let proposal_id = NextReporterProposalId::<T>::get();
    let current_block = frame_system::Pallet::<T>::block_number();

    let proposal = ReporterProposal {
        candidate: candidate.clone(),
        stake,
        supported_feeds: supported_feeds.clone(),
        proposer: proposer.clone(),
        created_at: current_block,
        voting_ends: current_block + T::VotingPeriod::get(),
        votes_for: BoundedVec::default(),
        votes_against: BoundedVec::default(),
    };

    ReporterProposals::<T>::insert(proposal_id, proposal);

    // Increment counter (Q2)
    NextReporterProposalId::<T>::put(proposal_id + 1);

    // Emit event (Q3)
    Self::deposit_event(Event::ReporterProposed {
        proposal_id,
        candidate,
        stake,
        proposer,
    });

    Ok(())
}
```

---

### Extrinsic: `vote_on_reporter`

#### ISO 24643 Formal Specification

```
┌─────────────────────────────────────────────────────────────────────────────┐
│ FUNCTION: vote_on_reporter                                                   │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│ SIGNATURE:                                                                   │
│   fn vote_on_reporter(                                                       │
│       origin: OriginFor<T>,                                                 │
│       proposal_id: u32,                                                     │
│       approve: bool,                                                        │
│   ) -> DispatchResult                                                       │
│                                                                              │
│ PRECONDITIONS:                                                               │
│   P1: origin is signed by existing validator                                │
│   P2: proposal_id ∈ ReporterProposals (proposal exists)                     │
│   P3: current_block < proposal.voting_ends (voting period active)           │
│   P4: origin ∉ proposal.votes_for ∧ origin ∉ proposal.votes_against         │
│       (validator has not already voted)                                     │
│                                                                              │
│ POSTCONDITIONS:                                                              │
│   Q1: if approve:                                                           │
│         proposal.votes_for.push(origin)                                     │
│       else:                                                                 │
│         proposal.votes_against.push(origin)                                 │
│   Q2: ReporterVotes[proposal_id][origin] = approve                          │
│   Q3: Event::ReporterVoteCast { proposal_id, voter, approve } emitted       │
│                                                                              │
│ INVARIANTS:                                                                  │
│   I1: Each validator votes at most once per proposal                        │
│   I2: Votes cannot be changed after casting                                 │
│                                                                              │
│ ERROR CONDITIONS:                                                            │
│   E1: !P1 → Error::NotValidator                                             │
│   E2: !P2 → Error::ProposalNotFound                                         │
│   E3: !P3 → Error::VotingEnded                                              │
│   E4: !P4 → Error::AlreadyVoted                                             │
│                                                                              │
│ GAS/WEIGHT:                                                                  │
│   Base: 30_000_000                                                          │
│   Storage: 1 read + 1 write (proposal), 1 write (votes)                     │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

### Extrinsic: `finalize_reporter_proposal`

#### ISO 24643 Formal Specification

```
┌─────────────────────────────────────────────────────────────────────────────┐
│ FUNCTION: finalize_reporter_proposal                                         │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│ SIGNATURE:                                                                   │
│   fn finalize_reporter_proposal(                                             │
│       origin: OriginFor<T>,                                                 │
│       proposal_id: u32,                                                     │
│   ) -> DispatchResult                                                       │
│                                                                              │
│ PRECONDITIONS:                                                               │
│   P1: origin is signed (any account can finalize)                           │
│   P2: proposal_id ∈ ReporterProposals                                       │
│   P3: current_block >= proposal.voting_ends (voting period ended)           │
│                                                                              │
│ POSTCONDITIONS:                                                              │
│   Let total_validators = |ValidatorSet|                                     │
│   Let votes_for = |proposal.votes_for|                                      │
│   Let threshold = (2 * total_validators) / 3 + 1                            │
│                                                                              │
│   Q1: if votes_for >= threshold:                                            │
│         Reporters[candidate] = Reporter {                                   │
│           account: candidate, stake, supported_feeds,                       │
│           reputation: 100, joined_at: current_block                         │
│         }                                                                   │
│         Lock stake from candidate's account                                 │
│         Event::ReporterApproved { proposal_id, candidate } emitted          │
│       else:                                                                 │
│         Event::ReporterRejected { proposal_id, candidate } emitted          │
│                                                                              │
│   Q2: ReporterProposals.remove(proposal_id)                                 │
│   Q3: ReporterVotes[proposal_id].clear()                                    │
│                                                                              │
│ INVARIANTS:                                                                  │
│   I1: Only proposals past voting period can be finalized                    │
│   I2: Each proposal finalized exactly once                                  │
│   I3: Stake locked only on approval                                         │
│                                                                              │
│ ERROR CONDITIONS:                                                            │
│   E1: !P2 → Error::ProposalNotFound                                         │
│   E2: !P3 → Error::VotingNotEnded                                           │
│                                                                              │
│ GAS/WEIGHT:                                                                  │
│   Base: 75_000_000                                                          │
│   If approved: + 25_000_000 (stake locking)                                 │
│   Storage: 1 read + 1 delete (proposal), potentially 1 write (reporter)     │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

### Extrinsic: `submit_signal`

#### ISO 24643 Formal Specification

```
┌─────────────────────────────────────────────────────────────────────────────┐
│ FUNCTION: submit_signal                                                      │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│ SIGNATURE:                                                                   │
│   fn submit_signal(                                                          │
│       origin: OriginFor<T>,                                                 │
│       signal: Signal<T>,                                                    │
│   ) -> DispatchResult                                                       │
│                                                                              │
│ PRECONDITIONS:                                                               │
│   P1: origin is signed by approved reporter                                 │
│   P2: signal.feed_id ∈ Reporters[origin].supported_feeds                    │
│   P3: signal.timestamp within acceptable range                              │
│       (current_time - MaxSignalAge <= signal.timestamp <= current_time)     │
│   P4: signal.data.len() <= MaxSignalDataSize                                │
│   P5: signal signature valid (Falcon-1024 verification)                     │
│                                                                              │
│ POSTCONDITIONS:                                                              │
│   Q1: Signals[signal_hash] = signal                                         │
│   Q2: Feeds[feed_id].last_value = signal.data                               │
│   Q3: Feeds[feed_id].last_update = current_block                            │
│   Q4: Reporters[origin].reputation updated based on signal quality          │
│   Q5: Event::SignalSubmitted { reporter, feed_id, signal_hash } emitted     │
│                                                                              │
│ INVARIANTS:                                                                  │
│   I1: Only approved reporters can submit                                    │
│   I2: Reporters can only submit to their registered feeds                   │
│   I3: Signal data immutable after submission                                │
│                                                                              │
│ ERROR CONDITIONS:                                                            │
│   E1: !P1 → Error::NotApprovedReporter                                      │
│   E2: !P2 → Error::FeedNotSupported                                         │
│   E3: !P3 → Error::SignalTooOld or Error::SignalFromFuture                  │
│   E4: !P4 → Error::SignalTooLarge                                           │
│   E5: !P5 → Error::InvalidSignature                                         │
│                                                                              │
│ GAS/WEIGHT:                                                                  │
│   Base: 100_000_000 (includes signature verification)                       │
│   Per byte: + 100 × signal.data.len()                                       │
│   Storage: 2 writes (signal, feed)                                          │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Validator Governance Pallet Specification

### Module: `pallet_validator_governance`

**Purpose:** Manage validator set through democratic voting among existing validators.

**Location:** `pallets/validator-governance/src/lib.rs`

---

### Extrinsic: `propose_validator`

```
┌─────────────────────────────────────────────────────────────────────────────┐
│ FUNCTION: propose_validator                                                  │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│ PRECONDITIONS:                                                               │
│   P1: origin is existing validator                                          │
│   P2: candidate ∉ ValidatorSet                                              │
│   P3: candidate has valid session keys registered                           │
│   P4: |ValidatorSet| < MaxValidators                                        │
│                                                                              │
│ POSTCONDITIONS:                                                              │
│   Q1: ValidatorProposal created                                             │
│   Q2: ValidatorProposed event emitted                                       │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Extrinsic: `vote_validator`

```
┌─────────────────────────────────────────────────────────────────────────────┐
│ FUNCTION: vote_validator                                                     │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│ PRECONDITIONS:                                                               │
│   P1: origin is existing validator                                          │
│   P2: proposal exists and voting active                                     │
│   P3: origin has not voted on this proposal                                 │
│                                                                              │
│ POSTCONDITIONS:                                                              │
│   Q1: Vote recorded                                                         │
│   Q2: If threshold reached, validator added/removed immediately             │
│   Q3: ValidatorVoteCast event emitted                                       │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Notarial Pallet Specification

### Module: `pallet_notarial`

**Purpose:** Provide tamper-evident timestamping and attestation of documents.

**Location:** `pallets/notarial/src/lib.rs`

---

### Extrinsic: `attest_document`

```
┌─────────────────────────────────────────────────────────────────────────────┐
│ FUNCTION: attest_document                                                    │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│ SIGNATURE:                                                                   │
│   fn attest_document(                                                        │
│       origin: OriginFor<T>,                                                 │
│       document_hash: H256,                                                  │
│       metadata: BoundedVec<u8, T::MaxMetadataSize>,                         │
│   ) -> DispatchResult                                                       │
│                                                                              │
│ PRECONDITIONS:                                                               │
│   P1: origin is signed                                                      │
│   P2: document_hash not already attested by this account                    │
│   P3: metadata.len() <= MaxMetadataSize                                     │
│   P4: attester has sufficient balance for fee                               │
│                                                                              │
│ POSTCONDITIONS:                                                              │
│   Q1: Attestations[attestation_id] = Attestation {                          │
│         attester: origin,                                                   │
│         document_hash,                                                      │
│         metadata,                                                           │
│         timestamp: current_block,                                           │
│         revoked: false                                                      │
│       }                                                                     │
│   Q2: AttestationFee deducted from attester                                 │
│   Q3: Event::DocumentAttested { attestation_id, attester, document_hash }   │
│                                                                              │
│ INVARIANTS:                                                                  │
│   I1: Attestation timestamp immutable                                       │
│   I2: Document hash immutable                                               │
│   I3: Each attestation has unique ID                                        │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Upgrade Mechanism

### Forkless Runtime Upgrades

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    RUNTIME UPGRADE PROCESS                                   │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  1. PROPOSAL                                                                │
│     └── Validator proposes new WASM runtime blob                            │
│         └── Runtime hash published for verification                         │
│                                                                              │
│  2. VOTING                                                                  │
│     └── Validators review and vote on upgrade                               │
│         └── 2/3+ approval required                                          │
│                                                                              │
│  3. ENACTMENT                                                               │
│     └── After approval + delay period:                                      │
│         └── system.setCode(new_wasm) executed                               │
│                                                                              │
│  4. MIGRATION                                                               │
│     └── on_runtime_upgrade() hooks execute                                  │
│         └── Storage migrations run atomically                               │
│                                                                              │
│  5. VERIFICATION                                                            │
│     └── New runtime active from next block                                  │
│         └── spec_version incremented                                        │
│                                                                              │
│  SAFETY GUARANTEES:                                                         │
│  • Atomic upgrade (all-or-nothing)                                          │
│  • Revertible if migration fails                                            │
│  • No network fork required                                                 │
│  • Backwards-compatible storage                                             │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Storage Migrations

```rust
/// ISO 24643 Upgrade Specification
///
/// Storage migrations must:
/// 1. Be idempotent (safe to run multiple times)
/// 2. Have bounded weight
/// 3. Handle missing data gracefully
/// 4. Emit migration events for auditability

pub struct MigrateOracleV1ToV2;

impl OnRuntimeUpgrade for MigrateOracleV1ToV2 {
    fn on_runtime_upgrade() -> Weight {
        // Check if migration needed
        if StorageVersion::get::<Pallet<T>>() != 1 {
            return Weight::zero();
        }

        let mut migrated = 0u32;

        // Migrate storage format
        OldReporters::<T>::drain().for_each(|(key, old_value)| {
            let new_value = Reporter {
                account: old_value.account,
                stake: old_value.stake,
                supported_feeds: old_value.feeds.try_into().unwrap_or_default(),
                reputation: 100, // New field with default
                joined_at: old_value.joined_at,
            };
            Reporters::<T>::insert(key, new_value);
            migrated += 1;
        });

        // Update storage version
        StorageVersion::new(2).put::<Pallet<T>>();

        // Emit event
        Pallet::<T>::deposit_event(Event::StorageMigrated {
            from_version: 1,
            to_version: 2,
            items_migrated: migrated,
        });

        T::DbWeight::get().reads_writes(migrated as u64, migrated as u64 + 1)
    }
}
```

---

## Testing Requirements

### Unit Test Coverage

| Pallet | Minimum Coverage | Critical Paths |
|--------|------------------|----------------|
| oracle | 90% | submit_signal, finalize_proposal |
| validator-governance | 90% | vote_validator, threshold logic |
| notarial | 85% | attest_document, verify |

### Integration Test Scenarios

1. **Reporter Lifecycle**
   - Propose → Vote → Approve → Submit Signal → Slash

2. **Validator Lifecycle**
   - Propose → Vote → Approve → Produce Blocks → Remove

3. **Upgrade Lifecycle**
   - Propose → Vote → Enact → Migrate → Verify

---

## References

- [ISO 24643:2023](https://www.iso.org/standard/78963.html) - Overview of Smart Contracts
- [ISO/CD 24642](https://www.iso.org/standard/79140.html) - Smart Contract Security Guidelines (Draft)
- [Substrate Pallet Development](https://docs.substrate.io/build/pallet-development/)
