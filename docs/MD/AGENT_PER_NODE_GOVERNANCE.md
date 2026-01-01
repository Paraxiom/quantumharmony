# Agent-Per-Node Governance Architecture

## Executive Summary

This document specifies a decentralized governance system where each validator node is paired with an autonomous AI agent. These agents collaborate to manage runtime upgrades, parameter tuning, and incident response without centralized sudo control.

```
┌────────────────────────────────────────────────────────────────────────────┐
│                    QUANTUMHARMONY AGENT GOVERNANCE                         │
├────────────────────────────────────────────────────────────────────────────┤
│                                                                            │
│   ┌──────────────┐    ┌──────────────┐    ┌──────────────┐                │
│   │   ALICE      │    │    BOB       │    │   CHARLIE    │                │
│   │  Validator   │    │  Validator   │    │  Validator   │                │
│   │  51.79.26.123│    │ 51.79.26.168 │    │ 209.38.225.4 │                │
│   └──────┬───────┘    └──────┬───────┘    └──────┬───────┘                │
│          │                   │                   │                         │
│   ┌──────▼───────┐    ┌──────▼───────┐    ┌──────▼───────┐                │
│   │ ALICE AGENT  │◄──►│  BOB AGENT   │◄──►│CHARLIE AGENT │                │
│   │              │    │              │    │              │                │
│   │ - Monitor    │    │ - Monitor    │    │ - Monitor    │                │
│   │ - Propose    │    │ - Propose    │    │ - Propose    │                │
│   │ - Vote       │    │ - Vote       │    │ - Vote       │                │
│   │ - Execute    │    │ - Execute    │    │ - Execute    │                │
│   └──────────────┘    └──────────────┘    └──────────────┘                │
│          │                   │                   │                         │
│          └───────────────────┼───────────────────┘                         │
│                              ▼                                             │
│                    ┌─────────────────┐                                     │
│                    │   CONSENSUS     │                                     │
│                    │   THRESHOLD     │                                     │
│                    │    (2/3 + 1)    │                                     │
│                    └────────┬────────┘                                     │
│                             ▼                                              │
│                    ┌─────────────────┐                                     │
│                    │   ON-CHAIN      │                                     │
│                    │   EXECUTION     │                                     │
│                    └─────────────────┘                                     │
│                                                                            │
└────────────────────────────────────────────────────────────────────────────┘
```

## 1. Agent Architecture

### 1.1 Agent Components

Each validator node runs a paired agent with these components:

```
┌─────────────────────────────────────────────────────────────┐
│                     VALIDATOR AGENT                         │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  ┌─────────────────┐  ┌─────────────────┐                  │
│  │   MONITOR       │  │   PROPOSER      │                  │
│  │                 │  │                 │                  │
│  │ • Block health  │  │ • Runtime upgr  │                  │
│  │ • Peer count    │  │ • Param changes │                  │
│  │ • Memory/CPU    │  │ • Emergency fix │                  │
│  │ • Finality lag  │  │ • New validator │                  │
│  └────────┬────────┘  └────────┬────────┘                  │
│           │                    │                            │
│           ▼                    ▼                            │
│  ┌─────────────────────────────────────────┐               │
│  │              DECISION ENGINE             │               │
│  │                                          │               │
│  │  • Evaluate proposals from other agents │               │
│  │  • Apply governance rules               │               │
│  │  • Sign votes with validator key        │               │
│  │  • Threshold verification               │               │
│  └─────────────────────────────────────────┘               │
│           │                    │                            │
│           ▼                    ▼                            │
│  ┌─────────────────┐  ┌─────────────────┐                  │
│  │   P2P GOSSIP    │  │   EXECUTOR      │                  │
│  │                 │  │                 │                  │
│  │ • Agent-to-agent│  │ • Submit extrin │                  │
│  │ • Proposal sync │  │ • Runtime swap  │                  │
│  │ • Vote collect  │  │ • Verify result │                  │
│  └─────────────────┘  └─────────────────┘                  │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 1.2 Agent Runtime

```rust
// Agent configuration
pub struct AgentConfig {
    /// Validator account this agent represents
    pub validator_account: AccountId,

    /// SPHINCS+ keypair for signing proposals/votes
    pub signing_key: SphincsKeypair,

    /// RPC endpoint of local node
    pub node_rpc: String,

    /// Peer agents to communicate with
    pub peer_agents: Vec<AgentPeer>,

    /// Governance thresholds
    pub thresholds: GovernanceThresholds,
}

pub struct GovernanceThresholds {
    /// Runtime upgrade requires 2/3 + 1 validators
    pub runtime_upgrade: Fraction,  // 2/3

    /// Parameter change requires majority
    pub parameter_change: Fraction,  // 1/2

    /// Emergency action requires unanimity
    pub emergency_action: Fraction,  // 1/1

    /// Proposal timeout in blocks
    pub proposal_timeout: BlockNumber,  // 100 blocks
}
```

## 2. Communication Protocol

### 2.1 Agent-to-Agent Messages

Agents communicate over a dedicated gossip channel separate from block propagation:

```rust
/// Agent gossip message types
#[derive(Encode, Decode)]
pub enum AgentMessage {
    /// New governance proposal
    Proposal(GovernanceProposal),

    /// Vote on existing proposal
    Vote(ProposalVote),

    /// Heartbeat with node status
    Heartbeat(AgentStatus),

    /// Emergency alert
    Alert(EmergencyAlert),
}

#[derive(Encode, Decode)]
pub struct GovernanceProposal {
    /// Unique proposal ID (hash of content)
    pub id: H256,

    /// Type of proposal
    pub proposal_type: ProposalType,

    /// Proposing agent's validator account
    pub proposer: AccountId,

    /// SPHINCS+ signature from proposer
    pub signature: SphincsSignature,

    /// Block number when proposed
    pub proposed_at: BlockNumber,

    /// Detailed proposal content
    pub content: ProposalContent,
}

#[derive(Encode, Decode)]
pub enum ProposalType {
    /// Runtime WASM upgrade
    RuntimeUpgrade {
        wasm_hash: H256,
        wasm_url: String,
        changelog: String,
    },

    /// Parameter change (e.g., block time, fees)
    ParameterChange {
        pallet: String,
        parameter: String,
        old_value: Vec<u8>,
        new_value: Vec<u8>,
    },

    /// Add new validator
    AddValidator {
        account: AccountId,
        peer_id: PeerId,
    },

    /// Remove validator
    RemoveValidator {
        account: AccountId,
        reason: String,
    },

    /// Emergency pause
    EmergencyPause {
        reason: String,
        duration_blocks: BlockNumber,
    },
}

#[derive(Encode, Decode)]
pub struct ProposalVote {
    /// Proposal being voted on
    pub proposal_id: H256,

    /// Voter's validator account
    pub voter: AccountId,

    /// Vote decision
    pub decision: VoteDecision,

    /// SPHINCS+ signature
    pub signature: SphincsSignature,

    /// Block number of vote
    pub voted_at: BlockNumber,
}

#[derive(Encode, Decode)]
pub enum VoteDecision {
    /// Approve the proposal
    Approve,

    /// Reject with reason
    Reject(String),

    /// Abstain (counts toward quorum but not threshold)
    Abstain,
}
```

### 2.2 Gossip Protocol

```
┌────────────────────────────────────────────────────────────────┐
│                    AGENT GOSSIP PROTOCOL                       │
├────────────────────────────────────────────────────────────────┤
│                                                                │
│  Port: 30334 (P2P + 1)                                        │
│  Protocol: /quantumharmony/agent/1.0.0                        │
│  Encryption: Noise protocol with SPHINCS+ identity            │
│                                                                │
│  Message Flow:                                                 │
│                                                                │
│  1. PROPOSAL                                                   │
│     Alice Agent ──proposal──► Bob Agent                       │
│                 ──proposal──► Charlie Agent                   │
│                                                                │
│  2. ACKNOWLEDGMENT                                             │
│     Bob Agent ──ack──► Alice Agent                            │
│     Charlie Agent ──ack──► Alice Agent                        │
│                                                                │
│  3. VOTING                                                     │
│     Bob Agent ──vote(approve)──► All                          │
│     Charlie Agent ──vote(approve)──► All                      │
│                                                                │
│  4. THRESHOLD REACHED                                          │
│     Any agent detects 2/3 approval                            │
│     ──threshold_reached──► All                                │
│                                                                │
│  5. EXECUTION                                                  │
│     First agent to see threshold submits extrinsic            │
│     Other agents verify on-chain execution                    │
│                                                                │
└────────────────────────────────────────────────────────────────┘
```

## 3. Threshold Governance Mechanism

### 3.1 Proposal Lifecycle

```
┌─────────────────────────────────────────────────────────────────┐
│                    PROPOSAL LIFECYCLE                           │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌──────────┐    ┌──────────┐    ┌──────────┐    ┌──────────┐  │
│  │ CREATED  │───►│ VOTING   │───►│ APPROVED │───►│ EXECUTED │  │
│  └──────────┘    └──────────┘    └──────────┘    └──────────┘  │
│       │               │               │               │         │
│       │               │               │               │         │
│       │          ┌────▼────┐          │               │         │
│       │          │ REJECTED│          │               │         │
│       │          └─────────┘          │               │         │
│       │               │               │               │         │
│       │          ┌────▼────┐          │               │         │
│       └─────────►│ EXPIRED │◄─────────┘               │         │
│                  └─────────┘                          │         │
│                       │                               │         │
│                  ┌────▼────┐                          │         │
│                  │ FAILED  │◄─────────────────────────┘         │
│                  └─────────┘                                    │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘

States:
  CREATED  - Proposal submitted by an agent
  VOTING   - Collecting votes from other agents
  APPROVED - Threshold reached, ready for execution
  REJECTED - Rejection threshold reached
  EXPIRED  - Timeout reached without decision
  EXECUTED - Successfully executed on-chain
  FAILED   - Execution failed (reverted)
```

### 3.2 Threshold Calculation

```rust
impl GovernanceThresholds {
    /// Calculate if proposal has reached approval threshold
    pub fn is_approved(&self, proposal_type: &ProposalType, votes: &[ProposalVote], total_validators: u32) -> bool {
        let threshold = match proposal_type {
            ProposalType::RuntimeUpgrade { .. } => self.runtime_upgrade,
            ProposalType::ParameterChange { .. } => self.parameter_change,
            ProposalType::AddValidator { .. } => self.parameter_change,
            ProposalType::RemoveValidator { .. } => self.runtime_upgrade,
            ProposalType::EmergencyPause { .. } => self.emergency_action,
        };

        let approvals = votes.iter()
            .filter(|v| matches!(v.decision, VoteDecision::Approve))
            .count() as u32;

        // threshold.numerator / threshold.denominator
        approvals * threshold.denominator >= total_validators * threshold.numerator
    }

    /// Calculate if proposal has been rejected
    pub fn is_rejected(&self, proposal_type: &ProposalType, votes: &[ProposalVote], total_validators: u32) -> bool {
        let rejections = votes.iter()
            .filter(|v| matches!(v.decision, VoteDecision::Reject(_)))
            .count() as u32;

        // More than 1/3 rejections = cannot reach 2/3 approval
        rejections * 3 > total_validators
    }
}
```

### 3.3 On-Chain Governance Pallet

```rust
#[frame_support::pallet]
pub mod pallet_agent_governance {
    use super::*;

    #[pallet::config]
    pub trait Config: frame_system::Config {
        type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

        /// Minimum validators for quorum
        type MinQuorum: Get<u32>;

        /// Proposal timeout in blocks
        type ProposalTimeout: Get<BlockNumberFor<Self>>;
    }

    #[pallet::storage]
    pub type Proposals<T: Config> = StorageMap<
        _,
        Blake2_128Concat,
        H256,  // proposal_id
        OnChainProposal<T>,
    >;

    #[pallet::storage]
    pub type Votes<T: Config> = StorageDoubleMap<
        _,
        Blake2_128Concat,
        H256,  // proposal_id
        Blake2_128Concat,
        T::AccountId,  // voter
        OnChainVote,
    >;

    #[pallet::call]
    impl<T: Config> Pallet<T> {
        /// Submit a proposal (called by agent)
        #[pallet::weight(10_000)]
        pub fn submit_proposal(
            origin: OriginFor<T>,
            proposal_id: H256,
            proposal_type: ProposalType,
            signature: Vec<u8>,
        ) -> DispatchResult {
            let proposer = ensure_signed(origin)?;
            ensure!(Self::is_validator(&proposer), Error::<T>::NotValidator);

            // Verify SPHINCS+ signature
            ensure!(
                Self::verify_sphincs_signature(&proposer, &proposal_id, &signature),
                Error::<T>::InvalidSignature
            );

            // Store proposal
            let proposal = OnChainProposal {
                proposer,
                proposal_type,
                proposed_at: frame_system::Pallet::<T>::block_number(),
                status: ProposalStatus::Voting,
            };
            Proposals::<T>::insert(proposal_id, proposal);

            Self::deposit_event(Event::ProposalSubmitted { proposal_id });
            Ok(())
        }

        /// Submit a vote (called by agent)
        #[pallet::weight(10_000)]
        pub fn submit_vote(
            origin: OriginFor<T>,
            proposal_id: H256,
            decision: VoteDecision,
            signature: Vec<u8>,
        ) -> DispatchResult {
            let voter = ensure_signed(origin)?;
            ensure!(Self::is_validator(&voter), Error::<T>::NotValidator);

            // Verify signature
            let vote_hash = Self::hash_vote(&proposal_id, &decision);
            ensure!(
                Self::verify_sphincs_signature(&voter, &vote_hash, &signature),
                Error::<T>::InvalidSignature
            );

            // Store vote
            Votes::<T>::insert(proposal_id, voter.clone(), OnChainVote {
                decision: decision.clone(),
                voted_at: frame_system::Pallet::<T>::block_number(),
            });

            // Check if threshold reached
            Self::check_and_execute(proposal_id)?;

            Self::deposit_event(Event::VoteSubmitted { proposal_id, voter, decision });
            Ok(())
        }

        /// Execute approved proposal (called by any agent after threshold)
        #[pallet::weight(100_000)]
        pub fn execute_proposal(
            origin: OriginFor<T>,
            proposal_id: H256,
        ) -> DispatchResult {
            let executor = ensure_signed(origin)?;
            ensure!(Self::is_validator(&executor), Error::<T>::NotValidator);

            let proposal = Proposals::<T>::get(proposal_id)
                .ok_or(Error::<T>::ProposalNotFound)?;

            ensure!(
                proposal.status == ProposalStatus::Approved,
                Error::<T>::NotApproved
            );

            // Execute based on type
            match proposal.proposal_type {
                ProposalType::RuntimeUpgrade { wasm_hash, .. } => {
                    Self::do_runtime_upgrade(wasm_hash)?;
                },
                ProposalType::ParameterChange { pallet, parameter, new_value, .. } => {
                    Self::do_parameter_change(pallet, parameter, new_value)?;
                },
                ProposalType::AddValidator { account, .. } => {
                    Self::do_add_validator(account)?;
                },
                ProposalType::RemoveValidator { account, .. } => {
                    Self::do_remove_validator(account)?;
                },
                ProposalType::EmergencyPause { duration_blocks, .. } => {
                    Self::do_emergency_pause(duration_blocks)?;
                },
            }

            Proposals::<T>::mutate(proposal_id, |p| {
                if let Some(prop) = p {
                    prop.status = ProposalStatus::Executed;
                }
            });

            Self::deposit_event(Event::ProposalExecuted { proposal_id, executor });
            Ok(())
        }
    }
}
```

## 4. Agent Implementation

### 4.1 Agent Service (Rust)

```rust
// agent/src/main.rs

use quantumharmony_agent::{
    Agent, AgentConfig, GovernanceThresholds,
    monitor::NodeMonitor,
    proposer::Proposer,
    voter::Voter,
    gossip::GossipNetwork,
    executor::Executor,
};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Load configuration
    let config = AgentConfig::from_env()?;

    // Initialize components
    let monitor = NodeMonitor::new(&config.node_rpc).await?;
    let gossip = GossipNetwork::new(&config.peer_agents, &config.signing_key).await?;
    let proposer = Proposer::new(&config);
    let voter = Voter::new(&config);
    let executor = Executor::new(&config.node_rpc, &config.signing_key);

    // Create agent
    let agent = Agent::new(
        config,
        monitor,
        gossip,
        proposer,
        voter,
        executor,
    );

    // Run agent loop
    agent.run().await
}

impl Agent {
    pub async fn run(&self) -> Result<(), AgentError> {
        loop {
            tokio::select! {
                // Monitor node health
                status = self.monitor.check_health() => {
                    self.handle_health_check(status).await?;
                }

                // Receive gossip messages
                msg = self.gossip.recv() => {
                    self.handle_gossip_message(msg).await?;
                }

                // Check for upgrade opportunities
                _ = tokio::time::sleep(Duration::from_secs(60)) => {
                    self.check_for_upgrades().await?;
                }
            }
        }
    }

    async fn handle_gossip_message(&self, msg: AgentMessage) -> Result<(), AgentError> {
        match msg {
            AgentMessage::Proposal(proposal) => {
                // Verify proposal signature
                if !self.verify_proposal(&proposal) {
                    return Ok(());
                }

                // Evaluate and vote
                let decision = self.voter.evaluate(&proposal).await?;
                let vote = self.create_vote(&proposal.id, decision);

                // Broadcast vote
                self.gossip.broadcast(AgentMessage::Vote(vote)).await?;

                // Submit to chain
                self.executor.submit_vote(&proposal.id, &decision).await?;
            }

            AgentMessage::Vote(vote) => {
                // Collect vote
                self.voter.record_vote(vote.clone());

                // Check threshold
                if self.voter.threshold_reached(&vote.proposal_id) {
                    self.executor.execute_proposal(&vote.proposal_id).await?;
                }
            }

            AgentMessage::Heartbeat(status) => {
                self.update_peer_status(status);
            }

            AgentMessage::Alert(alert) => {
                self.handle_emergency_alert(alert).await?;
            }
        }
        Ok(())
    }
}
```

### 4.2 Decision Engine

```rust
// agent/src/voter.rs

impl Voter {
    /// Evaluate a proposal and decide how to vote
    pub async fn evaluate(&self, proposal: &GovernanceProposal) -> Result<VoteDecision, VoterError> {
        match &proposal.proposal_type {
            ProposalType::RuntimeUpgrade { wasm_hash, wasm_url, changelog } => {
                self.evaluate_runtime_upgrade(wasm_hash, wasm_url, changelog).await
            }

            ProposalType::ParameterChange { pallet, parameter, old_value, new_value } => {
                self.evaluate_parameter_change(pallet, parameter, old_value, new_value)
            }

            ProposalType::AddValidator { account, peer_id } => {
                self.evaluate_add_validator(account, peer_id).await
            }

            ProposalType::RemoveValidator { account, reason } => {
                self.evaluate_remove_validator(account, reason)
            }

            ProposalType::EmergencyPause { reason, duration_blocks } => {
                self.evaluate_emergency_pause(reason, *duration_blocks)
            }
        }
    }

    async fn evaluate_runtime_upgrade(
        &self,
        wasm_hash: &H256,
        wasm_url: &str,
        changelog: &str,
    ) -> Result<VoteDecision, VoterError> {
        // 1. Download WASM
        let wasm = self.download_wasm(wasm_url).await?;

        // 2. Verify hash matches
        let computed_hash = sp_core::blake2_256(&wasm);
        if computed_hash != wasm_hash.as_bytes() {
            return Ok(VoteDecision::Reject("WASM hash mismatch".into()));
        }

        // 3. Validate WASM structure
        if !self.validate_wasm_structure(&wasm) {
            return Ok(VoteDecision::Reject("Invalid WASM structure".into()));
        }

        // 4. Check version increment
        if !self.check_version_increment(&wasm) {
            return Ok(VoteDecision::Reject("Version not incremented".into()));
        }

        // 5. Simulate execution (dry run)
        if let Err(e) = self.simulate_upgrade(&wasm).await {
            return Ok(VoteDecision::Reject(format!("Simulation failed: {}", e)));
        }

        // 6. Approved
        Ok(VoteDecision::Approve)
    }
}
```

## 5. Integration with Existing Pallets

### 5.1 Pallet Dependencies

```
┌────────────────────────────────────────────────────────────────┐
│                    PALLET INTEGRATION                          │
├────────────────────────────────────────────────────────────────┤
│                                                                │
│  pallet-agent-governance                                       │
│         │                                                      │
│         ├──► pallet-validator-governance (existing)            │
│         │         └── Validator set management                 │
│         │                                                      │
│         ├──► substrate-validator-set (existing)                │
│         │         └── Session-based validator rotation         │
│         │                                                      │
│         ├──► frame-system                                      │
│         │         └── set_code for runtime upgrades            │
│         │                                                      │
│         └──► pallet-sphincs-keystore (existing)                │
│                   └── SPHINCS+ signature verification          │
│                                                                │
└────────────────────────────────────────────────────────────────┘
```

### 5.2 Runtime Configuration

```rust
// runtime/src/lib.rs

impl pallet_agent_governance::Config for Runtime {
    type RuntimeEvent = RuntimeEvent;
    type MinQuorum = ConstU32<2>;  // At least 2 validators must vote
    type ProposalTimeout = ConstU64<100>;  // 100 blocks timeout
}

// Governance origin for privileged operations
pub type AgentGovernanceOrigin = EnsureProportionAtLeast<
    AccountId,
    ValidatorCollective,
    2, 3  // 2/3 threshold
>;

// Replace sudo with agent governance
impl frame_system::Config for Runtime {
    // ... other config
    type SetCodeOrigin = AgentGovernanceOrigin;
}
```

## 6. Security Considerations

### 6.1 Threat Model

| Threat | Mitigation |
|--------|------------|
| Rogue agent | Threshold requires 2/3 - single agent cannot act alone |
| Key compromise | SPHINCS+ post-quantum signatures, hardware key storage |
| Replay attacks | Proposal IDs include block number, votes are one-time |
| Eclipse attack | Agents connect to multiple peers, verify on-chain state |
| DoS on agent | Rate limiting, proof-of-work for proposals |

### 6.2 Key Management

```
┌────────────────────────────────────────────────────────────────┐
│                    AGENT KEY HIERARCHY                         │
├────────────────────────────────────────────────────────────────┤
│                                                                │
│  ┌─────────────────┐                                          │
│  │ VALIDATOR KEY   │  (Consensus: AURA/GRANDPA)               │
│  │ (Session Keys)  │  - Block production                       │
│  └────────┬────────┘  - Finality voting                        │
│           │                                                    │
│  ┌────────▼────────┐                                          │
│  │ AGENT KEY       │  (Governance: SPHINCS+)                  │
│  │ (Derived)       │  - Proposal signing                       │
│  └────────┬────────┘  - Vote signing                           │
│           │                                                    │
│  ┌────────▼────────┐                                          │
│  │ GOSSIP KEY      │  (P2P: Ed25519)                          │
│  │ (Ephemeral)     │  - Agent-to-agent encryption              │
│  └─────────────────┘  - Rotated periodically                   │
│                                                                │
└────────────────────────────────────────────────────────────────┘
```

## 7. Deployment Plan

### Phase 1: Agent Infrastructure (Week 1-2)
- [ ] Implement agent binary with monitor and gossip
- [ ] Deploy agents alongside existing validators
- [ ] Establish agent-to-agent communication

### Phase 2: On-Chain Governance (Week 3-4)
- [ ] Implement `pallet-agent-governance`
- [ ] Add to runtime (behind feature flag)
- [ ] Test with simulated proposals

### Phase 3: Sudo Migration (Week 5-6)
- [ ] Transfer runtime upgrade rights to governance pallet
- [ ] Transfer parameter change rights to governance pallet
- [ ] Deprecate sudo (keep for emergency only)

### Phase 4: Full Decentralization (Week 7-8)
- [ ] Remove sudo completely
- [ ] Enable emergency pause mechanism
- [ ] Monitor and tune thresholds

## 8. Agent Commands

```bash
# Start agent
quantumharmony-agent \
  --validator-account 5GrwvaEF... \
  --node-rpc ws://localhost:9944 \
  --agent-port 30334 \
  --peers /ip4/51.79.26.168/tcp/30334/p2p/12D3KooW... \
  --peers /ip4/209.38.225.4/tcp/30334/p2p/12D3KooW...

# Check agent status
quantumharmony-agent status

# Propose runtime upgrade
quantumharmony-agent propose upgrade \
  --wasm-file ./runtime.wasm \
  --changelog "Bug fixes and performance improvements"

# View active proposals
quantumharmony-agent proposals list

# Vote on proposal
quantumharmony-agent vote --proposal-id 0x1234... --approve
```

## 9. Monitoring Dashboard

Add to PROOFS tab in dashboard:

```javascript
// Governance status display
async function fetchGovernanceStatus() {
    const activeProposals = await rpc('agentGovernance_activeProposals', []);
    const agentStatus = await rpc('agentGovernance_agentStatus', []);

    return {
        proposals: activeProposals,
        agents: agentStatus,
        consensusHealth: calculateConsensusHealth(agentStatus)
    };
}
```

---

**Document Version:** 1.0
**Author:** Claude Opus 4.5
**Date:** 2025-12-31
