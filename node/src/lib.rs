//! QuantumHarmony Node Library
//!
//! This module exposes the node's internal components for use by external binaries
//! like chain spec generators and key management tools.

mod benchmarking;
pub mod chain_spec;
mod cli;
mod client;
mod coherence_gadget;
mod coherence_gossip;
mod coherence_inherent;
mod coherence_justification;
mod command;
pub mod entropy_gossip;
mod eth;
mod falcon_crypto;
mod pqtg_client;
mod priority_queue_rpc;
mod qpp;
pub mod quantum_manager;
pub mod pqc_oracle;
mod qpp_integration;
mod qssh_queue_manager;
mod quantum_entropy;
pub mod quantum_p2p;
mod quantum_vault;
pub mod rpc;
pub mod service;
mod software_entropy_vault;
mod test_accounts;
mod threshold_qrng;
mod unified_vault;
mod wallet_server;
pub mod sphincs_keygen;
pub mod segmented_pool;
pub mod parallel_proposer;
pub mod high_perf_verify;
pub mod sphincs_parallel_verify;
pub mod optimistic_executor;

// New modules for threshold QRNG network integration
pub mod round_coordinator;
pub mod test_account_setup;
