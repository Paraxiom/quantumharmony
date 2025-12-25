//! Substrate QuantumHarmony node.

#![warn(missing_docs)]

fn main() -> sc_cli::Result<()> {
    command::run()
}

mod benchmarking;
mod chain_spec;
mod cli;
mod client;
mod coherence_gadget;
mod coherence_gossip;
mod coherence_inherent;
mod coherence_justification;
mod command;
mod entropy_gossip;
mod eth;
mod falcon_crypto;
// #[cfg(test)]
// mod falcon_crypto_tests;  // Comprehensive Falcon1024 tests - TODO: Fix API mismatches
mod pqtg_client;
mod priority_queue_rpc;  // Priority Queue RPC Server for validators
// #[cfg(test)]
// mod priority_queue_rpc_tests;  // Priority Queue RPC tests - TODO: Fix stack overflow issues
mod qpp;  // Quantum Preservation Pattern
mod qpp_integration;  // QPP Production Integration Bridge
mod qssh_queue_manager;  // QSSH Queue Manager for multi-validator architecture
// TODO: qssh_queue_qpp needs SyncResult/AsyncResult types that don't exist yet
// mod qssh_queue_qpp;      // QPP-Enhanced QSSH Queue Manager with sync/persistence guarantees
mod wallet_server;       // Wallet WebSocket server with Falcon-1024 post-quantum signatures
// mod nat_traversal;  // TODO: Will be created for QSSH relay selection
mod quantum_entropy;
mod quantum_p2p;
mod quantum_vault;
mod software_entropy_vault;
mod sphincs_keygen;
mod unified_vault;
mod rpc;
mod segmented_pool;
mod parallel_proposer;
mod high_perf_verify;
mod sphincs_parallel_verify;
mod optimistic_executor;
mod service;
mod test_accounts;
mod threshold_qrng;
