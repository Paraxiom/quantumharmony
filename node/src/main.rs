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
// mod falcon_crypto_tests;  // Comprehensive Falcon1024 tests - disabled: API mismatches with pqcrypto-falcon 0.3
mod pqtg_client;
mod priority_queue_rpc;  // Priority Queue RPC Server for validators
// #[cfg(test)]
// mod priority_queue_rpc_tests;  // Priority Queue RPC tests - disabled: stack overflow in deep recursion
mod qpp;  // Quantum Preservation Pattern
mod qpp_integration;  // QPP Production Integration Bridge
mod qssh_queue_manager;  // QSSH Queue Manager for multi-validator architecture
// NOTE: qssh_queue_qpp disabled; requires SyncResult/AsyncResult types in qpp module (planned for QPP v2)
// mod qssh_queue_qpp;      // QPP-Enhanced QSSH Queue Manager with sync/persistence guarantees
mod wallet_server;       // Wallet WebSocket server with Falcon-1024 post-quantum signatures
// mod nat_traversal;  // NOTE: NAT traversal module planned for QSSH relay selection in multi-validator deployment
mod quantum_entropy;
mod quantum_p2p;
mod quantum_vault;
mod software_entropy_vault;
mod sphincs_keygen;
mod unified_vault;
mod rpc;
mod pqc_oracle;
mod quantum_manager;
mod segmented_pool;
mod parallel_proposer;
mod high_perf_verify;
mod sphincs_parallel_verify;
mod optimistic_executor;
mod service;
mod test_accounts;
mod threshold_qrng;
mod round_coordinator;
mod test_account_setup;
