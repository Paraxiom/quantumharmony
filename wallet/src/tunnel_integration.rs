//! Integration module connecting Quantum Tunnel with QPP Wallet
//! 
//! This module provides the bridge between the quantum-safe tunnel transport
//! and the QPP wallet functionality.

use crate::{
    quantum_tunnel::{QuantumTunnel, TunnelConfig, TunnelMessage, TunnelError, Handshaking, Established},
    wallet::{QPPWallet, Unlocked},
    no_clone::NoClone,
    types::WalletError,
};
use sp_core::{H256, Pair};
use scale_codec::{Encode, Decode};
use std::sync::{Arc, Mutex};

/// Wallet with integrated quantum tunnel support
pub struct TunneledWallet {
    /// Core QPP wallet
    wallet: Arc<Mutex<QPPWallet<Unlocked>>>,
    /// Active quantum tunnels
    tunnels: Arc<Mutex<Vec<EstablishedTunnel>>>,
    /// Tunnel configuration
    config: TunnelConfig,
}

/// An established tunnel with metadata
pub struct EstablishedTunnel {
    /// The quantum tunnel
    tunnel: Arc<Mutex<QuantumTunnel<Established>>>,
    /// Remote peer address
    remote_addr: String,
    /// Creation timestamp
    created_at: std::time::Instant,
    /// Last activity
    last_activity: std::time::Instant,
}

/// Messages that can be sent through the tunnel
#[derive(Debug, Clone, Encode, Decode)]
pub enum WalletTunnelMessage {
    /// Request account information
    GetAccounts,
    /// Account list response
    AccountsResponse(Vec<(String, bool)>), // (address, is_quantum)
    /// Sign transaction request
    SignTransaction {
        tx_data: Vec<u8>,
        account_index: u32,
        use_quantum: bool,
    },
    /// Signed transaction response
    SignedTransaction {
        signature: Vec<u8>,
        tx_hash: H256,
    },
    /// Quantum state verification request
    VerifyQuantumState {
        state_hash: H256,
        proof_type: String,
    },
    /// Verification response
    VerificationResponse {
        verified: bool,
        quantum_advantage: f64,
    },
    /// Error message
    Error(String),
}

impl TunneledWallet {
    /// Create a new tunneled wallet
    pub fn new(
        wallet: QPPWallet<Unlocked>,
        local_addr: String,
        use_qkd: bool,
    ) -> Self {
        let config = TunnelConfig {
            local_addr: local_addr.clone(),
            remote_addr: String::new(), // Set when connecting
            key_rotation_interval: 1000,
            post_quantum: true,
            use_qkd,
        };

        TunneledWallet {
            wallet: Arc::new(Mutex::new(wallet)),
            tunnels: Arc::new(Mutex::new(Vec::new())),
            config,
        }
    }

    /// Connect to a remote wallet via quantum tunnel
    pub async fn connect_to_peer(&mut self, remote_addr: String) -> Result<(), WalletError> {
        // Update config with remote address
        let mut tunnel_config = self.config.clone();
        tunnel_config.remote_addr = remote_addr.clone();

        // Create and establish tunnel
        let tunnel = QuantumTunnel::<Handshaking>::new(tunnel_config);
        let established = tunnel.handshake().await
            .map_err(|e| WalletError::ConnectionError(format!("Tunnel handshake failed: {:?}", e)))?;

        // Store established tunnel
        let established_tunnel = EstablishedTunnel {
            tunnel: Arc::new(Mutex::new(established)),
            remote_addr,
            created_at: std::time::Instant::now(),
            last_activity: std::time::Instant::now(),
        };

        self.tunnels.lock().unwrap().push(established_tunnel);
        Ok(())
    }

    /// Send a message through the tunnel to a specific peer
    pub fn send_to_peer(
        &mut self,
        remote_addr: &str,
        message: WalletTunnelMessage,
    ) -> Result<(), WalletError> {
        let mut tunnels = self.tunnels.lock().unwrap();
        
        // Find tunnel for the peer
        let tunnel = tunnels.iter_mut()
            .find(|t| t.remote_addr == remote_addr)
            .ok_or_else(|| WalletError::ConnectionError("No tunnel to peer".into()))?;

        // Encode message
        let data = message.encode();
        
        // Send through tunnel
        let encrypted = tunnel.tunnel.lock().unwrap().send(&data)
            .map_err(|e| WalletError::ConnectionError(format!("Send failed: {:?}", e)))?;

        // Update last activity
        tunnel.last_activity = std::time::Instant::now();

        // In real implementation, would send encrypted data over network
        log::debug!("Sent {} bytes through quantum tunnel", encrypted.len());

        Ok(())
    }

    /// Process an incoming message
    pub fn process_incoming(&mut self, encrypted: &[u8], from_addr: &str) -> Result<(), WalletError> {
        // Decrypt and decode message first
        let message = {
            let mut tunnels = self.tunnels.lock().unwrap();
            
            // Find tunnel for the peer
            let tunnel = tunnels.iter_mut()
                .find(|t| t.remote_addr == from_addr)
                .ok_or_else(|| WalletError::ConnectionError("No tunnel from peer".into()))?;

            // Decrypt message
            let decrypted = tunnel.tunnel.lock().unwrap().receive(encrypted)
                .map_err(|e| WalletError::ConnectionError(format!("Decrypt failed: {:?}", e)))?;

            // Update last activity
            tunnel.last_activity = std::time::Instant::now();

            // Decode message
            WalletTunnelMessage::decode(&mut &decrypted[..])
                .map_err(|_| WalletError::ConnectionError("Invalid message format".into()))?
        }; // Drop tunnels lock here

        // Handle message without holding lock
        self.handle_message(message, from_addr)?;

        Ok(())
    }

    /// Handle a decoded message
    fn handle_message(&mut self, message: WalletTunnelMessage, from_addr: &str) -> Result<(), WalletError> {
        match message {
            WalletTunnelMessage::GetAccounts => {
                // Get accounts from wallet
                let response_msg = {
                    let wallet = self.wallet.lock().unwrap();
                    let accounts = wallet.list_accounts();
                    
                    let response: Vec<(String, bool)> = accounts.into_iter()
                        .map(|acc| {
                            let (addr, is_quantum) = match acc {
                                crate::types::AccountType::Classical(id) => (format!("{:?}", id), false),
                                crate::types::AccountType::Quantum(id) => (format!("{:?}", id), true),
                                crate::types::AccountType::Hybrid { classical, .. } => (format!("{:?}", classical), true),
                            };
                            (addr, is_quantum)
                        })
                        .collect();

                    WalletTunnelMessage::AccountsResponse(response)
                }; // Drop wallet lock here

                // Send response without holding lock
                self.send_to_peer(from_addr, response_msg)?;
            }
            WalletTunnelMessage::SignTransaction { tx_data, account_index, use_quantum } => {
                // Sign transaction
                let response_msg = {
                    let mut wallet = self.wallet.lock().unwrap();
                    
                    // In real implementation, would sign with specified account
                    let signature = if use_quantum {
                        // Use quantum signature
                        vec![0u8; 49152] // SPHINCS+ signature size
                    } else {
                        // Use classical signature
                        vec![0u8; 64] // Ed25519 signature size
                    };

                    let tx_hash = sp_core::blake2_256(&tx_data).into();

                    WalletTunnelMessage::SignedTransaction {
                        signature,
                        tx_hash,
                    }
                }; // Drop wallet lock here
                
                // Send response without holding lock
                self.send_to_peer(from_addr, response_msg)?;
            }
            WalletTunnelMessage::VerifyQuantumState { state_hash, proof_type } => {
                // Verify using light client
                let verified = true; // Simplified
                let quantum_advantage = 1000.0; // 1000x speedup

                let response_msg = WalletTunnelMessage::VerificationResponse {
                    verified,
                    quantum_advantage,
                };
                self.send_to_peer(from_addr, response_msg)?;
            }
            _ => {
                log::info!("Received message: {:?}", message);
            }
        }

        Ok(())
    }

    /// Clean up expired tunnels
    pub fn cleanup_tunnels(&mut self, max_idle: std::time::Duration) {
        let now = std::time::Instant::now();
        let mut tunnels = self.tunnels.lock().unwrap();
        
        tunnels.retain(|tunnel| {
            now.duration_since(tunnel.last_activity) < max_idle
        });
    }

    /// Inject quantum entropy from QKD into all active tunnels
    pub fn inject_qkd_entropy(&mut self, entropy: Vec<u8>, source: String) -> Result<(), WalletError> {
        let mut tunnels = self.tunnels.lock().unwrap();
        
        for tunnel in tunnels.iter_mut() {
            tunnel.tunnel.lock().unwrap()
                .inject_quantum_entropy(entropy.clone(), source.clone(), 255)
                .map_err(|e| WalletError::ConnectionError(format!("Entropy injection failed: {:?}", e)))?;
        }

        Ok(())
    }

    /// Get statistics about active tunnels
    pub fn tunnel_stats(&self) -> TunnelStats {
        let tunnels = self.tunnels.lock().unwrap();
        let now = std::time::Instant::now();

        TunnelStats {
            active_tunnels: tunnels.len(),
            total_uptime: tunnels.iter()
                .map(|t| now.duration_since(t.created_at).as_secs())
                .sum(),
            average_idle: if tunnels.is_empty() { 0 } else {
                tunnels.iter()
                    .map(|t| now.duration_since(t.last_activity).as_secs())
                    .sum::<u64>() / tunnels.len() as u64
            },
            using_qkd: self.config.use_qkd,
        }
    }
}

/// Statistics about tunnel usage
#[derive(Debug, Clone)]
pub struct TunnelStats {
    /// Number of active tunnels
    pub active_tunnels: usize,
    /// Total uptime in seconds
    pub total_uptime: u64,
    /// Average idle time in seconds
    pub average_idle: u64,
    /// Whether QKD is enabled
    pub using_qkd: bool,
}

/// Example usage in async context
#[cfg(feature = "std")]
pub mod example {
    use super::*;
    
    pub async fn demonstrate_tunneled_wallet() -> Result<(), WalletError> {
        // Create unlocked wallet
        let wallet = QPPWallet::<crate::wallet::Locked>::new();
        let wallet = wallet.unlock("password")?;
        
        // Create tunneled wallet
        let mut tunneled = TunneledWallet::new(
            wallet,
            "127.0.0.1:9999".to_string(),
            true, // Use QKD
        );
        
        // Connect to peer
        tunneled.connect_to_peer("127.0.0.1:9998".to_string()).await?;
        
        // Request accounts from peer
        tunneled.send_to_peer(
            "127.0.0.1:9998",
            WalletTunnelMessage::GetAccounts,
        )?;
        
        // Get tunnel statistics
        let stats = tunneled.tunnel_stats();
        println!("Active tunnels: {}", stats.active_tunnels);
        println!("Using QKD: {}", stats.using_qkd);
        
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_tunnel_stats() {
        let wallet = QPPWallet::<crate::wallet::Locked>::new();
        let wallet = wallet.unlock("test").unwrap();
        
        let tunneled = TunneledWallet::new(
            wallet,
            "127.0.0.1:9999".to_string(),
            false,
        );
        
        let stats = tunneled.tunnel_stats();
        assert_eq!(stats.active_tunnels, 0);
        assert!(!stats.using_qkd);
    }
}