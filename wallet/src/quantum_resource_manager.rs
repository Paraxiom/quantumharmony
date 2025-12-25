//! Quantum Resource Manager for Context Switching
//! 
//! Manages QKD keys and RNG entropy during context switches to ensure
//! quantum resources are not depleted or compromised.

use crate::{
    types::WalletError,
    qpp_sync_context::{ContextId, SyncQuantumContext},
    no_clone::NoClone,
};
use sp_core::H256;
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use scale_codec::{Encode, Decode};

/// Size of entropy needed for secure context switch
pub const CONTEXT_SWITCH_ENTROPY: usize = 32; // bytes

/// Number of QKD keys consumed per context switch
pub const QKD_KEYS_PER_SWITCH: usize = 2;

/// Minimum entropy threshold before triggering refill
pub const MIN_ENTROPY_THRESHOLD: usize = 1024; // 1KB

/// Quantum resource manager for context-aware operations
pub struct QuantumResourceManager {
    /// QKD context manager
    qkd_manager: QKDContextManager,
    /// RNG entropy manager
    rng_manager: RNGContextManager,
    /// Resource consumption metrics
    metrics: ResourceMetrics,
    /// Switch policy
    switch_policy: SwitchPolicy,
}

/// QKD context manager
pub struct QKDContextManager {
    /// Active QKD sessions per context
    context_sessions: HashMap<ContextId, QKDSession>,
    /// Shared key pool for efficiency
    shared_key_pool: Arc<Mutex<QuantumKeyPool>>,
    /// Session checkpoints for recovery
    checkpoints: HashMap<ContextId, SessionCheckpoint>,
}

/// RNG entropy manager
pub struct RNGContextManager {
    /// Entropy buffers per context
    context_buffers: HashMap<ContextId, EntropyBuffer>,
    /// Global entropy pool
    global_pool: Arc<Mutex<QuantumEntropyPool>>,
    /// Depletion monitor
    depletion_monitor: DepletionMonitor,
}

/// Resource consumption metrics
#[derive(Debug, Clone)]
pub struct ResourceMetrics {
    /// Entropy consumption rate (bytes/sec)
    pub entropy_rate: f64,
    /// QKD key consumption rate (keys/sec)
    pub qkd_rate: f64,
    /// Context switch frequency (switches/sec)
    pub switch_frequency: f64,
    /// Current entropy level (0.0 - 1.0)
    pub entropy_level: f32,
    /// Available QKD keys
    pub qkd_keys_available: usize,
}

/// Switch policy determines when context switching is allowed
#[derive(Debug, Clone, Copy)]
pub enum SwitchPolicy {
    /// Always allow switching
    AlwaysAllow,
    /// Only switch when resources are abundant
    Conservative,
    /// Adaptive based on metrics
    Adaptive,
    /// Never allow switching (for testing)
    NeverAllow,
}

/// Resources needed for context switch
pub struct ContextSwitchResources {
    /// Entropy for randomization
    pub entropy: NoClone<Vec<u8>>,
    /// QKD session for target context
    pub qkd_session: QKDSession,
    /// Impact metrics
    pub impact: SwitchImpact,
}

/// Impact of context switch on resources
#[derive(Debug, Clone)]
pub struct SwitchImpact {
    /// Entropy consumed
    pub entropy_consumed: usize,
    /// QKD keys consumed
    pub qkd_keys_consumed: usize,
    /// Estimated performance impact (0.0 - 1.0)
    pub performance_impact: f32,
}

impl QuantumResourceManager {
    /// Create new quantum resource manager
    pub fn new(switch_policy: SwitchPolicy) -> Self {
        Self {
            qkd_manager: QKDContextManager::new(),
            rng_manager: RNGContextManager::new(),
            metrics: ResourceMetrics::default(),
            switch_policy,
        }
    }
    
    /// Check if context switch is allowed based on resources
    pub fn can_switch_context(&self) -> bool {
        match self.switch_policy {
            SwitchPolicy::AlwaysAllow => true,
            SwitchPolicy::NeverAllow => false,
            SwitchPolicy::Conservative => {
                self.metrics.entropy_level > 0.5 
                    && self.metrics.qkd_keys_available > 20
            }
            SwitchPolicy::Adaptive => {
                self.adaptive_switch_decision()
            }
        }
    }
    
    /// Adaptive switching decision based on current metrics
    fn adaptive_switch_decision(&self) -> bool {
        // Don't switch if entropy is critically low
        if self.metrics.entropy_level < 0.2 {
            return false;
        }
        
        // Don't switch if QKD keys are scarce
        if self.metrics.qkd_keys_available < 10 {
            return false;
        }
        
        // Consider switch frequency
        if self.metrics.switch_frequency > 10.0 {
            // Too frequent, only allow if resources are abundant
            return self.metrics.entropy_level > 0.8 
                && self.metrics.qkd_keys_available > 50;
        }
        
        true
    }
    
    /// Prepare resources for context switch
    pub fn prepare_context_switch(
        &mut self,
        from_context: ContextId,
        to_context: ContextId,
    ) -> Result<ContextSwitchResources, WalletError> {
        // Check if switch is allowed
        if !self.can_switch_context() {
            return Err(WalletError::ResourceExhausted(
                "Insufficient quantum resources for context switch".into()
            ));
        }
        
        // Checkpoint current QKD session
        self.qkd_manager.checkpoint_session(from_context)?;
        
        // Allocate entropy for switch
        let switch_entropy = self.rng_manager
            .allocate_switch_entropy(CONTEXT_SWITCH_ENTROPY)?;
        
        // Prepare QKD session for target context
        let target_qkd = self.qkd_manager
            .prepare_session(to_context)?;
        
        // Calculate impact
        let impact = self.calculate_switch_impact();
        
        Ok(ContextSwitchResources {
            entropy: switch_entropy,
            qkd_session: target_qkd,
            impact,
        })
    }
    
    /// Execute quantum-safe context switch
    pub fn execute_switch(
        &mut self,
        resources: ContextSwitchResources,
    ) -> Result<(), WalletError> {
        // Use entropy for timing randomization
        self.apply_timing_randomization(&resources.entropy)?;
        
        // Transition QKD sessions
        self.qkd_manager.activate_session(resources.qkd_session)?;
        
        // Update metrics
        self.update_metrics(resources.impact);
        
        Ok(())
    }
    
    /// Apply timing randomization using entropy
    fn apply_timing_randomization(&self, entropy: &NoClone<Vec<u8>>) -> Result<(), WalletError> {
        // Extract timing delay from entropy
        let delay_bytes = &entropy.as_ref()[..4];
        let delay_nanos = u32::from_le_bytes([
            delay_bytes[0], delay_bytes[1], 
            delay_bytes[2], delay_bytes[3]
        ]) % 1_000_000; // Max 1ms delay
        
        // Apply randomized delay
        std::thread::sleep(std::time::Duration::from_nanos(delay_nanos as u64));
        
        Ok(())
    }
    
    /// Calculate impact of context switch
    fn calculate_switch_impact(&self) -> SwitchImpact {
        SwitchImpact {
            entropy_consumed: CONTEXT_SWITCH_ENTROPY,
            qkd_keys_consumed: QKD_KEYS_PER_SWITCH,
            performance_impact: 0.1, // 10% impact estimate
        }
    }
    
    /// Update metrics after switch
    fn update_metrics(&mut self, impact: SwitchImpact) {
        self.metrics.entropy_rate += impact.entropy_consumed as f64;
        self.metrics.qkd_rate += impact.qkd_keys_consumed as f64;
        self.metrics.switch_frequency += 1.0;
    }
}

/// Quantum key pool for efficient key management
pub struct QuantumKeyPool {
    /// Available keys
    keys: Vec<QKDKey>,
    /// Maximum pool size
    max_size: usize,
    /// Refill threshold
    refill_threshold: usize,
}

/// QKD key
#[derive(Clone)]
pub struct QKDKey {
    /// Key material (protected)
    material: [u8; 32],
    /// Key ID
    id: H256,
    /// Generation timestamp
    generated_at: u64,
}

/// Quantum entropy pool
pub struct QuantumEntropyPool {
    /// Available entropy
    entropy: Vec<u8>,
    /// Maximum pool size
    max_size: usize,
    /// Current fill level
    fill_level: f32,
}

/// Entropy buffer for context
pub struct EntropyBuffer {
    /// Buffer data (protected)
    buffer: NoClone<Vec<u8>>,
    /// Buffer capacity
    capacity: usize,
    /// Minimum threshold
    min_threshold: usize,
}

impl EntropyBuffer {
    /// Create new entropy buffer
    pub fn new(capacity: usize) -> Self {
        Self {
            buffer: NoClone::new(Vec::with_capacity(capacity)),
            capacity,
            min_threshold: capacity / 4,
        }
    }
    
    /// Consume entropy from buffer
    pub fn consume(&mut self, amount: usize) -> Result<NoClone<Vec<u8>>, WalletError> {
        if self.buffer.as_ref().len() < amount {
            return Err(WalletError::ResourceExhausted(
                "Insufficient entropy in buffer".into()
            ));
        }
        
        // Check if refill needed
        if self.buffer.as_ref().len() - amount < self.min_threshold {
            // Trigger async refill
            self.trigger_refill()?;
        }
        
        // Extract entropy
        let entropy = self.buffer.as_mut().drain(..amount).collect();
        Ok(NoClone::new(entropy))
    }
    
    /// Trigger buffer refill
    fn trigger_refill(&self) -> Result<(), WalletError> {
        // In production, this would trigger async refill from QRNG
        Ok(())
    }
}

/// QKD session for secure key exchange
pub struct QKDSession {
    /// Session ID
    pub session_id: H256,
    /// Context ID
    pub context_id: ContextId,
    /// Key buffer
    key_buffer: Arc<Mutex<Vec<QKDKey>>>,
    /// Synchronization state
    sync_state: SyncState,
}

/// Session synchronization state
#[derive(Clone, Debug)]
pub struct SyncState {
    /// Current key index
    key_index: usize,
    /// Last sync timestamp
    last_sync: u64,
    /// Peer acknowledged index
    peer_ack_index: usize,
}

/// Session checkpoint for recovery
#[derive(Clone, Encode, Decode)]
pub struct SessionCheckpoint {
    /// Session ID
    session_id: H256,
    /// Key index at checkpoint
    key_index: usize,
    /// Timestamp
    timestamp: u64,
}

/// Depletion monitor tracks resource usage
pub struct DepletionMonitor {
    /// Entropy depletion events
    entropy_depletion_count: usize,
    /// QKD depletion events
    qkd_depletion_count: usize,
    /// Last depletion timestamp
    last_depletion: Option<u64>,
}

impl QKDContextManager {
    /// Create new QKD context manager
    pub fn new() -> Self {
        Self {
            context_sessions: HashMap::new(),
            shared_key_pool: Arc::new(Mutex::new(QuantumKeyPool {
                keys: Vec::new(),
                max_size: 1000,
                refill_threshold: 100,
            })),
            checkpoints: HashMap::new(),
        }
    }
    
    /// Checkpoint session state
    pub fn checkpoint_session(&mut self, context_id: ContextId) -> Result<(), WalletError> {
        let session = self.context_sessions.get(&context_id)
            .ok_or(WalletError::InvalidContext("Session not found".into()))?;
        
        let checkpoint = SessionCheckpoint {
            session_id: session.session_id,
            key_index: session.sync_state.key_index,
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
        };
        
        self.checkpoints.insert(context_id, checkpoint);
        Ok(())
    }
    
    /// Prepare session for context
    pub fn prepare_session(&mut self, context_id: ContextId) -> Result<QKDSession, WalletError> {
        // Check if session exists
        if let Some(session) = self.context_sessions.get(&context_id) {
            return Ok(session.clone());
        }
        
        // Create new session
        let session = QKDSession {
            session_id: H256::random(),
            context_id,
            key_buffer: self.shared_key_pool.clone(),
            sync_state: SyncState {
                key_index: 0,
                last_sync: 0,
                peer_ack_index: 0,
            },
        };
        
        self.context_sessions.insert(context_id, session.clone());
        Ok(session)
    }
    
    /// Activate session after switch
    pub fn activate_session(&mut self, session: QKDSession) -> Result<(), WalletError> {
        // Restore from checkpoint if available
        if let Some(checkpoint) = self.checkpoints.get(&session.context_id) {
            // Restore key index
            let mut session = session;
            session.sync_state.key_index = checkpoint.key_index;
        }
        
        Ok(())
    }
}

impl RNGContextManager {
    /// Create new RNG context manager
    pub fn new() -> Self {
        Self {
            context_buffers: HashMap::new(),
            global_pool: Arc::new(Mutex::new(QuantumEntropyPool {
                entropy: Vec::new(),
                max_size: 1024 * 1024, // 1MB
                fill_level: 1.0,
            })),
            depletion_monitor: DepletionMonitor {
                entropy_depletion_count: 0,
                qkd_depletion_count: 0,
                last_depletion: None,
            },
        }
    }
    
    /// Allocate entropy for context switch
    pub fn allocate_switch_entropy(&mut self, amount: usize) -> Result<NoClone<Vec<u8>>, WalletError> {
        // Try to get from global pool
        let mut pool = self.global_pool.lock()
            .map_err(|_| WalletError::CryptoError("Lock poisoned".into()))?;
        
        if pool.entropy.len() < amount {
            return Err(WalletError::ResourceExhausted("Insufficient entropy".into()));
        }
        
        let entropy = pool.entropy.drain(..amount).collect();
        pool.fill_level = pool.entropy.len() as f32 / pool.max_size as f32;
        
        Ok(NoClone::new(entropy))
    }
}

impl Default for ResourceMetrics {
    fn default() -> Self {
        Self {
            entropy_rate: 0.0,
            qkd_rate: 0.0,
            switch_frequency: 0.0,
            entropy_level: 1.0,
            qkd_keys_available: 100,
        }
    }
}

// Make QKDSession cloneable for the API
impl Clone for QKDSession {
    fn clone(&self) -> Self {
        Self {
            session_id: self.session_id,
            context_id: self.context_id,
            key_buffer: self.key_buffer.clone(),
            sync_state: self.sync_state.clone(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_resource_manager_creation() {
        let manager = QuantumResourceManager::new(SwitchPolicy::Adaptive);
        assert!(manager.can_switch_context());
    }
    
    #[test]
    fn test_entropy_buffer() {
        let mut buffer = EntropyBuffer::new(1024);
        // Would need to populate buffer first in real test
    }
    
    #[test]
    fn test_switch_policy() {
        let mut manager = QuantumResourceManager::new(SwitchPolicy::Conservative);
        manager.metrics.entropy_level = 0.3;
        assert!(!manager.can_switch_context());
        
        manager.metrics.entropy_level = 0.7;
        assert!(manager.can_switch_context());
    }
}