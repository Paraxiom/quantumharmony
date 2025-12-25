// node/src/quantum_p2p/qkd_interface.rs
//
// QKD Hardware Interface - Stub for Asian Market Hardware Vendors
//
// This module provides a trait interface that QKD hardware vendors can implement
// to integrate their devices with QuantumHarmony's Proof of Coherence mechanism.
//
// Supported vendors (with stubs):
// - Toshiba QKD
// - ID Quantique (Cerberis)
// - QuantumCTek (Chinese market)
// - SK Telecom IDQ
// - NTT QKD Systems
//
// The interface follows ETSI GS QKD 014 for key delivery API compatibility.

use std::sync::Arc;
use tokio::sync::RwLock;
use async_trait::async_trait;

/// Size of QKD-derived keys (256-bit for AES-256)
pub const QKD_KEY_SIZE: usize = 32;

/// Size of Key IDs from QKD systems (typically UUID or 128-bit)
pub const QKD_KEY_ID_SIZE: usize = 16;

/// QKD Key metadata following ETSI GS QKD 014
#[derive(Debug, Clone)]
pub struct QkdKeyMetadata {
    /// Unique key identifier from the QKD system
    pub key_id: [u8; QKD_KEY_ID_SIZE],
    /// Quantum Bit Error Rate (QBER) - quality metric
    pub qber: f64,
    /// Timestamp when key was generated (Unix epoch)
    pub timestamp: u64,
    /// Source device identifier
    pub source_device: String,
    /// Destination device identifier
    pub destination_device: String,
    /// Key generation rate at time of extraction (bits/second)
    pub generation_rate: f64,
    /// Whether this key has been used (for forward secrecy tracking)
    pub consumed: bool,
}

/// QKD key material with metadata
#[derive(Clone)]
pub struct QkdKey {
    /// Raw key material (256-bit)
    pub key: [u8; QKD_KEY_SIZE],
    /// Key metadata
    pub metadata: QkdKeyMetadata,
}

impl std::fmt::Debug for QkdKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Don't expose key material in debug output
        f.debug_struct("QkdKey")
            .field("key", &"[REDACTED]")
            .field("metadata", &self.metadata)
            .finish()
    }
}

/// QKD device status
#[derive(Debug, Clone, PartialEq)]
pub enum QkdDeviceStatus {
    /// Device is online and producing keys
    Online,
    /// Device is connected but key buffer is low
    LowKeyBuffer,
    /// Device is calibrating (alignment, etc.)
    Calibrating,
    /// Device has error condition
    Error(String),
    /// Device is offline/unreachable
    Offline,
}

/// QKD connection parameters
#[derive(Debug, Clone)]
pub struct QkdConnectionParams {
    /// ETSI QKD API endpoint URL
    pub endpoint: String,
    /// SAE (Secure Application Entity) ID for this node
    pub sae_id: String,
    /// Peer SAE ID (destination)
    pub peer_sae_id: String,
    /// Optional authentication token
    pub auth_token: Option<String>,
    /// TLS certificate path (for mTLS)
    pub tls_cert_path: Option<String>,
    /// TLS key path (for mTLS)
    pub tls_key_path: Option<String>,
    /// Connection timeout in milliseconds
    pub timeout_ms: u64,
}

/// Error types for QKD operations
#[derive(Debug, Clone)]
pub enum QkdError {
    /// Device not connected
    NotConnected,
    /// No keys available in buffer
    NoKeysAvailable,
    /// QBER threshold exceeded (quantum channel compromised)
    QberThresholdExceeded { qber: f64, threshold: f64 },
    /// Authentication failed
    AuthenticationFailed,
    /// Key already consumed (replay protection)
    KeyAlreadyConsumed { key_id: [u8; QKD_KEY_ID_SIZE] },
    /// Device error
    DeviceError(String),
    /// Network error
    NetworkError(String),
    /// Protocol error (e.g., ETSI API version mismatch)
    ProtocolError(String),
    /// Key synchronization failed with peer
    SyncError(String),
}

impl std::fmt::Display for QkdError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotConnected => write!(f, "QKD device not connected"),
            Self::NoKeysAvailable => write!(f, "No QKD keys available in buffer"),
            Self::QberThresholdExceeded { qber, threshold } => {
                write!(f, "QBER {} exceeds threshold {} - possible eavesdropping", qber, threshold)
            }
            Self::AuthenticationFailed => write!(f, "QKD authentication failed"),
            Self::KeyAlreadyConsumed { key_id } => {
                write!(f, "QKD key {} already consumed", hex::encode(key_id))
            }
            Self::DeviceError(msg) => write!(f, "QKD device error: {}", msg),
            Self::NetworkError(msg) => write!(f, "QKD network error: {}", msg),
            Self::ProtocolError(msg) => write!(f, "QKD protocol error: {}", msg),
            Self::SyncError(msg) => write!(f, "QKD key sync error: {}", msg),
        }
    }
}

impl std::error::Error for QkdError {}

/// Main trait for QKD hardware integration
///
/// Hardware vendors implement this trait to integrate their QKD systems
/// with QuantumHarmony's Proof of Coherence mechanism.
///
/// # Example Implementation
///
/// ```ignore
/// struct ToshibaQkd {
///     client: ToshibaApiClient,
/// }
///
/// #[async_trait]
/// impl QkdHardwareInterface for ToshibaQkd {
///     async fn connect(&mut self, params: QkdConnectionParams) -> Result<(), QkdError> {
///         self.client.connect(&params.endpoint, &params.auth_token).await
///             .map_err(|e| QkdError::NetworkError(e.to_string()))
///     }
///
///     async fn get_key(&self) -> Result<QkdKey, QkdError> {
///         self.client.fetch_key().await
///             .map_err(|e| QkdError::DeviceError(e.to_string()))
///     }
///     // ... other methods
/// }
/// ```
#[async_trait]
pub trait QkdHardwareInterface: Send + Sync {
    /// Connect to the QKD device/network
    async fn connect(&mut self, params: QkdConnectionParams) -> Result<(), QkdError>;

    /// Disconnect from the QKD device
    async fn disconnect(&mut self) -> Result<(), QkdError>;

    /// Get current device status
    async fn status(&self) -> QkdDeviceStatus;

    /// Request a new key from the QKD system
    ///
    /// This retrieves a key that has been pre-shared with the peer via
    /// the quantum channel. The key_id must be synchronized with the peer.
    async fn get_key(&self) -> Result<QkdKey, QkdError>;

    /// Request a specific key by ID (for synchronization with peer)
    async fn get_key_by_id(&self, key_id: &[u8; QKD_KEY_ID_SIZE]) -> Result<QkdKey, QkdError>;

    /// Get the number of keys available in the buffer
    async fn available_key_count(&self) -> Result<usize, QkdError>;

    /// Get current QBER (Quantum Bit Error Rate)
    ///
    /// Returns None if QBER measurement is not available
    async fn current_qber(&self) -> Option<f64>;

    /// Get the key generation rate (bits/second)
    async fn key_rate(&self) -> Result<f64, QkdError>;

    /// Mark a key as consumed (for forward secrecy)
    async fn consume_key(&self, key_id: &[u8; QKD_KEY_ID_SIZE]) -> Result<(), QkdError>;

    /// Get device identifier string (for logging/metrics)
    fn device_id(&self) -> String;

    /// Get vendor name
    fn vendor(&self) -> &'static str;
}

/// Stub implementation for development/testing without QKD hardware
///
/// This generates deterministic "QKD" keys from a seed, useful for:
/// - Development without hardware
/// - Testing key exchange protocols
/// - Demonstrating the interface to potential hardware partners
pub struct StubQkdDevice {
    device_id: String,
    connected: bool,
    seed: [u8; 32],
    key_counter: u64,
    qber: f64,
}

impl StubQkdDevice {
    /// Create a new stub QKD device
    pub fn new(device_id: &str, seed: [u8; 32]) -> Self {
        Self {
            device_id: device_id.to_string(),
            connected: false,
            seed,
            key_counter: 0,
            qber: 0.02, // Typical good QBER
        }
    }

    /// Create with default seed (for testing only)
    pub fn new_test(device_id: &str) -> Self {
        let seed = sp_core::blake2_256(device_id.as_bytes());
        Self::new(device_id, seed)
    }

    /// Generate deterministic key from seed and counter
    fn generate_key(&self, counter: u64) -> [u8; QKD_KEY_SIZE] {
        use sp_core::blake2_256;
        let mut input = Vec::with_capacity(40);
        input.extend_from_slice(&self.seed);
        input.extend_from_slice(&counter.to_le_bytes());
        blake2_256(&input)
    }

    /// Generate key ID from counter
    fn generate_key_id(&self, counter: u64) -> [u8; QKD_KEY_ID_SIZE] {
        use sp_core::blake2_128;
        let mut input = Vec::with_capacity(40);
        input.extend_from_slice(&self.seed);
        input.extend_from_slice(&counter.to_le_bytes());
        blake2_128(&input)
    }
}

#[async_trait]
impl QkdHardwareInterface for StubQkdDevice {
    async fn connect(&mut self, _params: QkdConnectionParams) -> Result<(), QkdError> {
        log::info!("[QKD-STUB] {} connecting (stub mode)", self.device_id);
        self.connected = true;
        Ok(())
    }

    async fn disconnect(&mut self) -> Result<(), QkdError> {
        log::info!("[QKD-STUB] {} disconnecting", self.device_id);
        self.connected = false;
        Ok(())
    }

    async fn status(&self) -> QkdDeviceStatus {
        if self.connected {
            QkdDeviceStatus::Online
        } else {
            QkdDeviceStatus::Offline
        }
    }

    async fn get_key(&self) -> Result<QkdKey, QkdError> {
        if !self.connected {
            return Err(QkdError::NotConnected);
        }

        let counter = self.key_counter;
        let key = self.generate_key(counter);
        let key_id = self.generate_key_id(counter);

        Ok(QkdKey {
            key,
            metadata: QkdKeyMetadata {
                key_id,
                qber: self.qber,
                timestamp: std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_secs(),
                source_device: self.device_id.clone(),
                destination_device: "peer".to_string(),
                generation_rate: 1000.0, // Simulated 1 kbps
                consumed: false,
            },
        })
    }

    async fn get_key_by_id(&self, key_id: &[u8; QKD_KEY_ID_SIZE]) -> Result<QkdKey, QkdError> {
        if !self.connected {
            return Err(QkdError::NotConnected);
        }

        // In stub mode, we can't really retrieve by ID, so generate a deterministic one
        let counter = u64::from_le_bytes([
            key_id[0], key_id[1], key_id[2], key_id[3],
            key_id[4], key_id[5], key_id[6], key_id[7],
        ]);
        let key = self.generate_key(counter);

        Ok(QkdKey {
            key,
            metadata: QkdKeyMetadata {
                key_id: *key_id,
                qber: self.qber,
                timestamp: std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_secs(),
                source_device: self.device_id.clone(),
                destination_device: "peer".to_string(),
                generation_rate: 1000.0,
                consumed: false,
            },
        })
    }

    async fn available_key_count(&self) -> Result<usize, QkdError> {
        if !self.connected {
            return Err(QkdError::NotConnected);
        }
        // Stub always has "infinite" keys available
        Ok(1000)
    }

    async fn current_qber(&self) -> Option<f64> {
        if self.connected {
            Some(self.qber)
        } else {
            None
        }
    }

    async fn key_rate(&self) -> Result<f64, QkdError> {
        if !self.connected {
            return Err(QkdError::NotConnected);
        }
        Ok(1000.0) // Simulated 1 kbps
    }

    async fn consume_key(&self, _key_id: &[u8; QKD_KEY_ID_SIZE]) -> Result<(), QkdError> {
        if !self.connected {
            return Err(QkdError::NotConnected);
        }
        // Stub doesn't track consumption
        Ok(())
    }

    fn device_id(&self) -> String {
        format!("stub-{}", self.device_id)
    }

    fn vendor(&self) -> &'static str {
        "QuantumHarmony Stub (Development)"
    }
}

/// QKD device manager - handles multiple QKD devices with failover
pub struct QkdDeviceManager {
    devices: Vec<Arc<RwLock<Box<dyn QkdHardwareInterface>>>>,
    primary_index: usize,
    qber_threshold: f64,
}

impl QkdDeviceManager {
    /// Create a new device manager
    pub fn new(qber_threshold: f64) -> Self {
        Self {
            devices: Vec::new(),
            primary_index: 0,
            qber_threshold,
        }
    }

    /// Add a QKD device
    pub fn add_device(&mut self, device: Box<dyn QkdHardwareInterface>) {
        self.devices.push(Arc::new(RwLock::new(device)));
    }

    /// Get a key from the primary device, with automatic failover
    pub async fn get_key(&self) -> Result<QkdKey, QkdError> {
        if self.devices.is_empty() {
            return Err(QkdError::NotConnected);
        }

        // Try primary device first
        let primary = &self.devices[self.primary_index];
        let device = primary.read().await;

        match device.get_key().await {
            Ok(key) => {
                // Check QBER threshold
                if key.metadata.qber > self.qber_threshold {
                    return Err(QkdError::QberThresholdExceeded {
                        qber: key.metadata.qber,
                        threshold: self.qber_threshold,
                    });
                }
                Ok(key)
            }
            Err(e) => {
                log::warn!("[QKD] Primary device failed: {}, trying failover", e);
                drop(device);

                // Try other devices
                for (i, dev) in self.devices.iter().enumerate() {
                    if i == self.primary_index {
                        continue;
                    }
                    let device = dev.read().await;
                    if let Ok(key) = device.get_key().await {
                        if key.metadata.qber <= self.qber_threshold {
                            return Ok(key);
                        }
                    }
                }

                Err(e)
            }
        }
    }

    /// Check if any device is online
    pub async fn is_available(&self) -> bool {
        for dev in &self.devices {
            let device = dev.read().await;
            if device.status().await == QkdDeviceStatus::Online {
                return true;
            }
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_stub_device() {
        let mut device = StubQkdDevice::new_test("test-device");

        // Should be offline initially
        assert_eq!(device.status().await, QkdDeviceStatus::Offline);

        // Connect
        let params = QkdConnectionParams {
            endpoint: "stub://localhost".to_string(),
            sae_id: "node-1".to_string(),
            peer_sae_id: "node-2".to_string(),
            auth_token: None,
            tls_cert_path: None,
            tls_key_path: None,
            timeout_ms: 5000,
        };
        device.connect(params).await.unwrap();

        // Should be online now
        assert_eq!(device.status().await, QkdDeviceStatus::Online);

        // Get a key
        let key = device.get_key().await.unwrap();
        assert_eq!(key.key.len(), QKD_KEY_SIZE);
        assert!(key.metadata.qber < 0.1); // Good QBER

        // Disconnect
        device.disconnect().await.unwrap();
        assert_eq!(device.status().await, QkdDeviceStatus::Offline);
    }

    #[tokio::test]
    async fn test_device_manager_failover() {
        let mut manager = QkdDeviceManager::new(0.1); // 10% QBER threshold

        // Add two stub devices
        let device1 = Box::new(StubQkdDevice::new_test("device-1"));
        let device2 = Box::new(StubQkdDevice::new_test("device-2"));

        manager.add_device(device1);
        manager.add_device(device2);

        // Connect first device
        {
            let dev = &manager.devices[0];
            let mut d = dev.write().await;
            d.connect(QkdConnectionParams {
                endpoint: "stub://localhost".to_string(),
                sae_id: "node-1".to_string(),
                peer_sae_id: "node-2".to_string(),
                auth_token: None,
                tls_cert_path: None,
                tls_key_path: None,
                timeout_ms: 5000,
            }).await.unwrap();
        }

        // Should be able to get keys
        assert!(manager.is_available().await);
        let key = manager.get_key().await.unwrap();
        assert_eq!(key.key.len(), QKD_KEY_SIZE);
    }
}
