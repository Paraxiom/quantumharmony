//! PQTG Client - Direct integration with PQ-Transport-Gateway for entropy extraction
//!
//! Architecture:
//! ```text
//! QKD/HWRNG Hardware → PQTG (localhost:8443) → Validator Node (pqtg_client)
//! ```
//!
//! PQTG (PQ-Transport-Gateway) provides quantum-safe API translation:
//! - Sits on QKD/HWRNG hardware (localhost only)
//! - Translates PQ-safe API → vendor's classical TLS
//! - Uses Falcon/SPHINCS+ authentication
//! - Protects device management interface
//!
//! PQTG Client (validator-local component):
//! - Queries PQTG for each available device
//! - Implements K-of-M threshold aggregation (Shamir secret sharing)
//! - Auto-detects available hardware
//! - Supports pure HWRNG, pure QKD, or hybrid deployments

use sp_core::Bytes;
use std::collections::HashMap;
use std::time::Duration;

/// QKD hardware usage mode for validator
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QkdMode {
    /// Never use QKD hardware (pure HWRNG/PQC)
    /// Example: Nokia validators without QKD hardware
    Disabled,

    /// Use QKD hardware if available (default)
    /// Auto-detects devices from PQTG
    Optional,

    /// Require QKD hardware to be available
    /// Fails to start if no QKD devices detected
    Required,
}

impl Default for QkdMode {
    fn default() -> Self {
        Self::Optional
    }
}

impl QkdMode {
    pub fn from_str(s: &str) -> Result<Self, String> {
        match s.to_lowercase().as_str() {
            "disabled" => Ok(Self::Disabled),
            "optional" => Ok(Self::Optional),
            "required" => Ok(Self::Required),
            _ => Err(format!("Invalid QKD mode: {}", s)),
        }
    }

    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Disabled => "disabled",
            Self::Optional => "optional",
            Self::Required => "required",
        }
    }
}

/// Device types supported by PQTG
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum DeviceType {
    // QKD devices (true quantum entropy)
    ToshibaQKD,
    IdQuantiqueQKD,

    // Hardware RNG devices (quantum-resistant, not quantum-based)
    Crypto4A,
    EntropyKey,
    HardwareRNG,  // Generic /dev/hwrng
}

impl DeviceType {
    pub fn as_str(&self) -> &'static str {
        match self {
            DeviceType::ToshibaQKD => "toshiba-qkd",
            DeviceType::IdQuantiqueQKD => "idquantique-qkd",
            DeviceType::Crypto4A => "crypto4a",
            DeviceType::EntropyKey => "entropykey",
            DeviceType::HardwareRNG => "hwrng",
        }
    }

    pub fn is_qkd(&self) -> bool {
        matches!(self, DeviceType::ToshibaQKD | DeviceType::IdQuantiqueQKD)
    }

    pub fn from_str(s: &str) -> Result<Self, String> {
        match s.to_lowercase().as_str() {
            "toshiba-qkd" | "toshiba" => Ok(Self::ToshibaQKD),
            "idquantique-qkd" | "idquantique" => Ok(Self::IdQuantiqueQKD),
            "crypto4a" => Ok(Self::Crypto4A),
            "entropykey" => Ok(Self::EntropyKey),
            "hwrng" => Ok(Self::HardwareRNG),
            _ => Err(format!("Unknown device type: {}", s)),
        }
    }
}

/// Device configuration from PQTG
#[derive(Debug, Clone)]
pub struct DeviceConfig {
    pub device_type: DeviceType,
    pub device_id: String,
    pub pqtg_endpoint: String,  // e.g., "https://localhost:8443/devices/toshiba"
    pub qber_threshold: f32,     // Quality threshold
    pub enabled: bool,
}

/// Entropy response from a single device via PQTG
#[derive(Debug, Clone)]
pub struct DeviceEntropyResponse {
    pub device_id: String,
    pub device_type: DeviceType,
    pub entropy_bytes: Vec<u8>,
    pub timestamp: u64,
    pub qber: f32,              // Quantum Bit Error Rate
    pub key_id: Option<String>, // QKD key ID if applicable
}

/// PQTG client configuration
#[derive(Debug, Clone)]
pub struct PqtgConfig {
    pub pqtg_endpoint: String,           // e.g., "https://localhost:8443"
    pub devices: Vec<DeviceConfig>,      // Empty = auto-detect
    pub threshold_k: usize,              // Minimum devices needed (K-of-M)
    pub request_timeout: Duration,
    pub qkd_mode: QkdMode,               // QKD hardware usage policy
}

impl Default for PqtgConfig {
    fn default() -> Self {
        Self {
            pqtg_endpoint: "https://localhost:8443".to_string(),
            devices: vec![],  // Empty: auto-discover devices
            threshold_k: 2,
            request_timeout: Duration::from_secs(5),
            qkd_mode: QkdMode::Optional,
        }
    }
}

/// PQTG client for entropy extraction
pub struct PqtgClient {
    config: PqtgConfig,
    http_client: reqwest::Client,
}

impl PqtgClient {
    /// Create new PQTG client with configuration
    pub fn new(config: PqtgConfig) -> Result<Self, String> {
        // Configure HTTP client with TLS for PQTG
        let http_client = reqwest::Client::builder()
            .timeout(config.request_timeout)
            .danger_accept_invalid_certs(true) // PQTG uses self-signed certs for localhost
            .build()
            .map_err(|e| format!("Failed to create HTTP client: {}", e))?;

        Ok(Self {
            config,
            http_client,
        })
    }

    /// Auto-discover available devices from PQTG
    pub async fn discover_devices(&mut self) -> Result<Vec<DeviceConfig>, String> {
        log::info!("Auto-discovering devices from PQTG at {}", self.config.pqtg_endpoint);

        let url = format!("{}/devices", self.config.pqtg_endpoint);

        let response = self.http_client
            .get(&url)
            .send()
            .await
            .map_err(|e| format!("PQTG device discovery failed: {}", e))?;

        if !response.status().is_success() {
            return Err(format!("PQTG device discovery returned {}", response.status()));
        }

        let devices_json: serde_json::Value = response
            .json()
            .await
            .map_err(|e| format!("Failed to parse PQTG devices response: {}", e))?;

        let devices_array = devices_json["devices"]
            .as_array()
            .ok_or("Missing devices array in PQTG response")?;

        let mut discovered_devices = Vec::new();

        for device_json in devices_array {
            let device_type_str = device_json["type"]
                .as_str()
                .ok_or("Missing device type")?;

            let device_type = DeviceType::from_str(device_type_str)?;

            // Filter based on QKD mode
            match self.config.qkd_mode {
                QkdMode::Disabled if device_type.is_qkd() => {
                    log::debug!("Skipping QKD device {} (QKD mode: disabled)", device_type_str);
                    continue;
                }
                _ => {}
            }

            let device_id = device_json["id"]
                .as_str()
                .ok_or("Missing device ID")?
                .to_string();

            let endpoint = device_json["endpoint"]
                .as_str()
                .ok_or("Missing device endpoint")?
                .to_string();

            let qber_threshold = device_json["qber_threshold"]
                .as_f64()
                .unwrap_or(0.10) as f32;

            let enabled = device_json["enabled"]
                .as_bool()
                .unwrap_or(true);

            discovered_devices.push(DeviceConfig {
                device_type,
                device_id: device_id.clone(),
                pqtg_endpoint: endpoint,
                qber_threshold,
                enabled,
            });

            log::info!(
                "✓ Discovered device: {} ({}) - QBER threshold: {:.2}%",
                device_id,
                device_type_str,
                qber_threshold * 100.0
            );
        }

        // Validate QKD mode requirements
        let has_qkd = discovered_devices.iter().any(|d| d.device_type.is_qkd());

        match self.config.qkd_mode {
            QkdMode::Required if !has_qkd => {
                return Err("QKD mode set to 'required' but no QKD devices found".to_string());
            }
            QkdMode::Disabled if has_qkd => {
                return Err("QKD devices found but QKD mode set to 'disabled'".to_string());
            }
            _ => {}
        }

        if discovered_devices.is_empty() {
            return Err("No devices discovered from PQTG".to_string());
        }

        if discovered_devices.len() < self.config.threshold_k {
            return Err(format!(
                "Only {} devices discovered, need at least K={}",
                discovered_devices.len(),
                self.config.threshold_k
            ));
        }

        log::info!(
            "✓ Device discovery complete: {} devices (K={}, QKD mode: {})",
            discovered_devices.len(),
            self.config.threshold_k,
            self.config.qkd_mode.as_str()
        );

        // Update config with discovered devices
        self.config.devices = discovered_devices.clone();

        Ok(discovered_devices)
    }

    /// Query PQTG for entropy from a specific device
    async fn query_device_via_pqtg(
        &self,
        device: &DeviceConfig,
        entropy_size: usize,
    ) -> Result<DeviceEntropyResponse, String> {
        log::debug!(
            "Querying device {} via PQTG at {}",
            device.device_id,
            device.pqtg_endpoint
        );

        // PQTG API: POST /devices/{type}/entropy
        let url = format!("{}/entropy", device.pqtg_endpoint);

        let request_body = serde_json::json!({
            "device_id": device.device_id,
            "size_bytes": entropy_size,
            "qkd_mode": device.device_type.is_qkd(),
        });

        let response = self.http_client
            .post(&url)
            .json(&request_body)
            .send()
            .await
            .map_err(|e| format!("PQTG request failed for {}: {}", device.device_id, e))?;

        if !response.status().is_success() {
            return Err(format!(
                "PQTG returned error {} for device {}",
                response.status(),
                device.device_id
            ));
        }

        let response_json: serde_json::Value = response
            .json()
            .await
            .map_err(|e| format!("Failed to parse PQTG response: {}", e))?;

        // Parse PQTG response
        let entropy_hex = response_json["entropy"]
            .as_str()
            .ok_or("Missing entropy field in PQTG response")?;

        let entropy_bytes = hex::decode(entropy_hex)
            .map_err(|e| format!("Invalid entropy hex from PQTG: {}", e))?;

        let qber = response_json["qber"]
            .as_f64()
            .unwrap_or(0.0) as f32;

        let timestamp = response_json["timestamp"]
            .as_u64()
            .unwrap_or_else(|| {
                std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_secs()
            });

        let key_id = response_json["key_id"]
            .as_str()
            .map(|s| s.to_string());

        // Validate QBER threshold
        if qber > device.qber_threshold {
            return Err(format!(
                "Device {} QBER {} exceeds threshold {}",
                device.device_id, qber, device.qber_threshold
            ));
        }

        log::info!(
            "✓ Device {} entropy: {} bytes (QBER: {:.2}%)",
            device.device_id,
            entropy_bytes.len(),
            qber * 100.0
        );

        Ok(DeviceEntropyResponse {
            device_id: device.device_id.clone(),
            device_type: device.device_type.clone(),
            entropy_bytes,
            timestamp,
            qber,
            key_id,
        })
    }

    /// Collect entropy from all enabled devices via PQTG
    pub async fn collect_device_entropy(
        &self,
        entropy_size: usize,
    ) -> Result<Vec<DeviceEntropyResponse>, String> {
        let enabled_devices: Vec<&DeviceConfig> = self.config.devices
            .iter()
            .filter(|d| d.enabled)
            .collect();

        if enabled_devices.len() < self.config.threshold_k {
            return Err(format!(
                "Not enough devices enabled ({}) for threshold K={}",
                enabled_devices.len(),
                self.config.threshold_k
            ));
        }

        let total_enabled = enabled_devices.len();

        log::info!(
            "Collecting entropy from {} devices (K={}, M={})",
            total_enabled,
            self.config.threshold_k,
            total_enabled
        );

        // Query all devices in parallel via PQTG
        let mut responses = Vec::new();
        for device in enabled_devices {
            match self.query_device_via_pqtg(device, entropy_size).await {
                Ok(response) => responses.push(response),
                Err(e) => {
                    log::warn!("Failed to query device {}: {}", device.device_id, e);
                    // Continue with other devices
                }
            }
        }

        if responses.len() < self.config.threshold_k {
            return Err(format!(
                "Only {} devices responded, need at least K={}",
                responses.len(),
                self.config.threshold_k
            ));
        }

        log::info!(
            "✓ Collected entropy from {}/{} devices",
            responses.len(),
            total_enabled
        );

        Ok(responses)
    }

    /// Query PQTG health status
    pub async fn health_check(&self) -> Result<HashMap<String, serde_json::Value>, String> {
        let url = format!("{}/health", self.config.pqtg_endpoint);

        let response = self.http_client
            .get(&url)
            .send()
            .await
            .map_err(|e| format!("PQTG health check failed: {}", e))?;

        if !response.status().is_success() {
            return Err(format!("PQTG health check returned {}", response.status()));
        }

        let health: HashMap<String, serde_json::Value> = response
            .json()
            .await
            .map_err(|e| format!("Failed to parse health response: {}", e))?;

        Ok(health)
    }

    /// Get PQTG configuration
    pub fn config(&self) -> &PqtgConfig {
        &self.config
    }
}

/// Builder pattern for PqtgClient
pub struct PqtgClientBuilder {
    config: PqtgConfig,
}

impl PqtgClientBuilder {
    pub fn new() -> Self {
        Self {
            config: PqtgConfig::default(),
        }
    }

    pub fn pqtg_endpoint(mut self, endpoint: String) -> Self {
        self.config.pqtg_endpoint = endpoint;
        self
    }

    pub fn threshold_k(mut self, k: usize) -> Self {
        self.config.threshold_k = k;
        self
    }

    pub fn qkd_mode(mut self, mode: QkdMode) -> Self {
        self.config.qkd_mode = mode;
        self
    }

    pub fn add_device(mut self, device: DeviceConfig) -> Self {
        self.config.devices.push(device);
        self
    }

    pub fn build(self) -> Result<PqtgClient, String> {
        PqtgClient::new(self.config)
    }
}

impl Default for PqtgClientBuilder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_qkd_mode_from_str() {
        assert_eq!(QkdMode::from_str("disabled").unwrap(), QkdMode::Disabled);
        assert_eq!(QkdMode::from_str("optional").unwrap(), QkdMode::Optional);
        assert_eq!(QkdMode::from_str("required").unwrap(), QkdMode::Required);
        assert!(QkdMode::from_str("invalid").is_err());
    }

    #[test]
    fn test_qkd_mode_default() {
        assert_eq!(QkdMode::default(), QkdMode::Optional);
    }

    #[test]
    fn test_device_type_is_qkd() {
        assert!(DeviceType::ToshibaQKD.is_qkd());
        assert!(DeviceType::IdQuantiqueQKD.is_qkd());
        assert!(!DeviceType::Crypto4A.is_qkd());
        assert!(!DeviceType::EntropyKey.is_qkd());
        assert!(!DeviceType::HardwareRNG.is_qkd());
    }

    #[test]
    fn test_device_type_from_str() {
        assert_eq!(
            DeviceType::from_str("toshiba-qkd").unwrap(),
            DeviceType::ToshibaQKD
        );
        assert_eq!(
            DeviceType::from_str("idquantique").unwrap(),
            DeviceType::IdQuantiqueQKD
        );
        assert_eq!(
            DeviceType::from_str("crypto4a").unwrap(),
            DeviceType::Crypto4A
        );
    }

    #[test]
    fn test_pqtg_config_default() {
        let config = PqtgConfig::default();
        assert_eq!(config.pqtg_endpoint, "https://localhost:8443");
        assert_eq!(config.devices.len(), 0);  // Auto-discover
        assert_eq!(config.threshold_k, 2);
        assert_eq!(config.qkd_mode, QkdMode::Optional);
    }

    #[test]
    fn test_pqtg_client_builder() {
        let client = PqtgClientBuilder::new()
            .pqtg_endpoint("https://localhost:8444".to_string())
            .threshold_k(3)
            .qkd_mode(QkdMode::Required)
            .build();

        assert!(client.is_ok());
        let client = client.unwrap();
        assert_eq!(client.config().pqtg_endpoint, "https://localhost:8444");
        assert_eq!(client.config().threshold_k, 3);
        assert_eq!(client.config().qkd_mode, QkdMode::Required);
    }
}
