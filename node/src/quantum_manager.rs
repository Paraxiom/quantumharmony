//! # Unified Quantum Manager
//!
//! Manages QKD devices, QRNG entropy sources, and CAD price oracle feeds
//! in a unified system for QuantumHarmony.
//!
//! ## Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────────────┐
//! │                     Quantum Manager                                      │
//! ├─────────────────────────────────────────────────────────────────────────┤
//! │                                                                          │
//! │  ┌────────────────┐  ┌────────────────┐  ┌────────────────┐            │
//! │  │  QKD Manager   │  │  QRNG Manager  │  │ Oracle Manager │            │
//! │  │                │  │                │  │                │            │
//! │  │ • Device Pool  │  │ • Entropy Pool │  │ • Price Feeds  │            │
//! │  │ • Key Exchange │  │ • QBER Monitor │  │ • Reporters    │            │
//! │  │ • QBER Verify  │  │ • Threshold    │  │ • Aggregation  │            │
//! │  └───────┬────────┘  └───────┬────────┘  └───────┬────────┘            │
//! │          │                   │                   │                      │
//! │          └───────────────────┼───────────────────┘                      │
//! │                              ↓                                          │
//! │              ┌────────────────────────────┐                             │
//! │              │   Priority Queue System    │                             │
//! │              │   (Unified Event Handler)  │                             │
//! │              └────────────────────────────┘                             │
//! │                              ↓                                          │
//! │              ┌────────────────────────────┐                             │
//! │              │   Blockchain Integration   │                             │
//! │              │   • Entropy Submission     │                             │
//! │              │   • Price Updates          │                             │
//! │              │   • Key Rotation           │                             │
//! │              └────────────────────────────┘                             │
//! │                                                                          │
//! └─────────────────────────────────────────────────────────────────────────┘
//! ```

use priority_queue::PriorityQueue;
use serde::{Deserialize, Serialize};
use std::{
    collections::HashMap,
    sync::{Arc, RwLock},
    time::{Duration, Instant, SystemTime, UNIX_EPOCH},
};
use tokio::sync::{broadcast, mpsc};
use tracing::{debug, error, info, warn};

// ==================== QUANTUM DEVICE TYPES ====================

/// QKD Device status
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum DeviceStatus {
    Online,
    Offline,
    Degraded,
    Calibrating,
}

/// QRNG entropy source
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct QrngDevice {
    pub id: String,
    pub name: String,
    pub status: DeviceStatus,
    pub qber_percent: f64,       // Quantum Bit Error Rate (lower is better)
    pub entropy_rate: u64,       // Bits per second
    pub last_entropy: Vec<u8>,   // Last entropy sample
    pub total_entropy: u64,      // Total entropy provided
    pub last_update: u64,        // Unix timestamp
}

/// QKD Device for key exchange
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct QkdDevice {
    pub id: String,
    pub name: String,
    pub status: DeviceStatus,
    pub peer_id: Option<String>,     // Connected peer
    pub key_rate: u64,               // Keys per second
    pub qber_threshold: f64,         // Maximum acceptable QBER
    pub current_qber: f64,           // Current measured QBER
    pub keys_exchanged: u64,         // Total keys exchanged
    pub last_update: u64,
}

/// CAD Price Reporter
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PriceReporter {
    pub id: String,
    pub name: String,
    pub account: String,             // Blockchain account
    pub status: DeviceStatus,
    pub reputation: u8,              // 0-100
    pub priority: u32,               // Priority in queue
    pub supported_feeds: Vec<String>,
    pub last_submission: u64,
    pub successful_submissions: u64,
    pub total_submissions: u64,
}

/// Price submission
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PriceSubmission {
    pub reporter_id: String,
    pub feed: String,                // "CAD_USD", "QMHY_USD", "QMHY_CAD"
    pub price: u128,                 // 18 decimals fixed point
    pub source: String,              // "binance", "kraken", "average"
    pub timestamp: u64,
    pub priority: u32,
}

// ==================== MANAGER EVENTS ====================

/// Event priority levels
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum EventPriority {
    Critical = 100,    // Security alerts, key compromises
    High = 75,         // Price updates, entropy submissions
    Normal = 50,       // Device status changes
    Low = 25,          // Metrics, telemetry
}

/// Manager event types
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum ManagerEvent {
    QrngEntropyReady {
        device_id: String,
        entropy_bytes: usize,
        qber: u32,  // QBER * 100 (e.g., 85 = 0.85%)
    },
    QkdKeyExchanged {
        device_id: String,
        peer_id: String,
        key_id: [u8; 32],
    },
    PriceSubmitted {
        reporter_id: String,
        feed: String,
        price: u128,
    },
    DeviceStatusChanged {
        device_type: String,
        device_id: String,
        old_status: String,
        new_status: String,
    },
    PriceAggregated {
        feed: String,
        price: u128,
        submission_count: u32,
    },
    QberAlert {
        device_id: String,
        qber_x100: u32,      // QBER * 100 (e.g., 1100 = 11.0%)
        threshold_x100: u32, // Threshold * 100 (e.g., 1100 = 11.0%)
    },
}

impl ManagerEvent {
    pub fn priority(&self) -> EventPriority {
        match self {
            ManagerEvent::QberAlert { .. } => EventPriority::Critical,
            ManagerEvent::QkdKeyExchanged { .. } => EventPriority::High,
            ManagerEvent::PriceSubmitted { .. } => EventPriority::High,
            ManagerEvent::QrngEntropyReady { .. } => EventPriority::High,
            ManagerEvent::PriceAggregated { .. } => EventPriority::Normal,
            ManagerEvent::DeviceStatusChanged { .. } => EventPriority::Low,
        }
    }
}

// ==================== AGGREGATE METRICS ====================

/// Aggregate metrics for dashboard
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct QuantumManagerMetrics {
    pub qrng: QrngMetrics,
    pub qkd: QkdMetrics,
    pub oracle: OracleMetrics,
    pub event_queue_depth: usize,
    pub uptime_seconds: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct QrngMetrics {
    pub device_count: usize,
    pub online_count: usize,
    pub total_entropy_rate: u64,
    pub average_qber: f64,
    pub entropy_pool_size: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct QkdMetrics {
    pub device_count: usize,
    pub online_count: usize,
    pub active_exchanges: usize,
    pub total_keys_exchanged: u64,
    pub average_qber: f64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OracleMetrics {
    pub reporter_count: usize,
    pub active_reporters: usize,
    pub supported_feeds: Vec<String>,
    pub latest_prices: HashMap<String, u128>,
    pub submissions_this_round: usize,
}

// ==================== QUANTUM MANAGER ====================

/// Unified Quantum Manager
pub struct QuantumManager {
    // Device registries
    qrng_devices: Arc<RwLock<HashMap<String, QrngDevice>>>,
    qkd_devices: Arc<RwLock<HashMap<String, QkdDevice>>>,
    price_reporters: Arc<RwLock<HashMap<String, PriceReporter>>>,

    // Price submissions (current round)
    current_submissions: Arc<RwLock<HashMap<String, Vec<PriceSubmission>>>>,

    // Entropy pool
    entropy_pool: Arc<RwLock<Vec<u8>>>,

    // Event queue
    event_queue: Arc<RwLock<PriorityQueue<ManagerEvent, EventPriority>>>,

    // Metrics broadcast
    metrics_tx: broadcast::Sender<QuantumManagerMetrics>,

    // Start time
    start_time: Instant,

    // Latest aggregated prices
    latest_prices: Arc<RwLock<HashMap<String, u128>>>,
}

impl QuantumManager {
    /// Create a new Quantum Manager
    pub fn new() -> Self {
        let (tx, _rx) = broadcast::channel(100);

        Self {
            qrng_devices: Arc::new(RwLock::new(HashMap::new())),
            qkd_devices: Arc::new(RwLock::new(HashMap::new())),
            price_reporters: Arc::new(RwLock::new(HashMap::new())),
            current_submissions: Arc::new(RwLock::new(HashMap::new())),
            entropy_pool: Arc::new(RwLock::new(Vec::new())),
            event_queue: Arc::new(RwLock::new(PriorityQueue::new())),
            metrics_tx: tx,
            start_time: Instant::now(),
            latest_prices: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    // ==================== QRNG MANAGEMENT ====================

    /// Register a QRNG device
    pub fn register_qrng_device(&self, device: QrngDevice) {
        let id = device.id.clone();
        let mut devices = self.qrng_devices.write().unwrap();
        devices.insert(id.clone(), device);
        info!("Registered QRNG device: {}", id);
    }

    /// Submit entropy from a QRNG device
    pub fn submit_entropy(&self, device_id: &str, entropy: Vec<u8>, qber: f64) -> Result<(), String> {
        // Update device
        {
            let mut devices = self.qrng_devices.write().unwrap();
            if let Some(device) = devices.get_mut(device_id) {
                device.last_entropy = entropy.clone();
                device.total_entropy = device.total_entropy.saturating_add(entropy.len() as u64);
                device.qber_percent = qber;
                device.last_update = SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .unwrap()
                    .as_secs();

                // Check QBER threshold (typical threshold is 11% for BB84)
                if qber > 11.0 {
                    let mut queue = self.event_queue.write().unwrap();
                    let alert = ManagerEvent::QberAlert {
                        device_id: device_id.to_string(),
                        qber_x100: (qber * 100.0) as u32,
                        threshold_x100: 1100, // 11.0%
                    };
                    queue.push(alert.clone(), alert.priority());
                    warn!("QBER alert for device {}: {}% > 11%", device_id, qber);
                }
            } else {
                return Err(format!("Device {} not found", device_id));
            }
        }

        // Add to entropy pool
        {
            let mut pool = self.entropy_pool.write().unwrap();
            pool.extend(entropy.iter());

            // Keep pool at reasonable size (1MB max)
            let pool_len = pool.len();
            if pool_len > 1_048_576 {
                let drain_count = pool_len - 1_048_576;
                pool.drain(0..drain_count);
            }
        }

        // Queue event
        let event = ManagerEvent::QrngEntropyReady {
            device_id: device_id.to_string(),
            entropy_bytes: entropy.len(),
            qber: (qber * 100.0) as u32,
        };
        self.queue_event(event);

        Ok(())
    }

    /// Get entropy from the pool
    pub fn get_entropy(&self, bytes: usize) -> Option<Vec<u8>> {
        let mut pool = self.entropy_pool.write().unwrap();
        if pool.len() >= bytes {
            Some(pool.drain(0..bytes).collect())
        } else {
            None
        }
    }

    // ==================== QKD MANAGEMENT ====================

    /// Register a QKD device
    pub fn register_qkd_device(&self, device: QkdDevice) {
        let id = device.id.clone();
        let mut devices = self.qkd_devices.write().unwrap();
        devices.insert(id.clone(), device);
        info!("Registered QKD device: {}", id);
    }

    /// Record a key exchange
    pub fn record_key_exchange(&self, device_id: &str, peer_id: &str, key_id: [u8; 32]) -> Result<(), String> {
        {
            let mut devices = self.qkd_devices.write().unwrap();
            if let Some(device) = devices.get_mut(device_id) {
                device.peer_id = Some(peer_id.to_string());
                device.keys_exchanged = device.keys_exchanged.saturating_add(1);
                device.last_update = SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .unwrap()
                    .as_secs();
            } else {
                return Err(format!("QKD device {} not found", device_id));
            }
        }

        let event = ManagerEvent::QkdKeyExchanged {
            device_id: device_id.to_string(),
            peer_id: peer_id.to_string(),
            key_id,
        };
        self.queue_event(event);

        Ok(())
    }

    // ==================== ORACLE MANAGEMENT ====================

    /// Register a price reporter
    pub fn register_reporter(&self, reporter: PriceReporter) {
        let id = reporter.id.clone();
        let mut reporters = self.price_reporters.write().unwrap();
        reporters.insert(id.clone(), reporter);
        info!("Registered price reporter: {}", id);
    }

    /// Submit a price
    pub fn submit_price(&self, submission: PriceSubmission) -> Result<(), String> {
        // Validate reporter
        {
            let reporters = self.price_reporters.read().unwrap();
            if !reporters.contains_key(&submission.reporter_id) {
                return Err(format!("Reporter {} not found", submission.reporter_id));
            }
        }

        // Add to current submissions
        {
            let mut submissions = self.current_submissions.write().unwrap();
            submissions
                .entry(submission.feed.clone())
                .or_insert_with(Vec::new)
                .push(submission.clone());
        }

        let event = ManagerEvent::PriceSubmitted {
            reporter_id: submission.reporter_id.clone(),
            feed: submission.feed.clone(),
            price: submission.price,
        };
        self.queue_event(event);

        Ok(())
    }

    /// Aggregate prices for a feed
    pub fn aggregate_prices(&self, feed: &str) -> Option<u128> {
        let submissions = {
            let subs = self.current_submissions.read().unwrap();
            subs.get(feed).cloned()
        };

        if let Some(mut subs) = submissions {
            if subs.len() < 3 {
                warn!("Not enough submissions for {}: {} < 3", feed, subs.len());
                return None;
            }

            // Sort by priority (descending)
            subs.sort_by(|a, b| b.priority.cmp(&a.priority));

            // Calculate weighted median
            let prices: Vec<u128> = subs.iter().map(|s| s.price).collect();
            let total_weight: u32 = subs.iter().map(|s| s.priority).sum();
            let half_weight = total_weight / 2;

            let mut sorted_prices: Vec<(u128, u32)> = subs
                .iter()
                .map(|s| (s.price, s.priority))
                .collect();
            sorted_prices.sort_by(|a, b| a.0.cmp(&b.0));

            let mut cumulative = 0u32;
            let median_price = sorted_prices
                .iter()
                .find(|(_, priority)| {
                    cumulative += *priority;
                    cumulative >= half_weight
                })
                .map(|(price, _)| *price)
                .unwrap_or(0);

            // Store latest price
            {
                let mut latest = self.latest_prices.write().unwrap();
                latest.insert(feed.to_string(), median_price);
            }

            // Clear submissions for this feed
            {
                let mut submissions = self.current_submissions.write().unwrap();
                submissions.remove(feed);
            }

            let event = ManagerEvent::PriceAggregated {
                feed: feed.to_string(),
                price: median_price,
                submission_count: subs.len() as u32,
            };
            self.queue_event(event);

            info!(
                "Aggregated {} price: {} from {} submissions",
                feed, median_price, subs.len()
            );

            Some(median_price)
        } else {
            None
        }
    }

    /// Get latest price for a feed
    pub fn get_latest_price(&self, feed: &str) -> Option<u128> {
        let prices = self.latest_prices.read().unwrap();
        prices.get(feed).copied()
    }

    // ==================== EVENT QUEUE ====================

    /// Queue an event
    fn queue_event(&self, event: ManagerEvent) {
        let priority = event.priority();
        let mut queue = self.event_queue.write().unwrap();
        queue.push(event, priority);
    }

    /// Pop the highest priority event
    pub fn pop_event(&self) -> Option<ManagerEvent> {
        let mut queue = self.event_queue.write().unwrap();
        queue.pop().map(|(event, _)| event)
    }

    /// Get event queue depth
    pub fn event_queue_depth(&self) -> usize {
        let queue = self.event_queue.read().unwrap();
        queue.len()
    }

    // ==================== METRICS ====================

    /// Get current metrics
    pub fn get_metrics(&self) -> QuantumManagerMetrics {
        let qrng_devices = self.qrng_devices.read().unwrap();
        let qkd_devices = self.qkd_devices.read().unwrap();
        let reporters = self.price_reporters.read().unwrap();
        let submissions = self.current_submissions.read().unwrap();
        let entropy_pool = self.entropy_pool.read().unwrap();
        let latest_prices = self.latest_prices.read().unwrap();

        // QRNG metrics
        let qrng_online: Vec<_> = qrng_devices
            .values()
            .filter(|d| d.status == DeviceStatus::Online)
            .collect();
        let qrng_metrics = QrngMetrics {
            device_count: qrng_devices.len(),
            online_count: qrng_online.len(),
            total_entropy_rate: qrng_online.iter().map(|d| d.entropy_rate).sum(),
            average_qber: if qrng_online.is_empty() {
                0.0
            } else {
                qrng_online.iter().map(|d| d.qber_percent).sum::<f64>() / qrng_online.len() as f64
            },
            entropy_pool_size: entropy_pool.len(),
        };

        // QKD metrics
        let qkd_online: Vec<_> = qkd_devices
            .values()
            .filter(|d| d.status == DeviceStatus::Online)
            .collect();
        let qkd_metrics = QkdMetrics {
            device_count: qkd_devices.len(),
            online_count: qkd_online.len(),
            active_exchanges: qkd_online.iter().filter(|d| d.peer_id.is_some()).count(),
            total_keys_exchanged: qkd_devices.values().map(|d| d.keys_exchanged).sum(),
            average_qber: if qkd_online.is_empty() {
                0.0
            } else {
                qkd_online.iter().map(|d| d.current_qber).sum::<f64>() / qkd_online.len() as f64
            },
        };

        // Oracle metrics
        let active_reporters: Vec<_> = reporters
            .values()
            .filter(|r| r.status == DeviceStatus::Online)
            .collect();
        let oracle_metrics = OracleMetrics {
            reporter_count: reporters.len(),
            active_reporters: active_reporters.len(),
            supported_feeds: vec![
                "CAD_USD".to_string(),
                "QMHY_USD".to_string(),
                "QMHY_CAD".to_string(),
            ],
            latest_prices: latest_prices.clone(),
            submissions_this_round: submissions.values().map(|v| v.len()).sum(),
        };

        QuantumManagerMetrics {
            qrng: qrng_metrics,
            qkd: qkd_metrics,
            oracle: oracle_metrics,
            event_queue_depth: self.event_queue_depth(),
            uptime_seconds: self.start_time.elapsed().as_secs(),
        }
    }

    /// Subscribe to metrics updates
    pub fn subscribe_metrics(&self) -> broadcast::Receiver<QuantumManagerMetrics> {
        self.metrics_tx.subscribe()
    }

    /// Broadcast current metrics
    pub fn broadcast_metrics(&self) {
        let metrics = self.get_metrics();
        let _ = self.metrics_tx.send(metrics);
    }

    // ==================== LIFECYCLE ====================

    /// Start the metrics broadcast loop
    pub async fn start_metrics_loop(manager: Arc<RwLock<QuantumManager>>) {
        tokio::spawn(async move {
            loop {
                tokio::time::sleep(Duration::from_secs(5)).await;
                let mgr = manager.read().unwrap();
                mgr.broadcast_metrics();
            }
        });
    }
}

impl Default for QuantumManager {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_entropy_submission() {
        let manager = QuantumManager::new();

        // Register device
        let device = QrngDevice {
            id: "qrng-1".to_string(),
            name: "Test QRNG".to_string(),
            status: DeviceStatus::Online,
            qber_percent: 0.5,
            entropy_rate: 1000,
            last_entropy: vec![],
            total_entropy: 0,
            last_update: 0,
        };
        manager.register_qrng_device(device);

        // Submit entropy
        let entropy = vec![0x42; 32];
        manager.submit_entropy("qrng-1", entropy.clone(), 0.5).unwrap();

        // Get entropy
        let retrieved = manager.get_entropy(16).unwrap();
        assert_eq!(retrieved.len(), 16);
    }

    #[test]
    fn test_price_aggregation() {
        let manager = QuantumManager::new();

        // Register reporters
        for i in 1..=5 {
            let reporter = PriceReporter {
                id: format!("reporter-{}", i),
                name: format!("Reporter {}", i),
                account: format!("0x{}", i),
                status: DeviceStatus::Online,
                reputation: 50 + i as u8 * 10,
                priority: 50 + i * 10,
                supported_feeds: vec!["CAD_USD".to_string()],
                last_submission: 0,
                successful_submissions: 0,
                total_submissions: 0,
            };
            manager.register_reporter(reporter);
        }

        // Submit prices (all around 0.74 CAD/USD)
        let prices = vec![
            740_000_000_000_000_000u128, // 0.74
            741_000_000_000_000_000u128, // 0.741
            739_000_000_000_000_000u128, // 0.739
            742_000_000_000_000_000u128, // 0.742
            738_000_000_000_000_000u128, // 0.738
        ];

        for (i, price) in prices.iter().enumerate() {
            let submission = PriceSubmission {
                reporter_id: format!("reporter-{}", i + 1),
                feed: "CAD_USD".to_string(),
                price: *price,
                source: "test".to_string(),
                timestamp: 0,
                priority: 50 + (i as u32 + 1) * 10,
            };
            manager.submit_price(submission).unwrap();
        }

        // Aggregate
        let aggregated = manager.aggregate_prices("CAD_USD").unwrap();

        // Should be weighted median (around 0.74)
        assert!(aggregated > 738_000_000_000_000_000);
        assert!(aggregated < 743_000_000_000_000_000);
    }

    #[test]
    fn test_event_priority() {
        let manager = QuantumManager::new();

        // Queue events in wrong order
        manager.queue_event(ManagerEvent::DeviceStatusChanged {
            device_type: "qrng".to_string(),
            device_id: "1".to_string(),
            old_status: "offline".to_string(),
            new_status: "online".to_string(),
        });

        manager.queue_event(ManagerEvent::QberAlert {
            device_id: "1".to_string(),
            qber_x100: 1500, // 15.0%
            threshold_x100: 1100, // 11.0%
        });

        // Pop should return critical event first
        let event = manager.pop_event().unwrap();
        assert!(matches!(event, ManagerEvent::QberAlert { .. }));
    }
}
