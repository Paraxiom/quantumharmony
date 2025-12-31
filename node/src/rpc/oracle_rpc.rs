//! Oracle RPC API
//!
//! Provides RPC endpoints for the decentralized oracle system:
//! - Price submissions from reporters
//! - Price queries for all feeds
//! - Reporter management
//! - Real-time metrics

use jsonrpsee::core::RpcResult;
use jsonrpsee::proc_macros::rpc;
use jsonrpsee::types::ErrorObjectOwned;
use serde::{Deserialize, Serialize};
use sp_api::ProvideRuntimeApi;
use sp_blockchain::HeaderBackend;
use sp_runtime::traits::Block as BlockT;
use std::collections::HashMap;
use std::marker::PhantomData;
use std::sync::{Arc, RwLock};
use std::time::{SystemTime, UNIX_EPOCH};

/// Price feed types
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum PriceFeed {
    CadUsd,
    QmhyUsd,
    QmhyCad,
}

impl std::fmt::Display for PriceFeed {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PriceFeed::CadUsd => write!(f, "CAD_USD"),
            PriceFeed::QmhyUsd => write!(f, "QMHY_USD"),
            PriceFeed::QmhyCad => write!(f, "QMHY_CAD"),
        }
    }
}

/// Reporter info returned by RPC
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReporterInfo {
    pub id: String,
    pub account: String,
    pub reputation: u8,
    pub priority: u32,
    pub status: String,
    pub supported_feeds: Vec<String>,
    pub successful_submissions: u64,
    pub total_submissions: u64,
}

/// Price submission request
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PriceSubmissionRequest {
    pub reporter_id: String,
    pub feed: String,
    pub price: String,       // String to handle large numbers safely
    pub source: String,      // e.g., "binance", "kraken", "average"
    pub signature: String,   // Hex-encoded SPHINCS+ signature
}

/// Price info returned by RPC
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PriceInfo {
    pub feed: String,
    pub price: String,           // String for precision
    pub price_formatted: String, // Human-readable format
    pub submission_count: u32,
    pub last_update: u64,
    pub std_deviation: String,
}

/// Oracle metrics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OracleMetrics {
    pub reporter_count: u32,
    pub active_reporters: u32,
    pub current_round: u64,
    pub submissions_this_round: HashMap<String, u32>,
    pub latest_prices: HashMap<String, PriceInfo>,
    pub uptime_seconds: u64,
}

/// Stored price submission
#[derive(Debug, Clone)]
struct StoredSubmission {
    reporter_id: String,
    price: u128,
    timestamp: u64,
    priority: u32,
    source: String,
}

/// Stored reporter
#[derive(Debug, Clone)]
struct StoredReporter {
    id: String,
    account: String,
    reputation: u8,
    priority: u32,
    status: String,
    supported_feeds: Vec<String>,
    successful_submissions: u64,
    total_submissions: u64,
}

/// Oracle RPC trait defining all methods
#[rpc(server, client)]
pub trait OracleApi {
    /// Submit a price for a feed
    #[method(name = "oracle_submitPrice")]
    async fn submit_price(&self, request: PriceSubmissionRequest) -> RpcResult<bool>;

    /// Get the latest price for a feed
    #[method(name = "oracle_getPrice")]
    async fn get_price(&self, feed: String) -> RpcResult<Option<PriceInfo>>;

    /// Get all latest prices
    #[method(name = "oracle_getAllPrices")]
    async fn get_all_prices(&self) -> RpcResult<HashMap<String, PriceInfo>>;

    /// Get CAD/USD exchange rate (convenience method)
    #[method(name = "oracle_getCadUsdRate")]
    async fn get_cad_usd_rate(&self) -> RpcResult<Option<String>>;

    /// Get QMHY/CAD price (convenience method)
    #[method(name = "oracle_getQmhyCadPrice")]
    async fn get_qmhy_cad_price(&self) -> RpcResult<Option<String>>;

    /// Register as a price reporter
    #[method(name = "oracle_registerReporter")]
    async fn register_reporter(
        &self,
        id: String,
        account: String,
        supported_feeds: Vec<String>,
    ) -> RpcResult<bool>;

    /// Get reporter info
    #[method(name = "oracle_getReporter")]
    async fn get_reporter(&self, reporter_id: String) -> RpcResult<Option<ReporterInfo>>;

    /// Get all reporters
    #[method(name = "oracle_getAllReporters")]
    async fn get_all_reporters(&self) -> RpcResult<Vec<ReporterInfo>>;

    /// Get oracle metrics
    #[method(name = "oracle_getMetrics")]
    async fn get_metrics(&self) -> RpcResult<OracleMetrics>;

    /// Get current submissions for a feed (this round)
    #[method(name = "oracle_getCurrentSubmissions")]
    async fn get_current_submissions(&self, feed: String) -> RpcResult<u32>;

    /// Force price aggregation (admin only - for testing)
    #[method(name = "oracle_forceAggregate")]
    async fn force_aggregate(&self, feed: String, admin_key: String) -> RpcResult<Option<PriceInfo>>;
}

/// Oracle RPC implementation
pub struct OracleRpc<C, Block> {
    client: Arc<C>,
    reporters: Arc<RwLock<HashMap<String, StoredReporter>>>,
    current_submissions: Arc<RwLock<HashMap<String, Vec<StoredSubmission>>>>,
    latest_prices: Arc<RwLock<HashMap<String, PriceInfo>>>,
    current_round: Arc<RwLock<u64>>,
    start_time: u64,
    _phantom: PhantomData<Block>,
}

impl<C, Block> OracleRpc<C, Block>
where
    Block: BlockT,
    C: ProvideRuntimeApi<Block> + HeaderBackend<Block> + 'static,
{
    pub fn new(client: Arc<C>) -> Self {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        Self {
            client,
            reporters: Arc::new(RwLock::new(HashMap::new())),
            current_submissions: Arc::new(RwLock::new(HashMap::new())),
            latest_prices: Arc::new(RwLock::new(HashMap::new())),
            current_round: Arc::new(RwLock::new(1)),
            start_time: now,
            _phantom: PhantomData,
        }
    }

    /// Calculate weighted median from submissions
    fn calculate_weighted_median(submissions: &[StoredSubmission]) -> u128 {
        if submissions.is_empty() {
            return 0;
        }

        // Sort by price
        let mut sorted: Vec<(u128, u32)> = submissions
            .iter()
            .map(|s| (s.price, s.priority))
            .collect();
        sorted.sort_by(|a, b| a.0.cmp(&b.0));

        // Calculate total weight
        let total_weight: u32 = sorted.iter().map(|(_, p)| *p).sum();
        let half_weight = total_weight / 2;

        // Find weighted median
        let mut cumulative = 0u32;
        for (price, priority) in sorted.iter() {
            cumulative += *priority;
            if cumulative >= half_weight {
                return *price;
            }
        }

        // Fallback
        sorted.last().map(|(p, _)| *p).unwrap_or(0)
    }

    /// Calculate standard deviation
    fn calculate_std_deviation(submissions: &[StoredSubmission], mean: u128) -> u128 {
        if submissions.is_empty() {
            return 0;
        }

        let variance: u128 = submissions.iter().map(|s| {
            let diff = if s.price > mean { s.price - mean } else { mean - s.price };
            diff.saturating_mul(diff) / submissions.len() as u128
        }).sum();

        // Integer square root
        Self::isqrt(variance)
    }

    fn isqrt(n: u128) -> u128 {
        if n == 0 {
            return 0;
        }
        let mut x = n;
        let mut y = (x + 1) / 2;
        while y < x {
            x = y;
            y = (x + n / x) / 2;
        }
        x
    }

    /// Format price for display (18 decimals -> human readable)
    fn format_price(price: u128) -> String {
        let whole = price / 1_000_000_000_000_000_000u128;
        let fraction = (price % 1_000_000_000_000_000_000u128) / 1_000_000_000_000u128;
        format!("{}.{:06}", whole, fraction)
    }
}

#[jsonrpsee::core::async_trait]
impl<C, Block> OracleApiServer for OracleRpc<C, Block>
where
    Block: BlockT,
    C: ProvideRuntimeApi<Block> + HeaderBackend<Block> + Send + Sync + 'static,
{
    async fn submit_price(&self, request: PriceSubmissionRequest) -> RpcResult<bool> {
        // Validate reporter exists
        {
            let reporters = self.reporters.read().unwrap();
            if !reporters.contains_key(&request.reporter_id) {
                return Err(ErrorObjectOwned::owned(
                    -32001,
                    format!("Reporter {} not registered", request.reporter_id),
                    None::<String>,
                ));
            }

            let reporter = reporters.get(&request.reporter_id).unwrap();
            if reporter.status != "active" {
                return Err(ErrorObjectOwned::owned(
                    -32002,
                    format!("Reporter {} is not active", request.reporter_id),
                    None::<String>,
                ));
            }

            // Check feed is supported
            if !reporter.supported_feeds.contains(&request.feed) {
                return Err(ErrorObjectOwned::owned(
                    -32003,
                    format!("Reporter {} does not support feed {}", request.reporter_id, request.feed),
                    None::<String>,
                ));
            }
        }

        // Parse price
        let price: u128 = request.price.parse().map_err(|_| {
            ErrorObjectOwned::owned(
                -32004,
                "Invalid price format".to_string(),
                None::<String>,
            )
        })?;

        if price == 0 {
            return Err(ErrorObjectOwned::owned(
                -32005,
                "Price cannot be zero".to_string(),
                None::<String>,
            ));
        }

        // Get reporter priority
        let priority = {
            let reporters = self.reporters.read().unwrap();
            reporters.get(&request.reporter_id).map(|r| r.priority).unwrap_or(50)
        };

        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        let submission = StoredSubmission {
            reporter_id: request.reporter_id.clone(),
            price,
            timestamp: now,
            priority,
            source: request.source,
        };

        // Add to current submissions
        {
            let mut submissions = self.current_submissions.write().unwrap();
            submissions
                .entry(request.feed.clone())
                .or_insert_with(Vec::new)
                .push(submission);
        }

        // Update reporter stats
        {
            let mut reporters = self.reporters.write().unwrap();
            if let Some(reporter) = reporters.get_mut(&request.reporter_id) {
                reporter.total_submissions += 1;
            }
        }

        log::info!(
            "Price submitted: {} = {} by {}",
            request.feed,
            Self::format_price(price),
            request.reporter_id
        );

        Ok(true)
    }

    async fn get_price(&self, feed: String) -> RpcResult<Option<PriceInfo>> {
        let prices = self.latest_prices.read().unwrap();
        Ok(prices.get(&feed).cloned())
    }

    async fn get_all_prices(&self) -> RpcResult<HashMap<String, PriceInfo>> {
        let prices = self.latest_prices.read().unwrap();
        Ok(prices.clone())
    }

    async fn get_cad_usd_rate(&self) -> RpcResult<Option<String>> {
        let prices = self.latest_prices.read().unwrap();
        Ok(prices.get("CAD_USD").map(|p| p.price_formatted.clone()))
    }

    async fn get_qmhy_cad_price(&self) -> RpcResult<Option<String>> {
        let prices = self.latest_prices.read().unwrap();
        Ok(prices.get("QMHY_CAD").map(|p| p.price_formatted.clone()))
    }

    async fn register_reporter(
        &self,
        id: String,
        account: String,
        supported_feeds: Vec<String>,
    ) -> RpcResult<bool> {
        // Validate feeds
        let valid_feeds = ["CAD_USD", "QMHY_USD", "QMHY_CAD"];
        for feed in &supported_feeds {
            if !valid_feeds.contains(&feed.as_str()) {
                return Err(ErrorObjectOwned::owned(
                    -32010,
                    format!("Invalid feed: {}", feed),
                    None::<String>,
                ));
            }
        }

        let reporter = StoredReporter {
            id: id.clone(),
            account,
            reputation: 50,  // Start with neutral reputation
            priority: 50,    // Initial priority
            status: "active".to_string(),
            supported_feeds,
            successful_submissions: 0,
            total_submissions: 0,
        };

        {
            let mut reporters = self.reporters.write().unwrap();
            reporters.insert(id.clone(), reporter);
        }

        log::info!("Reporter registered: {}", id);

        Ok(true)
    }

    async fn get_reporter(&self, reporter_id: String) -> RpcResult<Option<ReporterInfo>> {
        let reporters = self.reporters.read().unwrap();
        Ok(reporters.get(&reporter_id).map(|r| ReporterInfo {
            id: r.id.clone(),
            account: r.account.clone(),
            reputation: r.reputation,
            priority: r.priority,
            status: r.status.clone(),
            supported_feeds: r.supported_feeds.clone(),
            successful_submissions: r.successful_submissions,
            total_submissions: r.total_submissions,
        }))
    }

    async fn get_all_reporters(&self) -> RpcResult<Vec<ReporterInfo>> {
        let reporters = self.reporters.read().unwrap();
        Ok(reporters.values().map(|r| ReporterInfo {
            id: r.id.clone(),
            account: r.account.clone(),
            reputation: r.reputation,
            priority: r.priority,
            status: r.status.clone(),
            supported_feeds: r.supported_feeds.clone(),
            successful_submissions: r.successful_submissions,
            total_submissions: r.total_submissions,
        }).collect())
    }

    async fn get_metrics(&self) -> RpcResult<OracleMetrics> {
        let reporters = self.reporters.read().unwrap();
        let submissions = self.current_submissions.read().unwrap();
        let prices = self.latest_prices.read().unwrap();
        let round = *self.current_round.read().unwrap();

        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        let submissions_count: HashMap<String, u32> = submissions
            .iter()
            .map(|(k, v)| (k.clone(), v.len() as u32))
            .collect();

        Ok(OracleMetrics {
            reporter_count: reporters.len() as u32,
            active_reporters: reporters.values().filter(|r| r.status == "active").count() as u32,
            current_round: round,
            submissions_this_round: submissions_count,
            latest_prices: prices.clone(),
            uptime_seconds: now.saturating_sub(self.start_time),
        })
    }

    async fn get_current_submissions(&self, feed: String) -> RpcResult<u32> {
        let submissions = self.current_submissions.read().unwrap();
        Ok(submissions.get(&feed).map(|v| v.len() as u32).unwrap_or(0))
    }

    async fn force_aggregate(&self, feed: String, admin_key: String) -> RpcResult<Option<PriceInfo>> {
        // Simple admin key check (in production, use proper auth)
        if admin_key != "quantum-admin-key" {
            return Err(ErrorObjectOwned::owned(
                -32100,
                "Invalid admin key".to_string(),
                None::<String>,
            ));
        }

        let submissions = {
            let mut subs = self.current_submissions.write().unwrap();
            subs.remove(&feed).unwrap_or_default()
        };

        if submissions.len() < 3 {
            return Err(ErrorObjectOwned::owned(
                -32101,
                format!("Not enough submissions for {}: {} < 3", feed, submissions.len()),
                None::<String>,
            ));
        }

        let median_price = Self::calculate_weighted_median(&submissions);
        let std_dev = Self::calculate_std_deviation(&submissions, median_price);

        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        let price_info = PriceInfo {
            feed: feed.clone(),
            price: median_price.to_string(),
            price_formatted: Self::format_price(median_price),
            submission_count: submissions.len() as u32,
            last_update: now,
            std_deviation: std_dev.to_string(),
        };

        // Store the aggregated price
        {
            let mut prices = self.latest_prices.write().unwrap();
            prices.insert(feed.clone(), price_info.clone());
        }

        // Update reporter reputations
        {
            let mut reporters = self.reporters.write().unwrap();
            for sub in &submissions {
                if let Some(reporter) = reporters.get_mut(&sub.reporter_id) {
                    // Calculate deviation
                    let deviation = if sub.price > median_price {
                        ((sub.price - median_price) as f64 / median_price as f64) * 100.0
                    } else {
                        ((median_price - sub.price) as f64 / median_price as f64) * 100.0
                    };

                    // Adjust reputation based on accuracy
                    if deviation < 1.0 {
                        reporter.reputation = reporter.reputation.saturating_add(2).min(100);
                        reporter.successful_submissions += 1;
                    } else if deviation < 2.0 {
                        reporter.reputation = reporter.reputation.saturating_add(1).min(100);
                        reporter.successful_submissions += 1;
                    } else if deviation > 5.0 {
                        reporter.reputation = reporter.reputation.saturating_sub(2);
                    } else if deviation > 10.0 {
                        reporter.reputation = reporter.reputation.saturating_sub(5);
                    }

                    // Update priority based on reputation
                    reporter.priority = 50 + (reporter.reputation as u32 / 2);
                }
            }
        }

        // Increment round
        {
            let mut round = self.current_round.write().unwrap();
            *round += 1;
        }

        log::info!(
            "Aggregated {} price: {} from {} submissions",
            feed,
            Self::format_price(median_price),
            submissions.len()
        );

        Ok(Some(price_info))
    }
}
