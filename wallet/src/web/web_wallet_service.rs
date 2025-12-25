use jsonrpsee::ws_client::WsClient;
use serde::{Deserialize, Serialize};
use warp::{Filter, Rejection, Reply};
use std::sync::Arc;
use tokio::sync::RwLock;
use sp_core::{crypto::Ss58Codec, sr25519, Pair};

/// Web-friendly wallet service that provides REST API
pub struct WebWalletService {
    substrate_client: Arc<WsClient>,
    quantum_proxy: Option<Arc<QuantumProxy>>,
    operator_registry: Arc<RwLock<OperatorRegistry>>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct CreateAccountRequest {
    pub name: String,
    pub account_type: AccountType,
}

#[derive(Debug, Serialize, Deserialize)]
pub enum AccountType {
    Basic,
    NodeOperator,
    QuantumOperator,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct AccountInfo {
    pub address: String,
    pub seed_phrase: String,  // Only shown once!
    pub account_type: AccountType,
    pub quantum_ready: bool,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct TransferRequest {
    pub from: String,
    pub to: String,
    pub amount: String,
    pub password: String,  // For encrypted keystore
}

#[derive(Debug, Serialize, Deserialize)]
pub struct StakeRequest {
    pub delegator: String,
    pub validator: String,
    pub amount: String,
    pub password: String,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct OperatorInfo {
    pub address: String,
    pub operator_type: OperatorType,
    pub stake: String,
    pub commission: f32,
    pub uptime: f32,
    pub quantum_services: Option<QuantumServices>,
}

#[derive(Debug, Serialize, Deserialize, PartialEq)]
pub enum OperatorType {
    Classical,
    QuantumEnabled,
}

#[derive(Debug, Serialize, Deserialize, PartialEq)]
pub struct QuantumServices {
    pub qrng_available: bool,
    pub qkd_endpoints: Vec<String>,
    pub entropy_price: String,  // COHR per MB
    pub last_proof: u64,        // Block number
}

pub struct OperatorRegistry {
    operators: std::collections::HashMap<String, OperatorInfo>,
}

pub struct QuantumProxy {
    // Proxies quantum requests to actual quantum operators
    quantum_operators: Vec<String>,
}

impl WebWalletService {
    pub async fn new(substrate_url: &str) -> Result<Self, Box<dyn std::error::Error>> {
        let client = jsonrpsee::ws_client::WsClientBuilder::default()
            .build(substrate_url)
            .await?;
            
        Ok(Self {
            substrate_client: Arc::new(client),
            quantum_proxy: None,
            operator_registry: Arc::new(RwLock::new(OperatorRegistry {
                operators: std::collections::HashMap::new(),
            })),
        })
    }
    
    /// Start the web service
    pub async fn run(self: Arc<Self>, port: u16) {
        let service = self.clone();
        
        // Health check
        let health = warp::path("health")
            .map(|| warp::reply::json(&serde_json::json!({"status": "ok"})));
        
        // Create account
        let create_account = warp::path("account")
            .and(warp::post())
            .and(warp::body::json())
            .and(with_service(service.clone()))
            .and_then(handle_create_account);
            
        // Get balance
        let get_balance = warp::path!("balance" / String)
            .and(warp::get())
            .and(with_service(service.clone()))
            .and_then(handle_get_balance);
            
        // Transfer
        let transfer = warp::path("transfer")
            .and(warp::post())
            .and(warp::body::json())
            .and(with_service(service.clone()))
            .and_then(handle_transfer);
            
        // Stake
        let stake = warp::path("stake")
            .and(warp::post())
            .and(warp::body::json())
            .and(with_service(service.clone()))
            .and_then(handle_stake);
            
        // List operators
        let operators = warp::path("operators")
            .and(warp::get())
            .and(with_service(service.clone()))
            .and_then(handle_list_operators);
            
        // Get quantum status
        let quantum_status = warp::path("quantum")
            .and(warp::get())
            .and(with_service(service.clone()))
            .and_then(handle_quantum_status);
        
        let routes = health
            .or(create_account)
            .or(get_balance)
            .or(transfer)
            .or(stake)
            .or(operators)
            .or(quantum_status)
            .with(warp::cors().allow_any_origin());
        
        println!("🌐 Web Wallet Service running on http://0.0.0.0:{}", port);
        warp::serve(routes).run(([0, 0, 0, 0], port)).await;
    }
}

// Helper function to inject service
fn with_service(
    service: Arc<WebWalletService>,
) -> impl Filter<Extract = (Arc<WebWalletService>,), Error = std::convert::Infallible> + Clone {
    warp::any().map(move || service.clone())
}

// Handler functions
async fn handle_create_account(
    req: CreateAccountRequest,
    service: Arc<WebWalletService>,
) -> Result<impl Reply, Rejection> {
    // Generate new account based on type
    use sp_core::{sr25519, Pair};
    
    let (pair, seed, _) = sr25519::Pair::generate_with_phrase(None);
    let address = pair.public().to_ss58check();
    
    let quantum_ready = matches!(req.account_type, AccountType::QuantumOperator);
    
    let account = AccountInfo {
        address,
        seed_phrase: seed,
        account_type: req.account_type,
        quantum_ready,
    };
    
    Ok(warp::reply::json(&account))
}

async fn handle_get_balance(
    address: String,
    service: Arc<WebWalletService>,
) -> Result<impl Reply, Rejection> {
    // Query balance from chain
    // TODO: Implement actual balance query
    let balance = serde_json::json!({
        "address": address,
        "free": "1000000000000000000000",  // 1000 COHR
        "reserved": "0",
        "total": "1000000000000000000000",
    });
    
    Ok(warp::reply::json(&balance))
}

async fn handle_transfer(
    req: TransferRequest,
    service: Arc<WebWalletService>,
) -> Result<impl Reply, Rejection> {
    // TODO: Implement actual transfer
    let result = serde_json::json!({
        "tx_hash": "0x1234567890abcdef",
        "from": req.from,
        "to": req.to,
        "amount": req.amount,
        "status": "pending",
    });
    
    Ok(warp::reply::json(&result))
}

async fn handle_stake(
    req: StakeRequest,
    service: Arc<WebWalletService>,
) -> Result<impl Reply, Rejection> {
    // TODO: Implement staking
    let result = serde_json::json!({
        "tx_hash": "0xabcdef1234567890",
        "delegator": req.delegator,
        "validator": req.validator,
        "amount": req.amount,
        "status": "pending",
    });
    
    Ok(warp::reply::json(&result))
}

async fn handle_list_operators(
    service: Arc<WebWalletService>,
) -> Result<impl Reply, Rejection> {
    let registry = service.operator_registry.read().await;
    let operators: Vec<&OperatorInfo> = registry.operators.values().collect();
    
    Ok(warp::reply::json(&operators))
}

async fn handle_quantum_status(
    service: Arc<WebWalletService>,
) -> Result<impl Reply, Rejection> {
    let status = serde_json::json!({
        "quantum_operators_online": 3,
        "qrng_available": true,
        "qkd_endpoints": [
            "wss://quantum1.drista.network:9999",
            "wss://quantum2.drista.network:9999",
        ],
        "network_quantum_readiness": 0.3,
        "your_quantum_score": 0.0,  // Would check user's usage
    });
    
    Ok(warp::reply::json(&status))
}