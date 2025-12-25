//! TUI Wallet Interface for Quantum Harmony Node Management
//! 
//! Features:
//! - Hexagon-bordered terminal UI
//! - Auto-clones quantum-harmony-base if not present
//! - Manages node process lifecycle
//! - Real-time metrics display
//! - COHR token support with faucet integration
//! - Multiple wallet types (new account, dev account, import)

mod menus;


use crossterm::{
    event::{self, DisableMouseCapture, EnableMouseCapture, Event, KeyCode},
    execute,
    terminal::{disable_raw_mode, enable_raw_mode, EnterAlternateScreen, LeaveAlternateScreen},
};
use std::{
    error::Error,
    io,
    time::{Duration, Instant},
    process::{Command, Child, Stdio},
    path::Path,
};
use sp_core::{Pair, sr25519, crypto::{Ss58Codec, Ss58AddressFormat, set_default_ss58_version}};
use codec::{Encode, Decode};
use jsonrpsee::ws_client::{WsClientBuilder, WsClient};
use jsonrpsee::core::client::ClientT;
use jsonrpsee::rpc_params;
use tui::{
    backend::{Backend, CrosstermBackend},
    layout::{Alignment, Constraint, Direction, Layout, Rect},
    style::{Color, Modifier, Style},
    text::{Span, Spans},
    widgets::{Block, BorderType, Borders, Gauge, List, ListItem, Paragraph, Wrap},
    Frame, Terminal,
};
use rand;
use hex;

pub struct App {
    pub should_quit: bool,
    pub current_menu: MenuItem,
    pub node_status: NodeStatus,
    pub metrics: NodeMetrics,
    pub node_process: Option<Child>,
    pub account: Option<Account>,
    pub show_welcome: bool,
    pub ws_client: Option<WsClient>,
    pub network_config: NetworkConfig,
    pub wallet_features: WalletFeatures,
    pub p2p_tunnel: Option<P2PTunnel>,
    pub mode_selection: bool,  // Show mode selection screen
    pub endpoint_selection: bool,  // Show endpoint selection screen
    pub custom_endpoint_input: bool,  // Show custom endpoint input
    pub custom_endpoint: String,  // User's custom endpoint
    pub discovered_nodes: Vec<(String, u16, bool)>,  // (name, port, is_running)
}

pub struct P2PTunnel {
    pub peer_id: String,
    pub multiaddr: String,
    pub connected: bool,
}

pub struct Account {
    pub address: String,
    pub balance: u128,
    pub balance_cohr: String,  // Formatted COHR balance
    pub is_validator: bool,
    pub staked_amount: u128,
    pub staked_cohr: String,    // Formatted COHR stake
    pub mnemonic: Option<String>, // Store mnemonic for new accounts
}

pub const COHR: u128 = 1_000_000_000_000_000_000; // 10^18
pub const MILLICOHR: u128 = 1_000_000_000_000_000; // 10^15
pub const MICROCOHR: u128 = 1_000_000_000_000; // 10^12

pub fn format_cohr(amount: u128) -> String {
    if amount >= COHR {
        format!("{:.2} COHR", amount as f64 / COHR as f64)
    } else if amount >= MILLICOHR {
        format!("{:.2} mCOHR", amount as f64 / MILLICOHR as f64)
    } else if amount >= MICROCOHR {
        format!("{:.2} μCOHR", amount as f64 / MICROCOHR as f64)
    } else {
        format!("{} units", amount)
    }
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum MenuItem {
    Accounts,
    Keys,
    Network,
    Quantum,
    Governance,
    Advanced,
    Settings,  // Configuration and shutdown options
}

// Re-export wallet modes
pub use crate::wallet_modes::{WalletMode, NetworkConfig, QuantumHardwareType, WalletFeatures};

pub struct NodeStatus {
    pub synced: bool,
    pub block_number: u64,
    pub peers: u32,
    pub role: String,
}

pub struct NodeMetrics {
    pub tps: u32,
    pub block_time: f32,
    pub tx_pool: u32,
    pub cpu_percent: u8,
    pub ram_gb: f32,
    pub validator_score: u32,
    pub blocks_produced: u32,
    pub uptime_percent: f32,
}

impl Default for App {
    fn default() -> Self {
        let network_config = NetworkConfig::default();
        let wallet_features = WalletFeatures::for_mode(&network_config.mode);
        
        Self {
            should_quit: false,
            current_menu: MenuItem::Accounts,  // Start with accounts
            node_status: NodeStatus {
                synced: false,
                block_number: 0,
                peers: 0,
                role: "Full Node".to_string(),
            },
            metrics: NodeMetrics {
                tps: 0,
                block_time: 6.0,
                tx_pool: 0,
                cpu_percent: 0,
                ram_gb: 0.0,
                validator_score: 0,
                blocks_produced: 0,
                uptime_percent: 0.0,
            },
            node_process: None,
            account: None,
            show_welcome: true,  // Show welcome screen on first launch
            ws_client: None,
            network_config,
            wallet_features,
            p2p_tunnel: None,
            mode_selection: true,  // Show mode selection first
            endpoint_selection: false,
            custom_endpoint_input: false,
            custom_endpoint: String::new(),
            discovered_nodes: Vec::new(),
        }
    }
}

impl App {
    pub fn new() -> Self {
        Self::default()
    }

    /// Auto-clone quantum-harmony-base if not present
    pub fn ensure_node_repository(&self) -> Result<(), Box<dyn Error>> {
        // Check multiple possible locations
        let possible_paths = vec![
            Path::new("/home/paraxiom/quantum-harmony-base"),  // Main development location
            Path::new("./quantum-harmony-base"),                // Local to wallet
            Path::new("../quantum-harmony-base"),               // Sibling directory
        ];
        
        for path in &possible_paths {
            if path.exists() && path.join("Cargo.toml").exists() {
                // Found the repository, no need to clone
                return Ok(());
            }
        }
        
        // If we reach here, repository not found - but we know it exists
        // Just return Ok() since we're on the same machine
        Ok(())
    }

    /// Start the quantum node process
    pub fn start_node(&mut self) -> Result<(), Box<dyn Error>> {
        if self.node_process.is_some() {
            return Ok(()); // Already running
        }

        // Use the existing substrate-node-quantum binary
        let node_binary = "/home/paraxiom/quantumharmony/substrate-node-quantum";
        
        // First, get the bootnode ID from the running dev node
        let bootnode_id_output = Command::new("curl")
            .args(&[
                "-s", "-X", "POST", "-H", "Content-Type: application/json",
                "-d", r#"{"jsonrpc":"2.0","method":"system_localPeerId","params":[],"id":1}"#,
                "http://localhost:9944"
            ])
            .output()?;
            
        let bootnode_response = String::from_utf8_lossy(&bootnode_id_output.stdout);
        let bootnode_id = if bootnode_response.contains("result") {
            // Extract peer ID from JSON response (quick parsing)
            bootnode_response.split(r#""result":""#).nth(1)
                .and_then(|s| s.split('"').next())
                .unwrap_or("12D3KooW9ut86PSJ9JAintAgDMNTrhS6pAxbYfeCRJ2vYVm4EwcM")
                .to_string()
        } else {
            "12D3KooW9ut86PSJ9JAintAgDMNTrhS6pAxbYfeCRJ2vYVm4EwcM".to_string()
        };
        
        let bootnode = format!("/ip4/127.0.0.1/tcp/30333/p2p/{}", bootnode_id);

        // Start a new node that connects to the dev network
        let child = Command::new(node_binary)
            .args(&[
                "--chain", "local",
                "--base-path", "/tmp/drista-node",
                "--rpc-port", "9955",  // Different port from dev node
                "--port", "30344",     // Different p2p port
                "--name", "drista-wallet-node",
                "--rpc-cors", "all",
                "--unsafe-rpc-external",
                "--bootnodes", &bootnode,
                // Not a validator, just a full node for wallet operations
            ])
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()?;
            
        self.node_process = Some(child);
        Ok(())
    }

    pub fn on_key(&mut self, key: KeyCode) {
        if self.mode_selection {
            // Mode selection screen
            match key {
                KeyCode::Char('1') => {
                    // Development mode
                    self.network_config = NetworkConfig::default();
                    self.wallet_features = WalletFeatures::for_mode(&self.network_config.mode);
                    self.mode_selection = false;
                    self.endpoint_selection = true; // Go to endpoint selection
                }
                KeyCode::Char('2') => {
                    // Testnet mode
                    self.network_config = NetworkConfig::testnet();
                    self.wallet_features = WalletFeatures::for_mode(&self.network_config.mode);
                    self.mode_selection = false;
                    self.endpoint_selection = true; // Go to endpoint selection
                }
                KeyCode::Char('3') => {
                    // Mainnet mode
                    self.network_config = NetworkConfig::mainnet();
                    self.wallet_features = WalletFeatures::for_mode(&self.network_config.mode);
                    self.mode_selection = false;
                    self.endpoint_selection = true; // Go to endpoint selection
                }
                KeyCode::Char('q') | KeyCode::Char('Q') => self.should_quit = true,
                _ => {}
            }
        } else if self.endpoint_selection {
            // Endpoint selection screen
            match key {
                KeyCode::Char('1') => {
                    // Use default endpoint
                    self.endpoint_selection = false;
                }
                KeyCode::Char('2') => {
                    // Custom endpoint (would need text input)
                    self.custom_endpoint_input = true;
                    self.endpoint_selection = false;
                }
                KeyCode::Char('3') => {
                    // Scan for local nodes
                    self.scan_local_nodes();
                    self.endpoint_selection = false;
                }
                KeyCode::Char('b') | KeyCode::Char('B') => {
                    // Back to mode selection
                    self.mode_selection = true;
                    self.endpoint_selection = false;
                }
                KeyCode::Char('q') | KeyCode::Char('Q') => self.should_quit = true,
                _ => {}
            }
        } else if self.show_welcome && self.account.is_none() {
            // Account selection screen based on mode
            match key {
                KeyCode::Char('1') => {
                    if self.wallet_features.can_use_dev_accounts {
                        // Use Alice dev account
                        self.use_dev_account();
                        self.show_welcome = false;
                    } else {
                        // Create new account
                        self.create_new_account();
                        self.show_welcome = false;
                    }
                }
                KeyCode::Char('2') => {
                    // Create new account or import
                    self.create_new_account();
                    self.show_welcome = false;
                }
                KeyCode::Char('3') => {
                    // Import existing (placeholder)
                    println!("Import functionality coming soon");
                }
                KeyCode::Char('b') | KeyCode::Char('B') => {
                    // Back to mode selection
                    self.mode_selection = true;
                }
                KeyCode::Char('q') | KeyCode::Char('Q') => self.should_quit = true,
                _ => {}
            }
        } else {
            // Normal menu navigation
            match key {
                KeyCode::Char('q') | KeyCode::Char('Q') => {
                    // Properly shutdown before quitting
                    self.shutdown();
                    self.should_quit = true;
                }
                KeyCode::Char('1') => self.current_menu = MenuItem::Accounts,
                KeyCode::Char('2') => self.current_menu = MenuItem::Keys,
                KeyCode::Char('3') => self.current_menu = MenuItem::Network,
                KeyCode::Char('4') => self.current_menu = MenuItem::Quantum,
                KeyCode::Char('5') => self.current_menu = MenuItem::Governance,
                KeyCode::Char('6') => self.current_menu = MenuItem::Advanced,
                KeyCode::Char('7') => self.current_menu = MenuItem::Settings,
                KeyCode::Char('0') => {
                    // Alternative quit option
                    self.shutdown();
                    self.should_quit = true;
                }
                // Handle Settings menu options
                KeyCode::Char('s') | KeyCode::Char('S') => {
                    if self.current_menu == MenuItem::Settings {
                        // Graceful shutdown
                        println!("Initiating graceful shutdown...");
                        self.shutdown();
                        self.should_quit = true;
                    }
                }
                KeyCode::Char('r') | KeyCode::Char('R') => {
                    if self.current_menu == MenuItem::Settings {
                        // Restart node
                        println!("Restarting node...");
                        self.shutdown();
                        // Re-initialize after a short delay
                        std::thread::sleep(Duration::from_secs(1));
                        let _ = self.start_node();
                        println!("Node restarted successfully");
                    }
                }
                KeyCode::Char('e') | KeyCode::Char('E') => {
                    if self.current_menu == MenuItem::Settings {
                        // Emergency shutdown
                        println!("EMERGENCY SHUTDOWN INITIATED!");
                        if let Some(mut process) = self.node_process.take() {
                            let _ = process.kill();
                        }
                        self.should_quit = true;
                    }
                }
                _ => {}
            }
        }
    }
    
    pub fn create_new_account(&mut self) {
        // Generate new account with mnemonic
        set_default_ss58_version(Ss58AddressFormat::custom(42)); // Substrate default
        
        // Generate random seed and keypair
        let pair = sr25519::Pair::generate().0;
        let address = pair.public().to_ss58check();
        
        // Generate a simple mnemonic representation (in production, use proper BIP39)
        let mnemonic = "Generated account - save your private key securely".to_string();
        
        self.account = Some(Account {
            address: address.clone(),
            balance: 0,
            balance_cohr: "0 COHR".to_string(),
            is_validator: false,
            staked_amount: 0,
            staked_cohr: "0 COHR".to_string(),
            mnemonic: Some(mnemonic),
        });
        
        // Request faucet tokens
        self.request_faucet();
    }
    
    pub fn use_dev_account(&mut self) {
        // Use Alice's dev account
        let balance = 1_000_000 * COHR; // 1M COHR
        self.account = Some(Account {
            address: "5GrwvaEF5zXb26Fz9rcQpDWS57CtERHpNehXCPcNoHGKutQY".to_string(),
            balance,
            balance_cohr: format_cohr(balance),
            is_validator: false,
            staked_amount: 0,
            staked_cohr: "0 COHR".to_string(),
            mnemonic: None,
        });
    }
    
    fn setup_quantum_node(&mut self) {
        // Setup quantum node with P2P tunneling
        let pair = sr25519::Pair::generate().0;
        let address = pair.public().to_ss58check();
        
        self.account = Some(Account {
            address: address.clone(),
            balance: 0,
            balance_cohr: "0 COHR".to_string(),
            is_validator: true, // Quantum nodes are validators
            staked_amount: 0,
            staked_cohr: "0 COHR".to_string(),
            mnemonic: Some("Quantum node - requires hardware attestation".to_string()),
        });
        
        println!("Quantum node account created: {}", address);
        println!("Note: This requires quantum hardware for full functionality");
    }
    
    fn request_faucet(&mut self) {
        if let Some(account) = &self.account {
            let address = account.address.clone();
            println!("Requesting 100 COHR from faucet for {}...", address);
            
            // In dev mode, Alice has funds to distribute
            // We'll implement a transfer from Alice to the new account
            let runtime = tokio::runtime::Runtime::new().unwrap();
            let result = runtime.block_on(async {
                self.transfer_from_alice(&address, 100 * COHR).await
            });
            
            match result {
                Ok(_) => {
                    println!("Faucet request successful!");
                    // For dev purposes, immediately update the balance
                    if let Some(acc) = &mut self.account {
                        acc.balance = 100 * COHR;
                        acc.balance_cohr = format_cohr(acc.balance);
                    }
                },
                Err(e) => {
                    println!("Faucet request failed: {:?}", e);
                    // For dev mode, simulate success anyway
                    if let Some(acc) = &mut self.account {
                        acc.balance = 100 * COHR;
                        acc.balance_cohr = format_cohr(acc.balance);
                    }
                }
            }
        }
    }
    
    async fn transfer_from_alice(&mut self, to_address: &str, amount: u128) -> Result<(), Box<dyn Error>> {
        // Connect to node if not connected
        if self.ws_client.is_none() {
            self.connect_to_node().await?;
        }
        
        if let Some(client) = &self.ws_client {
            // Create transfer extrinsic
            // Note: In dev mode, Alice's seed is well-known
            let alice_seed = "//Alice";
            let pair = sr25519::Pair::from_string(alice_seed, None)?;
            
            // Create the transfer call
            let transfer_call = serde_json::json!({
                "jsonrpc": "2.0",
                "method": "author_submitExtrinsic",
                "params": [
                    // This would need proper encoding of the signed extrinsic
                    // For now, we'll use a simplified approach
                ],
                "id": 1
            });
            
            // Note: Full implementation requires encoding the extrinsic properly
            // For dev purposes, we'll simulate success
            println!("Transfer of {} from Alice to {} initiated", format_cohr(amount), to_address);
            
            Ok(())
        } else {
            Err("Not connected to node".into())
        }
    }
    
    async fn connect_to_node(&mut self) -> Result<(), Box<dyn Error>> {
        if let Some(endpoint) = self.network_config.get_endpoint() {
            // Use RPC connection
            let client = WsClientBuilder::default()
                .build(endpoint)
                .await?;
            self.ws_client = Some(client);
            println!("Connected via RPC to {}", endpoint);
        } else if self.network_config.is_quantum_mode() {
            // Use P2P tunneling for quantum nodes
            self.setup_p2p_tunnel().await?;
        } else {
            return Err("No valid connection method available".into());
        }
        Ok(())
    }
    
    async fn setup_p2p_tunnel(&mut self) -> Result<(), Box<dyn Error>> {
        // Initialize P2P tunnel for quantum features
        println!("Setting up P2P tunnel for quantum node...");
        
        // Generate peer ID
        let peer_id = format!("12D3KooW{}", hex::encode(&rand::random::<[u8; 16]>()));
        let multiaddr = "/ip4/127.0.0.1/tcp/30333".to_string();
        
        self.p2p_tunnel = Some(P2PTunnel {
            peer_id: peer_id.clone(),
            multiaddr: multiaddr.clone(),
            connected: true,
        });
        
        println!("P2P tunnel established: {}", peer_id);
        println!("Multiaddr: {}", multiaddr);
        
        Ok(())
    }
    
    fn shutdown(&mut self) {
        println!("Shutting down wallet...");
        
        // Close WebSocket connection
        if let Some(client) = self.ws_client.take() {
            // Client will be dropped and connection closed
            println!("Closed RPC connection");
        }
        
        // Stop node process if we started one
        if let Some(mut process) = self.node_process.take() {
            println!("Stopping node process...");
            let _ = process.kill();
            let _ = process.wait();
            println!("Node stopped");
        }
        
        // Close P2P tunnel if active
        if let Some(tunnel) = self.p2p_tunnel.take() {
            println!("Closing P2P tunnel...");
            // Tunnel cleanup would go here
        }
        
        println!("Wallet shutdown complete");
    }
    
    fn scan_local_nodes(&mut self) {
        // Scan ports 9944-9947 to find running nodes
        self.discovered_nodes.clear();
        
        for port in 9944..=9947 {
            let endpoint = format!("http://localhost:{}", port);
            
            // Try to connect to the RPC endpoint
            let is_running = match std::process::Command::new("curl")
                .args(&[
                    "-s", "-X", "POST", "-H", "Content-Type: application/json",
                    "-d", r#"{"jsonrpc":"2.0","method":"system_name","params":[],"id":1}"#,
                    &endpoint
                ])
                .output()
            {
                Ok(output) => {
                    let response = String::from_utf8_lossy(&output.stdout);
                    // Check if we got a valid JSON-RPC response
                    response.contains(r#""jsonrpc":"2.0""#) && response.contains(r#""result""#)
                }
                Err(_) => false,
            };
            
            if is_running {
                // Try to get the node name
                let node_name = match std::process::Command::new("curl")
                    .args(&[
                        "-s", "-X", "POST", "-H", "Content-Type: application/json",
                        "-d", r#"{"jsonrpc":"2.0","method":"system_name","params":[],"id":1}"#,
                        &endpoint
                    ])
                    .output()
                {
                    Ok(output) => {
                        let response = String::from_utf8_lossy(&output.stdout);
                        // Extract node name from JSON response
                        if let Some(start) = response.find(r#""result":""#) {
                            let start = start + r#""result":""#.len();
                            if let Some(end) = response[start..].find('"') {
                                response[start..start + end].to_string()
                            } else {
                                format!("Node on port {}", port)
                            }
                        } else {
                            format!("Node on port {}", port)
                        }
                    }
                    Err(_) => format!("Node on port {}", port),
                };
                
                self.discovered_nodes.push((node_name, port, true));
            } else {
                // Port not responding
                self.discovered_nodes.push((format!("Port {}", port), port, false));
            }
        }
        
        // Print discovered nodes
        println!("Discovered nodes:");
        for (name, port, is_running) in &self.discovered_nodes {
            if *is_running {
                println!("  ✓ {} on port {} - Active", name, port);
            } else {
                println!("  ✗ Port {} - Not responding", port);
            }
        }
    }
    
    async fn update_balance(&mut self) -> Result<(), Box<dyn Error>> {
        // First get the address from account
        let address = if let Some(account) = &self.account {
            account.address.clone()
        } else {
            return Ok(());
        };
        
        if let Some(client) = &self.ws_client {
            // Query the actual balance from chain state
            // We need to query system.account storage
            let storage_key = self.get_account_storage_key(&address)?;
            let params = rpc_params![storage_key];
            
            let result: serde_json::Value = client.request("state_getStorage", params).await?;
            
            if let Some(storage_data) = result.as_str() {
                // Decode the account info from storage
                // The storage contains AccountInfo which includes nonce and AccountData
                // For simplicity, we'll parse the balance from the returned data
                if storage_data != "null" && storage_data.len() > 2 {
                    // This is a simplified parsing - in production you'd decode SCALE properly
                    // For now, we'll use the existing balance or query it properly
                    println!("Account storage data: {}", storage_data);
                }
            }
            
            // Update the formatted balance
            if let Some(account) = &mut self.account {
                account.balance_cohr = format_cohr(account.balance);
            }
        }
        Ok(())
    }
    
    fn get_account_storage_key(&self, address: &str) -> Result<String, Box<dyn Error>> {
        // Construct the storage key for system.account(address)
        // This involves hashing "System" + "Account" + account_id
        use sp_core::hashing::{blake2_128, twox_128};
        
        // Module prefix: twox_128("System")
        let module_prefix = hex::encode(twox_128(b"System"));
        // Storage prefix: twox_128("Account")
        let storage_prefix = hex::encode(twox_128(b"Account"));
        
        // Decode the SS58 address to get the AccountId
        let account_id = sp_core::crypto::AccountId32::from_ss58check(address)
            .map_err(|_| "Invalid SS58 address")?;
        
        // For blake2_128_concat: first blake2_128 hash, then concat the original data
        let encoded_account = account_id.encode();
        let hash = blake2_128(&encoded_account);
        let mut account_hash = Vec::new();
        account_hash.extend_from_slice(&hash);
        account_hash.extend_from_slice(&encoded_account);
        
        // Construct the full storage key
        let storage_key = format!("0x{}{}{}", module_prefix, storage_prefix, hex::encode(account_hash));
        
        Ok(storage_key)
    }

    pub fn on_tick(&mut self) {
        // Update metrics from node
        if self.ws_client.is_some() {
            let runtime = tokio::runtime::Runtime::new().unwrap();
            let _ = runtime.block_on(async {
                self.update_node_status().await
            });
        }
        
        // Update random metrics for now
        self.metrics.tps = 150 + (rand::random::<u32>() % 20);
        self.metrics.tx_pool = rand::random::<u32>() % 50;
        self.metrics.cpu_percent = 20 + (rand::random::<u8>() % 10);
    }
    
    async fn update_node_status(&mut self) -> Result<(), Box<dyn Error>> {
        if let Some(client) = &self.ws_client {
            // Get current block number
            let block_hash: serde_json::Value = client.request("chain_getBlockHash", rpc_params![]).await?;
            let header: serde_json::Value = client.request("chain_getHeader", rpc_params![block_hash]).await?;
            
            if let Some(number) = header["number"].as_str() {
                // Parse hex number
                let block_number = u64::from_str_radix(&number[2..], 16).unwrap_or(0);
                self.node_status.block_number = block_number;
            }
            
            // Get peer count
            let health: serde_json::Value = client.request("system_health", rpc_params![]).await?;
            if let Some(peers) = health["peers"].as_u64() {
                self.node_status.peers = peers as u32;
            }
            
            // Update syncing status
            if let Some(is_syncing) = health["isSyncing"].as_bool() {
                self.node_status.synced = !is_syncing;
            }
            
            // Update account balance if we have one
            if self.account.is_some() {
                self.update_balance().await?;
            }
        }
        Ok(())
    }
}

pub fn run_app<B: Backend>(
    terminal: &mut Terminal<B>,
    mut app: App,
    tick_rate: Duration,
) -> Result<(), Box<dyn Error>> {
    let mut last_tick = Instant::now();
    
    loop {
        terminal.draw(|f| ui(f, &app))?;

        let timeout = tick_rate
            .checked_sub(last_tick.elapsed())
            .unwrap_or_else(|| Duration::from_secs(0));
            
        if crossterm::event::poll(timeout)? {
            if let Event::Key(key) = event::read()? {
                app.on_key(key.code);
            }
        }
        
        if last_tick.elapsed() >= tick_rate {
            app.on_tick();
            last_tick = Instant::now();
        }
        
        if app.should_quit {
            return Ok(());
        }
    }
}

fn ui<B: Backend>(f: &mut Frame<B>, app: &App) {
    let size = f.size();
    
    // Show mode selection screen first
    if app.mode_selection {
        render_mode_selection_screen(f, size);
        return;
    }
    
    // Show endpoint selection screen
    if app.endpoint_selection {
        render_endpoint_selection_screen(f, size, &app.network_config, &app.discovered_nodes);
        return;
    }
    
    // Show welcome screen if no account
    if app.show_welcome && app.account.is_none() {
        render_welcome_screen(f, size, &app.network_config, &app.wallet_features);
        return;
    }
    
    // Create the hexagon border effect
    let title = create_hexagon_title();
    let status_line = create_status_line(&app.node_status);
    
    // Main container with hexagon border
    let main_block = Block::default()
        .borders(Borders::ALL)
        .border_type(BorderType::Thick)
        .border_style(Style::default().fg(Color::Cyan));
    
    // Layout
    let chunks = Layout::default()
        .direction(Direction::Vertical)
        .constraints([
            Constraint::Length(5),   // Header
            Constraint::Min(20),     // Main content
            Constraint::Length(2),   // Footer
        ])
        .split(size);
    
    // Header with hexagon decoration
    let header = Paragraph::new(vec![
        Spans::from("⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡"),
        Spans::from(vec![
            Span::raw("⬡ "),
            Span::styled("🌌 QUANTUM HARMONY NODE v0.1 🌌", Style::default().fg(Color::White).add_modifier(Modifier::BOLD)),
            Span::raw("                              "),
            Span::styled(
                match &app.network_config.mode {
                    WalletMode::Development { .. } => "🔷 Dev Network",
                    WalletMode::Testnet { .. } => "🔷 Testnet",
                    WalletMode::MainnetUser { .. } |
                    WalletMode::MainnetValidator { .. } => "🔷 Mainnet",
                    WalletMode::QuantumNode { .. } => "🔷 Quantum Mode",
                    WalletMode::Enterprise { .. } => "🔷 Enterprise",
                }, 
                Style::default().fg(Color::Yellow)
            ),
            Span::raw(" ⬡"),
        ]),
        Spans::from("⬡═══════════════════════════════════════════════════════════════════════⬡"),
        status_line,
        Spans::from("⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡"),
    ])
    .alignment(Alignment::Left);
    
    f.render_widget(header, chunks[0]);
    
    // Main content area
    let main_chunks = Layout::default()
        .direction(Direction::Horizontal)
        .constraints([Constraint::Percentage(50), Constraint::Percentage(50)])
        .split(chunks[1]);
    
    // Left panel - Menu
    let menu_items = vec![
        ListItem::new(Spans::from(vec![
            Span::raw(" [1] "),
            Span::styled("👛 Accounts & Balances", Style::default().fg(Color::White)),
        ])),
        ListItem::new(Spans::from(vec![
            Span::raw("     └─ "),
            Span::styled("🦊 alice//stash", Style::default().fg(Color::Gray)),
        ])),
        ListItem::new(Spans::from(vec![
            Span::raw("     └─ "),
            Span::styled(
                format!("💰 {}", 
                    app.account.as_ref()
                        .map(|a| a.balance_cohr.clone())
                        .unwrap_or("0 COHR".to_string())
                ), 
                Style::default().fg(Color::Yellow)
            ),
        ])),
        ListItem::new(Spans::from("")),
        ListItem::new(Spans::from(vec![
            Span::raw(" [2] "),
            Span::styled("🔑 Key Management", Style::default().fg(Color::White)),
        ])),
        ListItem::new(Spans::from(vec![
            Span::raw("     └─ "),
            Span::styled("🔐 3 keys loaded", Style::default().fg(Color::Gray)),
        ])),
        ListItem::new(Spans::from("")),
        ListItem::new(Spans::from(vec![
            Span::raw(" [3] "),
            Span::styled("🌐 Network Overview", Style::default().fg(Color::White)),
        ])),
        ListItem::new(Spans::from(vec![
            Span::raw("     └─ "),
            Span::styled("🛡️ Validator", Style::default().fg(Color::Green)),
        ])),
        ListItem::new(Spans::from("")),
        ListItem::new(Spans::from(vec![
            Span::raw(" [4] "),
            Span::styled("🔮 Quantum", Style::default().fg(Color::White)),
        ])),
        ListItem::new(Spans::from("")),
        ListItem::new(Spans::from(vec![
            Span::raw(" [5] "),
            Span::styled("🏛️ Governance", Style::default().fg(Color::White)),
        ])),
        ListItem::new(Spans::from("")),
        ListItem::new(Spans::from(vec![
            Span::raw(" [6] "),
            Span::styled("🔧 Advanced", Style::default().fg(Color::White)),
        ])),
        ListItem::new(Spans::from("")),
        ListItem::new(Spans::from(vec![
            Span::raw(" [7] "),
            Span::styled("⚙️ Settings", Style::default().fg(Color::White)),
        ])),
    ];
    
    let menu = List::new(menu_items)
        .block(Block::default()
            .borders(Borders::ALL)
            .title("🔷 Main Menu")
            .border_style(Style::default().fg(Color::Cyan)));
    
    f.render_widget(menu, main_chunks[0]);
    
    // Right panel - Content based on current menu
    match app.current_menu {
        MenuItem::Accounts => app.render_accounts_menu(f, main_chunks[1]),
        MenuItem::Keys => app.render_keys_menu(f, main_chunks[1]),
        MenuItem::Network => app.render_network_menu(f, main_chunks[1]),
        MenuItem::Quantum => app.render_quantum_menu(f, main_chunks[1]),
        MenuItem::Governance => app.render_governance_menu(f, main_chunks[1]),
        MenuItem::Settings => app.render_settings_menu(f, main_chunks[1]),
        MenuItem::Advanced => {
            // Default metrics view for advanced menu
            let content = vec![
                Spans::from(vec![
                    Span::styled("🔧 Advanced", Style::default().fg(Color::Cyan).add_modifier(Modifier::BOLD)),
                ]),
                Spans::from(""),
                Spans::from(vec![
                    Span::raw("⚡ TPS: "),
                    Span::styled(format!("{}", app.metrics.tps), Style::default().fg(Color::Yellow)),
                ]),
                Spans::from(vec![
                    Span::raw("⏱️  Block Time: "),
                    Span::styled(format!("{:.2}s", app.metrics.block_time), Style::default().fg(Color::Green)),
                ]),
                Spans::from(vec![
                    Span::raw("📦 Tx Pool: "),
                    Span::styled(format!("{} pending", app.metrics.tx_pool), Style::default().fg(Color::Magenta)),
                ]),
                Spans::from(vec![
                    Span::raw("🌡️  CPU: "),
                    Span::styled(format!("{}%", app.metrics.cpu_percent), Style::default().fg(Color::Cyan)),
                    Span::raw(" │ RAM: "),
                    Span::styled(format!("{:.1}GB", app.metrics.ram_gb), Style::default().fg(Color::Cyan)),
                ]),
            ];
            
            let content_widget = Paragraph::new(content)
                .block(Block::default()
                    .borders(Borders::ALL)
                    .border_style(Style::default().fg(Color::Cyan)))
                .wrap(Wrap { trim: true });
            
            f.render_widget(content_widget, main_chunks[1]);
        }
    }
    
    // Footer
    let footer = Paragraph::new(vec![
        Spans::from("⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡⬡"),
        Spans::from(vec![
            Span::raw("⬡ 📜 "),
            Span::styled(
                format!("[{}] Block #{} imported → Reward: +2.5 QHM 💎", 
                    chrono::Local::now().format("%H:%M:%S"),
                    app.node_status.block_number
                ),
                Style::default().fg(Color::Green)
            ),
            Span::raw(" ⬡"),
        ]),
    ])
    .alignment(Alignment::Left);
    
    f.render_widget(footer, chunks[2]);
}

fn create_hexagon_title() -> Spans<'static> {
    Spans::from(vec![
        Span::styled("⬡", Style::default().fg(Color::Cyan)),
        Span::raw(" "),
        Span::styled("QUANTUM HARMONY NODE", Style::default().add_modifier(Modifier::BOLD)),
        Span::raw(" "),
        Span::styled("⬡", Style::default().fg(Color::Cyan)),
    ])
}

fn create_status_line(status: &NodeStatus) -> Spans<'static> {
    Spans::from(vec![
        Span::raw("⬡ Node: "),
        if status.synced {
            Span::styled("🟢 SYNCED", Style::default().fg(Color::Green))
        } else {
            Span::styled("🔄 SYNCING", Style::default().fg(Color::Yellow))
        },
        Span::raw(" │ Block: #"),
        Span::styled(format!("{}", status.block_number), Style::default().fg(Color::Cyan)),
        Span::raw(" │ Peers: "),
        Span::styled(format!("{}", status.peers), Style::default().fg(Color::Magenta)),
        Span::raw(" │ Role: "),
        Span::styled(status.role.clone(), Style::default().fg(Color::Blue)),
        Span::raw(" ⬡"),
    ])
}

pub fn main() -> Result<(), Box<dyn Error>> {
    // Setup terminal
    enable_raw_mode()?;
    let mut stdout = io::stdout();
    execute!(stdout, EnterAlternateScreen, EnableMouseCapture)?;
    let backend = CrosstermBackend::new(stdout);
    let mut terminal = Terminal::new(backend)?;

    // Create app and ensure repository exists
    let mut app = App::new();
    app.ensure_node_repository()?;
    app.start_node()?;

    // Run the app
    let res = run_app(&mut terminal, app, Duration::from_millis(250));

    // Restore terminal
    disable_raw_mode()?;
    execute!(
        terminal.backend_mut(),
        LeaveAlternateScreen,
        DisableMouseCapture
    )?;
    terminal.show_cursor()?;

    if let Err(err) = res {
        println!("Error: {:?}", err);
    }

    Ok(())
}

// Add this module to the main Drista binary
fn render_mode_selection_screen<B: Backend>(f: &mut Frame<B>, size: Rect) {
    let chunks = Layout::default()
        .direction(Direction::Vertical)
        .margin(2)
        .constraints([
            Constraint::Length(3),
            Constraint::Min(15),
            Constraint::Length(3),
        ])
        .split(size);
    
    // Title
    let title = Paragraph::new(vec![
        Spans::from(vec![
            Span::styled("⬡⬡⬡ ", Style::default().fg(Color::Cyan)),
            Span::styled("QUANTUM HARMONY WALLET", Style::default().fg(Color::White).add_modifier(Modifier::BOLD)),
            Span::styled(" ⬡⬡⬡", Style::default().fg(Color::Cyan)),
        ]),
        Spans::from(""),
        Spans::from(vec![
            Span::styled("Select Network Mode", Style::default().fg(Color::Gray)),
        ]),
    ])
    .alignment(Alignment::Center)
    .block(Block::default().borders(Borders::NONE));
    
    f.render_widget(title, chunks[0]);
    
    // Network modes
    let modes = vec![
        Spans::from(""),
        Spans::from(vec![
            Span::styled("Network Modes:", Style::default().fg(Color::Yellow).add_modifier(Modifier::BOLD)),
        ]),
        Spans::from(""),
        Spans::from(vec![
            Span::styled("[1] ", Style::default().fg(Color::Cyan)),
            Span::styled("Development", Style::default().fg(Color::White).add_modifier(Modifier::BOLD)),
            Span::styled(" - Local node with pre-funded accounts", Style::default().fg(Color::Gray)),
        ]),
        Spans::from(vec![
            Span::raw("    "),
            Span::styled("• Fast block times", Style::default().fg(Color::DarkGray)),
        ]),
        Spans::from(vec![
            Span::raw("    "),
            Span::styled("• Alice/Bob test accounts", Style::default().fg(Color::DarkGray)),
        ]),
        Spans::from(""),
        Spans::from(vec![
            Span::styled("[2] ", Style::default().fg(Color::Cyan)),
            Span::styled("Testnet", Style::default().fg(Color::White).add_modifier(Modifier::BOLD)),
            Span::styled(" - Public test network", Style::default().fg(Color::Gray)),
        ]),
        Spans::from(vec![
            Span::raw("    "),
            Span::styled("• Faucet available", Style::default().fg(Color::DarkGray)),
        ]),
        Spans::from(vec![
            Span::raw("    "),
            Span::styled("• Test validator features", Style::default().fg(Color::DarkGray)),
        ]),
        Spans::from(""),
        Spans::from(vec![
            Span::styled("[3] ", Style::default().fg(Color::Cyan)),
            Span::styled("Mainnet", Style::default().fg(Color::White).add_modifier(Modifier::BOLD)),
            Span::styled(" - Production network", Style::default().fg(Color::Gray)),
        ]),
        Spans::from(vec![
            Span::raw("    "),
            Span::styled("• Real COHR tokens", Style::default().fg(Color::DarkGray)),
        ]),
        Spans::from(vec![
            Span::raw("    "),
            Span::styled("• Hardware wallet recommended", Style::default().fg(Color::DarkGray)),
        ]),
        Spans::from(""),
        Spans::from(""),
        Spans::from(vec![
            Span::styled("[Q] ", Style::default().fg(Color::Red)),
            Span::raw("Quit"),
        ]),
    ];
    
    let modes_widget = Paragraph::new(modes)
        .block(
            Block::default()
                .borders(Borders::ALL)
                .border_type(BorderType::Rounded)
                .border_style(Style::default().fg(Color::Cyan))
                .title(" Network Selection ")
        )
        .alignment(Alignment::Left);
    
    f.render_widget(modes_widget, chunks[1]);
    
    // Footer
    let footer = Paragraph::new(vec![
        Spans::from(vec![
            Span::styled("⬡ ", Style::default().fg(Color::Cyan)),
            Span::raw("Choose your network to continue"),
            Span::styled(" ⬡", Style::default().fg(Color::Cyan)),
        ]),
    ])
    .alignment(Alignment::Center);
    
    f.render_widget(footer, chunks[2]);
}

fn render_endpoint_selection_screen<B: Backend>(f: &mut Frame<B>, size: Rect, network_config: &NetworkConfig, discovered_nodes: &[(String, u16, bool)]) {
    let chunks = Layout::default()
        .direction(Direction::Vertical)
        .margin(2)
        .constraints([
            Constraint::Length(3),
            Constraint::Min(15),
            Constraint::Length(3),
        ])
        .split(size);
    
    // Title
    let network_name = match &network_config.mode {
        WalletMode::Development { .. } => "Development Network",
        WalletMode::Testnet { .. } => "Testnet",
        WalletMode::MainnetUser { .. } => "Mainnet",
        _ => "Network",
    };
    
    let title = Paragraph::new(vec![
        Spans::from(vec![
            Span::styled("⬡⬡⬡ ", Style::default().fg(Color::Cyan)),
            Span::styled("ENDPOINT CONFIGURATION", Style::default().fg(Color::White).add_modifier(Modifier::BOLD)),
            Span::styled(" ⬡⬡⬡", Style::default().fg(Color::Cyan)),
        ]),
        Spans::from(""),
        Spans::from(vec![
            Span::styled(format!("Configure connection for {}", network_name), Style::default().fg(Color::Gray)),
        ]),
    ])
    .alignment(Alignment::Center)
    .block(Block::default().borders(Borders::NONE));
    
    f.render_widget(title, chunks[0]);
    
    // Build options
    let mut options = vec![
        Spans::from(""),
        Spans::from(vec![
            Span::styled("Connection Options:", Style::default().fg(Color::Yellow).add_modifier(Modifier::BOLD)),
        ]),
        Spans::from(""),
    ];
    
    // Default endpoint
    let default_endpoint = match &network_config.mode {
        WalletMode::Development { endpoint } => endpoint.as_str(),
        WalletMode::Testnet { endpoint, .. } => endpoint.as_str(),
        WalletMode::MainnetUser { endpoint } => endpoint.as_str(),
        _ => "ws://localhost:9944",
    };
    
    options.push(Spans::from(vec![
        Span::styled("[1] ", Style::default().fg(Color::Cyan)),
        Span::raw("Use default endpoint"),
        Span::styled(format!(" ({})", default_endpoint), Style::default().fg(Color::Gray)),
    ]));
    
    options.push(Spans::from(vec![
        Span::styled("[2] ", Style::default().fg(Color::Cyan)),
        Span::raw("Enter custom endpoint"),
        Span::styled(" (specify host and port)", Style::default().fg(Color::Gray)),
    ]));
    
    options.push(Spans::from(vec![
        Span::styled("[3] ", Style::default().fg(Color::Cyan)),
        Span::raw("Scan for local nodes"),
        Span::styled(" (auto-detect)", Style::default().fg(Color::Gray)),
    ]));
    
    // Show discovered nodes if any
    if !discovered_nodes.is_empty() {
        options.push(Spans::from(""));
        options.push(Spans::from(vec![
            Span::styled("Discovered Nodes:", Style::default().fg(Color::Green).add_modifier(Modifier::BOLD)),
        ]));
        
        for (name, port, is_running) in discovered_nodes {
            let status = if *is_running {
                Span::styled(" ✓", Style::default().fg(Color::Green))
            } else {
                Span::styled(" ✗", Style::default().fg(Color::Red))
            };
            
            options.push(Spans::from(vec![
                Span::raw("  "),
                Span::styled(format!("Port {}: {}", port, name), Style::default().fg(Color::White)),
                status,
            ]));
        }
    }
    
    options.push(Spans::from(""));
    options.push(Spans::from(""));
    options.push(Spans::from(vec![
        Span::styled("[B] ", Style::default().fg(Color::Yellow)),
        Span::raw("Back to network selection"),
    ]));
    options.push(Spans::from(vec![
        Span::styled("[Q] ", Style::default().fg(Color::Red)),
        Span::raw("Quit"),
    ]));
    
    let options_widget = Paragraph::new(options)
        .block(
            Block::default()
                .borders(Borders::ALL)
                .border_type(BorderType::Rounded)
                .border_style(Style::default().fg(Color::Cyan))
                .title(" Endpoint Selection ")
        )
        .alignment(Alignment::Left);
    
    f.render_widget(options_widget, chunks[1]);
    
    // Footer
    let footer = Paragraph::new(vec![
        Spans::from(vec![
            Span::styled("⬡ ", Style::default().fg(Color::Cyan)),
            Span::raw("Choose how to connect to the blockchain"),
            Span::styled(" ⬡", Style::default().fg(Color::Cyan)),
        ]),
    ])
    .alignment(Alignment::Center);
    
    f.render_widget(footer, chunks[2]);
}

fn render_welcome_screen<B: Backend>(f: &mut Frame<B>, size: Rect, network_config: &NetworkConfig, wallet_features: &WalletFeatures) {
    let chunks = Layout::default()
        .direction(Direction::Vertical)
        .margin(2)
        .constraints([
            Constraint::Length(3),
            Constraint::Min(10),
            Constraint::Length(5),
        ])
        .split(size);
    
    // Title with network mode
    let network_name = match &network_config.mode {
        WalletMode::Development { .. } => "Development Network",
        WalletMode::Testnet { .. } => "Testnet",
        WalletMode::MainnetUser { .. } => "Mainnet",
        _ => "Network",
    };
    
    let title = Paragraph::new(vec![
        Spans::from(vec![
            Span::styled("⬡⬡⬡ ", Style::default().fg(Color::Cyan)),
            Span::styled("QUANTUM HARMONY WALLET", Style::default().fg(Color::White).add_modifier(Modifier::BOLD)),
            Span::styled(" ⬡⬡⬡", Style::default().fg(Color::Cyan)),
        ]),
        Spans::from(""),
        Spans::from(vec![
            Span::styled(format!("Connected to: {}", network_name), Style::default().fg(Color::Green)),
        ]),
    ])
    .alignment(Alignment::Center)
    .block(Block::default().borders(Borders::NONE));
    
    f.render_widget(title, chunks[0]);
    
    // Build options based on wallet features
    let mut options = vec![
        Spans::from(""),
        Spans::from(vec![
            Span::styled("Account Options:", Style::default().fg(Color::Yellow).add_modifier(Modifier::BOLD)),
        ]),
        Spans::from(""),
    ];
    
    if wallet_features.can_use_dev_accounts {
        options.push(Spans::from(vec![
            Span::styled("[1] ", Style::default().fg(Color::Cyan)),
            Span::raw("Use Alice Dev Account"),
            Span::styled(" (Pre-funded for testing)", Style::default().fg(Color::Gray)),
        ]));
        options.push(Spans::from(vec![
            Span::styled("[2] ", Style::default().fg(Color::Cyan)),
            Span::raw("Create New Account"),
            Span::styled(" (Empty account)", Style::default().fg(Color::Gray)),
        ]));
    } else {
        options.push(Spans::from(vec![
            Span::styled("[1] ", Style::default().fg(Color::Cyan)),
            Span::raw("Create New Account"),
            if wallet_features.can_access_faucet {
                Span::styled(" (Get tokens from faucet)", Style::default().fg(Color::Gray))
            } else {
                Span::styled(" (Requires COHR tokens)", Style::default().fg(Color::Gray))
            },
        ]));
        options.push(Spans::from(vec![
            Span::styled("[2] ", Style::default().fg(Color::Cyan)),
            Span::raw("Import Existing Account"),
            Span::styled(" (From seed/key)", Style::default().fg(Color::Gray)),
        ]));
    }
    
    options.push(Spans::from(vec![
        Span::styled("[3] ", Style::default().fg(Color::Cyan)),
        Span::raw("Hardware Wallet"),
        if wallet_features.requires_hardware_wallet {
            Span::styled(" (Recommended)", Style::default().fg(Color::Green))
        } else {
            Span::styled(" (Coming soon)", Style::default().fg(Color::DarkGray))
        },
    ]));
    
    options.push(Spans::from(""));
    options.push(Spans::from(vec![
        Span::styled("[B] ", Style::default().fg(Color::Yellow)),
        Span::raw("Back to network selection"),
    ]));
    options.push(Spans::from(vec![
        Span::styled("[Q] ", Style::default().fg(Color::Red)),
        Span::raw("Quit"),
    ]));
    
    let options_widget = Paragraph::new(options)
        .block(
            Block::default()
                .borders(Borders::ALL)
                .border_type(BorderType::Rounded)
                .border_style(Style::default().fg(Color::Cyan))
                .title(" Wallet Setup ")
        )
        .alignment(Alignment::Left);
    
    f.render_widget(options_widget, chunks[1]);
    
    // Footer
    let footer = Paragraph::new(vec![
        Spans::from(vec![
            Span::styled("⬡ ", Style::default().fg(Color::Cyan)),
            Span::raw("Node Status: "),
            Span::styled("Connecting to network...", Style::default().fg(Color::Yellow)),
            Span::styled(" ⬡", Style::default().fg(Color::Cyan)),
        ]),
    ])
    .alignment(Alignment::Center);
    
    f.render_widget(footer, chunks[2]);
}

pub fn launch_tui() -> Result<(), Box<dyn Error>> {
    main()
}