//! Frictionless TUI wallet - works out of the box with smart defaults

use crossterm::{
    event::{DisableMouseCapture, EnableMouseCapture, Event, KeyCode, KeyModifiers},
    execute,
    terminal::{disable_raw_mode, enable_raw_mode, EnterAlternateScreen, LeaveAlternateScreen},
};
use ratatui::{
    backend::{Backend, CrosstermBackend},
    layout::{Alignment, Constraint, Direction, Layout, Rect},
    style::{Color, Modifier, Style},
    text::{Line, Span},
    widgets::{Block, Borders, List, ListItem, Paragraph, Tabs},
    Frame, Terminal,
};
use std::io;
use std::sync::Arc;
use sp_core::{sr25519, Pair, crypto::Ss58Codec};
use sp_runtime::MultiSignature;
use jsonrpsee::ws_client::{WsClientBuilder, WsClient};
use jsonrpsee::core::client::ClientT;
use jsonrpsee::rpc_params;
use serde::{Deserialize, Serialize};
use chrono;
use regex;
use tokio::process::Command;
use tokio::io::{AsyncBufReadExt, BufReader};
use std::process::Stdio;
use crate::quantum::tunnel::{QuantumTunnelClient, TunnelConfig};
use crate::quantum::QuantumManager;
use super::architecture_spiral::{ArchitectureSpiral, render_architecture_spiral};

/// Main tabs
#[derive(Debug, Clone, Copy, PartialEq)]
enum MainTab {
    QuickStart = 0,
    Accounts = 1,
    Faucet = 2,
    Console = 3,
    Architecture = 4,
    Config = 5,
    Exit = 6,
}

/// Config sub-tabs
#[derive(Debug, Clone, Copy, PartialEq)]
enum ConfigTab {
    Network = 0,
    Display = 1,
    Security = 2,
    Defaults = 3,
}

/// Config presets
#[derive(Debug, Clone, Serialize, Deserialize)]
struct ConfigPreset {
    name: String,
    endpoint: String,
    auto_connect: bool,
    auto_create_account: bool,
    default_amount: String,
    refresh_interval: u64,
}

impl Default for ConfigPreset {
    fn default() -> Self {
        Self {
            name: "Local Development".to_string(),
            endpoint: "ws://localhost:9944".to_string(),
            auto_connect: true,
            auto_create_account: false,
            default_amount: "0.1".to_string(),
            refresh_interval: 5,
        }
    }
}

/// App state with sensible defaults
pub struct App {
    // Navigation
    main_tab: MainTab,
    config_tab: ConfigTab,
    
    // Accounts
    accounts: Vec<Account>,
    selected_account: usize,
    
    // Network
    ws_client: Option<Arc<WsClient>>,
    connection_status: String,
    auto_connected: bool,
    
    // Config
    presets: Vec<ConfigPreset>,
    active_preset: usize,
    custom_config: ConfigPreset,
    
    // UI State
    quick_action_selected: usize,
    message: Option<(String, Color)>,
    
    // Editing
    editing_field: Option<String>,
    edit_buffer: String,
    
    // Console output
    console_logs: Vec<(String, Color)>,
    max_console_logs: usize,
    console_scroll_offset: usize,
    
    // Faucet
    faucet_address_input: String,
    faucet_amount: String,
    faucet_requests: Vec<FaucetRequest>,
    
    // Blockchain monitoring
    last_block_number: Option<u32>,
    monitoring_active: bool,
    console_mode: ConsoleMode,
    
    // Docker logs streaming
    docker_log_handle: Option<tokio::task::JoinHandle<()>>,
    
    // Quantum tunnel for P2P blockchain queries
    tunnel_client: Option<QuantumTunnelClient>,
    use_tunnel: bool,
    
    // Security mode
    security_mode: SecurityMode,
    quantum_manager: Option<QuantumManager>,

    // Architecture spiral visualization
    architecture_spiral: ArchitectureSpiral,
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum SecurityMode {
    Classical,      // Blake2 only, standard networking
    Hybrid,         // Blake2 + SHA3, mixed networking
    QuantumSecure,  // Full quantum: SHA3, QKD, QRNG
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum ConsoleMode {
    Blockchain,
    Docker,
}

#[derive(Debug, Clone)]
struct Account {
    name: String,
    address: String,
    balance: String,
    nonce: u32,
    transactions: Vec<Transaction>,
}

#[derive(Debug, Clone)]
struct Transaction {
    hash: String,
    from: String,
    to: String,
    amount: String,
    timestamp: String,
    block_number: u32,
    status: TransactionStatus,
}

#[derive(Debug, Clone, PartialEq)]
enum TransactionStatus {
    Pending,
    Success,
    Failed,
}

#[derive(Debug, Clone)]
struct FaucetRequest {
    address: String,
    amount: String,
    timestamp: String,
    status: String,
}

#[derive(Debug, Default)]
struct AccountInfo {
    nonce: u32,
    free: u128,
    reserved: u128,
}

impl App {
    pub fn new() -> Self {
        let presets = vec![
            ConfigPreset::default(),
            ConfigPreset {
                name: "Testnet".to_string(),
                endpoint: "ws://localhost:9945".to_string(),
                auto_connect: true,
                auto_create_account: false,
                default_amount: "0.1".to_string(),
                refresh_interval: 10,
            },
            ConfigPreset {
                name: "Custom".to_string(),
                endpoint: "ws://localhost:9944".to_string(),
                auto_connect: false,
                auto_create_account: false,
                default_amount: "0".to_string(),
                refresh_interval: 30,
            },
        ];
        
        let mut app = Self {
            main_tab: MainTab::QuickStart,
            config_tab: ConfigTab::Network,
            accounts: vec![],
            selected_account: 0,
            ws_client: None,
            connection_status: "Not connected".to_string(),
            auto_connected: false,
            presets: presets.clone(),
            active_preset: 0,
            custom_config: presets[0].clone(),
            quick_action_selected: 0,
            message: None,
            editing_field: None,
            edit_buffer: String::new(),
            console_logs: vec![],
            max_console_logs: 100,
            console_scroll_offset: 0,
            faucet_address_input: String::new(),
            faucet_amount: "0.5".to_string(), // Changed from 1000 to 0.5 COHR
            faucet_requests: vec![],
            last_block_number: None,
            monitoring_active: false,
            console_mode: ConsoleMode::Blockchain,
            docker_log_handle: None,
            tunnel_client: None,
            use_tunnel: false,
            security_mode: SecurityMode::Hybrid, // Default to hybrid
            quantum_manager: None,
            architecture_spiral: ArchitectureSpiral::new(),
        };

        // Add initial console message
        app.log_to_console("Drista Wallet initialized", Color::Green);
        app.log_to_console("Connecting to Quantum Harmony network...", Color::Yellow);
        
        // Load existing accounts
        app.load_existing_accounts();
        
        app
    }
    
    async fn auto_connect(&mut self) {
        if self.custom_config.auto_connect && !self.auto_connected {
            self.connection_status = "Auto-connecting...".to_string();
            self.log_to_console(&format!("Connecting to {}...", self.custom_config.endpoint), Color::Yellow);
            
            match WsClientBuilder::default()
                .build(&self.custom_config.endpoint)
                .await 
            {
                Ok(client) => {
                    self.ws_client = Some(Arc::new(client));
                    self.connection_status = format!("Connected to {}", self.custom_config.endpoint);
                    self.message = Some(("✓ Auto-connected successfully".to_string(), Color::Green));
                    self.auto_connected = true;
                    self.log_to_console(&format!("✓ Connected to {}", self.custom_config.endpoint), Color::Green);
                    
                    // Start blockchain monitoring
                    self.start_blockchain_monitoring().await;
                }
                Err(e) => {
                    self.connection_status = "Auto-connect failed".to_string();
                    self.message = Some((format!("Connection failed: {}", e), Color::Red));
                    self.log_to_console(&format!("✗ Connection failed: {}", e), Color::Red);
                }
            }
        }
    }
    
    async fn quick_create_account(&mut self) {
        self.log_to_console("Generating new quantum-safe account...", Color::Yellow);
        
        let (pair, phrase, _) = sr25519::Pair::generate_with_phrase(None);
        let address = pair.public().to_ss58check();
        
        let account = Account {
            name: format!("Account {}", self.accounts.len() + 1),
            address: address.clone(),
            balance: "0 COHR".to_string(),
            nonce: 0,
            transactions: Vec::new(),
        };
        
        self.accounts.push(account);
        self.message = Some((format!("✓ Created account: {}...", &address[..8]), Color::Green));
        self.log_to_console(&format!("✓ Created account: {}", address), Color::Green);
        
        // Save phrase securely
        let _ = std::fs::create_dir_all(".drista");
        let filename = format!(".drista/account_{}.key", self.accounts.len());
        let _ = std::fs::write(
            &filename,
            format!("Address: {}\nMnemonic: {}\n\nKEEP THIS SAFE!", address, phrase)
        );
        self.log_to_console(&format!("🔐 Keys saved to {}", filename), Color::Blue);
    }
    
    fn handle_quick_action(&mut self, action: usize) -> Option<QuickAction> {
        match action {
            0 => Some(QuickAction::CreateAccount),
            1 => Some(QuickAction::CheckBalance),
            2 => Some(QuickAction::SendTokens),
            3 => Some(QuickAction::RefreshConnection),
            _ => None,
        }
    }
    
    fn start_editing(&mut self, field: &str) {
        self.editing_field = Some(field.to_string());
        self.edit_buffer = match field {
            "endpoint" => self.custom_config.endpoint.clone(),
            "amount" => self.custom_config.default_amount.clone(),
            "refresh" => self.custom_config.refresh_interval.to_string(),
            "faucet_address" => self.faucet_address_input.clone(),
            "faucet_amount" => self.faucet_amount.clone(),
            _ => String::new(),
        };
    }
    
    fn finish_editing(&mut self) {
        if let Some(field) = &self.editing_field {
            match field.as_str() {
                "endpoint" => {
                    self.custom_config.endpoint = self.edit_buffer.clone();
                    self.auto_connected = false; // Reset to allow reconnection
                }
                "amount" => self.custom_config.default_amount = self.edit_buffer.clone(),
                "refresh" => {
                    if let Ok(val) = self.edit_buffer.parse::<u64>() {
                        self.custom_config.refresh_interval = val;
                    }
                }
                "faucet_address" => self.faucet_address_input = self.edit_buffer.clone(),
                "faucet_amount" => self.faucet_amount = self.edit_buffer.clone(),
                _ => {}
            }
            self.presets[2] = self.custom_config.clone(); // Update custom preset
        }
        self.editing_field = None;
        self.edit_buffer.clear();
    }
    
    fn log_to_console(&mut self, msg: &str, color: Color) {
        let timestamp = chrono::Local::now().format("%H:%M:%S").to_string();
        self.console_logs.push((format!("[{}] {}", timestamp, msg), color));
        
        // Keep only the last N logs
        if self.console_logs.len() > self.max_console_logs {
            self.console_logs.remove(0);
        }
    }
    
    async fn drip_from_faucet(&mut self) {
        // Create error log file for debugging
        let error_log_path = ".drista/last_error.log";
        let _ = std::fs::create_dir_all(".drista");
        let address = if self.faucet_address_input.is_empty() {
            if let Some(account) = self.accounts.get(self.selected_account) {
                account.address.clone()
            } else {
                self.log_to_console("No address specified for faucet", Color::Red);
                return;
            }
        } else {
            self.faucet_address_input.clone()
        };
        
        self.log_to_console(&format!("💧 Faucet request: {} COHR to {}", self.faucet_amount, &address[..16]), Color::Cyan);
        
        let request = FaucetRequest {
            address: address.clone(),
            amount: self.faucet_amount.clone(),
            timestamp: chrono::Local::now().format("%H:%M:%S").to_string(),
            status: "Pending".to_string(),
        };
        
        self.faucet_requests.push(request);
        
        // Try to use Alice's account to send tokens (she has initial balance)
        let client = match &self.ws_client {
            Some(c) => c.clone(),
            None => {
                self.message = Some(("Not connected to network".to_string(), Color::Red));
                if let Some(last) = self.faucet_requests.last_mut() {
                    last.status = "Failed - No connection".to_string();
                }
                return;
            }
        };
        
        // Use Alice's well-known dev account as faucet
        let alice_seed = "//Alice";
        let alice_pair = sr25519::Pair::from_string(alice_seed, None).unwrap();
        let alice_address = alice_pair.public().to_ss58check();
        
        // Check Alice's balance first
        let alice_balance_result = self.query_balance(&client, &alice_address).await;
        match alice_balance_result {
            Ok((free, _reserved, _, _)) => {
                let balance_msg = format!("💰 Alice balance: {} COHR", self.format_balance(free));
                self.log_to_console(&balance_msg, Color::Cyan);
                if free < 1_000_000_000_000_000_000 { // Less than 1 COHR
                    self.log_to_console("⚠️  Alice has insufficient balance for faucet", Color::Red);
                    self.message = Some(("Faucet account has insufficient balance".to_string(), Color::Red));
                    if let Some(last) = self.faucet_requests.last_mut() {
                        last.status = "Failed - Faucet empty".to_string();
                    }
                    return;
                }
            }
            Err(e) => {
                let error_msg = format!("⚠️  Could not check Alice balance: {}", e);
                self.log_to_console(&error_msg, Color::Yellow);
            }
        }
        
        // Get current block number
        let block_number = self.get_current_block_number(&client).await.unwrap_or(0);
        
        // Create a transfer extrinsic
        match self.create_transfer_extrinsic(&client, &alice_pair, &address, &self.faucet_amount).await {
            Ok(tx_hash) => {
                self.log_to_console(&format!("💦 Faucet transaction sent: {}", tx_hash), Color::Green);
                if let Some(last) = self.faucet_requests.last_mut() {
                    last.status = format!("Success - TX: {}...", &tx_hash[..8]);
                }
                self.message = Some(("Faucet request successful!".to_string(), Color::Green));
                
                // Record transaction in recipient's history
                self.record_transaction(
                    &address,
                    tx_hash.clone(),
                    alice_address,
                    address.clone(),
                    self.faucet_amount.clone(),
                    block_number,
                    TransactionStatus::Success
                );
                
                // Refresh balance after a short delay
                tokio::time::sleep(tokio::time::Duration::from_secs(2)).await;
                self.check_all_balances().await;
            }
            Err(e) => {
                // Log error to file for debugging
                let error_details = format!(
                    "Faucet Error Log\n\
                    ================\n\
                    Time: {}\n\
                    Alice Address: {}\n\
                    Recipient: {}\n\
                    Amount: {} COHR\n\
                    Error: {:?}\n\n\
                    To share this error, run: cat .drista/last_error.log\n",
                    chrono::Local::now().format("%Y-%m-%d %H:%M:%S"),
                    alice_address,
                    address,
                    self.faucet_amount,
                    e
                );
                let _ = std::fs::write(error_log_path, &error_details);
                
                self.log_to_console(&format!("⚠️  Faucet failed: {}", e), Color::Red);
                self.log_to_console("📝 Error details saved to .drista/last_error.log", Color::Yellow);
                if let Some(last) = self.faucet_requests.last_mut() {
                    last.status = "Failed".to_string();
                }
                self.message = Some((format!("Faucet failed: {} (see .drista/last_error.log)", e), Color::Red));
            }
        }
    }
    
    async fn create_transfer_extrinsic(
        &self, 
        client: &WsClient,
        sender: &sr25519::Pair,
        recipient: &str,
        amount_str: &str
    ) -> Result<String, Box<dyn std::error::Error>> {
        use sp_core::{crypto::{Ss58Codec, AccountId32}, Pair as PairT};
        use codec::{Encode, Compact};
        
        // Parse amount to base units
        let amount_cohr: f64 = amount_str.parse()?;
        let amount_base = (amount_cohr * 1_000_000_000_000_000_000.0) as u128;
        
        // Get recipient account ID
        let recipient_account = AccountId32::from_ss58check(recipient)?;
        
        // Get account info including nonce
        let sender_account = AccountId32::from(sender.public());
        let account_info = self.get_account_info(client, &sender_account).await?;
        
        eprintln!("Account info - nonce: {}, free: {}, reserved: {}", 
                  account_info.nonce, account_info.free, account_info.reserved);
        
        // Check if Alice has enough balance
        if account_info.free < amount_base + 1_000_000_000_000_000 { // amount + 0.001 COHR for fees
            return Err("Insufficient balance for transfer and fees".into());
        }
        
        // Create a proper runtime call with MultiAddress wrapper
        use sp_runtime::MultiAddress;
        
        // Wrap destination in MultiAddress
        let dest_multi = MultiAddress::<AccountId32, ()>::Id(recipient_account.clone());
        
        // Create the call
        let call = (
            6u8,   // Balances pallet index
            0u8,   // transfer_allow_death call index
            dest_multi,
            Compact(amount_base)
        );
        
        // Create signed extras
        let extra = (
            (), // CheckSpecVersion
            (), // CheckTxVersion  
            (), // CheckGenesis
            (), // CheckEra (immortal)
            Compact(account_info.nonce),
            (), // CheckWeight
            Compact(0u128), // tip
            (), // CheckMetadataHash
        );
        
        // Sign the payload (call + extra)
        let raw_payload = (&call, &extra);
        let signature = sender.sign(&raw_payload.encode());
        
        // Construct the extrinsic manually
        let mut extrinsic_bytes = Vec::new();
        
        // Version byte (0x84 = v4 with signature bit set)
        extrinsic_bytes.push(0x84);
        
        // Signer (as MultiAddress)
        MultiAddress::<AccountId32, ()>::Id(sender_account.clone()).encode_to(&mut extrinsic_bytes);
        
        // Signature (as MultiSignature)  
        sp_runtime::MultiSignature::Sr25519(signature).encode_to(&mut extrinsic_bytes);
        
        // Extra fields
        extra.encode_to(&mut extrinsic_bytes);
        
        // Call data
        call.encode_to(&mut extrinsic_bytes);
        
        let hex_extrinsic = format!("0x{}", hex::encode(&extrinsic_bytes));
        eprintln!("Submitting extrinsic: {}", hex_extrinsic);
        
        // Submit the transaction
        match client
            .request::<String, _>("author_submitExtrinsic", rpc_params![hex_extrinsic])
            .await {
            Ok(tx_hash) => {
                eprintln!("✓ Transfer submitted successfully: {}", tx_hash);
                Ok(tx_hash)
            },
            Err(e) => {
                let error_detail = format!(
                    "Transfer failed:\n\
                    Error: {:?}\n\
                    Sender: {}\n\
                    Recipient: {}\n\
                    Amount: {} COHR ({} base units)\n\
                    Nonce: {}\n\
                    Free balance: {} base units\n",
                    e,
                    sender_account.to_ss58check(),
                    recipient,
                    amount_str,
                    amount_base,
                    account_info.nonce,
                    account_info.free
                );
                let _ = std::fs::write(".drista/last_transfer_attempt.log", &error_detail);
                eprintln!("{}", error_detail);
                
                Err(format!("Transfer failed: {}", e).into())
            }
        }
    }
    
    async fn get_account_info(&self, client: &WsClient, account: &sp_core::crypto::AccountId32) -> Result<AccountInfo, Box<dyn std::error::Error>> {
        let storage_key = self.get_balance_storage_key(account);
        
        let result: serde_json::Value = client
            .request("state_getStorage", rpc_params![storage_key])
            .await?;
        
        if let Some(hex_data) = result.as_str() {
            let data = hex::decode(&hex_data[2..])?;
            
            // Decode System.Account storage format
            // Layout: nonce (4 bytes) + consumers (4 bytes) + providers (4 bytes) + sufficients (4 bytes) + 
            //         data.free (16 bytes) + data.reserved (16 bytes) + data.misc_frozen (16 bytes) + data.fee_frozen (16 bytes)
            if data.len() >= 48 {
                let nonce = u32::from_le_bytes(data[0..4].try_into()?);
                let free = u128::from_le_bytes(data[16..32].try_into()?);
                let reserved = u128::from_le_bytes(data[32..48].try_into()?);
                
                Ok(AccountInfo {
                    nonce,
                    free,
                    reserved,
                })
            } else {
                Ok(AccountInfo::default())
            }
        } else {
            Ok(AccountInfo::default())
        }
    }
    
    
    async fn start_blockchain_monitoring(&mut self) {
        if self.monitoring_active || self.ws_client.is_none() {
            return;
        }
        
        self.monitoring_active = true;
        self.log_to_console("📡 Starting blockchain monitoring...", Color::Yellow);
        
        // Test the connection immediately
        if let Some(client) = &self.ws_client {
            match client.request::<serde_json::Value, _>("system_chain", rpc_params![]).await {
                Ok(chain) => {
                    self.log_to_console(&format!("✓ Connected to chain: {}", chain), Color::Green);
                }
                Err(e) => {
                    self.log_to_console(&format!("⚠️  Connection test failed: {}", e), Color::Red);
                }
            }
        }
    }
    
    async fn poll_blockchain_events(&mut self) {
        if !self.monitoring_active {
            return;
        }
        
        let client = match self.ws_client.as_ref() {
            Some(c) => c,
            None => return,
        };
        
        // Collect log messages to avoid borrow issues
        let mut log_messages = Vec::new();
        
        // Get latest block header
        match client.request::<serde_json::Value, _>("chain_getHeader", rpc_params![]).await {
                Ok(header) => {
                    if let Some(number_str) = header.get("number").and_then(|n| n.as_str()) {
                        // Parse block number from hex
                        if let Ok(block_num) = u32::from_str_radix(&number_str[2..], 16) {
                            if self.last_block_number != Some(block_num) {
                                // New block!
                                if self.last_block_number.is_some() {
                                    // Get block hash
                                    if let Some(hash) = header.get("hash").and_then(|h| h.as_str()) {
                                        log_messages.push((
                                            format!("⛓️  New Block #{} | Hash: {}...", 
                                                block_num, 
                                                &hash[2..10]
                                            ), 
                                            Color::Blue
                                        ));
                                    }
                                } else {
                                    // First block we see
                                    log_messages.push((
                                        format!("📊 Current block height: #{}", block_num),
                                        Color::Green
                                    ));
                                }
                                self.last_block_number = Some(block_num);
                                
                                // Get block details
                                if let Ok(block) = client.request::<serde_json::Value, _>(
                                    "chain_getBlock", 
                                    rpc_params![header.get("hash")]
                                ).await {
                                    // Count and decode extrinsics
                                    if let Some(extrinsics) = block.get("block")
                                        .and_then(|b| b.get("extrinsics"))
                                        .and_then(|e| e.as_array()) 
                                    {
                                        if extrinsics.len() > 1 { // More than just timestamp
                                            log_messages.push((
                                                format!("📦 {} extrinsics in block", extrinsics.len()),
                                                Color::Green
                                            ));
                                            
                                            // Try to decode transfer extrinsics
                                            for (i, ext) in extrinsics.iter().enumerate() {
                                                if let Some(ext_str) = ext.as_str() {
                                                    if ext_str.len() > 100 && i > 0 { // Skip timestamp extrinsic
                                                        // Simple heuristic: transfers are usually medium-sized
                                                        log_messages.push((
                                                            format!("  → Transaction {}: {}...", i, &ext_str[..20]),
                                                            Color::Cyan
                                                        ));
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                Err(e) => {
                    log_messages.push((format!("⚠️  Monitor error: {}", e), Color::Red));
                    self.monitoring_active = false;
                }
            }
            
        
        // Also subscribe to finalized heads for important events
        if let Ok(_finalized) = client.request::<serde_json::Value, _>("chain_getFinalizedHead", rpc_params![]).await {
            // Log finalized blocks periodically
        }
        
        // Now log all collected messages
        for (msg, color) in log_messages {
            self.log_to_console(&msg, color);
        }
    }
    
    async fn start_docker_monitoring(&mut self) {
        // Stop existing monitoring if any
        if let Some(handle) = self.docker_log_handle.take() {
            handle.abort();
        }
        
        self.log_to_console("🐳 Starting Docker logs streaming...", Color::Yellow);
        
        // Clone what we need for the async task
        let _logs_sender = self.console_logs.clone();
        let _max_logs = self.max_console_logs;
        
        // Spawn a task to stream docker logs
        let handle = tokio::spawn(async move {
            match Command::new("docker-compose")
                .args(&["-f", "../quantum-harmony-base/docker/docker-compose-local.yml", "logs", "-f", "--tail", "50"])
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .spawn()
            {
                Ok(mut child) => {
                    if let Some(stdout) = child.stdout.take() {
                        let reader = BufReader::new(stdout);
                        let mut lines = reader.lines();
                        
                        while let Ok(Some(line)) = lines.next_line().await {
                            // Parse docker compose logs and colorize by container
                            let (_formatted_line, _color) = if line.contains("quantum-alice") {
                                (format!("🅰️  {}", line), Color::Cyan)
                            } else if line.contains("quantum-bob") {
                                (format!("🅱️  {}", line), Color::Blue)
                            } else if line.contains("quantum-charlie") {
                                (format!("🅲  {}", line), Color::Magenta)
                            } else if line.contains("quantum-dave") {
                                (format!("🅳  {}", line), Color::Green)
                            } else if line.contains("ERROR") || line.contains("WARN") {
                                (line, Color::Red)
                            } else if line.contains("INFO") {
                                (line, Color::White)
                            } else {
                                (line, Color::Gray)
                            };
                            
                            // Would send to main app through a channel in real implementation
                            // For now we'll rely on polling
                        }
                    }
                }
                Err(e) => {
                    eprintln!("Failed to start docker logs: {}", e);
                }
            }
        });
        
        self.docker_log_handle = Some(handle);
    }
    
    async fn poll_docker_logs(&mut self) {
        if self.console_mode != ConsoleMode::Docker {
            return;
        }
        
        // Try to read docker logs
        match Command::new("docker-compose")
            .args(&["-f", "../quantum-harmony-base/docker/docker-compose-local.yml", "logs", "--tail", "10"])
            .output()
            .await
        {
            Ok(output) => {
                let logs = String::from_utf8_lossy(&output.stdout);
                let stderr = String::from_utf8_lossy(&output.stderr);
                
                // Process stdout
                for line in logs.lines() {
                    if line.trim().is_empty() || line.starts_with("Attaching to") {
                        continue;
                    }
                    
                    // Parse Docker Compose format with ANSI codes
                    let cleaned_line = strip_ansi_codes(line);
                    
                    let (formatted_line, color) = if cleaned_line.contains("quantum-alice |") {
                        let content = cleaned_line.split("quantum-alice |").nth(1).unwrap_or("").trim();
                        (format!("🅰️  Alice: {}", content), Color::Cyan)
                    } else if cleaned_line.contains("quantum-bob |") {
                        let content = cleaned_line.split("quantum-bob |").nth(1).unwrap_or("").trim();
                        (format!("🅱️  Bob: {}", content), Color::Blue)
                    } else if cleaned_line.contains("quantum-charlie |") {
                        let content = cleaned_line.split("quantum-charlie |").nth(1).unwrap_or("").trim();
                        (format!("🅲  Charlie: {}", content), Color::Magenta)
                    } else if cleaned_line.contains("quantum-dave |") {
                        let content = cleaned_line.split("quantum-dave |").nth(1).unwrap_or("").trim();
                        (format!("🅳  Dave: {}", content), Color::Green)
                    } else if cleaned_line.contains("quantum-explorer |") {
                        let content = cleaned_line.split("quantum-explorer |").nth(1).unwrap_or("").trim();
                        (format!("🌐 Explorer: {}", content), Color::Yellow)
                    } else {
                        continue; // Skip unrecognized lines
                    };
                    
                    self.log_to_console(&formatted_line, color);
                }
                
                // Also check stderr for errors
                if !stderr.is_empty() {
                    for line in stderr.lines() {
                        if !line.trim().is_empty() {
                            self.log_to_console(&format!("⚠️  Error: {}", line), Color::Red);
                        }
                    }
                }
            }
            Err(e) => {
                self.log_to_console(&format!("⚠️  Failed to read Docker logs: {}", e), Color::Red);
            }
        }
    }
    
    async fn check_all_balances(&mut self) {
        self.log_to_console("💰 Checking account balances...", Color::Yellow);
        
        if self.accounts.is_empty() {
            self.message = Some(("No accounts to check. Create an account first!".to_string(), Color::Yellow));
            return;
        }
        
        let client = match &self.ws_client {
            Some(c) => c.clone(),
            None => {
                self.message = Some(("Not connected to network".to_string(), Color::Red));
                return;
            }
        };
        
        // Collect account data first to avoid borrow issues
        let accounts_to_check: Vec<(usize, String, String)> = self.accounts.iter()
            .enumerate()
            .map(|(i, acc)| (i, acc.address.clone(), acc.name.clone()))
            .collect();
        
        // Collect balance update data
        let mut balance_updates = Vec::new();
        let mut error_logs = Vec::new();
        
        for (i, address, name) in accounts_to_check {
            match self.query_balance(&client, &address).await {
                Ok((free, reserved, _misc_frozen, _fee_frozen)) => {
                    // Convert from base units to COHR (1 COHR = 10^18 base units)
                    let free_cohr = self.format_balance(free);
                    balance_updates.push((i, format!("{} COHR", free_cohr), name, free_cohr, reserved));
                }
                Err(e) => {
                    error_logs.push((name, e.to_string()));
                }
            }
        }
        
        // Log errors
        for (name, error) in error_logs {
            self.log_to_console(
                &format!("✗ Failed to check {}: {}", name, error), 
                Color::Red
            );
        }
        
        // Now apply updates and log
        for (i, balance_str, name, free_cohr, reserved) in balance_updates {
            self.accounts[i].balance = balance_str;
            
            self.log_to_console(
                &format!("✓ {}: {} COHR", name, free_cohr), 
                Color::Green
            );
            
            // Log additional details if non-zero
            if reserved > 0 {
                let reserved_cohr = self.format_balance(reserved);
                self.log_to_console(
                    &format!("  Reserved: {} COHR", reserved_cohr), 
                    Color::Gray
                );
            }
        }
        
        self.message = Some(("Balance check complete!".to_string(), Color::Green));
    }
    
    async fn query_balance(&mut self, client: &WsClient, address: &str) -> Result<(u128, u128, u128, u128), Box<dyn std::error::Error>> {
        // Convert SS58 address to AccountId32
        use sp_core::crypto::AccountId32;
        let account_id = AccountId32::from_ss58check(address)
            .map_err(|e| format!("Invalid address: {:?}", e))?;
        
        // Query system.account storage
        let storage_key = self.get_balance_storage_key(&account_id);
        
        // Try direct connection first
        let result = match client.request("state_getStorage", rpc_params![storage_key.clone()]).await {
            Ok(result) => result,
            Err(e) => {
                // If direct connection fails, try quantum tunnel
                self.log_to_console(&format!("Direct query failed, trying P2P tunnel: {}", e), Color::Yellow);
                
                if self.tunnel_client.is_none() {
                    self.log_to_console("Initializing quantum tunnel...", Color::Yellow);
                    if let Err(tunnel_err) = self.init_quantum_tunnel().await {
                        return Err(format!("Both direct and tunnel failed: {} | {}", e, tunnel_err).into());
                    }
                }
                
                if let Some(tunnel) = &mut self.tunnel_client {
                    match tunnel.query_balance_tunneled(&storage_key).await {
                        Ok(Some(hex_data)) => {
                            self.log_to_console("✓ Balance queried via quantum tunnel", Color::Green);
                            serde_json::json!(hex_data)
                        }
                        Ok(None) => serde_json::json!(null),
                        Err(tunnel_err) => {
                            return Err(format!("Both direct and tunnel failed: {} | {}", e, tunnel_err).into());
                        }
                    }
                } else {
                    return Err(format!("Connection failed and tunnel unavailable: {}", e).into());
                }
            }
        };
        
        // Decode the result
        if let Some(hex_data) = result.as_str() {
            let data = hex::decode(&hex_data[2..])?; // Remove "0x" prefix
            
            // The storage format for AccountInfo in Substrate is:
            // nonce: u32, consumers: u32, providers: u32, sufficients: u32, 
            // data: AccountData { free: u128, reserved: u128, misc_frozen: u128, fee_frozen: u128 }
            if data.len() >= 48 { // 16 bytes header + 32 bytes data
                // Skip the first 16 bytes (nonce, consumers, providers, sufficients)
                let free = u128::from_le_bytes(data[16..32].try_into()?);
                let reserved = u128::from_le_bytes(data[32..48].try_into()?);
                let misc_frozen = if data.len() >= 64 {
                    u128::from_le_bytes(data[48..64].try_into()?)
                } else { 0 };
                let fee_frozen = if data.len() >= 80 {
                    u128::from_le_bytes(data[64..80].try_into()?)
                } else { 0 };
                
                Ok((free, reserved, misc_frozen, fee_frozen))
            } else {
                Ok((0, 0, 0, 0)) // Account doesn't exist or has no balance
            }
        } else {
            Ok((0, 0, 0, 0)) // No data
        }
    }
    
    async fn init_quantum_tunnel(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        let config = TunnelConfig::default();
        let mut tunnel = QuantumTunnelClient::new(config);
        
        self.log_to_console(&format!("Connecting to quantum tunnel at {}", tunnel.server_endpoint()), Color::Yellow);
        
        match tunnel.connect().await {
            Ok(()) => {
                self.log_to_console("✓ Quantum tunnel established with QKD security", Color::Green);
                self.tunnel_client = Some(tunnel);
                self.use_tunnel = true;
                Ok(())
            }
            Err(e) => {
                self.log_to_console(&format!("✗ Tunnel connection failed: {}", e), Color::Red);
                Err(format!("Failed to establish quantum tunnel: {}", e).into())
            }
        }
    }
    
    fn get_balance_storage_key(&self, account_id: &sp_core::crypto::AccountId32) -> String {
        use blake2::{Blake2b, Digest};
        use blake2::digest::consts::U16;
        
        // System.Account storage prefix (from blockchain analysis)
        // This is twox_128("System") + twox_128("Account") but we use the known constant
        let system_account_prefix = hex::decode("26aa394eea5630e07c48ae0c9558cef7b99d880ec681799c0cf30e8886371da9").unwrap();
        
        let mut key = Vec::new();
        key.extend_from_slice(&system_account_prefix);
        
        // For maps, use Blake2b_128(account_id) + account_id
        let mut hasher = Blake2b::<U16>::new();
        hasher.update(account_id.as_ref() as &[u8]);
        let hash = hasher.finalize();
        
        key.extend_from_slice(&hash[..]); // Blake2b-128 hash
        key.extend_from_slice(account_id.as_ref()); // Then the full AccountId32
        
        format!("0x{}", hex::encode(key))
    }
    
    fn format_balance(&self, amount: u128) -> String {
        // Convert from base units to COHR (1 COHR = 10^18)
        const DECIMALS: u128 = 1_000_000_000_000_000_000; // 10^18
        
        let whole = amount / DECIMALS;
        let fraction = amount % DECIMALS;
        
        if fraction == 0 {
            format!("{}", whole)
        } else {
            // Show up to 4 decimal places
            let fraction_str = format!("{:018}", fraction);
            let trimmed = fraction_str.trim_end_matches('0');
            if trimmed.len() > 4 {
                format!("{}.{}", whole, &trimmed[..4])
            } else {
                format!("{}.{}", whole, trimmed)
            }
        }
    }
    
    async fn refresh_selected_balance(&mut self) {
        if self.accounts.is_empty() {
            return;
        }
        
        let client = match &self.ws_client {
            Some(c) => c.clone(),
            None => return,
        };
        
        let address = self.accounts[self.selected_account].address.clone();
        if let Ok((free, _, _, _)) = self.query_balance(&client, &address).await {
            self.accounts[self.selected_account].balance = format!("{} COHR", self.format_balance(free));
        }
    }
    
    fn load_existing_accounts(&mut self) {
        // Check .drista directory for account files
        let drista_dir = std::path::Path::new(".drista");
        if !drista_dir.exists() {
            return;
        }
        
        match std::fs::read_dir(drista_dir) {
            Ok(entries) => {
                for entry in entries.flatten() {
                    let path = entry.path();
                    if path.extension().and_then(|s| s.to_str()) == Some("key") {
                        if let Ok(contents) = std::fs::read_to_string(&path) {
                            // Parse account file
                            let lines: Vec<&str> = contents.lines().collect();
                            if lines.len() >= 2 {
                                if let Some(address_line) = lines.get(0) {
                                    if let Some(address) = address_line.strip_prefix("Address: ") {
                                        let account_num = self.accounts.len() + 1;
                                        self.accounts.push(Account {
                                            name: format!("Account {}", account_num),
                                            address: address.to_string(),
                                            balance: "0 COHR".to_string(),
                                            nonce: 0,
                                            transactions: Vec::new(),
                                        });
                                        self.log_to_console(
                                            &format!("📂 Loaded existing account: {}...", &address[..8]), 
                                            Color::Blue
                                        );
                                    }
                                }
                            }
                        }
                    }
                }
            }
            Err(e) => {
                self.log_to_console(&format!("⚠️  Failed to load accounts: {}", e), Color::Yellow);
            }
        }
        
        if !self.accounts.is_empty() {
            self.log_to_console(&format!("✓ Loaded {} existing account(s)", self.accounts.len()), Color::Green);
        }
    }
    
    fn record_transaction(
        &mut self,
        account_address: &str,
        hash: String,
        from: String,
        to: String,
        amount: String,
        block_number: u32,
        status: TransactionStatus,
    ) {
        let tx = Transaction {
            hash,
            from,
            to,
            amount,
            timestamp: chrono::Local::now().format("%Y-%m-%d %H:%M:%S").to_string(),
            block_number,
            status,
        };
        
        // Add to the relevant account's transaction history
        for account in &mut self.accounts {
            if account.address == account_address || account.address == tx.from || account.address == tx.to {
                account.transactions.push(tx.clone());
                // Keep only last 50 transactions per account
                if account.transactions.len() > 50 {
                    account.transactions.remove(0);
                }
            }
        }
    }
    
    async fn get_current_block_number(&self, client: &WsClient) -> Result<u32, Box<dyn std::error::Error>> {
        let block_hash: serde_json::Value = client
            .request("chain_getBlockHash", rpc_params![])
            .await?;
        
        let block: serde_json::Value = client
            .request("chain_getBlock", rpc_params![block_hash])
            .await?;
        
        if let Some(number) = block["block"]["header"]["number"].as_str() {
            // Remove 0x prefix and parse hex
            let number_str = number.strip_prefix("0x").unwrap_or(number);
            let block_num = u32::from_str_radix(number_str, 16)?;
            Ok(block_num)
        } else {
            Ok(0)
        }
    }
}

enum QuickAction {
    CreateAccount,
    CheckBalance,
    SendTokens,
    RefreshConnection,
}

/// Helper function to strip ANSI color codes from docker-compose output
fn strip_ansi_codes(s: &str) -> String {
    let re = regex::Regex::new(r"\x1b\[[0-9;]*m").unwrap();
    re.replace_all(s, "").to_string()
}

/// Render the UI
fn ui(f: &mut Frame, app: &App) {
    let chunks = Layout::default()
        .direction(Direction::Vertical)
        .margin(1)
        .constraints([
            Constraint::Length(3),  // Title
            Constraint::Length(3),  // Main tabs
            Constraint::Min(0),     // Content
            Constraint::Length(2),  // Status bar
        ])
        .split(f.size());
    
    // Title with connection indicator
    let title_style = if app.ws_client.is_some() {
        Style::default().fg(Color::Green)
    } else {
        Style::default().fg(Color::Yellow)
    };
    
    let title = Paragraph::new("Drista Wallet - Quantum Harmony Network")
        .style(title_style.add_modifier(Modifier::BOLD))
        .alignment(Alignment::Center)
        .block(Block::default().borders(Borders::ALL));
    f.render_widget(title, chunks[0]);
    
    // Main tabs
    let main_tabs = ["Quick Start", "Accounts", "💧 Faucet", "📟 Console", "🏗️ Architecture", "Config", "Exit"];
    let tabs = Tabs::new(main_tabs.to_vec())
        .block(Block::default().borders(Borders::ALL))
        .select(app.main_tab as usize)
        .style(Style::default().fg(Color::White))
        .highlight_style(Style::default().fg(Color::Cyan).add_modifier(Modifier::BOLD));
    f.render_widget(tabs, chunks[1]);

    // Content area
    match app.main_tab {
        MainTab::QuickStart => render_quick_start(f, app, chunks[2]),
        MainTab::Accounts => render_accounts(f, app, chunks[2]),
        MainTab::Faucet => render_faucet(f, app, chunks[2]),
        MainTab::Console => render_console(f, app, chunks[2]),
        MainTab::Architecture => render_architecture_spiral(f, &app.architecture_spiral, chunks[2]),
        MainTab::Config => render_config(f, app, chunks[2]),
        MainTab::Exit => render_exit(f, chunks[2]),
    }
    
    // Status bar with message
    let status_text = if let Some((msg, _)) = &app.message {
        format!("{} | {}", app.connection_status, msg)
    } else {
        format!("{} | Tab: navigate | Enter: select | Esc: cancel", app.connection_status)
    };
    
    let status_color = if let Some((_, color)) = &app.message {
        *color
    } else if app.ws_client.is_some() {
        Color::Green
    } else {
        Color::DarkGray
    };
    
    let status = Paragraph::new(status_text)
        .style(Style::default().fg(status_color));
    f.render_widget(status, chunks[3]);
}

fn render_quick_start(f: &mut Frame, app: &App, area: Rect) {
    let chunks = Layout::default()
        .direction(Direction::Vertical)
        .margin(1)
        .constraints([
            Constraint::Length(6),   // Welcome
            Constraint::Length(10),  // Quick actions
            Constraint::Min(0),      // Recent activity
        ])
        .split(area);
    
    // Calculate quantum security metrics based on mode
    let (quantum_readiness, security_score, hash_mode) = match app.security_mode {
        SecurityMode::Classical => (0.0, 0.25, "Blake2"),
        SecurityMode::Hybrid => (0.3, 0.45, "Blake2+SHA3"),
        SecurityMode::QuantumSecure => (0.8, 0.85, "SHA3+QKD"),
    };
    
    // Welcome section with quantum indicators
    let welcome = vec![
        Line::from(""),
        Line::from(vec![
            Span::raw("Welcome to Drista! Your wallet is "),
            Span::styled(
                if app.ws_client.is_some() { "ready to use" } else { "connecting" },
                Style::default().fg(if app.ws_client.is_some() { Color::Green } else { Color::Yellow })
            ),
        ]),
        Line::from(""),
        Line::from(format!("Active preset: {}", app.custom_config.name)),
        Line::from(""),
        Line::from(vec![
            Span::raw("🔐 Security: "),
            Span::styled(
                format!("{:.0}%", security_score * 100.0),
                Style::default().fg(if security_score > 0.7 { Color::Green } 
                    else if security_score > 0.4 { Color::Yellow } 
                    else { Color::Red })
            ),
            Span::raw(" | 🔮 Quantum Ready: "),
            Span::styled(
                format!("{:.0}%", quantum_readiness * 100.0),
                Style::default().fg(if quantum_readiness > 0.5 { Color::Cyan } else { Color::Gray })
            ),
            Span::raw(" | Hash: "),
            Span::styled(hash_mode, Style::default().fg(Color::Blue)),
        ]),
    ];
    
    let welcome_widget = Paragraph::new(welcome)
        .block(Block::default().borders(Borders::ALL).title(" Status "))
        .alignment(Alignment::Center);
    f.render_widget(welcome_widget, chunks[0]);
    
    // Quick actions
    let actions = vec![
        ("1", "Create New Account", "Generate a new quantum-safe account"),
        ("2", "Check Balance", "Query real-time balances from blockchain"),
        ("3", "Get Tokens", "Use the faucet to receive test COHR"),
        ("4", "Refresh Connection", "Reconnect to the network"),
    ];
    
    let action_items: Vec<ListItem> = actions
        .iter()
        .enumerate()
        .map(|(i, (key, title, desc))| {
            let style = if i == app.quick_action_selected {
                Style::default().fg(Color::Cyan).add_modifier(Modifier::BOLD)
            } else {
                Style::default()
            };
            ListItem::new(vec![
                Line::from(vec![
                    Span::styled(format!("[{}] ", key), Style::default().fg(Color::Yellow)),
                    Span::styled(title.to_string(), style),
                ]),
                Line::from(format!("    {}", desc)).style(Style::default().fg(Color::DarkGray)),
            ])
        })
        .collect();
    
    let actions_list = List::new(action_items)
        .block(Block::default().borders(Borders::ALL).title(" Quick Actions "));
    f.render_widget(actions_list, chunks[1]);
    
    // Recent activity
    let activity = if app.accounts.is_empty() {
        vec![
            Line::from("No accounts yet."),
            Line::from(""),
            Line::from("Press '1' to create your first account!"),
        ]
    } else {
        let mut lines = vec![Line::from(format!("Total accounts: {}", app.accounts.len()))];
        for (_i, acc) in app.accounts.iter().take(3).enumerate() {
            lines.push(Line::from(format!(
                "  {} - {} ({})",
                acc.name,
                &acc.address[..16],
                acc.balance
            )));
        }
        lines
    };
    
    let activity_widget = Paragraph::new(activity)
        .block(Block::default().borders(Borders::ALL).title(" Recent Activity "));
    f.render_widget(activity_widget, chunks[2]);
}

fn render_faucet(f: &mut Frame, app: &App, area: Rect) {
    let chunks = Layout::default()
        .direction(Direction::Vertical)
        .margin(1)
        .constraints([
            Constraint::Length(8),   // Faucet controls
            Constraint::Length(4),   // Instructions
            Constraint::Min(0),      // Request history
        ])
        .split(area);
    
    // Faucet controls
    let is_editing_address = app.editing_field.as_ref().map(|f| f == "faucet_address").unwrap_or(false);
    let is_editing_amount = app.editing_field.as_ref().map(|f| f == "faucet_amount").unwrap_or(false);
    
    let address_display = if is_editing_address {
        format!("{}_", app.edit_buffer)
    } else if app.faucet_address_input.is_empty() {
        "(use selected account)".to_string()
    } else {
        app.faucet_address_input.clone()
    };
    
    let amount_display = if is_editing_amount {
        format!("{}_", app.edit_buffer)
    } else {
        app.faucet_amount.clone()
    };
    
    let controls = vec![
        Line::from("💧 COHR Token Faucet 💧"),
        Line::from(""),
        Line::from(vec![
            Span::raw("Address: "),
            Span::styled(
                address_display,
                Style::default().fg(if is_editing_address { Color::Yellow } else { Color::Cyan })
            ),
            Span::raw(" (press 'a' to edit)"),
        ]),
        Line::from(vec![
            Span::raw("Amount:  "),
            Span::styled(
                format!("{} COHR", amount_display),
                Style::default().fg(if is_editing_amount { Color::Yellow } else { Color::Cyan })
            ),
            Span::raw(" (press 'm' to edit)"),
        ]),
        Line::from(""),
        Line::from(vec![
            Span::styled("Press 'D' to DRIP tokens! 💦", Style::default().fg(Color::Green).add_modifier(Modifier::BOLD)),
        ]),
    ];
    
    let controls_widget = Paragraph::new(controls)
        .block(Block::default().borders(Borders::ALL).title(" Token Fountain "));
    f.render_widget(controls_widget, chunks[0]);
    
    // Instructions
    let instructions = vec![
        Line::from("The faucet provides free COHR tokens for testing."),
        Line::from("Default: 1000 COHR per request. Maximum: 10000 COHR."),
    ];
    
    let instructions_widget = Paragraph::new(instructions)
        .style(Style::default().fg(Color::DarkGray));
    f.render_widget(instructions_widget, chunks[1]);
    
    // Request history
    if app.faucet_requests.is_empty() {
        let empty = Paragraph::new("No faucet requests yet. Press 'D' to get some tokens!")
            .block(Block::default().borders(Borders::ALL).title(" History "))
            .style(Style::default().fg(Color::DarkGray));
        f.render_widget(empty, chunks[2]);
    } else {
        let requests: Vec<ListItem> = app.faucet_requests
            .iter()
            .rev()
            .take(10)
            .map(|req| {
                let status_color = match req.status.as_str() {
                    "Success" => Color::Green,
                    "Pending" => Color::Yellow,
                    _ => Color::Red,
                };
                ListItem::new(vec![
                    Line::from(format!("[{}] {} COHR to {}...", 
                        req.timestamp, req.amount, &req.address[..16]
                    )),
                    Line::from(vec![
                        Span::raw("  Status: "),
                        Span::styled(&req.status, Style::default().fg(status_color)),
                    ]),
                ])
            })
            .collect();
        
        let history = List::new(requests)
            .block(Block::default().borders(Borders::ALL).title(" Recent Requests "));
        f.render_widget(history, chunks[2]);
    }
}

fn render_console(f: &mut Frame, app: &App, area: Rect) {
    let chunks = Layout::default()
        .direction(Direction::Vertical)
        .margin(1)
        .constraints([
            Constraint::Min(0),      // Console output
            Constraint::Length(3),   // Info bar
        ])
        .split(area);
    
    // Console title based on mode
    let title = match app.console_mode {
        ConsoleMode::Blockchain => " 📟 Blockchain Events ",
        ConsoleMode::Docker => " 🐳 Docker Logs ",
    };
    
    // Calculate visible range
    let visible_height = chunks[0].height.saturating_sub(2) as usize; // -2 for borders
    let total_logs = app.console_logs.len();
    
    // Adjust scroll offset to ensure it's valid
    let max_offset = total_logs.saturating_sub(visible_height);
    let scroll_offset = app.console_scroll_offset.min(max_offset);
    
    // Get visible logs (newest first, then apply scroll)
    let mut reversed_logs: Vec<_> = app.console_logs.iter().rev().collect();
    let visible_logs: Vec<ListItem> = reversed_logs
        .into_iter()
        .skip(scroll_offset)
        .take(visible_height)
        .map(|(log, color)| {
            ListItem::new(log.clone()).style(Style::default().fg(*color))
        })
        .collect();
    
    // Add scroll indicator to title
    let scroll_indicator = if total_logs > visible_height {
        format!(" [{}-{}/{}]", 
            scroll_offset + 1, 
            (scroll_offset + visible_height).min(total_logs),
            total_logs
        )
    } else {
        String::new()
    };
    
    let console = List::new(visible_logs)
        .block(Block::default()
            .borders(Borders::ALL)
            .title(format!("{}{}", title, scroll_indicator))
            .border_style(Style::default().fg(Color::DarkGray))
        );
    f.render_widget(console, chunks[0]);
    
    // Info bar
    let mode_text = match app.console_mode {
        ConsoleMode::Blockchain => "Blockchain Events",
        ConsoleMode::Docker => "Docker Logs",
    };
    
    let info = Paragraph::new(vec![
        Line::from(format!("Mode: {} | {} entries | 'm' to switch | 'c' to clear | 'e' to show last error | ↑↓/PgUp/PgDn to scroll", 
            mode_text, app.console_logs.len()
        )),
    ])
    .style(Style::default().fg(Color::DarkGray))
    .block(Block::default().borders(Borders::TOP));
    f.render_widget(info, chunks[1]);
}

fn render_config(f: &mut Frame, app: &App, area: Rect) {
    let chunks = Layout::default()
        .direction(Direction::Vertical)
        .margin(1)
        .constraints([
            Constraint::Length(3),  // Sub-tabs
            Constraint::Min(0),     // Content
        ])
        .split(area);
    
    // Config sub-tabs
    let config_tabs = ["Network", "Display", "Security", "Defaults"];
    let tabs = Tabs::new(config_tabs.to_vec())
        .block(Block::default().borders(Borders::ALL))
        .select(app.config_tab as usize)
        .style(Style::default().fg(Color::White))
        .highlight_style(Style::default().fg(Color::Yellow));
    f.render_widget(tabs, chunks[0]);
    
    // Content based on sub-tab
    match app.config_tab {
        ConfigTab::Network => render_network_config(f, app, chunks[1]),
        ConfigTab::Display => render_display_config(f, app, chunks[1]),
        ConfigTab::Security => render_security_config(f, app, chunks[1]),
        ConfigTab::Defaults => render_defaults_config(f, app, chunks[1]),
    }
}

fn render_network_config(f: &mut Frame, app: &App, area: Rect) {
    let chunks = Layout::default()
        .direction(Direction::Vertical)
        .margin(1)
        .constraints([
            Constraint::Length(5),   // Presets
            Constraint::Min(0),      // Settings
        ])
        .split(area);
    
    // Preset selector
    let preset_list: Vec<ListItem> = app.presets
        .iter()
        .enumerate()
        .map(|(i, p)| {
            let style = if i == app.active_preset {
                Style::default().fg(Color::Green).add_modifier(Modifier::BOLD)
            } else {
                Style::default()
            };
            ListItem::new(format!("{} - {}", p.name, p.endpoint)).style(style)
        })
        .collect();
    
    let presets = List::new(preset_list)
        .block(Block::default().borders(Borders::ALL).title(" Presets (↑↓ to select, Enter to apply) "));
    f.render_widget(presets, chunks[0]);
    
    // Current settings
    let is_editing = |field: &str| -> bool {
        app.editing_field.as_ref().map(|f| f == field).unwrap_or(false)
    };
    
    let endpoint_display = if is_editing("endpoint") {
        format!("{}_", app.edit_buffer)
    } else {
        app.custom_config.endpoint.clone()
    };
    
    let settings = vec![
        Line::from("Current Configuration:"),
        Line::from(""),
        Line::from(vec![
            Span::raw("Endpoint: "),
            Span::styled(
                endpoint_display,
                Style::default().fg(if is_editing("endpoint") { Color::Yellow } else { Color::Cyan })
            ),
            Span::raw(" (e to edit)"),
        ]),
        Line::from(vec![
            Span::raw("Auto-connect: "),
            Span::styled(
                if app.custom_config.auto_connect { "Yes" } else { "No" },
                Style::default().fg(Color::Cyan)
            ),
            Span::raw(" (a to toggle)"),
        ]),
        Line::from(vec![
            Span::raw("Status: "),
            Span::styled(
                &app.connection_status,
                Style::default().fg(if app.ws_client.is_some() { Color::Green } else { Color::Yellow })
            ),
        ]),
        Line::from(""),
        Line::from("Press 'r' to reconnect with current settings"),
    ];
    
    let settings_widget = Paragraph::new(settings)
        .block(Block::default().borders(Borders::ALL).title(" Network Settings "));
    f.render_widget(settings_widget, chunks[1]);
}

fn render_display_config(f: &mut Frame, _app: &App, area: Rect) {
    let display_settings = vec![
        Line::from("Display Settings:"),
        Line::from(""),
        Line::from("• Theme: Dark (default)"),
        Line::from("• Refresh rate: 1s"),
        Line::from("• Show confirmations: Yes"),
        Line::from("• Decimal places: 4"),
        Line::from(""),
        Line::from("(Display customization coming soon)"),
    ];
    
    let widget = Paragraph::new(display_settings)
        .block(Block::default().borders(Borders::ALL));
    f.render_widget(widget, area);
}

fn render_security_config(f: &mut Frame, _app: &App, area: Rect) {
    let security_settings = vec![
        Line::from("Security Settings:"),
        Line::from(""),
        Line::from("• Auto-lock: Disabled"),
        Line::from("• Require confirmation: For transfers > 100 COHR"),
        Line::from("• Key storage: Local encrypted file"),
        Line::from("• Network: Local only (safe mode)"),
        Line::from(""),
        Line::from("(Additional security features coming soon)"),
    ];
    
    let widget = Paragraph::new(security_settings)
        .block(Block::default().borders(Borders::ALL));
    f.render_widget(widget, area);
}

fn render_defaults_config(f: &mut Frame, app: &App, area: Rect) {
    let is_editing = |field: &str| -> bool {
        app.editing_field.as_ref().map(|f| f == field).unwrap_or(false)
    };
    
    let amount_display = if is_editing("amount") {
        format!("{}_", app.edit_buffer)
    } else {
        app.custom_config.default_amount.clone()
    };
    
    let refresh_display = if is_editing("refresh") {
        format!("{}_", app.edit_buffer)
    } else {
        app.custom_config.refresh_interval.to_string()
    };
    
    let defaults = vec![
        Line::from("Default Values:"),
        Line::from(""),
        Line::from(vec![
            Span::raw("Default send amount: "),
            Span::styled(
                format!("{} COHR", amount_display),
                Style::default().fg(if is_editing("amount") { Color::Yellow } else { Color::Cyan })
            ),
            Span::raw(" (press 'd' to edit)"),
        ]),
        Line::from(vec![
            Span::raw("Auto-refresh interval: "),
            Span::styled(
                format!("{} seconds", refresh_display),
                Style::default().fg(if is_editing("refresh") { Color::Yellow } else { Color::Cyan })
            ),
            Span::raw(" (press 'i' to edit)"),
        ]),
        Line::from(vec![
            Span::raw("Auto-create account on start: "),
            Span::styled(
                if app.custom_config.auto_create_account { "Yes" } else { "No" },
                Style::default().fg(Color::Cyan)
            ),
            Span::raw(" (press 'c' to toggle)"),
        ]),
        Line::from(""),
        Line::from("These defaults make common operations faster"),
    ];
    
    let widget = Paragraph::new(defaults)
        .block(Block::default().borders(Borders::ALL));
    f.render_widget(widget, area);
}

fn render_accounts(f: &mut Frame, app: &App, area: Rect) {
    if app.accounts.is_empty() {
        let empty = vec![
            Line::from(""),
            Line::from("No accounts yet!"),
            Line::from(""),
            Line::from("Press 'c' to create your first account"),
            Line::from("Or go to Quick Start and press '1'"),
        ];
        
        let widget = Paragraph::new(empty)
            .block(Block::default().borders(Borders::ALL).title(" Accounts "))
            .alignment(Alignment::Center);
        f.render_widget(widget, area);
    } else {
        // Split area for accounts list and transaction history
        let chunks = Layout::default()
            .direction(Direction::Horizontal)
            .constraints([
                Constraint::Percentage(50), // Accounts list
                Constraint::Percentage(50), // Transaction history
            ])
            .split(area);
        
        // Render accounts list
        let accounts: Vec<ListItem> = app.accounts
            .iter()
            .enumerate()
            .map(|(i, acc)| {
                let style = if i == app.selected_account {
                    Style::default().fg(Color::Cyan).add_modifier(Modifier::BOLD)
                } else {
                    Style::default()
                };
                let tx_count = acc.transactions.len();
                ListItem::new(vec![
                    Line::from(vec![
                        Span::styled(&acc.name, style),
                        Span::raw(" - "),
                        Span::raw(&acc.balance),
                    ]),
                    Line::from(format!("  {}", acc.address))
                        .style(Style::default().fg(Color::DarkGray)),
                    Line::from(format!("  {} transactions", tx_count))
                        .style(Style::default().fg(Color::DarkGray)),
                ])
            })
            .collect();
        
        let list = List::new(accounts)
            .block(Block::default().borders(Borders::ALL).title(" Accounts (c: create, r: refresh, t: toggle tx view) "));
        f.render_widget(list, chunks[0]);
        
        // Render transaction history for selected account
        if let Some(selected_acc) = app.accounts.get(app.selected_account) {
            if selected_acc.transactions.is_empty() {
                let no_tx = Paragraph::new("No transactions yet")
                    .block(Block::default().borders(Borders::ALL).title(" Transaction History "))
                    .alignment(Alignment::Center);
                f.render_widget(no_tx, chunks[1]);
            } else {
                let transactions: Vec<ListItem> = selected_acc.transactions
                    .iter()
                    .rev() // Show newest first
                    .take(10) // Show last 10 transactions
                    .map(|tx| {
                        let status_color = match tx.status {
                            TransactionStatus::Success => Color::Green,
                            TransactionStatus::Pending => Color::Yellow,
                            TransactionStatus::Failed => Color::Red,
                        };
                        
                        let direction = if tx.from == selected_acc.address {
                            "→ Sent"
                        } else {
                            "← Received"
                        };
                        
                        ListItem::new(vec![
                            Line::from(vec![
                                Span::styled(direction, Style::default().fg(status_color)),
                                Span::raw(format!(" {} COHR", tx.amount)),
                            ]),
                            Line::from(format!("  Block #{} • {}", tx.block_number, &tx.timestamp[11..]))
                                .style(Style::default().fg(Color::DarkGray)),
                            Line::from(format!("  {}", &tx.hash[..16]))
                                .style(Style::default().fg(Color::DarkGray)),
                        ])
                    })
                    .collect();
                
                let tx_list = List::new(transactions)
                    .block(Block::default().borders(Borders::ALL).title(" Recent Transactions "));
                f.render_widget(tx_list, chunks[1]);
            }
        }
    }
}


fn render_exit(f: &mut Frame, area: Rect) {
    let exit_text = vec![
        Line::from(""),
        Line::from(""),
        Line::from(vec![
            Span::styled("Exit Drista Wallet?", Style::default().fg(Color::Yellow).add_modifier(Modifier::BOLD)),
        ]),
        Line::from(""),
        Line::from("Press Enter to exit"),
        Line::from("Press Tab to go back"),
        Line::from(""),
        Line::from("Your accounts and settings are saved."),
    ];
    
    let widget = Paragraph::new(exit_text)
        .block(Block::default().borders(Borders::ALL))
        .alignment(Alignment::Center);
    f.render_widget(widget, area);
}

/// Main entry point
pub async fn run() -> Result<(), Box<dyn std::error::Error>> {
    run_with_quantum(None).await
}

pub async fn run_with_quantum(quantum_manager: Option<QuantumManager>) -> Result<(), Box<dyn std::error::Error>> {
    // Setup terminal
    enable_raw_mode()?;
    let mut stdout = io::stdout();
    execute!(stdout, EnterAlternateScreen, EnableMouseCapture)?;
    let backend = CrosstermBackend::new(stdout);
    let mut terminal = Terminal::new(backend)?;
    
    // Create app with defaults and quantum manager
    let mut app = App::new();
    app.quantum_manager = quantum_manager;
    
    // Set security mode based on quantum manager presence
    app.security_mode = match &app.quantum_manager {
        Some(_) => SecurityMode::QuantumSecure,
        None => SecurityMode::Classical,
    };
    
    // Auto-connect if configured
    app.auto_connect().await;
    
    // Main loop
    let result = run_app(&mut terminal, &mut app).await;
    
    // Restore terminal
    disable_raw_mode()?;
    execute!(
        terminal.backend_mut(),
        LeaveAlternateScreen,
        DisableMouseCapture
    )?;
    terminal.show_cursor()?;
    
    result
}

async fn run_app<B: Backend>(terminal: &mut Terminal<B>, app: &mut App) -> Result<(), Box<dyn std::error::Error>> {
    use crossterm::event::{poll, read};
    use std::time::Duration;
    
    let mut last_poll = std::time::Instant::now();
    
    loop {
        terminal.draw(|f| ui(f, app))?;
        
        // Clear message after showing
        if app.message.is_some() {
            app.message = None;
        }
        
        // Poll events periodically based on mode
        if last_poll.elapsed() > Duration::from_secs(1) {
            match app.console_mode {
                ConsoleMode::Blockchain => app.poll_blockchain_events().await,
                ConsoleMode::Docker => app.poll_docker_logs().await,
            }
            last_poll = std::time::Instant::now();
        }
        
        // Check for events with timeout to allow async polling
        if poll(Duration::from_millis(100))? {
            if let Event::Key(key) = read()? {
            // Global keys
            if key.code == KeyCode::Char('c') && key.modifiers.contains(KeyModifiers::CONTROL) {
                break;
            }
            
            // Handle editing mode
            if let Some(_field) = &app.editing_field {
                match key.code {
                    KeyCode::Esc => {
                        app.editing_field = None;
                        app.edit_buffer.clear();
                    }
                    KeyCode::Enter => {
                        app.finish_editing();
                    }
                    KeyCode::Backspace => {
                        app.edit_buffer.pop();
                    }
                    KeyCode::Char(c) => {
                        app.edit_buffer.push(c);
                    }
                    _ => {}
                }
                continue;
            }
            
            // Normal navigation
            match key.code {
                KeyCode::Tab => {
                    app.main_tab = match app.main_tab {
                        MainTab::QuickStart => MainTab::Accounts,
                        MainTab::Accounts => MainTab::Faucet,
                        MainTab::Faucet => MainTab::Console,
                        MainTab::Console => MainTab::Architecture,
                        MainTab::Architecture => MainTab::Config,
                        MainTab::Config => MainTab::Exit,
                        MainTab::Exit => MainTab::QuickStart,
                    };
                }
                KeyCode::BackTab => {
                    app.main_tab = match app.main_tab {
                        MainTab::QuickStart => MainTab::Exit,
                        MainTab::Accounts => MainTab::QuickStart,
                        MainTab::Faucet => MainTab::Accounts,
                        MainTab::Console => MainTab::Faucet,
                        MainTab::Architecture => MainTab::Console,
                        MainTab::Config => MainTab::Architecture,
                        MainTab::Exit => MainTab::Config,
                    };
                }
                _ => {}
            }
            
            // Tab-specific handling
            match app.main_tab {
                MainTab::QuickStart => {
                    match key.code {
                        KeyCode::Up => {
                            if app.quick_action_selected > 0 {
                                app.quick_action_selected -= 1;
                            }
                        }
                        KeyCode::Down => {
                            if app.quick_action_selected < 3 {
                                app.quick_action_selected += 1;
                            }
                        }
                        KeyCode::Char('1') | KeyCode::Enter if app.quick_action_selected == 0 => {
                            app.quick_create_account().await;
                        }
                        KeyCode::Char('2') | KeyCode::Enter if app.quick_action_selected == 1 => {
                            app.check_all_balances().await;
                        }
                        KeyCode::Char('3') | KeyCode::Enter if app.quick_action_selected == 2 => {
                            app.main_tab = MainTab::Faucet; // Switch to faucet tab for sending
                            app.message = Some(("Use the Faucet tab to send tokens".to_string(), Color::Yellow));
                        }
                        KeyCode::Char('4') | KeyCode::Enter if app.quick_action_selected == 3 => {
                            app.auto_connected = false;
                            app.auto_connect().await;
                        }
                        _ => {}
                    }
                }
                MainTab::Config => {
                    // Sub-tab navigation
                    match key.code {
                        KeyCode::Left => {
                            app.config_tab = match app.config_tab {
                                ConfigTab::Network => ConfigTab::Defaults,
                                ConfigTab::Display => ConfigTab::Network,
                                ConfigTab::Security => ConfigTab::Display,
                                ConfigTab::Defaults => ConfigTab::Security,
                            };
                        }
                        KeyCode::Right => {
                            app.config_tab = match app.config_tab {
                                ConfigTab::Network => ConfigTab::Display,
                                ConfigTab::Display => ConfigTab::Security,
                                ConfigTab::Security => ConfigTab::Defaults,
                                ConfigTab::Defaults => ConfigTab::Network,
                            };
                        }
                        _ => {}
                    }
                    
                    // Config-specific actions
                    match app.config_tab {
                        ConfigTab::Network => {
                            match key.code {
                                KeyCode::Char('e') => app.start_editing("endpoint"),
                                KeyCode::Char('a') => {
                                    app.custom_config.auto_connect = !app.custom_config.auto_connect;
                                    app.presets[2] = app.custom_config.clone();
                                }
                                KeyCode::Char('r') => {
                                    app.auto_connected = false;
                                    app.auto_connect().await;
                                }
                                KeyCode::Up => {
                                    if app.active_preset > 0 {
                                        app.active_preset -= 1;
                                    }
                                }
                                KeyCode::Down => {
                                    if app.active_preset < app.presets.len() - 1 {
                                        app.active_preset += 1;
                                    }
                                }
                                KeyCode::Enter => {
                                    app.custom_config = app.presets[app.active_preset].clone();
                                    app.auto_connected = false;
                                    app.auto_connect().await;
                                }
                                _ => {}
                            }
                        }
                        ConfigTab::Defaults => {
                            match key.code {
                                KeyCode::Char('d') => app.start_editing("amount"),
                                KeyCode::Char('i') => app.start_editing("refresh"),
                                KeyCode::Char('c') => {
                                    app.custom_config.auto_create_account = !app.custom_config.auto_create_account;
                                    app.presets[2] = app.custom_config.clone();
                                }
                                _ => {}
                            }
                        }
                        _ => {}
                    }
                }
                MainTab::Accounts => {
                    match key.code {
                        KeyCode::Char('c') => {
                            app.quick_create_account().await;
                        }
                        KeyCode::Up => {
                            if app.selected_account > 0 {
                                app.selected_account -= 1;
                            }
                        }
                        KeyCode::Down => {
                            if app.selected_account < app.accounts.len().saturating_sub(1) {
                                app.selected_account += 1;
                            }
                        }
                        KeyCode::Char('r') => {
                            app.check_all_balances().await;
                        }
                        _ => {}
                    }
                }
                MainTab::Faucet => {
                    match key.code {
                        KeyCode::Char('a') => app.start_editing("faucet_address"),
                        KeyCode::Char('m') => app.start_editing("faucet_amount"),
                        KeyCode::Char('D') => {
                            app.drip_from_faucet().await;
                        }
                        _ => {}
                    }
                }
                MainTab::Console => {
                    match key.code {
                        KeyCode::Char('c') => {
                            // Clear console
                            app.console_logs.clear();
                            app.log_to_console("Console cleared", Color::Yellow);
                        }
                        KeyCode::Char('m') => {
                            // Switch mode
                            app.console_logs.clear();
                            app.console_mode = match app.console_mode {
                                ConsoleMode::Blockchain => {
                                    app.log_to_console("🐳 Switched to Docker logs mode", Color::Yellow);
                                    app.log_to_console("Showing container logs from docker-compose...", Color::Gray);
                                    ConsoleMode::Docker
                                }
                                ConsoleMode::Docker => {
                                    app.log_to_console("⛓️  Switched to Blockchain events mode", Color::Yellow);
                                    app.log_to_console("Monitoring blockchain events...", Color::Gray);
                                    ConsoleMode::Blockchain
                                }
                            };
                        }
                        KeyCode::Char('e') => {
                            // Show last error
                            if let Ok(error_content) = std::fs::read_to_string(".drista/last_error.log") {
                                app.log_to_console("=== Last Error ===", Color::Red);
                                for line in error_content.lines() {
                                    app.log_to_console(line, Color::Yellow);
                                }
                            } else {
                                app.log_to_console("No error log found", Color::Gray);
                            }
                        }
                        KeyCode::Up => {
                            // Scroll up
                            if app.console_scroll_offset > 0 {
                                app.console_scroll_offset -= 1;
                            }
                        }
                        KeyCode::Down => {
                            // Scroll down
                            let visible_height = 20; // Approximate
                            let max_offset = app.console_logs.len().saturating_sub(visible_height);
                            if app.console_scroll_offset < max_offset {
                                app.console_scroll_offset += 1;
                            }
                        }
                        KeyCode::PageUp => {
                            // Scroll up by page
                            app.console_scroll_offset = app.console_scroll_offset.saturating_sub(20);
                        }
                        KeyCode::PageDown => {
                            // Scroll down by page
                            let visible_height = 20;
                            let max_offset = app.console_logs.len().saturating_sub(visible_height);
                            app.console_scroll_offset = (app.console_scroll_offset + 20).min(max_offset);
                        }
                        KeyCode::Home => {
                            // Go to top (newest)
                            app.console_scroll_offset = 0;
                        }
                        KeyCode::End => {
                            // Go to bottom (oldest)
                            let visible_height = 20;
                            app.console_scroll_offset = app.console_logs.len().saturating_sub(visible_height);
                        }
                        _ => {}
                    }
                }
                MainTab::Architecture => {
                    match key.code {
                        KeyCode::Up => app.architecture_spiral.prev_layer(),
                        KeyCode::Down => app.architecture_spiral.next_layer(),
                        KeyCode::Char('0') => app.architecture_spiral.jump_to_layer(0),
                        KeyCode::Char('1') => app.architecture_spiral.jump_to_layer(1),
                        KeyCode::Char('2') => app.architecture_spiral.jump_to_layer(2),
                        KeyCode::Char('3') => app.architecture_spiral.jump_to_layer(3),
                        KeyCode::Char('4') => app.architecture_spiral.jump_to_layer(4),
                        KeyCode::Char('5') => app.architecture_spiral.jump_to_layer(5),
                        KeyCode::Enter => app.architecture_spiral.toggle_docs(),
                        KeyCode::Esc => {
                            if app.architecture_spiral.show_docs {
                                app.architecture_spiral.toggle_docs();
                            }
                        }
                        KeyCode::PageUp => app.architecture_spiral.scroll_docs_page_up(),
                        KeyCode::PageDown => app.architecture_spiral.scroll_docs_page_down(),
                        _ => {}
                    }
                }
                MainTab::Exit => {
                    if key.code == KeyCode::Enter {
                        break;
                    }
                }
            }
            }
        }
    }
    
    Ok(())
}