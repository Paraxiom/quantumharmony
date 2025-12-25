//! TUI Wallet Menu Implementations
//! 
//! This module contains the implementation for each menu option in the TUI wallet

use super::{App, Account, MenuItem, COHR, format_cohr};
use tui::{
    backend::Backend,
    layout::{Alignment, Constraint, Direction, Layout, Rect},
    style::{Color, Modifier, Style},
    text::{Span, Spans},
    widgets::{Block, BorderType, Borders, List, ListItem, Paragraph, Wrap, Gauge},
    Frame,
};
use std::error::Error;

impl App {
    /// Render the Accounts menu
    pub fn render_accounts_menu<B: Backend>(&self, f: &mut Frame<B>, area: Rect) {
        let chunks = Layout::default()
            .direction(Direction::Vertical)
            .constraints([
                Constraint::Length(3),  // Title
                Constraint::Length(10), // Account info
                Constraint::Min(5),     // Actions
                Constraint::Length(3),  // Help
            ])
            .split(area);
        
        // Title
        let title = Paragraph::new(vec![
            Spans::from(vec![
                Span::styled("💰 ", Style::default().fg(Color::Yellow)),
                Span::styled("ACCOUNTS & BALANCES", Style::default().fg(Color::White).add_modifier(Modifier::BOLD)),
            ]),
        ])
        .alignment(Alignment::Center)
        .block(Block::default().borders(Borders::BOTTOM));
        
        f.render_widget(title, chunks[0]);
        
        // Account information
        if let Some(account) = &self.account {
            let account_info = vec![
                Spans::from(""),
                Spans::from(vec![
                    Span::raw("Address: "),
                    Span::styled(&account.address, Style::default().fg(Color::Cyan)),
                ]),
                Spans::from(""),
                Spans::from(vec![
                    Span::raw("Balance: "),
                    Span::styled(&account.balance_cohr, Style::default().fg(Color::Green).add_modifier(Modifier::BOLD)),
                ]),
                Spans::from(vec![
                    Span::raw("Staked: "),
                    Span::styled(&account.staked_cohr, Style::default().fg(Color::Yellow)),
                ]),
                Spans::from(""),
                Spans::from(vec![
                    Span::raw("Validator: "),
                    Span::styled(
                        if account.is_validator { "Yes ✓" } else { "No ✗" },
                        Style::default().fg(if account.is_validator { Color::Green } else { Color::Gray })
                    ),
                ]),
            ];
            
            let account_widget = Paragraph::new(account_info)
                .block(Block::default().borders(Borders::ALL).border_type(BorderType::Rounded));
            
            f.render_widget(account_widget, chunks[1]);
        } else {
            let no_account = Paragraph::new(vec![
                Spans::from(""),
                Spans::from("No account loaded"),
                Spans::from(""),
                Spans::from("Press [N] to create a new account"),
                Spans::from("Press [I] to import an existing account"),
            ])
            .alignment(Alignment::Center)
            .block(Block::default().borders(Borders::ALL).border_type(BorderType::Rounded));
            
            f.render_widget(no_account, chunks[1]);
        }
        
        // Actions
        let actions = vec![
            Spans::from(vec![
                Span::styled("[T] ", Style::default().fg(Color::Cyan)),
                Span::raw("Transfer COHR"),
            ]),
            Spans::from(vec![
                Span::styled("[S] ", Style::default().fg(Color::Cyan)),
                Span::raw("Stake COHR"),
            ]),
            Spans::from(vec![
                Span::styled("[F] ", Style::default().fg(Color::Cyan)),
                Span::raw("Request from Faucet"),
                Span::styled(" (Testnet only)", Style::default().fg(Color::Gray)),
            ]),
            Spans::from(vec![
                Span::styled("[E] ", Style::default().fg(Color::Cyan)),
                Span::raw("Export Account"),
            ]),
            Spans::from(vec![
                Span::styled("[B] ", Style::default().fg(Color::Yellow)),
                Span::raw("Back to Main Menu"),
            ]),
        ];
        
        let actions_widget = Paragraph::new(actions)
            .block(Block::default().borders(Borders::ALL).title(" Actions "));
        
        f.render_widget(actions_widget, chunks[2]);
    }
    
    /// Render the Keys menu
    pub fn render_keys_menu<B: Backend>(&self, f: &mut Frame<B>, area: Rect) {
        let chunks = Layout::default()
            .direction(Direction::Vertical)
            .constraints([
                Constraint::Length(3),  // Title
                Constraint::Min(10),    // Key list
                Constraint::Length(5),  // Actions
            ])
            .split(area);
        
        // Title
        let title = Paragraph::new(vec![
            Spans::from(vec![
                Span::styled("🔑 ", Style::default().fg(Color::Yellow)),
                Span::styled("KEY MANAGEMENT", Style::default().fg(Color::White).add_modifier(Modifier::BOLD)),
            ]),
        ])
        .alignment(Alignment::Center)
        .block(Block::default().borders(Borders::BOTTOM));
        
        f.render_widget(title, chunks[0]);
        
        // Key types
        let keys = vec![
            ListItem::new(Spans::from(vec![
                Span::styled("Session Keys", Style::default().fg(Color::White).add_modifier(Modifier::BOLD)),
            ])),
            ListItem::new(Spans::from(vec![
                Span::raw("  • "),
                Span::styled("BABE", Style::default().fg(Color::Green)),
                Span::raw(" - Block production"),
            ])),
            ListItem::new(Spans::from(vec![
                Span::raw("  • "),
                Span::styled("GRANDPA", Style::default().fg(Color::Green)),
                Span::raw(" - Finality"),
            ])),
            ListItem::new(Spans::from(vec![
                Span::raw("  • "),
                Span::styled("ImOnline", Style::default().fg(Color::Green)),
                Span::raw(" - Liveness"),
            ])),
            ListItem::new(Spans::from(vec![
                Span::raw("  • "),
                Span::styled("AuthorityDiscovery", Style::default().fg(Color::Green)),
                Span::raw(" - P2P discovery"),
            ])),
            ListItem::new(Spans::from("")),
            ListItem::new(Spans::from(vec![
                Span::styled("Quantum Keys", Style::default().fg(Color::White).add_modifier(Modifier::BOLD)),
            ])),
            ListItem::new(Spans::from(vec![
                Span::raw("  • "),
                Span::styled("QKD Key", Style::default().fg(Color::Yellow)),
                Span::raw(" - Not configured"),
            ])),
            ListItem::new(Spans::from(vec![
                Span::raw("  • "),
                Span::styled("Lamport Signature", Style::default().fg(Color::Yellow)),
                Span::raw(" - Ready"),
            ])),
        ];
        
        let keys_list = List::new(keys)
            .block(Block::default().borders(Borders::ALL).title(" Keys "));
        
        f.render_widget(keys_list, chunks[1]);
        
        // Actions
        let actions = vec![
            Spans::from(vec![
                Span::styled("[R] ", Style::default().fg(Color::Cyan)),
                Span::raw("Rotate Session Keys"),
            ]),
            Spans::from(vec![
                Span::styled("[G] ", Style::default().fg(Color::Cyan)),
                Span::raw("Generate Quantum Keys"),
            ]),
            Spans::from(vec![
                Span::styled("[B] ", Style::default().fg(Color::Yellow)),
                Span::raw("Back to Main Menu"),
            ]),
        ];
        
        let actions_widget = Paragraph::new(actions)
            .block(Block::default().borders(Borders::TOP));
        
        f.render_widget(actions_widget, chunks[2]);
    }
    
    /// Render the Network menu
    pub fn render_network_menu<B: Backend>(&self, f: &mut Frame<B>, area: Rect) {
        let chunks = Layout::default()
            .direction(Direction::Vertical)
            .constraints([
                Constraint::Length(3),   // Title
                Constraint::Length(8),   // Network stats
                Constraint::Length(10),  // Peer list
                Constraint::Min(5),      // Actions
            ])
            .split(area);
        
        // Title
        let title = Paragraph::new(vec![
            Spans::from(vec![
                Span::styled("🌐 ", Style::default().fg(Color::Blue)),
                Span::styled("NETWORK OVERVIEW", Style::default().fg(Color::White).add_modifier(Modifier::BOLD)),
            ]),
        ])
        .alignment(Alignment::Center)
        .block(Block::default().borders(Borders::BOTTOM));
        
        f.render_widget(title, chunks[0]);
        
        // Network statistics
        let stats = vec![
            Spans::from(vec![
                Span::raw("Block Height: "),
                Span::styled(
                    format!("#{}", self.node_status.block_number),
                    Style::default().fg(Color::Cyan).add_modifier(Modifier::BOLD)
                ),
            ]),
            Spans::from(vec![
                Span::raw("Network: "),
                Span::styled(&self.network_config.chain_id, Style::default().fg(Color::Green)),
            ]),
            Spans::from(vec![
                Span::raw("Peers: "),
                Span::styled(
                    format!("{}", self.node_status.peers),
                    Style::default().fg(if self.node_status.peers > 0 { Color::Green } else { Color::Red })
                ),
            ]),
            Spans::from(vec![
                Span::raw("Sync Status: "),
                Span::styled(
                    if self.node_status.synced { "Synced ✓" } else { "Syncing..." },
                    Style::default().fg(if self.node_status.synced { Color::Green } else { Color::Yellow })
                ),
            ]),
            Spans::from(vec![
                Span::raw("TPS: "),
                Span::styled(format!("{}", self.metrics.tps), Style::default().fg(Color::White)),
            ]),
        ];
        
        let stats_widget = Paragraph::new(stats)
            .block(Block::default().borders(Borders::ALL).title(" Network Status "));
        
        f.render_widget(stats_widget, chunks[1]);
        
        // Peer information
        let peer_info = if self.node_status.peers > 0 {
            vec![
                Spans::from(vec![
                    Span::styled("Connected Peers:", Style::default().fg(Color::White).add_modifier(Modifier::BOLD)),
                ]),
                Spans::from(""),
                Spans::from(vec![
                    Span::raw("• "),
                    Span::styled("Alice", Style::default().fg(Color::Green)),
                    Span::raw(" - Validator"),
                ]),
                Spans::from(vec![
                    Span::raw("• "),
                    Span::styled("Bob", Style::default().fg(Color::Green)),
                    Span::raw(" - Full Node"),
                ]),
                Spans::from(vec![
                    Span::raw("• "),
                    Span::styled("Charlie", Style::default().fg(Color::Green)),
                    Span::raw(" - Light Client"),
                ]),
            ]
        } else {
            vec![
                Spans::from(""),
                Spans::from(vec![
                    Span::styled("No peers connected", Style::default().fg(Color::Red)),
                ]),
                Spans::from(""),
                Spans::from(vec![
                    Span::raw("Waiting for connections..."),
                ]),
            ]
        };
        
        let peers_widget = Paragraph::new(peer_info)
            .block(Block::default().borders(Borders::ALL).title(" Peers "));
        
        f.render_widget(peers_widget, chunks[2]);
        
        // Actions
        let actions = vec![
            Spans::from(vec![
                Span::styled("[A] ", Style::default().fg(Color::Cyan)),
                Span::raw("Add Custom Bootnode"),
            ]),
            Spans::from(vec![
                Span::styled("[R] ", Style::default().fg(Color::Cyan)),
                Span::raw("Refresh Network Status"),
            ]),
            Spans::from(vec![
                Span::styled("[B] ", Style::default().fg(Color::Yellow)),
                Span::raw("Back to Main Menu"),
            ]),
        ];
        
        let actions_widget = Paragraph::new(actions)
            .block(Block::default().borders(Borders::TOP));
        
        f.render_widget(actions_widget, chunks[3]);
    }
    
    /// Render the Quantum menu
    pub fn render_quantum_menu<B: Backend>(&self, f: &mut Frame<B>, area: Rect) {
        let chunks = Layout::default()
            .direction(Direction::Vertical)
            .constraints([
                Constraint::Length(3),   // Title
                Constraint::Length(10),  // Quantum features status
                Constraint::Min(10),     // Entropy display
                Constraint::Length(5),   // Actions
            ])
            .split(area);
        
        // Title
        let title = Paragraph::new(vec![
            Spans::from(vec![
                Span::styled("🔮 ", Style::default().fg(Color::Magenta)),
                Span::styled("QUANTUM FEATURES", Style::default().fg(Color::White).add_modifier(Modifier::BOLD)),
            ]),
        ])
        .alignment(Alignment::Center)
        .block(Block::default().borders(Borders::BOTTOM));
        
        f.render_widget(title, chunks[0]);
        
        // Quantum status
        let quantum_status = vec![
            Spans::from(vec![
                Span::styled("Quantum Hardware:", Style::default().fg(Color::White).add_modifier(Modifier::BOLD)),
            ]),
            Spans::from(vec![
                Span::raw("  Type: "),
                Span::styled("QRNG (Simulated)", Style::default().fg(Color::Yellow)),
            ]),
            Spans::from(vec![
                Span::raw("  Status: "),
                Span::styled("Active", Style::default().fg(Color::Green)),
            ]),
            Spans::from(""),
            Spans::from(vec![
                Span::styled("Features:", Style::default().fg(Color::White).add_modifier(Modifier::BOLD)),
            ]),
            Spans::from(vec![
                Span::raw("  • QKD: "),
                Span::styled("Disabled", Style::default().fg(Color::Gray)),
            ]),
            Spans::from(vec![
                Span::raw("  • QRNG: "),
                Span::styled("Enabled", Style::default().fg(Color::Green)),
            ]),
            Spans::from(vec![
                Span::raw("  • Post-Quantum Crypto: "),
                Span::styled("Active", Style::default().fg(Color::Green)),
            ]),
        ];
        
        let status_widget = Paragraph::new(quantum_status)
            .block(Block::default().borders(Borders::ALL).title(" Status "));
        
        f.render_widget(status_widget, chunks[1]);
        
        // Entropy display
        let entropy_display = vec![
            Spans::from(vec![
                Span::styled("Current Entropy:", Style::default().fg(Color::White).add_modifier(Modifier::BOLD)),
            ]),
            Spans::from(""),
            Spans::from(vec![
                Span::styled(
                    "0x4f2d8a9c7e3b1f6d9a8c5e2b7f4d1a9c...",
                    Style::default().fg(Color::Cyan)
                ),
            ]),
            Spans::from(""),
            Spans::from(vec![
                Span::raw("Entropy Pool: "),
                Span::styled("87%", Style::default().fg(Color::Green)),
            ]),
        ];
        
        let entropy_widget = Paragraph::new(entropy_display)
            .block(Block::default().borders(Borders::ALL).title(" Quantum Entropy "));
        
        f.render_widget(entropy_widget, chunks[2]);
        
        // Actions
        let actions = vec![
            Spans::from(vec![
                Span::styled("[G] ", Style::default().fg(Color::Cyan)),
                Span::raw("Generate New Entropy"),
            ]),
            Spans::from(vec![
                Span::styled("[Q] ", Style::default().fg(Color::Cyan)),
                Span::raw("Initiate QKD Session"),
            ]),
            Spans::from(vec![
                Span::styled("[T] ", Style::default().fg(Color::Cyan)),
                Span::raw("Test Quantum Features"),
            ]),
            Spans::from(vec![
                Span::styled("[B] ", Style::default().fg(Color::Yellow)),
                Span::raw("Back to Main Menu"),
            ]),
        ];
        
        let actions_widget = Paragraph::new(actions)
            .block(Block::default().borders(Borders::TOP));
        
        f.render_widget(actions_widget, chunks[3]);
    }
    
    /// Render the Governance menu
    pub fn render_governance_menu<B: Backend>(&self, f: &mut Frame<B>, area: Rect) {
        let chunks = Layout::default()
            .direction(Direction::Vertical)
            .constraints([
                Constraint::Length(3),   // Title
                Constraint::Length(10),  // Active proposals
                Constraint::Min(5),      // Voting power
                Constraint::Length(5),   // Actions
            ])
            .split(area);
        
        // Title
        let title = Paragraph::new(vec![
            Spans::from(vec![
                Span::styled("🏛️ ", Style::default().fg(Color::Blue)),
                Span::styled("GOVERNANCE", Style::default().fg(Color::White).add_modifier(Modifier::BOLD)),
            ]),
        ])
        .alignment(Alignment::Center)
        .block(Block::default().borders(Borders::BOTTOM));
        
        f.render_widget(title, chunks[0]);
        
        // Active proposals
        let proposals = vec![
            Spans::from(vec![
                Span::styled("Active Proposals:", Style::default().fg(Color::White).add_modifier(Modifier::BOLD)),
            ]),
            Spans::from(""),
            Spans::from(vec![
                Span::styled("#1 ", Style::default().fg(Color::Cyan)),
                Span::raw("Increase Validator Set to 100"),
            ]),
            Spans::from(vec![
                Span::raw("   Status: "),
                Span::styled("Voting", Style::default().fg(Color::Yellow)),
                Span::raw(" | Ends in: "),
                Span::styled("2 days", Style::default().fg(Color::Gray)),
            ]),
            Spans::from(""),
            Spans::from(vec![
                Span::styled("#2 ", Style::default().fg(Color::Cyan)),
                Span::raw("Enable Quantum Staking Rewards"),
            ]),
            Spans::from(vec![
                Span::raw("   Status: "),
                Span::styled("Passed", Style::default().fg(Color::Green)),
                Span::raw(" | Executing in: "),
                Span::styled("12 hours", Style::default().fg(Color::Gray)),
            ]),
        ];
        
        let proposals_widget = Paragraph::new(proposals)
            .block(Block::default().borders(Borders::ALL).title(" Proposals "));
        
        f.render_widget(proposals_widget, chunks[1]);
        
        // Voting power
        let voting_power = if let Some(account) = &self.account {
            let voting_cohr = account.balance + account.staked_amount;
            vec![
                Spans::from(vec![
                    Span::styled("Your Voting Power:", Style::default().fg(Color::White).add_modifier(Modifier::BOLD)),
                ]),
                Spans::from(""),
                Spans::from(vec![
                    Span::raw("Available: "),
                    Span::styled(format_cohr(voting_cohr), Style::default().fg(Color::Green)),
                ]),
                Spans::from(vec![
                    Span::raw("Delegated: "),
                    Span::styled("0 COHR", Style::default().fg(Color::Gray)),
                ]),
            ]
        } else {
            vec![
                Spans::from(""),
                Spans::from(vec![
                    Span::styled("No account loaded", Style::default().fg(Color::Red)),
                ]),
                Spans::from(vec![
                    Span::raw("Create an account to participate in governance"),
                ]),
            ]
        };
        
        let voting_widget = Paragraph::new(voting_power)
            .block(Block::default().borders(Borders::ALL).title(" Voting Power "));
        
        f.render_widget(voting_widget, chunks[2]);
        
        // Actions
        let actions = vec![
            Spans::from(vec![
                Span::styled("[V] ", Style::default().fg(Color::Cyan)),
                Span::raw("Vote on Proposal"),
            ]),
            Spans::from(vec![
                Span::styled("[P] ", Style::default().fg(Color::Cyan)),
                Span::raw("Create New Proposal"),
            ]),
            Spans::from(vec![
                Span::styled("[D] ", Style::default().fg(Color::Cyan)),
                Span::raw("Delegate Voting Power"),
            ]),
            Spans::from(vec![
                Span::styled("[B] ", Style::default().fg(Color::Yellow)),
                Span::raw("Back to Main Menu"),
            ]),
        ];
        
        let actions_widget = Paragraph::new(actions)
            .block(Block::default().borders(Borders::TOP));
        
        f.render_widget(actions_widget, chunks[3]);
    }
    
    /// Render the Settings menu
    pub fn render_settings_menu<B: Backend>(&self, f: &mut Frame<B>, area: Rect) {
        let chunks = Layout::default()
            .direction(Direction::Vertical)
            .constraints([
                Constraint::Length(3),   // Title
                Constraint::Length(10),  // Connection settings
                Constraint::Min(10),     // Node control
                Constraint::Length(6),   // Actions
            ])
            .split(area);
        
        // Title
        let title = Paragraph::new(vec![
            Spans::from(vec![
                Span::styled("⚙️ ", Style::default().fg(Color::Gray)),
                Span::styled("SETTINGS", Style::default().fg(Color::White).add_modifier(Modifier::BOLD)),
            ]),
        ])
        .alignment(Alignment::Center)
        .block(Block::default().borders(Borders::BOTTOM));
        
        f.render_widget(title, chunks[0]);
        
        // Connection settings
        let endpoint = self.network_config.get_endpoint()
            .unwrap_or_else(|| "P2P Mode");
        
        let settings = vec![
            Spans::from(vec![
                Span::styled("Connection Settings:", Style::default().fg(Color::White).add_modifier(Modifier::BOLD)),
            ]),
            Spans::from(""),
            Spans::from(vec![
                Span::raw("Network: "),
                Span::styled(&self.network_config.chain_id, Style::default().fg(Color::Cyan)),
            ]),
            Spans::from(vec![
                Span::raw("Endpoint: "),
                Span::styled(endpoint, Style::default().fg(Color::Green)),
            ]),
            Spans::from(vec![
                Span::raw("Mode: "),
                Span::styled(
                    match &self.network_config.mode {
                        crate::wallet_modes::WalletMode::Development { .. } => "Development",
                        crate::wallet_modes::WalletMode::Testnet { .. } => "Testnet",
                        crate::wallet_modes::WalletMode::MainnetUser { .. } => "Mainnet User",
                        crate::wallet_modes::WalletMode::MainnetValidator { .. } => "Mainnet Validator",
                        crate::wallet_modes::WalletMode::QuantumNode { .. } => "Quantum Node",
                        crate::wallet_modes::WalletMode::Enterprise { .. } => "Enterprise",
                    },
                    Style::default().fg(Color::Yellow)
                ),
            ]),
        ];
        
        let settings_widget = Paragraph::new(settings)
            .block(Block::default().borders(Borders::ALL).title(" Configuration "));
        
        f.render_widget(settings_widget, chunks[1]);
        
        // Node control
        let node_control = vec![
            Spans::from(vec![
                Span::styled("Node Control:", Style::default().fg(Color::White).add_modifier(Modifier::BOLD)),
            ]),
            Spans::from(""),
            Spans::from(vec![
                Span::raw("Status: "),
                Span::styled(
                    if self.node_process.is_some() { "Running" } else { "Stopped" },
                    Style::default().fg(if self.node_process.is_some() { Color::Green } else { Color::Red })
                ),
            ]),
            Spans::from(""),
            Spans::from(vec![
                Span::styled("[S] ", Style::default().fg(Color::Green)),
                Span::raw("Graceful Shutdown"),
            ]),
            Spans::from(vec![
                Span::styled("[R] ", Style::default().fg(Color::Yellow)),
                Span::raw("Restart Node"),
            ]),
            Spans::from(vec![
                Span::styled("[E] ", Style::default().fg(Color::Red)),
                Span::raw("Emergency Shutdown (Force Kill)"),
            ]),
        ];
        
        let control_widget = Paragraph::new(node_control)
            .block(Block::default().borders(Borders::ALL).title(" Node Management "));
        
        f.render_widget(control_widget, chunks[2]);
        
        // Actions
        let actions = vec![
            Spans::from(vec![
                Span::styled("[C] ", Style::default().fg(Color::Cyan)),
                Span::raw("Change Network"),
            ]),
            Spans::from(vec![
                Span::styled("[L] ", Style::default().fg(Color::Cyan)),
                Span::raw("View Logs"),
            ]),
            Spans::from(vec![
                Span::styled("[X] ", Style::default().fg(Color::Cyan)),
                Span::raw("Export Configuration"),
            ]),
            Spans::from(vec![
                Span::styled("[B] ", Style::default().fg(Color::Yellow)),
                Span::raw("Back to Main Menu"),
            ]),
        ];
        
        let actions_widget = Paragraph::new(actions)
            .block(Block::default().borders(Borders::TOP));
        
        f.render_widget(actions_widget, chunks[3]);
    }
}

/// Helper function to render a transaction dialog
pub fn render_transaction_dialog<B: Backend>(f: &mut Frame<B>, area: Rect) {
    let block = Block::default()
        .borders(Borders::ALL)
        .border_type(BorderType::Double)
        .border_style(Style::default().fg(Color::Cyan))
        .title(" Send Transaction ");
    
    let chunks = Layout::default()
        .direction(Direction::Vertical)
        .margin(2)
        .constraints([
            Constraint::Length(3),  // Recipient
            Constraint::Length(3),  // Amount
            Constraint::Length(3),  // Fee estimate
            Constraint::Min(2),     // Actions
        ])
        .split(area);
    
    let content = vec![
        Spans::from(vec![
            Span::raw("Recipient: "),
            Span::styled("[Enter address]", Style::default().fg(Color::Gray)),
        ]),
    ];
    
    let dialog = Paragraph::new(content)
        .block(block);
    
    f.render_widget(dialog, area);
}

/// Helper function to render a staking dialog
pub fn render_staking_dialog<B: Backend>(f: &mut Frame<B>, area: Rect, current_stake: u128) {
    let block = Block::default()
        .borders(Borders::ALL)
        .border_type(BorderType::Double)
        .border_style(Style::default().fg(Color::Yellow))
        .title(" Staking ");
    
    let content = vec![
        Spans::from(""),
        Spans::from(vec![
            Span::raw("Current Stake: "),
            Span::styled(format_cohr(current_stake), Style::default().fg(Color::Green)),
        ]),
        Spans::from(""),
        Spans::from(vec![
            Span::raw("Amount to Stake: "),
            Span::styled("[Enter amount]", Style::default().fg(Color::Gray)),
        ]),
        Spans::from(""),
        Spans::from(vec![
            Span::styled("[S] ", Style::default().fg(Color::Green)),
            Span::raw("Stake"),
            Span::raw("  "),
            Span::styled("[U] ", Style::default().fg(Color::Yellow)),
            Span::raw("Unstake"),
            Span::raw("  "),
            Span::styled("[ESC] ", Style::default().fg(Color::Red)),
            Span::raw("Cancel"),
        ]),
    ];
    
    let dialog = Paragraph::new(content)
        .block(block)
        .alignment(Alignment::Center);
    
    f.render_widget(dialog, area);
}