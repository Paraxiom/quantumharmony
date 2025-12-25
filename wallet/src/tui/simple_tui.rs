//! Simple, clean TUI wallet focused on local network interaction

use crossterm::{
    event::{self, DisableMouseCapture, EnableMouseCapture, Event, KeyCode, KeyModifiers},
    execute,
    terminal::{disable_raw_mode, enable_raw_mode, EnterAlternateScreen, LeaveAlternateScreen},
};
use ratatui::{
    backend::{Backend, CrosstermBackend},
    layout::{Alignment, Constraint, Direction, Layout, Rect},
    style::{Color, Modifier, Style},
    text::{Line, Span},
    widgets::{Block, Borders, List, ListItem, Paragraph, Tabs, Wrap},
    Frame, Terminal,
};
use std::io;
use log::{info, error};
use sp_core::{sr25519, Pair, crypto::Ss58Codec};
use jsonrpsee::ws_client::{WsClientBuilder, WsClient};
use jsonrpsee::core::client::ClientT;
use jsonrpsee::rpc_params;

/// Tab indices
#[derive(Debug, Clone, Copy, PartialEq)]
enum Tab {
    Accounts = 0,
    Send = 1,
    Network = 2,
    Config = 3,
    Exit = 4,
}

impl Tab {
    fn all() -> Vec<(&'static str, Tab)> {
        vec![
            ("Accounts", Tab::Accounts),
            ("Send", Tab::Send),
            ("Network", Tab::Network),
            ("Config", Tab::Config),
            ("Exit", Tab::Exit),
        ]
    }
    
    fn next(self) -> Self {
        match self {
            Tab::Accounts => Tab::Send,
            Tab::Send => Tab::Network,
            Tab::Network => Tab::Config,
            Tab::Config => Tab::Exit,
            Tab::Exit => Tab::Accounts,
        }
    }
    
    fn prev(self) -> Self {
        match self {
            Tab::Accounts => Tab::Exit,
            Tab::Send => Tab::Accounts,
            Tab::Network => Tab::Send,
            Tab::Config => Tab::Network,
            Tab::Exit => Tab::Config,
        }
    }
}

/// Account info
#[derive(Debug, Clone)]
struct Account {
    name: String,
    address: String,
    balance: String,
}

/// App state
pub struct App {
    current_tab: Tab,
    accounts: Vec<Account>,
    selected_account: usize,
    network_endpoint: String,
    ws_client: Option<WsClient>,
    connection_status: String,
    error_message: Option<String>,
    should_quit: bool,
}

impl App {
    pub fn new() -> Self {
        Self {
            current_tab: Tab::Accounts,
            accounts: vec![],
            selected_account: 0,
            network_endpoint: "ws://localhost:9944".to_string(),
            ws_client: None,
            connection_status: "Not connected".to_string(),
            error_message: None,
            should_quit: false,
        }
    }
    
    async fn connect_to_network(&mut self) {
        self.connection_status = "Connecting...".to_string();
        
        match WsClientBuilder::default()
            .build(&self.network_endpoint)
            .await 
        {
            Ok(client) => {
                self.ws_client = Some(client);
                self.connection_status = format!("Connected to {}", self.network_endpoint);
                self.error_message = None;
                info!("Connected to network at {}", self.network_endpoint);
            }
            Err(e) => {
                self.connection_status = "Connection failed".to_string();
                self.error_message = Some(format!("Failed to connect: {}", e));
                error!("Connection failed: {}", e);
            }
        }
    }
    
    async fn create_account(&mut self) {
        let (pair, phrase, _) = sr25519::Pair::generate_with_phrase(None);
        let address = pair.public().to_ss58check();
        
        let account_num = self.accounts.len() + 1;
        let account = Account {
            name: format!("Account {}", account_num),
            address: address.clone(),
            balance: "0 COHR".to_string(),
        };
        
        self.accounts.push(account);
        self.selected_account = self.accounts.len() - 1;
        
        // Save mnemonic to file for demo purposes
        let filename = format!("account_{}.txt", account_num);
        if let Err(e) = std::fs::write(&filename, format!("Address: {}\nMnemonic: {}", address, phrase)) {
            self.error_message = Some(format!("Failed to save account: {}", e));
        } else {
            self.error_message = Some(format!("Account saved to {}", filename));
        }
    }
    
    async fn refresh_balances(&mut self) {
        if let Some(client) = &self.ws_client {
            for account in &mut self.accounts {
                // Query balance - simplified for demo
                match client.request::<serde_json::Value, _>("system_accountNextIndex", rpc_params![&account.address]).await {
                    Ok(_) => {
                        account.balance = "0 COHR".to_string(); // Would query actual balance
                    }
                    Err(_) => {
                        account.balance = "Error".to_string();
                    }
                }
            }
        }
    }
    
    fn handle_key(&mut self, key: KeyCode) -> bool {
        match key {
            KeyCode::Tab => {
                self.current_tab = self.current_tab.next();
                if self.current_tab == Tab::Exit {
                    self.error_message = Some("Press Enter to exit, Tab to continue".to_string());
                } else {
                    self.error_message = None;
                }
            }
            KeyCode::BackTab => {
                self.current_tab = self.current_tab.prev();
                if self.current_tab == Tab::Exit {
                    self.error_message = Some("Press Enter to exit, Tab to continue".to_string());
                } else {
                    self.error_message = None;
                }
            }
            KeyCode::Enter => {
                if self.current_tab == Tab::Exit {
                    return true; // Signal to quit
                }
            }
            KeyCode::Up => {
                if self.current_tab == Tab::Accounts && self.selected_account > 0 {
                    self.selected_account -= 1;
                }
            }
            KeyCode::Down => {
                if self.current_tab == Tab::Accounts && self.selected_account < self.accounts.len().saturating_sub(1) {
                    self.selected_account += 1;
                }
            }
            KeyCode::Char('q') => {
                self.current_tab = Tab::Exit;
                self.error_message = Some("Press Enter to exit, Tab to continue".to_string());
            }
            KeyCode::Char('c') if self.current_tab == Tab::Accounts => {
                // Create account will be handled in update
                self.should_quit = false;
            }
            KeyCode::Char('r') if self.current_tab == Tab::Network => {
                // Reconnect will be handled in update
                self.should_quit = false;
            }
            _ => {}
        }
        false
    }
}

/// Main UI render function
fn ui(f: &mut Frame, app: &App) {
    let chunks = Layout::default()
        .direction(Direction::Vertical)
        .margin(1)
        .constraints([
            Constraint::Length(3),  // Title
            Constraint::Length(3),  // Tabs
            Constraint::Min(0),     // Content
            Constraint::Length(3),  // Status bar
        ])
        .split(f.size());
    
    // Title
    let title = Paragraph::new("Drista Wallet - Local Network")
        .style(Style::default().fg(Color::Cyan).add_modifier(Modifier::BOLD))
        .alignment(Alignment::Center)
        .block(Block::default().borders(Borders::ALL));
    f.render_widget(title, chunks[0]);
    
    // Tabs
    let tab_titles: Vec<&str> = Tab::all().iter().map(|(title, _)| *title).collect();
    let current_tab_title = tab_titles[app.current_tab as usize];
    let tabs = Tabs::new(tab_titles)
        .block(Block::default().borders(Borders::ALL))
        .select(app.current_tab as usize)
        .style(Style::default().fg(Color::White))
        .highlight_style(Style::default().fg(Color::Yellow).add_modifier(Modifier::BOLD));
    f.render_widget(tabs, chunks[1]);
    
    // Content area
    let content_block = Block::default()
        .borders(Borders::ALL)
        .title(format!(" {} ", current_tab_title));
    
    match app.current_tab {
        Tab::Accounts => render_accounts(f, app, chunks[2], content_block),
        Tab::Send => render_send(f, app, chunks[2], content_block),
        Tab::Network => render_network(f, app, chunks[2], content_block),
        Tab::Config => render_config(f, app, chunks[2], content_block),
        Tab::Exit => render_exit(f, chunks[2], content_block),
    }
    
    // Status bar
    let status_text = if let Some(error) = &app.error_message {
        format!(" {} | {}", app.connection_status, error)
    } else {
        format!(" {} | Tab: navigate | Enter: select | q: exit", app.connection_status)
    };
    
    let status_color = if app.error_message.is_some() {
        Color::Red
    } else if app.ws_client.is_some() {
        Color::Green
    } else {
        Color::Yellow
    };
    
    let status = Paragraph::new(status_text)
        .style(Style::default().fg(status_color))
        .block(Block::default().borders(Borders::ALL));
    f.render_widget(status, chunks[3]);
}

fn render_accounts(f: &mut Frame, app: &App, area: Rect, block: Block) {
    let chunks = Layout::default()
        .direction(Direction::Vertical)
        .constraints([Constraint::Min(0), Constraint::Length(3)])
        .split(area);
    
    // Account list
    let accounts: Vec<ListItem> = app.accounts
        .iter()
        .enumerate()
        .map(|(i, acc)| {
            let style = if i == app.selected_account {
                Style::default().fg(Color::Yellow).add_modifier(Modifier::BOLD)
            } else {
                Style::default()
            };
            ListItem::new(format!("{}: {} - {}", acc.name, acc.address, acc.balance))
                .style(style)
        })
        .collect();
    
    let accounts_list = if accounts.is_empty() {
        List::new(vec![ListItem::new("No accounts yet. Press 'c' to create one.")])
    } else {
        List::new(accounts)
    };
    
    f.render_widget(accounts_list.block(block), chunks[0]);
    
    // Help text
    let help = Paragraph::new(" c: create account | ↑↓: select | Enter: view details")
        .style(Style::default().fg(Color::DarkGray))
        .block(Block::default().borders(Borders::TOP));
    f.render_widget(help, chunks[1]);
}

fn render_send(f: &mut Frame, app: &App, area: Rect, block: Block) {
    let text = if app.accounts.is_empty() {
        vec![
            Line::from("No accounts available."),
            Line::from(""),
            Line::from("Create an account first in the Accounts tab."),
        ]
    } else if app.ws_client.is_none() {
        vec![
            Line::from("Not connected to network."),
            Line::from(""),
            Line::from("Connect to the network in the Network tab."),
        ]
    } else {
        vec![
            Line::from("Send COHR tokens"),
            Line::from(""),
            Line::from("Feature coming soon..."),
            Line::from(""),
            Line::from("This will allow you to:"),
            Line::from("- Select source account"),
            Line::from("- Enter recipient address"),
            Line::from("- Specify amount"),
            Line::from("- Sign and submit transaction"),
        ]
    };
    
    let paragraph = Paragraph::new(text)
        .block(block)
        .wrap(Wrap { trim: true });
    f.render_widget(paragraph, area);
}

fn render_network(f: &mut Frame, app: &App, area: Rect, block: Block) {
    let network_info = vec![
        Line::from(vec![
            Span::raw("Endpoint: "),
            Span::styled(&app.network_endpoint, Style::default().fg(Color::Cyan)),
        ]),
        Line::from(""),
        Line::from(vec![
            Span::raw("Status: "),
            Span::styled(
                &app.connection_status,
                Style::default().fg(if app.ws_client.is_some() { Color::Green } else { Color::Yellow }),
            ),
        ]),
        Line::from(""),
        Line::from("Available nodes:"),
        Line::from("  • Alice: ws://localhost:9944"),
        Line::from("  • Bob:   ws://localhost:9945"),
        Line::from("  • Charlie: ws://localhost:9946"),
        Line::from("  • Dave:  ws://localhost:9947"),
        Line::from(""),
        Line::from(vec![
            Span::raw("Press "),
            Span::styled("'r'", Style::default().fg(Color::Yellow)),
            Span::raw(" to reconnect"),
        ]),
    ];
    
    let paragraph = Paragraph::new(network_info)
        .block(block)
        .wrap(Wrap { trim: true });
    f.render_widget(paragraph, area);
}

fn render_config(f: &mut Frame, _app: &App, area: Rect, block: Block) {
    let config_text = vec![
        Line::from("Configuration"),
        Line::from(""),
        Line::from("Settings:"),
        Line::from("  • Network: Local testnet"),
        Line::from("  • Chain: Quantum Harmony"),
        Line::from("  • Token: COHR"),
        Line::from("  • SS58 Prefix: 42"),
        Line::from(""),
        Line::from("Data directory: ~/.drista/"),
        Line::from(""),
        Line::from("Advanced settings coming soon..."),
    ];
    
    let paragraph = Paragraph::new(config_text)
        .block(block)
        .wrap(Wrap { trim: true });
    f.render_widget(paragraph, area);
}

fn render_exit(f: &mut Frame, area: Rect, block: Block) {
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
        Line::from(""),
        Line::from("Your accounts are saved locally."),
    ];
    
    let paragraph = Paragraph::new(exit_text)
        .block(block)
        .alignment(Alignment::Center)
        .wrap(Wrap { trim: true });
    f.render_widget(paragraph, area);
}

/// Main TUI entry point
pub async fn run() -> Result<(), Box<dyn std::error::Error>> {
    // Setup terminal
    enable_raw_mode()?;
    let mut stdout = io::stdout();
    execute!(stdout, EnterAlternateScreen, EnableMouseCapture)?;
    let backend = CrosstermBackend::new(stdout);
    let mut terminal = Terminal::new(backend)?;
    
    // Create app
    let mut app = App::new();
    
    // Initial connection
    app.connect_to_network().await;
    
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
    loop {
        terminal.draw(|f| ui(f, app))?;
        
        if let Event::Key(key) = event::read()? {
            // Handle Ctrl+C gracefully
            if key.code == KeyCode::Char('c') && key.modifiers.contains(KeyModifiers::CONTROL) {
                break;
            }
            
            if app.handle_key(key.code) {
                break; // User confirmed exit
            }
            
            // Handle async operations
            match (app.current_tab, key.code) {
                (Tab::Accounts, KeyCode::Char('c')) => {
                    app.create_account().await;
                }
                (Tab::Network, KeyCode::Char('r')) => {
                    app.connect_to_network().await;
                }
                (Tab::Accounts, KeyCode::Char('r')) => {
                    app.refresh_balances().await;
                }
                _ => {}
            }
        }
    }
    
    Ok(())
}