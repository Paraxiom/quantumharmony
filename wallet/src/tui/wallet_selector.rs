use crossterm::{
    event::{self, DisableMouseCapture, EnableMouseCapture, Event, KeyCode},
    execute,
    terminal::{disable_raw_mode, enable_raw_mode, EnterAlternateScreen, LeaveAlternateScreen},
};
use ratatui::{
    backend::CrosstermBackend,
    layout::{Alignment, Constraint, Direction, Layout, Rect},
    style::{Color, Modifier, Style},
    text::{Line, Span},
    widgets::{Block, Borders, List, ListItem, Paragraph},
    Frame, Terminal,
};
use std::io;

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum WalletMode {
    User,              // Regular user wallet
    NodeOperator,      // Classical node operator with staking
    QuantumOperator,   // Full quantum operator
    Exit,
}

pub struct WalletSelector {
    selected: usize,
    modes: Vec<(WalletMode, &'static str, &'static str)>,
}

impl WalletSelector {
    pub fn new() -> Self {
        Self {
            selected: 0,
            modes: vec![
                (
                    WalletMode::User,
                    "User Wallet",
                    "Regular wallet for transfers, balance checks, and basic operations"
                ),
                (
                    WalletMode::NodeOperator,
                    "Node Operator (Classical)",
                    "Run a validator node with staking capabilities and network monitoring"
                ),
                (
                    WalletMode::QuantumOperator,
                    "Quantum Operator (Full)",
                    "Operate quantum infrastructure with QKD, QRNG, and enhanced rewards"
                ),
                (
                    WalletMode::Exit,
                    "Exit",
                    "Exit the wallet"
                ),
            ],
        }
    }
    
    pub async fn run() -> Result<WalletMode, Box<dyn std::error::Error>> {
        // Setup terminal
        enable_raw_mode()?;
        let mut stdout = io::stdout();
        execute!(stdout, EnterAlternateScreen, EnableMouseCapture)?;
        let backend = CrosstermBackend::new(stdout);
        let mut terminal = Terminal::new(backend)?;
        
        let mut selector = WalletSelector::new();
        let result = selector.select_mode(&mut terminal).await;
        
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
    
    async fn select_mode(&mut self, terminal: &mut Terminal<CrosstermBackend<io::Stdout>>) -> Result<WalletMode, Box<dyn std::error::Error>> {
        loop {
            terminal.draw(|f| self.render(f))?;
            
            if let Event::Key(key) = event::read()? {
                match key.code {
                    KeyCode::Up => {
                        if self.selected > 0 {
                            self.selected -= 1;
                        }
                    }
                    KeyCode::Down => {
                        if self.selected < self.modes.len() - 1 {
                            self.selected += 1;
                        }
                    }
                    KeyCode::Enter => {
                        return Ok(self.modes[self.selected].0);
                    }
                    KeyCode::Char('q') | KeyCode::Esc => {
                        return Ok(WalletMode::Exit);
                    }
                    _ => {}
                }
            }
        }
    }
    
    fn render(&self, f: &mut Frame) {
        let chunks = Layout::default()
            .direction(Direction::Vertical)
            .margin(2)
            .constraints([
                Constraint::Length(8),   // Header
                Constraint::Min(10),     // Mode list
                Constraint::Length(3),   // Footer
            ])
            .split(f.size());
        
        // Header
        let header = vec![
            Line::from(""),
            Line::from(vec![
                Span::styled("╔═══════════════════════════════════════╗", Style::default().fg(Color::Cyan)),
            ]),
            Line::from(vec![
                Span::styled("║     ", Style::default().fg(Color::Cyan)),
                Span::styled("DRISTA QUANTUM WALLET", Style::default().fg(Color::Yellow).add_modifier(Modifier::BOLD)),
                Span::styled("      ║", Style::default().fg(Color::Cyan)),
            ]),
            Line::from(vec![
                Span::styled("║  ", Style::default().fg(Color::Cyan)),
                Span::styled("Bridging Classical to Quantum", Style::default().fg(Color::Gray)),
                Span::styled("  ║", Style::default().fg(Color::Cyan)),
            ]),
            Line::from(vec![
                Span::styled("╚═══════════════════════════════════════╝", Style::default().fg(Color::Cyan)),
            ]),
            Line::from(""),
            Line::from("Select wallet mode:"),
        ];
        
        let header_widget = Paragraph::new(header)
            .alignment(Alignment::Center);
        f.render_widget(header_widget, chunks[0]);
        
        // Mode selection
        let items: Vec<ListItem> = self.modes.iter().enumerate().map(|(i, (mode, name, desc))| {
            let selected = i == self.selected;
            
            let content = vec![
                Line::from(vec![
                    Span::raw(if selected { "▶ " } else { "  " }),
                    Span::styled(
                        name.to_string(),
                        Style::default()
                            .fg(match mode {
                                WalletMode::User => Color::Green,
                                WalletMode::NodeOperator => Color::Yellow,
                                WalletMode::QuantumOperator => Color::Cyan,
                                WalletMode::Exit => Color::Red,
                            })
                            .add_modifier(if selected { Modifier::BOLD } else { Modifier::empty() })
                    ),
                ]),
                Line::from(vec![
                    Span::raw("    "),
                    Span::styled(
                        desc.to_string(),
                        Style::default().fg(Color::DarkGray)
                    ),
                ]),
                Line::from(""),
            ];
            
            ListItem::new(content)
        }).collect();
        
        let list = List::new(items)
            .block(Block::default().borders(Borders::ALL).title(" Select Mode "))
            .style(Style::default().fg(Color::White));
        
        f.render_widget(list, chunks[1]);
        
        // Footer
        let footer = Paragraph::new(vec![
            Line::from(""),
            Line::from("Use ↑↓ to navigate, Enter to select, Esc/q to exit"),
        ])
        .alignment(Alignment::Center)
        .style(Style::default().fg(Color::DarkGray));
        
        f.render_widget(footer, chunks[2]);
    }
}