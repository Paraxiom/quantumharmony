//! 3D Spiral Architecture Visualization for TUI
//!
//! This module implements the self-documenting wallet concept where
//! the wallet IS the documentation. Users navigate through a 3D spiral
//! representing the 6-layer blockchain architecture.

use ratatui::{
    layout::{Alignment, Constraint, Direction, Layout, Rect},
    style::{Color, Modifier, Style},
    text::{Line, Span},
    widgets::{Block, Borders, List, ListItem, Paragraph, Wrap},
    Frame,
};

use crate::core::Layer;

/// ASCII art spiral visualization
const SPIRAL_ART: &str = r#"
        ╭─── Layer 5: Application ───╮
       ↗   (QSBR RPC, Ternary)      ↖
     ↗                                ↖
    ╭─── Layer 4: Signatures ─────────╮
   ↗   (SPHINCS+, Falcon1024)         ↖
  │                                    │
  ╰─── Layer 3: Key Management ───────╯
   ↖    (Triple Ratchet, SPQDR)      ↗
    ↖                                ↗
     ╰─── Layer 2: Network ─────────╯
      ↖   (QUIC, P2P Gossip)       ↗
       ↖                           ↗
        ╰─── Layer 1: Consensus ──╯
         ↖  (Aura, GRANDPA)      ↗
          ↖                     ↗
           ╰─── Layer 0: Entropy╯
               (QKD, QRNG)
"#;

/// State for the architecture spiral view
pub struct ArchitectureSpiral {
    pub selected_layer: Layer,
    pub show_docs: bool,
    pub doc_scroll_offset: usize,
}

impl Default for ArchitectureSpiral {
    fn default() -> Self {
        Self {
            selected_layer: Layer::Application, // Start at top of spiral
            show_docs: false,
            doc_scroll_offset: 0,
        }
    }
}

impl ArchitectureSpiral {
    pub fn new() -> Self {
        Self::default()
    }

    /// Navigate to next layer (down the spiral)
    pub fn next_layer(&mut self) {
        self.selected_layer = match self.selected_layer {
            Layer::Entropy => Layer::Consensus,
            Layer::Consensus => Layer::Network,
            Layer::Network => Layer::KeyManagement,
            Layer::KeyManagement => Layer::Signatures,
            Layer::Signatures => Layer::Application,
            Layer::Application => Layer::Entropy, // Wrap around
        };
        self.doc_scroll_offset = 0; // Reset scroll when changing layers
    }

    /// Navigate to previous layer (up the spiral)
    pub fn prev_layer(&mut self) {
        self.selected_layer = match self.selected_layer {
            Layer::Entropy => Layer::Application, // Wrap around
            Layer::Consensus => Layer::Entropy,
            Layer::Network => Layer::Consensus,
            Layer::KeyManagement => Layer::Network,
            Layer::Signatures => Layer::KeyManagement,
            Layer::Application => Layer::Signatures,
        };
        self.doc_scroll_offset = 0;
    }

    /// Jump directly to a layer by number (0-5)
    pub fn jump_to_layer(&mut self, layer_num: u8) {
        self.selected_layer = match layer_num {
            0 => Layer::Entropy,
            1 => Layer::Consensus,
            2 => Layer::Network,
            3 => Layer::KeyManagement,
            4 => Layer::Signatures,
            5 => Layer::Application,
            _ => return, // Invalid layer number
        };
        self.doc_scroll_offset = 0;
    }

    /// Toggle documentation panel
    pub fn toggle_docs(&mut self) {
        self.show_docs = !self.show_docs;
        self.doc_scroll_offset = 0;
    }

    /// Scroll documentation up
    pub fn scroll_docs_up(&mut self) {
        self.doc_scroll_offset = self.doc_scroll_offset.saturating_sub(1);
    }

    /// Scroll documentation down
    pub fn scroll_docs_down(&mut self) {
        self.doc_scroll_offset = self.doc_scroll_offset.saturating_add(1);
    }

    /// Scroll documentation by page
    pub fn scroll_docs_page_up(&mut self) {
        self.doc_scroll_offset = self.doc_scroll_offset.saturating_sub(10);
    }

    pub fn scroll_docs_page_down(&mut self) {
        self.doc_scroll_offset = self.doc_scroll_offset.saturating_add(10);
    }

    /// Load documentation for the selected layer
    fn load_layer_docs(&self) -> Vec<Line<'static>> {
        // Load embedded markdown documentation
        let content = match self.selected_layer {
            Layer::Entropy => include_str!("../docs/layer_0_entropy.md"),
            Layer::Consensus => include_str!("../docs/layer_1_consensus.md"),
            Layer::Network => include_str!("../docs/layer_2_network.md"),
            Layer::KeyManagement => include_str!("../docs/layer_3_keys.md"),
            Layer::Signatures => include_str!("../docs/layer_4_signatures.md"),
            Layer::Application => include_str!("../docs/layer_5_application.md"),
        };

        // Simple markdown parsing for TUI display
        content
            .lines()
            .map(|line| {
                // Parse basic markdown
                if line.starts_with("# ") {
                    // H1 headers - cyan, bold
                    Line::from(Span::styled(
                        line.trim_start_matches("# "),
                        Style::default().fg(Color::Cyan).add_modifier(Modifier::BOLD),
                    ))
                } else if line.starts_with("## ") {
                    // H2 headers - yellow, bold
                    Line::from(Span::styled(
                        line.trim_start_matches("## "),
                        Style::default().fg(Color::Yellow).add_modifier(Modifier::BOLD),
                    ))
                } else if line.starts_with("### ") {
                    // H3 headers - green
                    Line::from(Span::styled(
                        line.trim_start_matches("### "),
                        Style::default().fg(Color::Green),
                    ))
                } else if line.starts_with("```") {
                    // Code fence markers - gray
                    Line::from(Span::styled(
                        line,
                        Style::default().fg(Color::DarkGray),
                    ))
                } else if line.trim().starts_with("- ") || line.trim().starts_with("* ") {
                    // Bullet points - light blue
                    Line::from(Span::styled(
                        line,
                        Style::default().fg(Color::LightBlue),
                    ))
                } else if line.starts_with("|") {
                    // Table rows - magenta
                    Line::from(Span::styled(
                        line,
                        Style::default().fg(Color::Magenta),
                    ))
                } else if line.trim().starts_with("**") {
                    // Bold text - white, bold
                    Line::from(Span::styled(
                        line.trim().trim_matches('*'),
                        Style::default().fg(Color::White).add_modifier(Modifier::BOLD),
                    ))
                } else {
                    // Regular text
                    Line::from(line.to_string())
                }
            })
            .collect()
    }
}

/// Render the architecture spiral view
pub fn render_architecture_spiral(f: &mut Frame, spiral: &ArchitectureSpiral, area: Rect) {
    if spiral.show_docs {
        // Show documentation panel (full screen)
        render_documentation_panel(f, spiral, area);
    } else {
        // Show spiral visualization with layer info
        render_spiral_view(f, spiral, area);
    }
}

/// Render the main spiral visualization
fn render_spiral_view(f: &mut Frame, spiral: &ArchitectureSpiral, area: Rect) {
    let chunks = Layout::default()
        .direction(Direction::Horizontal)
        .constraints([
            Constraint::Percentage(60), // Spiral art + layer list
            Constraint::Percentage(40), // Selected layer info
        ])
        .split(area);

    // Left side: Spiral art + layer list
    let left_chunks = Layout::default()
        .direction(Direction::Vertical)
        .constraints([
            Constraint::Length(18), // Spiral ASCII art
            Constraint::Min(0),     // Layer list
        ])
        .split(chunks[0]);

    // Render spiral ASCII art
    render_spiral_art(f, spiral, left_chunks[0]);

    // Render layer list
    render_layer_list(f, spiral, left_chunks[1]);

    // Right side: Selected layer details
    render_layer_details(f, spiral, chunks[1]);
}

/// Render the ASCII spiral art
fn render_spiral_art(f: &mut Frame, spiral: &ArchitectureSpiral, area: Rect) {
    // Highlight the selected layer in the spiral
    let lines: Vec<Line> = SPIRAL_ART
        .lines()
        .enumerate()
        .map(|(idx, line)| {
            let layer_line = match idx {
                1..=2 => Some(Layer::Application),
                4..=5 => Some(Layer::Signatures),
                7..=8 => Some(Layer::KeyManagement),
                10..=11 => Some(Layer::Network),
                13..=14 => Some(Layer::Consensus),
                16..=17 => Some(Layer::Entropy),
                _ => None,
            };

            if let Some(layer) = layer_line {
                if layer == spiral.selected_layer {
                    // Highlight selected layer
                    Line::from(Span::styled(
                        line.to_string(),
                        Style::default()
                            .fg(Color::Cyan)
                            .add_modifier(Modifier::BOLD),
                    ))
                } else {
                    Line::from(line.to_string())
                }
            } else {
                Line::from(line.to_string())
            }
        })
        .collect();

    let spiral_widget = Paragraph::new(lines)
        .block(Block::default().borders(Borders::ALL).title(" 3D Spiral Architecture "))
        .alignment(Alignment::Center);

    f.render_widget(spiral_widget, area);
}

/// Render the layer list
fn render_layer_list(f: &mut Frame, spiral: &ArchitectureSpiral, area: Rect) {
    let layers = vec![
        Layer::Application,
        Layer::Signatures,
        Layer::KeyManagement,
        Layer::Network,
        Layer::Consensus,
        Layer::Entropy,
    ];

    let items: Vec<ListItem> = layers
        .iter()
        .map(|layer| {
            let (r, g, b) = layer.color_rgb();
            let color = Color::Rgb(r, g, b);

            let style = if *layer == spiral.selected_layer {
                Style::default()
                    .fg(color)
                    .add_modifier(Modifier::BOLD)
                    .add_modifier(Modifier::UNDERLINED)
            } else {
                Style::default().fg(color)
            };

            let indicator = if *layer == spiral.selected_layer {
                "→ "
            } else {
                "  "
            };

            ListItem::new(vec![
                Line::from(vec![
                    Span::raw(indicator),
                    Span::styled(format!("Layer {}: ", *layer as u8), style),
                    Span::styled(layer.name(), style),
                ]),
                Line::from(Span::styled(
                    format!("    {}", layer.description()),
                    Style::default().fg(Color::DarkGray)
                )),
            ])
        })
        .collect();

    let list = List::new(items).block(
        Block::default()
            .borders(Borders::ALL)
            .title(" Layers (0-5: jump, ↑↓: navigate, Enter: docs) "),
    );

    f.render_widget(list, area);
}

/// Render selected layer details
fn render_layer_details(f: &mut Frame, spiral: &ArchitectureSpiral, area: Rect) {
    let layer = spiral.selected_layer;
    let (r, g, b) = layer.color_rgb();
    let color = Color::Rgb(r, g, b);

    let details = vec![
        Line::from(vec![
            Span::styled(
                format!("Layer {}: {}", layer as u8, layer.name()),
                Style::default().fg(color).add_modifier(Modifier::BOLD),
            ),
        ]),
        Line::from(""),
        Line::from(layer.description()),
        Line::from(""),
        Line::from(vec![
            Span::raw("Components: "),
            Span::styled(
                layer.components().join(", "),
                Style::default().fg(Color::Yellow),
            ),
        ]),
        Line::from(""),
        Line::from(vec![
            Span::raw("Security: "),
            Span::styled(
                layer.security_features(),
                Style::default().fg(Color::Green),
            ),
        ]),
        Line::from(""),
        Line::from(vec![
            Span::styled(
                "Press Enter to view full documentation",
                Style::default().fg(Color::Cyan).add_modifier(Modifier::ITALIC),
            ),
        ]),
        Line::from(""),
        Line::from("Quick Actions:"),
        Line::from("  • 0-5: Jump to layer"),
        Line::from("  • ↑↓: Navigate spiral"),
        Line::from("  • Enter: View docs"),
        Line::from("  • U: Check upgrades"),
        Line::from("  • Q: Back to menu"),
    ];

    let widget = Paragraph::new(details)
        .block(Block::default().borders(Borders::ALL).title(" Layer Details "))
        .wrap(Wrap { trim: true });

    f.render_widget(widget, area);
}

/// Render the documentation panel (full screen)
fn render_documentation_panel(f: &mut Frame, spiral: &ArchitectureSpiral, area: Rect) {
    let layer = spiral.selected_layer;
    let (r, g, b) = layer.color_rgb();
    let color = Color::Rgb(r, g, b);

    // Load documentation
    let doc_lines = spiral.load_layer_docs();

    // Calculate visible range
    let visible_height = area.height.saturating_sub(3) as usize; // Account for borders and title
    let total_lines = doc_lines.len();
    let max_offset = total_lines.saturating_sub(visible_height);
    let scroll_offset = spiral.doc_scroll_offset.min(max_offset);

    // Get visible portion
    let visible_lines: Vec<Line> = doc_lines
        .into_iter()
        .skip(scroll_offset)
        .take(visible_height)
        .collect();

    // Scroll indicator
    let scroll_indicator = if total_lines > visible_height {
        format!(" [{}-{}/{}] ", scroll_offset + 1, (scroll_offset + visible_height).min(total_lines), total_lines)
    } else {
        String::new()
    };

    let title = format!(
        " Layer {}: {}{} (Esc: back, ↑↓/PgUp/PgDn: scroll) ",
        layer as u8,
        layer.name(),
        scroll_indicator
    );

    let doc_widget = Paragraph::new(visible_lines)
        .block(
            Block::default()
                .borders(Borders::ALL)
                .title(title)
                .border_style(Style::default().fg(color)),
        )
        .wrap(Wrap { trim: false });

    f.render_widget(doc_widget, area);
}
