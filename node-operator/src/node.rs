//! Node lifecycle management
//!
//! Handles starting, stopping, and monitoring the QuantumHarmony node process.

use std::{
    collections::VecDeque,
    io::{BufRead, BufReader},
    path::PathBuf,
    process::{Child, Command, Stdio},
    sync::Arc,
};
use tokio::sync::{broadcast, Mutex};
use tracing::{info, warn, error, debug};

use crate::OperatorConfig;

const MAX_LOG_LINES: usize = 1000;

/// Manages the node process lifecycle
pub struct NodeManager {
    process: Option<Child>,
    logs: VecDeque<String>,
    log_file: Option<PathBuf>,
    log_broadcast: broadcast::Sender<String>,
}

impl NodeManager {
    pub fn new(log_broadcast: broadcast::Sender<String>) -> Self {
        Self {
            process: None,
            logs: VecDeque::with_capacity(MAX_LOG_LINES),
            log_file: Some(PathBuf::from("/tmp/quantumharmony-node.log")),
            log_broadcast,
        }
    }

    /// Check if the node is running
    pub fn is_running(&self) -> bool {
        self.process.as_ref().map_or(false, |p| {
            // Try to check if process is still alive
            // This is a bit hacky but works
            std::process::Command::new("kill")
                .args(["-0", &p.id().to_string()])
                .output()
                .map_or(false, |o| o.status.success())
        })
    }

    /// Get the process ID if running
    pub fn pid(&self) -> Option<u32> {
        self.process.as_ref().map(|p| p.id())
    }

    /// Start the node
    pub async fn start(
        &mut self,
        config: &OperatorConfig,
        validator: bool,
        name: &str,
    ) -> Result<u32, String> {
        if self.is_running() {
            return Err("Node is already running".to_string());
        }

        // Build command
        let mut cmd = Command::new(&config.node_binary);

        // Chain spec
        if let Some(ref chain_spec) = config.chain_spec {
            cmd.arg("--chain").arg(chain_spec);
        }

        // Basic args
        cmd.arg("--name").arg(name)
            .arg("--rpc-port").arg(config.rpc_port.to_string())
            .arg("--port").arg(config.p2p_port.to_string())
            .arg("--rpc-cors").arg("all")
            .arg("--rpc-methods").arg("Unsafe")
            .arg("--rpc-external");

        // Validator mode
        if validator {
            cmd.arg("--validator");
        }

        // Bootnode
        if let Some(ref bootnode) = config.bootnode {
            cmd.arg("--bootnodes").arg(bootnode);
        }

        // Data directory
        if let Some(ref data_dir) = config.data_dir {
            cmd.arg("--base-path").arg(data_dir);
        }

        // Redirect output to log file
        let log_file = std::fs::File::create("/tmp/quantumharmony-node.log")
            .map_err(|e| format!("Failed to create log file: {}", e))?;

        cmd.stdout(Stdio::from(log_file.try_clone().map_err(|e| e.to_string())?))
            .stderr(Stdio::from(log_file));

        info!("Starting node: {:?}", cmd);
        self.add_log(format!("Starting node: {} {}",
            config.node_binary.display(),
            if validator { "--validator" } else { "" }
        ));

        // Spawn process
        let child = cmd.spawn().map_err(|e| format!("Failed to spawn node: {}", e))?;
        let pid = child.id();
        self.process = Some(child);

        self.add_log(format!("Node started with PID: {}", pid));

        // Start log reader task
        self.start_log_reader();

        Ok(pid)
    }

    /// Stop the node
    pub async fn stop(&mut self) -> Result<(), String> {
        if let Some(mut process) = self.process.take() {
            let pid = process.id();
            info!("Stopping node (PID: {})", pid);
            self.add_log(format!("Stopping node (PID: {})", pid));

            // Try graceful shutdown first (SIGTERM)
            #[cfg(unix)]
            {
                use std::os::unix::process::CommandExt;
                let _ = std::process::Command::new("kill")
                    .args(["-TERM", &pid.to_string()])
                    .output();
            }

            // Wait a bit for graceful shutdown
            tokio::time::sleep(tokio::time::Duration::from_secs(5)).await;

            // Check if still running and force kill if needed
            if self.check_process_exists(pid) {
                warn!("Node didn't stop gracefully, sending SIGKILL");
                self.add_log("Node didn't stop gracefully, forcing shutdown".to_string());

                #[cfg(unix)]
                {
                    let _ = std::process::Command::new("kill")
                        .args(["-KILL", &pid.to_string()])
                        .output();
                }

                let _ = process.kill();
            }

            let _ = process.wait();
            self.add_log("Node stopped".to_string());
            Ok(())
        } else {
            Ok(()) // Already stopped
        }
    }

    /// Get recent logs
    pub fn get_logs(&self, count: usize) -> Vec<String> {
        self.logs.iter().rev().take(count).cloned().collect()
    }

    /// Add a log entry
    fn add_log(&mut self, message: String) {
        let timestamp = chrono_lite_timestamp();
        let log_line = format!("[{}] {}", timestamp, message);

        if self.logs.len() >= MAX_LOG_LINES {
            self.logs.pop_front();
        }
        self.logs.push_back(log_line.clone());
        let _ = self.log_broadcast.send(log_line);
    }

    /// Start a background task to read logs
    fn start_log_reader(&self) {
        let log_file = self.log_file.clone();
        let tx = self.log_broadcast.clone();

        tokio::spawn(async move {
            if let Some(path) = log_file {
                tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;

                loop {
                    if let Ok(file) = std::fs::File::open(&path) {
                        let reader = BufReader::new(file);
                        for line in reader.lines().flatten() {
                            // Parse and forward relevant log lines
                            if line.contains("best:") ||
                               line.contains("finalized") ||
                               line.contains("Syncing") ||
                               line.contains("peers") ||
                               line.contains("Error") ||
                               line.contains("Started") ||
                               line.contains("Running") {
                                let _ = tx.send(line);
                            }
                        }
                    }
                    tokio::time::sleep(tokio::time::Duration::from_secs(2)).await;
                }
            }
        });
    }

    fn check_process_exists(&self, pid: u32) -> bool {
        std::process::Command::new("kill")
            .args(["-0", &pid.to_string()])
            .output()
            .map_or(false, |o| o.status.success())
    }
}

/// Simple timestamp without chrono dependency
fn chrono_lite_timestamp() -> String {
    use std::time::{SystemTime, UNIX_EPOCH};
    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default();
    let secs = now.as_secs();
    let hours = (secs % 86400) / 3600;
    let mins = (secs % 3600) / 60;
    let secs = secs % 60;
    format!("{:02}:{:02}:{:02}", hours, mins, secs)
}
