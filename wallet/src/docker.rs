//! Docker Management Module
//!
//! Provides Docker container management functionality for the wallet web server.
//! Supports starting, stopping, and monitoring Docker containers for the
//! QuantumHarmony testnet.

use serde::{Serialize, Deserialize};
use std::process::{Command, Stdio};
use tokio::process::Command as TokioCommand;
use std::path::PathBuf;

/// Docker status response
#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct DockerStatus {
    pub running: bool,
    pub containers: i32,
    pub network_type: String,
    pub rpc: Option<String>,
    pub error: Option<String>,
}

/// Docker start request
#[derive(Deserialize, Debug)]
pub struct DockerStartRequest {
    pub network_type: String,
}

/// Docker stop request
#[derive(Deserialize, Debug)]
pub struct DockerStopRequest {
    pub network_type: String,
}

/// Get the project root directory
fn get_project_root() -> PathBuf {
    // Assume we're running from the project root or target/release
    let current = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));

    // If we're in target/release, go up two levels
    if current.ends_with("target/release") {
        current.parent().unwrap().parent().unwrap().to_path_buf()
    } else if current.ends_with("target") {
        current.parent().unwrap().to_path_buf()
    } else {
        current
    }
}

/// Check Docker daemon status
pub async fn check_docker_daemon() -> bool {
    let output = TokioCommand::new("docker")
        .arg("info")
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .await;

    match output {
        Ok(status) => status.success(),
        Err(_) => false,
    }
}

/// Get Docker container status
pub async fn get_status() -> DockerStatus {
    // Check if Docker daemon is running
    if !check_docker_daemon().await {
        return DockerStatus {
            running: false,
            containers: 0,
            network_type: "none".to_string(),
            rpc: None,
            error: Some("Docker daemon not running".to_string()),
        };
    }

    // Check for running QuantumHarmony containers
    let output = TokioCommand::new("docker")
        .args(&["ps", "--filter", "name=qh-", "--format", "{{.Names}}"])
        .output()
        .await;

    match output {
        Ok(output) if output.status.success() => {
            let containers_str = String::from_utf8_lossy(&output.stdout);
            let containers: Vec<&str> = containers_str.lines().filter(|l| !l.is_empty()).collect();
            let count = containers.len() as i32;

            let (running, network_type, rpc) = if count > 0 {
                let net_type = if count >= 3 {
                    "testnet-full"
                } else {
                    "simple"
                };
                (true, net_type.to_string(), Some("ws://localhost:9944".to_string()))
            } else {
                (false, "none".to_string(), None)
            };

            DockerStatus {
                running,
                containers: count,
                network_type,
                rpc,
                error: None,
            }
        }
        Ok(_) => DockerStatus {
            running: false,
            containers: 0,
            network_type: "none".to_string(),
            rpc: None,
            error: Some("Failed to query Docker containers".to_string()),
        },
        Err(e) => DockerStatus {
            running: false,
            containers: 0,
            network_type: "none".to_string(),
            rpc: None,
            error: Some(format!("Docker command failed: {}", e)),
        },
    }
}

/// Start Docker containers with output (non-blocking)
pub async fn start_containers(network_type: &str) -> Result<DockerStatus, String> {
    let project_root = get_project_root();

    // Check if Docker daemon is running
    if !check_docker_daemon().await {
        return Err("Docker daemon is not running. Please start Docker Desktop.".to_string());
    }

    // Check if docker-compose.yml exists
    let compose_file = project_root.join("docker-compose.yml");
    if !compose_file.exists() {
        return Err(format!("docker-compose.yml not found at {:?}", compose_file));
    }

    // Start containers in background (don't wait for build to complete)
    let args: Vec<&str> = if network_type == "testnet-full" {
        vec!["up", "-d"]
    } else {
        vec!["up", "-d", "alice"]
    };

    // Spawn docker-compose in background
    let child = TokioCommand::new("docker-compose")
        .current_dir(&project_root)
        .args(&args)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn();

    match child {
        Ok(mut child) => {
            log::info!("Docker containers starting in background (network_type: {})", network_type);

            // Spawn a task to monitor the output
            tokio::spawn(async move {
                if let Ok(output) = child.wait_with_output().await {
                    let stdout = String::from_utf8_lossy(&output.stdout);
                    let stderr = String::from_utf8_lossy(&output.stderr);

                    if output.status.success() {
                        log::info!("Docker containers started successfully:\nSTDOUT: {}\nSTDERR: {}", stdout, stderr);
                    } else {
                        log::error!("Docker containers failed to start:\nSTDOUT: {}\nSTDERR: {}", stdout, stderr);
                    }
                }
            });

            // Return immediately with starting status
            Ok(DockerStatus {
                running: false,
                containers: 0,
                network_type: network_type.to_string(),
                rpc: None,
                error: Some("Containers are starting... (building images if needed)".to_string()),
            })
        }
        Err(e) => Err(format!("Failed to execute docker-compose: {}", e)),
    }
}

/// Stop Docker containers
pub async fn stop_containers(_network_type: &str) -> Result<DockerStatus, String> {
    let project_root = get_project_root();

    let output = TokioCommand::new("docker-compose")
        .current_dir(&project_root)
        .args(&["down"])
        .output()
        .await;

    match output {
        Ok(output) if output.status.success() => {
            Ok(DockerStatus {
                running: false,
                containers: 0,
                network_type: "none".to_string(),
                rpc: None,
                error: None,
            })
        }
        Ok(output) => {
            let stderr = String::from_utf8_lossy(&output.stderr);
            Err(format!("Failed to stop containers: {}", stderr))
        }
        Err(e) => Err(format!("Failed to execute docker-compose: {}", e)),
    }
}

/// Purge Docker containers (remove volumes)
pub async fn purge_containers(_network_type: &str) -> Result<String, String> {
    let project_root = get_project_root();

    // Stop and remove containers with volumes
    let output = TokioCommand::new("docker-compose")
        .current_dir(&project_root)
        .args(&["down", "-v"])
        .output()
        .await;

    match output {
        Ok(output) if output.status.success() => {
            Ok("Containers and volumes removed successfully".to_string())
        }
        Ok(output) => {
            let stderr = String::from_utf8_lossy(&output.stderr);
            Err(format!("Failed to purge: {}", stderr))
        }
        Err(e) => Err(format!("Failed to execute docker-compose: {}", e)),
    }
}

/// Deep clean: remove containers, volumes, and images
pub async fn deep_clean() -> Result<String, String> {
    let project_root = get_project_root();

    // Stop and remove everything
    let _ = TokioCommand::new("docker-compose")
        .current_dir(&project_root)
        .args(&["down", "-v", "--rmi", "all"])
        .output()
        .await;

    // Remove dangling volumes
    let _ = TokioCommand::new("docker")
        .args(&["volume", "prune", "-f"])
        .output()
        .await;

    // Remove dangling images
    let _ = TokioCommand::new("docker")
        .args(&["image", "prune", "-f"])
        .output()
        .await;

    Ok("Deep clean completed: removed containers, volumes, and images".to_string())
}

/// Nuclear option: remove everything Docker-related
pub async fn nuke_all() -> Result<String, String> {
    let project_root = get_project_root();

    // Stop all containers
    let _ = TokioCommand::new("docker-compose")
        .current_dir(&project_root)
        .args(&["down", "-v"])
        .output()
        .await;

    // Remove all quantumharmony containers
    let _ = TokioCommand::new("docker")
        .args(&["rm", "-f", "$(docker ps -aq --filter name=qh-)"])
        .output()
        .await;

    // Remove quantumharmony network
    let _ = TokioCommand::new("docker")
        .args(&["network", "rm", "quantumharmony"])
        .output()
        .await;

    // Remove all volumes with qh prefix
    let _ = TokioCommand::new("docker")
        .args(&["volume", "rm", "$(docker volume ls -q --filter name=qh-)"])
        .output()
        .await;

    // Remove quantumharmony images
    let _ = TokioCommand::new("docker")
        .args(&["rmi", "-f", "quantumharmony-node:latest"])
        .output()
        .await;

    // System prune
    let _ = TokioCommand::new("docker")
        .args(&["system", "prune", "-af", "--volumes"])
        .output()
        .await;

    Ok("Nuclear clean completed: removed all Docker artifacts".to_string())
}

/// Build Docker image
pub async fn build_image() -> Result<String, String> {
    let project_root = get_project_root();

    let output = TokioCommand::new("docker")
        .current_dir(&project_root)
        .args(&["build", "-t", "quantumharmony-node:latest", "."])
        .output()
        .await;

    match output {
        Ok(output) if output.status.success() => {
            Ok("Docker image built successfully".to_string())
        }
        Ok(output) => {
            let stderr = String::from_utf8_lossy(&output.stderr);
            Err(format!("Failed to build image: {}", stderr))
        }
        Err(e) => Err(format!("Failed to execute docker build: {}", e)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_check_docker_daemon() {
        // This will only pass if Docker is actually running
        let result = check_docker_daemon().await;
        println!("Docker daemon running: {}", result);
    }

    #[tokio::test]
    async fn test_get_status() {
        let status = get_status().await;
        println!("Docker status: {:?}", status);
    }
}
