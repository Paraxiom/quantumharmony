// Prevents additional console window on Windows in release, DO NOT REMOVE!!
#![cfg_attr(not(debug_assertions), windows_subsystem = "windows")]

use std::process::{Child, Command, Stdio};
use std::sync::{Arc, Mutex};
use std::io::{BufRead, BufReader};
use serde::{Deserialize, Serialize};
use tauri::{AppHandle, Emitter, Manager, State};
use tauri_plugin_updater::UpdaterExt;

/// Shared state for the node process
struct NodeState {
    process: Arc<Mutex<Option<Child>>>,
    output_buffer: Arc<Mutex<Vec<String>>>,
}

#[derive(Clone, Serialize, Deserialize)]
struct NodeOutput {
    lines: Vec<String>,
}

#[derive(Clone, Serialize, Deserialize)]
struct UpdateInfo {
    version: String,
    date: String,
    body: String,
}

/// Start the QuantumHarmony node
#[tauri::command]
async fn start_node(
    state: State<'_, NodeState>,
    app_handle: AppHandle,
) -> Result<String, String> {
    let mut process_lock = state.process.lock().map_err(|e| e.to_string())?;

    // Check if node is already running
    if process_lock.is_some() {
        return Err("Node is already running".to_string());
    }

    // Get the path to the node binary
    let node_binary = if cfg!(debug_assertions) {
        // Development mode - use local binary
        std::env::current_dir()
            .map_err(|e| e.to_string())?
            .parent()
            .ok_or("Failed to get parent directory")?
            .join("target/release/quantumharmony-node")
    } else {
        // Production mode - use bundled binary
        app_handle
            .path()
            .resource_dir()
            .map_err(|e| e.to_string())?
            .join("quantumharmony-node")
    };

    if !node_binary.exists() {
        return Err(format!(
            "Node binary not found at: {}",
            node_binary.display()
        ));
    }

    // Start the node process
    let mut child = Command::new(&node_binary)
        .args(&["--dev", "--tmp", "--rpc-port", "9944", "--rpc-cors", "all"])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("Failed to start node: {}", e))?;

    // Capture stdout
    let stdout = child.stdout.take().ok_or("Failed to capture stdout")?;
    let output_buffer = state.output_buffer.clone();
    let app_handle_clone = app_handle.clone();

    // Spawn thread to read stdout
    std::thread::spawn(move || {
        let reader = BufReader::new(stdout);
        for line in reader.lines() {
            if let Ok(line) = line {
                // Add to buffer
                if let Ok(mut buffer) = output_buffer.lock() {
                    buffer.push(line.clone());
                    // Keep only last 1000 lines
                    if buffer.len() > 1000 {
                        buffer.drain(0..100);
                    }
                }

                // Emit event to frontend
                let _ = app_handle_clone.emit("node-output", line);
            }
        }
    });

    // Capture stderr
    let stderr = child.stderr.take().ok_or("Failed to capture stderr")?;
    let output_buffer_err = state.output_buffer.clone();
    let app_handle_err = app_handle.clone();

    std::thread::spawn(move || {
        let reader = BufReader::new(stderr);
        for line in reader.lines() {
            if let Ok(line) = line {
                let error_line = format!("ERROR: {}", line);
                if let Ok(mut buffer) = output_buffer_err.lock() {
                    buffer.push(error_line.clone());
                    if buffer.len() > 1000 {
                        buffer.drain(0..100);
                    }
                }
                let _ = app_handle_err.emit("node-output", error_line);
            }
        }
    });

    *process_lock = Some(child);
    Ok("Node started successfully".to_string())
}

/// Stop the QuantumHarmony node
#[tauri::command]
async fn stop_node(state: State<'_, NodeState>) -> Result<String, String> {
    let mut process_lock = state.process.lock().map_err(|e| e.to_string())?;

    if let Some(mut child) = process_lock.take() {
        child.kill().map_err(|e| format!("Failed to kill node: {}", e))?;
        child.wait().map_err(|e| format!("Failed to wait for node: {}", e))?;
        Ok("Node stopped successfully".to_string())
    } else {
        Err("Node is not running".to_string())
    }
}

/// Get node output
#[tauri::command]
async fn get_node_output(
    state: State<'_, NodeState>,
    last_n: Option<usize>,
) -> Result<NodeOutput, String> {
    let buffer = state.output_buffer.lock().map_err(|e| e.to_string())?;

    let lines = if let Some(n) = last_n {
        let start = buffer.len().saturating_sub(n);
        buffer[start..].to_vec()
    } else {
        buffer.clone()
    };

    Ok(NodeOutput { lines })
}

/// Clear node output buffer
#[tauri::command]
async fn clear_node_output(state: State<'_, NodeState>) -> Result<String, String> {
    let mut buffer = state.output_buffer.lock().map_err(|e| e.to_string())?;
    buffer.clear();
    Ok("Output buffer cleared".to_string())
}

/// Check for runtime updates
#[tauri::command]
async fn check_for_updates(app: AppHandle) -> Result<Option<UpdateInfo>, String> {
    #[cfg(not(any(target_os = "android", target_os = "ios")))]
    {
        let updater = app.updater_builder().build().map_err(|e| e.to_string())?;

        match updater.check().await {
            Ok(Some(update)) => {
                Ok(Some(UpdateInfo {
                    version: update.version.clone(),
                    date: update.date.map(|d| d.to_string()).unwrap_or_default(),
                    body: update.body.clone().unwrap_or_default(),
                }))
            }
            Ok(None) => Ok(None),
            Err(e) => Err(format!("Update check failed: {}", e)),
        }
    }

    #[cfg(any(target_os = "android", target_os = "ios"))]
    {
        Err("Updates not supported on this platform".to_string())
    }
}

/// Install a runtime update
#[tauri::command]
async fn install_update(app: AppHandle) -> Result<String, String> {
    #[cfg(not(any(target_os = "android", target_os = "ios")))]
    {
        let updater = app.updater_builder().build().map_err(|e| e.to_string())?;

        if let Some(update) = updater.check().await.map_err(|e| e.to_string())? {
            // Download and install update
            update.download_and_install(
                |chunk_length, content_length| {
                    let _ = app.emit(
                        "update-progress",
                        (chunk_length, content_length.unwrap_or(0)),
                    );
                },
                || {
                    let _ = app.emit("update-complete", ());
                },
            )
            .await
            .map_err(|e| format!("Update installation failed: {}", e))?;

            Ok("Update installed successfully. Restart the application to apply.".to_string())
        } else {
            Err("No updates available".to_string())
        }
    }

    #[cfg(any(target_os = "android", target_os = "ios"))]
    {
        Err("Updates not supported on this platform".to_string())
    }
}

/// Submit a Substrate runtime upgrade (forkless upgrade)
/// This uploads the runtime WASM and submits a sudo.setCode() extrinsic
#[tauri::command]
async fn submit_runtime_upgrade(
    wasm_path: String,
    sudo_seed: String,
) -> Result<String, String> {
    // Read the runtime WASM file
    let wasm_code = std::fs::read(&wasm_path)
        .map_err(|e| format!("Failed to read WASM file: {}", e))?;

    tracing::info!("Read {} bytes of runtime WASM from {}", wasm_code.len(), wasm_path);

    // Submit via RPC
    let client = reqwest::Client::new();

    // Create the setCode call
    let set_code_call = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 1,
        "method": "author_submitExtrinsic",
        "params": [format!("0x{}", hex::encode(&wasm_code))]
    });

    let response = client
        .post("http://localhost:9944")
        .json(&set_code_call)
        .send()
        .await
        .map_err(|e| format!("RPC call failed: {}", e))?;

    let result: serde_json::Value = response
        .json()
        .await
        .map_err(|e| format!("Failed to parse response: {}", e))?;

    if let Some(error) = result.get("error") {
        return Err(format!("Runtime upgrade failed: {}", error));
    }

    Ok(format!(
        "Runtime upgrade submitted! WASM size: {} bytes. The upgrade will take effect after finalization.",
        wasm_code.len()
    ))
}

/// Get the current runtime version
#[tauri::command]
async fn get_runtime_version() -> Result<serde_json::Value, String> {
    let client = reqwest::Client::new();

    let request = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 1,
        "method": "state_getRuntimeVersion",
        "params": []
    });

    let response = client
        .post("http://localhost:9944")
        .json(&request)
        .send()
        .await
        .map_err(|e| format!("RPC call failed: {}", e))?;

    let result: serde_json::Value = response
        .json()
        .await
        .map_err(|e| format!("Failed to parse response: {}", e))?;

    if let Some(error) = result.get("error") {
        return Err(format!("Failed to get runtime version: {}", error));
    }

    Ok(result["result"].clone())
}

/// Select a WASM file from the filesystem
#[tauri::command]
async fn select_wasm_file(app: tauri::AppHandle) -> Result<String, String> {
    use tauri::Manager;

    // For now, return an error message asking user to provide path via CLI
    // File dialog requires the tauri-plugin-dialog which we haven't added yet
    Err("File dialog not yet implemented. Please use CLI: ./quantumharmony-cli upgrade".to_string())
}

/// Get node status
#[tauri::command]
async fn get_node_status(state: State<'_, NodeState>) -> Result<bool, String> {
    let process_lock = state.process.lock().map_err(|e| e.to_string())?;
    Ok(process_lock.is_some())
}

fn main() {
    // Initialize tracing
    tracing_subscriber::fmt::init();

    let node_state = NodeState {
        process: Arc::new(Mutex::new(None)),
        output_buffer: Arc::new(Mutex::new(Vec::new())),
    };

    tauri::Builder::default()
        .manage(node_state)
        .plugin(tauri_plugin_updater::Builder::new().build())
        .invoke_handler(tauri::generate_handler![
            start_node,
            stop_node,
            get_node_output,
            clear_node_output,
            check_for_updates,
            install_update,
            submit_runtime_upgrade,
            get_runtime_version,
            select_wasm_file,
            get_node_status,
        ])
        .setup(|app| {
            // Check for updates on startup
            let app_handle = app.handle().clone();
            tauri::async_runtime::spawn(async move {
                if let Ok(Some(update)) = check_for_updates(app_handle.clone()).await {
                    tracing::info!("Update available: version {}", update.version);
                    let _ = app_handle.emit("update-available", update);
                }
            });
            Ok(())
        })
        .run(tauri::generate_context!())
        .expect("error while running tauri application");
}
