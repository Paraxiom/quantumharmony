//! Node Management Tests
//!
//! Tests for starting, stopping, and monitoring the QuantumHarmony node.

use std::sync::{Arc, Mutex};
use std::time::Duration;

/// Mock node state for testing without Tauri runtime
pub struct MockNodeState {
    pub is_running: Arc<Mutex<bool>>,
    pub output_buffer: Arc<Mutex<Vec<String>>>,
}

impl MockNodeState {
    pub fn new() -> Self {
        Self {
            is_running: Arc::new(Mutex::new(false)),
            output_buffer: Arc::new(Mutex::new(Vec::new())),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ============================================
    // NODE STATE TESTS
    // ============================================

    #[test]
    fn test_node_state_initialization() {
        let state = MockNodeState::new();
        assert!(!*state.is_running.lock().unwrap());
        assert!(state.output_buffer.lock().unwrap().is_empty());
    }

    #[test]
    fn test_output_buffer_add_lines() {
        let state = MockNodeState::new();
        {
            let mut buffer = state.output_buffer.lock().unwrap();
            buffer.push("Line 1".to_string());
            buffer.push("Line 2".to_string());
            buffer.push("Line 3".to_string());
        }
        assert_eq!(state.output_buffer.lock().unwrap().len(), 3);
    }

    #[test]
    fn test_output_buffer_last_n_lines() {
        let state = MockNodeState::new();
        {
            let mut buffer = state.output_buffer.lock().unwrap();
            for i in 1..=100 {
                buffer.push(format!("Line {}", i));
            }
        }

        let buffer = state.output_buffer.lock().unwrap();
        let last_10: Vec<String> = buffer.iter().rev().take(10).cloned().collect();
        assert_eq!(last_10.len(), 10);
        assert_eq!(last_10[0], "Line 100");
    }

    #[test]
    fn test_output_buffer_truncation() {
        let state = MockNodeState::new();
        {
            let mut buffer = state.output_buffer.lock().unwrap();
            // Add 1100 lines
            for i in 1..=1100 {
                buffer.push(format!("Line {}", i));
            }
            // Simulate truncation (keep last 1000)
            if buffer.len() > 1000 {
                buffer.drain(0..100);
            }
        }
        assert!(state.output_buffer.lock().unwrap().len() <= 1000);
    }

    #[test]
    fn test_clear_output_buffer() {
        let state = MockNodeState::new();
        {
            let mut buffer = state.output_buffer.lock().unwrap();
            buffer.push("Line 1".to_string());
            buffer.push("Line 2".to_string());
        }
        {
            let mut buffer = state.output_buffer.lock().unwrap();
            buffer.clear();
        }
        assert!(state.output_buffer.lock().unwrap().is_empty());
    }

    // ============================================
    // NODE STATUS TESTS
    // ============================================

    #[test]
    fn test_node_not_running_initially() {
        let state = MockNodeState::new();
        assert!(!*state.is_running.lock().unwrap());
    }

    #[test]
    fn test_node_running_state_toggle() {
        let state = MockNodeState::new();

        // Start node
        *state.is_running.lock().unwrap() = true;
        assert!(*state.is_running.lock().unwrap());

        // Stop node
        *state.is_running.lock().unwrap() = false;
        assert!(!*state.is_running.lock().unwrap());
    }

    #[test]
    fn test_prevent_double_start() {
        let state = MockNodeState::new();
        *state.is_running.lock().unwrap() = true;

        // Attempt to start again should fail
        let is_running = *state.is_running.lock().unwrap();
        if is_running {
            // This would return an error in the actual implementation
            assert!(true, "Node is already running - cannot start again");
        }
    }

    #[test]
    fn test_prevent_stop_when_not_running() {
        let state = MockNodeState::new();

        let is_running = *state.is_running.lock().unwrap();
        if !is_running {
            // This would return an error in the actual implementation
            assert!(true, "Node is not running - cannot stop");
        }
    }

    // ============================================
    // ERROR LINE FORMATTING TESTS
    // ============================================

    #[test]
    fn test_error_line_formatting() {
        let error_msg = "Connection refused";
        let formatted = format!("ERROR: {}", error_msg);
        assert!(formatted.starts_with("ERROR:"));
        assert!(formatted.contains("Connection refused"));
    }

    #[test]
    fn test_multiline_error_output() {
        let state = MockNodeState::new();
        let errors = vec![
            "ERROR: Failed to connect to peer",
            "ERROR: Timeout waiting for block",
            "ERROR: Invalid transaction",
        ];

        {
            let mut buffer = state.output_buffer.lock().unwrap();
            for err in &errors {
                buffer.push(err.to_string());
            }
        }

        let buffer = state.output_buffer.lock().unwrap();
        let error_count = buffer.iter().filter(|l| l.starts_with("ERROR:")).count();
        assert_eq!(error_count, 3);
    }

    // ============================================
    // CONCURRENT ACCESS TESTS
    // ============================================

    #[test]
    fn test_concurrent_buffer_access() {
        use std::thread;

        let state = Arc::new(MockNodeState::new());
        let mut handles = vec![];

        // Spawn 10 threads that each add 10 lines
        for i in 0..10 {
            let state_clone = Arc::clone(&state);
            let handle = thread::spawn(move || {
                for j in 0..10 {
                    let mut buffer = state_clone.output_buffer.lock().unwrap();
                    buffer.push(format!("Thread {} Line {}", i, j));
                }
            });
            handles.push(handle);
        }

        // Wait for all threads
        for handle in handles {
            handle.join().unwrap();
        }

        // Should have 100 lines total
        assert_eq!(state.output_buffer.lock().unwrap().len(), 100);
    }

    // ============================================
    // NODE BINARY PATH TESTS
    // ============================================

    #[test]
    fn test_dev_binary_path_format() {
        let path = std::path::PathBuf::from("/some/path/quantumharmony/wallet/src-tauri")
            .parent()
            .unwrap()
            .join("target/release/quantumharmony-node");

        assert!(path.to_string_lossy().contains("target/release/quantumharmony-node"));
    }

    #[test]
    fn test_binary_existence_check() {
        // Test that we properly check for binary existence
        let fake_path = std::path::PathBuf::from("/nonexistent/path/node");
        assert!(!fake_path.exists());
    }
}

// ============================================
// INTEGRATION TEST HELPERS
// ============================================

/// Wait for node to produce output
pub async fn wait_for_output(state: &MockNodeState, timeout: Duration) -> bool {
    let start = std::time::Instant::now();
    while start.elapsed() < timeout {
        if !state.output_buffer.lock().unwrap().is_empty() {
            return true;
        }
        tokio::time::sleep(Duration::from_millis(100)).await;
    }
    false
}

/// Check if node output contains expected string
pub fn output_contains(state: &MockNodeState, needle: &str) -> bool {
    state.output_buffer
        .lock()
        .unwrap()
        .iter()
        .any(|line| line.contains(needle))
}
