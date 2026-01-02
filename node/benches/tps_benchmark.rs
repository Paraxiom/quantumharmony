//! TPS Benchmark for QuantumHarmony
//!
//! Tests transaction throughput with different parallelization strategies:
//! - Sequential processing (baseline)
//! - Parallel processing with 2-512 segments
//!
//! Based on 8x8x8 toroidal mesh architecture for parallel processing

use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use sp_core::{ed25519, Pair, H256};
use sp_runtime::traits::{BlakeTwo256, Hash};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Instant;

/// Mock transaction for benchmarking
#[derive(Clone)]
struct MockTransaction {
    from: [u8; 32],
    to: [u8; 32],
    amount: u64,
    nonce: u64,
    segment_id: u32,
}

impl MockTransaction {
    fn new(from: [u8; 32], to: [u8; 32], amount: u64, nonce: u64) -> Self {
        // Assign to segment based on sender address (first byte)
        let segment_id = (from[0] as u32) % 512;
        Self {
            from,
            to,
            amount,
            nonce,
            segment_id,
        }
    }

    /// Compute transaction hash (simulates processing work)
    fn hash(&self) -> H256 {
        let mut data = Vec::new();
        data.extend_from_slice(&self.from);
        data.extend_from_slice(&self.to);
        data.extend_from_slice(&self.amount.to_le_bytes());
        data.extend_from_slice(&self.nonce.to_le_bytes());
        BlakeTwo256::hash(&data)
    }

    /// Verify transaction (simulates signature verification)
    fn verify(&self) -> bool {
        // Simulate verification work with hashing
        let _hash = self.hash();
        true
    }
}

/// Sequential transaction processing (baseline)
fn process_sequential(transactions: &[MockTransaction]) -> (usize, f64) {
    let start = Instant::now();
    let mut successful = 0;

    for tx in transactions {
        if tx.verify() {
            let _hash = tx.hash();
            successful += 1;
        }
    }

    let elapsed = start.elapsed();
    (successful, elapsed.as_secs_f64())
}

/// Parallel transaction processing with segmentation
fn process_parallel(transactions: &[MockTransaction], num_segments: usize) -> (usize, f64) {
    // Partition transactions by segment
    let mut segment_txs: Vec<Vec<MockTransaction>> = vec![Vec::new(); num_segments];

    for tx in transactions {
        let segment_idx = (tx.segment_id as usize) % num_segments;
        segment_txs[segment_idx].push(tx.clone());
    }

    let successful = Arc::new(Mutex::new(0usize));
    let mut handles = vec![];

    let start = Instant::now();

    // Process each segment in parallel
    for segment_transactions in segment_txs {
        let successful_clone = Arc::clone(&successful);

        let handle = thread::spawn(move || {
            let mut count = 0;
            for tx in &segment_transactions {
                if tx.verify() {
                    let _hash = tx.hash();
                    count += 1;
                }
            }

            let mut total = successful_clone.lock().unwrap();
            *total += count;
        });
        handles.push(handle);
    }

    // Wait for all segments to complete
    for handle in handles {
        handle.join().unwrap();
    }

    let elapsed = start.elapsed();
    let total_successful = *successful.lock().unwrap();

    (total_successful, elapsed.as_secs_f64())
}

/// Benchmark different TPS scenarios
fn bench_tps(c: &mut Criterion) {
    let mut group = c.benchmark_group("TPS");

    let tx_counts = [100, 500, 1000, 5000, 10000];

    for &count in &tx_counts {
        // Generate mock transactions
        let transactions: Vec<MockTransaction> = (0..count)
            .map(|i| {
                let from = {
                    let mut addr = [0u8; 32];
                    addr[0..8].copy_from_slice(&(i as u64).to_le_bytes());
                    addr
                };
                let to = {
                    let mut addr = [0u8; 32];
                    addr[0..8].copy_from_slice(&((i + 1) as u64).to_le_bytes());
                    addr
                };
                MockTransaction::new(from, to, 1000, i as u64)
            })
            .collect();

        // Benchmark sequential processing
        group.bench_with_input(
            BenchmarkId::new("Sequential", count),
            &count,
            |b, _| {
                b.iter(|| {
                    let (successful, _) = process_sequential(black_box(&transactions));
                    black_box(successful);
                });
            },
        );

        // Benchmark parallel processing with different segment counts
        for num_segments in [2, 4, 8, 16, 32, 64, 128, 256, 512] {
            group.bench_with_input(
                BenchmarkId::new(format!("Parallel-{}-segments", num_segments), count),
                &count,
                |b, _| {
                    b.iter(|| {
                        let (successful, _) =
                            process_parallel(black_box(&transactions), num_segments);
                        black_box(successful);
                    });
                },
            );
        }
    }

    group.finish();
}

/// Calculate and display TPS metrics
fn calculate_tps() {
    println!("\n=== QUANTUMHARMONY TPS BENCHMARK ===\n");
    println!("Testing transaction throughput with toroidal mesh segmentation\n");

    let tx_counts = [1000, 5000, 10000, 30000];

    for &count in &tx_counts {
        println!("Testing with {} transactions:", count);

        // Generate transactions
        let transactions: Vec<MockTransaction> = (0..count)
            .map(|i| {
                let from = {
                    let mut addr = [0u8; 32];
                    addr[0..8].copy_from_slice(&(i as u64).to_le_bytes());
                    addr
                };
                let to = {
                    let mut addr = [0u8; 32];
                    addr[0..8].copy_from_slice(&((i + 1) as u64).to_le_bytes());
                    addr
                };
                MockTransaction::new(from, to, 1000, i as u64)
            })
            .collect();

        // Sequential baseline
        let (seq_success, seq_time) = process_sequential(&transactions);
        let seq_tps = seq_success as f64 / seq_time;

        println!("  Sequential: {:.0} TPS ({:.3}s)", seq_tps, seq_time);

        // Parallel processing with different segment counts
        for num_segments in [2, 4, 8, 16, 64, 256, 512] {
            let (par_success, par_time) = process_parallel(&transactions, num_segments);
            let par_tps = par_success as f64 / par_time;
            let speedup = par_tps / seq_tps;

            println!(
                "  {:3} segments: {:.0} TPS ({:.3}s) - {:.2}x speedup",
                num_segments, par_tps, par_time, speedup
            );
        }

        println!();
    }

    println!("Note: This benchmark uses Blake2 hashing to simulate transaction processing");
    println!("Actual TPS with SPHINCS+ signatures will be lower due to verification overhead\n");
}

criterion_group!(benches, bench_tps);
criterion_main!(benches);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tps_calculation() {
        calculate_tps();
    }
}
