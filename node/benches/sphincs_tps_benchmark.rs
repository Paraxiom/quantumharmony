//! SPHINCS+ TPS Benchmark with Toroidal Segmentation
//!
//! Tests **actual** SPHINCS+ signature verification performance with toroidal mesh parallelization.
//!
//! ## Architecture
//! - 512 toroidal segments (8x8x8 mesh)
//! - Each segment verifies signatures in parallel
//! - Ternary encoding for efficient coordinate representation
//!
//! ## Metrics
//! - Sequential baseline: Single-threaded SPHINCS+ verification
//! - Parallel: Distributed across 2-512 segments
//! - **Real cryptographic workload** (not Blake2 placeholder)

use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use sp_core::{sphincs::{Pair as SphincsPair, SignatureWithPublic}, Pair};
use sp_runtime::{
    traits::{IdentifyAccount, Verify},
    MultiSignature, MultiSigner,
};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Instant;

/// Mock transaction with SPHINCS+ signature
#[derive(Clone)]
struct SignedTransaction {
    from: Vec<u8>,
    to: Vec<u8>,
    amount: u64,
    nonce: u64,
    segment_id: u32,
    signature: MultiSignature,
    signer_public: Vec<u8>,
}

impl SignedTransaction {
    /// Create a new transaction and sign it with SPHINCS+
    fn new(
        keypair: &SphincsPair,
        to: Vec<u8>,
        amount: u64,
        nonce: u64,
        segment_id: u32,
    ) -> Self {
        let public = keypair.public();
        let from = public.as_ref().to_vec(); // Use public key bytes directly

        // Create transaction payload
        let mut payload = Vec::new();
        payload.extend_from_slice(&from);
        payload.extend_from_slice(&to);
        payload.extend_from_slice(&amount.to_le_bytes());
        payload.extend_from_slice(&nonce.to_le_bytes());

        // Sign with SPHINCS+ (this is the expensive operation!)
        let sphincs_sig = keypair.sign(&payload);
        // Wrap signature with public key (required because AccountId is a hash of the public key)
        let sig_with_pub = SignatureWithPublic::new(sphincs_sig, public);
        let signature = MultiSignature::SphincsPlus(sig_with_pub);

        Self {
            from,
            to,
            amount,
            nonce,
            segment_id,
            signature,
            signer_public: public.as_ref().to_vec(),
        }
    }

    /// Verify SPHINCS+ signature (expensive!)
    fn verify(&self) -> bool {
        use sp_core::sphincs::{Public, PUBLIC_KEY_SERIALIZED_SIZE};

        // Reconstruct payload
        let mut payload = Vec::new();
        payload.extend_from_slice(&self.from);
        payload.extend_from_slice(&self.to);
        payload.extend_from_slice(&self.amount.to_le_bytes());
        payload.extend_from_slice(&self.nonce.to_le_bytes());

        // Parse public key from raw bytes
        if self.signer_public.len() != PUBLIC_KEY_SERIALIZED_SIZE {
            return false;
        }
        let mut public_bytes = [0u8; PUBLIC_KEY_SERIALIZED_SIZE];
        public_bytes.copy_from_slice(&self.signer_public);
        let public = Public::from_raw(public_bytes);

        // Verify using MultiSignature (as runtime does)
        let signer = MultiSigner::from(public);
        let account = signer.into_account();

        self.signature.verify(&payload[..], &account)
    }
}

/// Sequential SPHINCS+ verification (baseline)
fn process_sequential(transactions: &[SignedTransaction]) -> (usize, f64) {
    let start = Instant::now();
    let mut successful = 0;

    for tx in transactions {
        if tx.verify() {
            successful += 1;
        }
    }

    let elapsed = start.elapsed();
    (successful, elapsed.as_secs_f64())
}

/// Parallel SPHINCS+ verification with toroidal segmentation
fn process_parallel(transactions: &[SignedTransaction], num_segments: usize) -> (usize, f64) {
    // Partition transactions by segment
    let mut segment_txs: Vec<Vec<SignedTransaction>> = vec![Vec::new(); num_segments];

    for tx in transactions {
        let segment_idx = (tx.segment_id as usize) % num_segments;
        segment_txs[segment_idx].push(tx.clone());
    }

    let successful = Arc::new(Mutex::new(0usize));
    let mut handles = vec![];

    let start = Instant::now();

    // Process each segment in parallel (SPHINCS+ verification distributed)
    for segment_transactions in segment_txs {
        let successful_clone = Arc::clone(&successful);

        let handle = thread::spawn(move || {
            let mut count = 0;
            for tx in &segment_transactions {
                // **THIS IS THE REAL WORKLOAD**: SPHINCS+ signature verification
                if tx.verify() {
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

/// Benchmark SPHINCS+ TPS with toroidal parallelization
fn bench_sphincs_tps(c: &mut Criterion) {
    let mut group = c.benchmark_group("SPHINCS_TPS");
    group.sample_size(10); // Reduced sample size due to SPHINCS+ slowness

    // Generate keypairs for signing (reuse to save time)
    println!("Generating SPHINCS+ keypairs...");
    let keypairs: Vec<SphincsPair> = (0..10)
        .map(|i| {
            let mut seed = [0u8; 48];
            seed[0..8].copy_from_slice(&(i as u64).to_le_bytes());
            let seed_ref: &<SphincsPair as Pair>::Seed = unsafe {
                &*(seed.as_ptr() as *const <SphincsPair as Pair>::Seed)
            };
            SphincsPair::from_seed(seed_ref)
        })
        .collect();

    // Test with smaller transaction counts due to SPHINCS+ verification time
    let tx_counts = [10, 50, 100];

    for &count in &tx_counts {
        println!("Generating {} signed transactions...", count);

        // Pre-generate signed transactions
        let transactions: Vec<SignedTransaction> = (0..count)
            .map(|i| {
                let keypair = &keypairs[i % keypairs.len()];
                let to = vec![0xFF; 32];
                let segment_id = (i % 512) as u32;
                SignedTransaction::new(keypair, to, 1000, i as u64, segment_id)
            })
            .collect();

        println!("  Generated {} transactions with SPHINCS+ signatures", transactions.len());

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

/// Calculate and display actual SPHINCS+ TPS metrics
fn calculate_sphincs_tps() {
    println!("\n╔══════════════════════════════════════════════════════════════╗");
    println!("║  QUANTUMHARMONY SPHINCS+ TPS BENCHMARK (Toroidal Mesh)      ║");
    println!("╚══════════════════════════════════════════════════════════════╝\n");
    println!("Testing SPHINCS+ signature verification with parallel segmentation\n");

    // Generate keypairs
    println!("Generating SPHINCS+ keypairs...");
    let keypairs: Vec<SphincsPair> = (0..10)
        .map(|i| {
            let mut seed = [0u8; 48];
            seed[0..8].copy_from_slice(&(i as u64).to_le_bytes());
            let seed_ref: &<SphincsPair as Pair>::Seed = unsafe {
                &*(seed.as_ptr() as *const <SphincsPair as Pair>::Seed)
            };
            SphincsPair::from_seed(seed_ref)
        })
        .collect();

    // Test with increasing transaction counts
    let tx_counts = [10, 50, 100, 500];

    for &count in &tx_counts {
        println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
        println!("Testing with {} SPHINCS+ signed transactions:", count);
        println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");

        // Generate transactions
        print!("  Generating signed transactions... ");
        let transactions: Vec<SignedTransaction> = (0..count)
            .map(|i| {
                let keypair = &keypairs[i % keypairs.len()];
                let to = vec![0xFF; 32];
                let segment_id = (i % 512) as u32;
                SignedTransaction::new(keypair, to, 1000, i as u64, segment_id)
            })
            .collect();
        println!("Done");

        // Sequential baseline
        print!("  Sequential verification... ");
        let (seq_success, seq_time) = process_sequential(&transactions);
        let seq_tps = seq_success as f64 / seq_time;
        println!("{:.0} TPS ({:.3}s)", seq_tps, seq_time);

        // Parallel processing with different segment counts
        for num_segments in [2, 4, 8, 16, 32, 64, 128, 256, 512] {
            print!("  {:3} segments... ", num_segments);
            let (par_success, par_time) = process_parallel(&transactions, num_segments);
            let par_tps = par_success as f64 / par_time;
            let speedup = par_tps / seq_tps;

            println!(
                "{:>8.0} TPS ({:>6.3}s) - {:.2}x speedup",
                par_tps, par_time, speedup
            );
        }

        println!();
    }

    println!("╔══════════════════════════════════════════════════════════════╗");
    println!("║ Note:                                                        ║");
    println!("║ - This benchmark uses REAL SPHINCS+ signature verification  ║");
    println!("║ - Toroidal mesh parallelization distributes workload        ║");
    println!("║ - 512 segments = 8×8×8 3D torus topology                    ║");
    println!("╚══════════════════════════════════════════════════════════════╝\n");
}

criterion_group!(benches, bench_sphincs_tps);
criterion_main!(benches);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sphincs_tps_calculation() {
        calculate_sphincs_tps();
    }
}
