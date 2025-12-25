//! Benchmarks for Ternary and Quaternary Encoding
//!
//! Measures performance improvements from:
//! - Ternary coordinate encoding vs binary
//! - Quaternary checksums vs binary
//! - Size comparisons

use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use pallet_runtime_segmentation::{
    ternary::{TernaryCoordinates, TernarySegmentId},
    quaternary::{QuaternaryChecksum, compute_checksum},
    SegmentCoordinates, coordinates_to_id, id_to_coordinates,
};
use codec::{Encode, Decode};

/// Benchmark ternary coordinate encoding
fn bench_ternary_encoding(c: &mut Criterion) {
    let mut group = c.benchmark_group("ternary_coordinate_encoding");

    // Test with various coordinate values
    let coords = vec![
        (0, 0, 0),
        (3, 4, 5),
        (7, 7, 7),
    ];

    for (x, y, z) in coords {
        group.bench_with_input(
            BenchmarkId::new("encode", format!("({},{},{})", x, y, z)),
            &(x, y, z),
            |b, &(x, y, z)| {
                b.iter(|| {
                    let encoded = TernaryCoordinates::encode(black_box(x), black_box(y), black_box(z));
                    black_box(encoded);
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("decode", format!("({},{},{})", x, y, z)),
            &(x, y, z),
            |b, &(x, y, z)| {
                let encoded = TernaryCoordinates::encode(x, y, z);
                b.iter(|| {
                    let decoded = black_box(&encoded).decode();
                    black_box(decoded);
                });
            },
        );
    }

    group.finish();
}

/// Benchmark binary coordinate encoding (baseline)
fn bench_binary_encoding(c: &mut Criterion) {
    let mut group = c.benchmark_group("binary_coordinate_encoding");

    let coords = vec![
        SegmentCoordinates { x: 0, y: 0, z: 0 },
        SegmentCoordinates { x: 3, y: 4, z: 5 },
        SegmentCoordinates { x: 7, y: 7, z: 7 },
    ];

    for coord in coords {
        group.bench_with_input(
            BenchmarkId::new("encode", format!("({},{},{})", coord.x, coord.y, coord.z)),
            &coord,
            |b, coord| {
                b.iter(|| {
                    let encoded = black_box(coord).encode();
                    black_box(encoded);
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("decode", format!("({},{},{})", coord.x, coord.y, coord.z)),
            &coord,
            |b, coord| {
                let encoded = coord.encode();
                b.iter(|| {
                    let decoded = SegmentCoordinates::decode(&mut &encoded[..]).unwrap();
                    black_box(decoded);
                });
            },
        );
    }

    group.finish();
}

/// Benchmark segment ID encoding
fn bench_segment_id_encoding(c: &mut Criterion) {
    let mut group = c.benchmark_group("segment_id_encoding");

    let ids = vec![0, 256, 511];

    for id in ids {
        // Ternary encoding
        group.bench_with_input(
            BenchmarkId::new("ternary_encode", id),
            &id,
            |b, &id| {
                b.iter(|| {
                    let encoded = TernarySegmentId::encode(black_box(id));
                    black_box(encoded);
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("ternary_decode", id),
            &id,
            |b, &id| {
                let encoded = TernarySegmentId::encode(id);
                b.iter(|| {
                    let decoded = black_box(&encoded).decode();
                    black_box(decoded);
                });
            },
        );

        // Binary encoding (baseline)
        group.bench_with_input(
            BenchmarkId::new("binary_encode", id),
            &id,
            |b, &id| {
                b.iter(|| {
                    let encoded = black_box(id).encode();
                    black_box(encoded);
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("binary_decode", id),
            &id,
            |b, &id| {
                let encoded = id.encode();
                b.iter(|| {
                    let decoded = u32::decode(&mut &encoded[..]).unwrap();
                    black_box(decoded);
                });
            },
        );
    }

    group.finish();
}

/// Benchmark quaternary checksums
fn bench_quaternary_checksum(c: &mut Criterion) {
    let mut group = c.benchmark_group("quaternary_checksum");

    let data_sizes = vec![32, 128, 512, 2048];

    for size in data_sizes {
        let data: Vec<u8> = (0..size).map(|i| (i % 256) as u8).collect();

        group.bench_with_input(
            BenchmarkId::new("compute", size),
            &data,
            |b, data| {
                b.iter(|| {
                    let checksum = compute_checksum(black_box(data));
                    black_box(checksum);
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("verify", size),
            &data,
            |b, data| {
                let checksum1 = compute_checksum(data);
                let checksum2 = compute_checksum(data);
                b.iter(|| {
                    let result = black_box(&checksum1).verify(black_box(&checksum2));
                    black_box(result);
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("hamming_distance", size),
            &data,
            |b, data| {
                let checksum1 = compute_checksum(data);
                let mut data2 = data.clone();
                data2[0] ^= 0xFF; // Flip some bits
                let checksum2 = compute_checksum(&data2);
                b.iter(|| {
                    let dist = black_box(&checksum1).hamming_distance(black_box(&checksum2));
                    black_box(dist);
                });
            },
        );
    }

    group.finish();
}

/// Benchmark DNA encoding
fn bench_dna_encoding(c: &mut Criterion) {
    let mut group = c.benchmark_group("dna_encoding");

    let quarts = [0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3];
    let checksum = QuaternaryChecksum::from_quarts(quarts).unwrap();

    group.bench_function("to_dna_string", |b| {
        b.iter(|| {
            let dna = black_box(&checksum).to_dna_string();
            black_box(dna);
        });
    });

    let dna = b"ATGCATGCATGCATGC";
    group.bench_function("from_dna_string", |b| {
        b.iter(|| {
            let checksum = QuaternaryChecksum::from_dna_string(black_box(dna)).unwrap();
            black_box(checksum);
        });
    });

    group.finish();
}

/// Benchmark size comparison
fn bench_size_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("size_comparison");

    // Measure encoding sizes
    group.bench_function("ternary_coords_size", |b| {
        let coords = TernaryCoordinates::encode(7, 7, 7);
        b.iter(|| {
            let encoded = black_box(&coords).encode();
            black_box(encoded.len());
        });
    });

    group.bench_function("binary_coords_size", |b| {
        let coords = SegmentCoordinates { x: 7, y: 7, z: 7 };
        b.iter(|| {
            let encoded = black_box(&coords).encode();
            black_box(encoded.len());
        });
    });

    group.bench_function("ternary_segment_id_size", |b| {
        let id = TernarySegmentId::encode(511);
        b.iter(|| {
            let encoded = black_box(&id).encode();
            black_box(encoded.len());
        });
    });

    group.bench_function("binary_segment_id_size", |b| {
        let id = 511u32;
        b.iter(|| {
            let encoded = black_box(&id).encode();
            black_box(encoded.len());
        });
    });

    group.finish();
}

/// Benchmark exhaustive coordinate encoding
fn bench_all_coordinates(c: &mut Criterion) {
    let mut group = c.benchmark_group("all_coordinates");
    group.sample_size(10); // Reduce sample size for exhaustive test

    group.bench_function("ternary_all_512", |b| {
        b.iter(|| {
            for x in 0..8u8 {
                for y in 0..8u8 {
                    for z in 0..8u8 {
                        let coords = TernaryCoordinates::encode(x, y, z);
                        let (x2, y2, z2) = coords.decode();
                        black_box((x2, y2, z2));
                    }
                }
            }
        });
    });

    group.bench_function("binary_all_512", |b| {
        b.iter(|| {
            for id in 0..512u32 {
                let coords = id_to_coordinates(id);
                let id2 = coordinates_to_id(&coords);
                black_box(id2);
            }
        });
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_ternary_encoding,
    bench_binary_encoding,
    bench_segment_id_encoding,
    bench_quaternary_checksum,
    bench_dna_encoding,
    bench_size_comparison,
    bench_all_coordinates,
);
criterion_main!(benches);
