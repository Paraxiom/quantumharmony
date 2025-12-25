use pallet_runtime_segmentation::ternary::{TernaryCoordinates, TernarySegmentId};
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use codec::{Encode, Decode};

fn bench_ternary_encoding(c: &mut Criterion) {
    c.bench_function("ternary_encode_coordinates", |b| {
        b.iter(|| {
            TernaryCoordinates::encode(
                black_box(5),
                black_box(3),
                black_box(7),
            )
        })
    });

    c.bench_function("ternary_decode_coordinates", |b| {
        let coords = TernaryCoordinates::encode(5, 3, 7);
        b.iter(|| {
            black_box(coords).decode()
        })
    });

    c.bench_function("ternary_roundtrip_coordinates", |b| {
        b.iter(|| {
            let coords = TernaryCoordinates::encode(
                black_box(5),
                black_box(3),
                black_box(7),
            );
            black_box(coords.decode())
        })
    });
}

fn bench_segment_id_encoding(c: &mut Criterion) {
    c.bench_function("ternary_encode_segment_id", |b| {
        b.iter(|| {
            TernarySegmentId::encode(black_box(256))
        })
    });

    c.bench_function("ternary_decode_segment_id", |b| {
        let seg_id = TernarySegmentId::encode(256);
        b.iter(|| {
            black_box(seg_id).decode()
        })
    });
}

fn bench_codec_serialization(c: &mut Criterion) {
    c.bench_function("ternary_codec_encode", |b| {
        let coords = TernaryCoordinates::encode(5, 3, 7);
        b.iter(|| {
            black_box(coords).encode()
        })
    });

    c.bench_function("ternary_codec_decode", |b| {
        let coords = TernaryCoordinates::encode(5, 3, 7);
        let encoded = coords.encode();
        b.iter(|| {
            TernaryCoordinates::decode(&mut black_box(&encoded[..])).unwrap()
        })
    });

    c.bench_function("binary_tuple_encode", |b| {
        let coords = (5u8, 3u8, 7u8);
        b.iter(|| {
            black_box(coords).encode()
        })
    });

    c.bench_function("binary_tuple_decode", |b| {
        let coords = (5u8, 3u8, 7u8);
        let encoded = coords.encode();
        b.iter(|| {
            <(u8, u8, u8)>::decode(&mut black_box(&encoded[..])).unwrap()
        })
    });
}

criterion_group!(
    benches,
    bench_ternary_encoding,
    bench_segment_id_encoding,
    bench_codec_serialization
);
criterion_main!(benches);
