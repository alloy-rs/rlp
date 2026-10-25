//! Benchmarks for the RLP encoding and decoding hot paths.

#![allow(missing_docs)]

use alloy_rlp::{encode_list, length_of_length, list_length, Bytes, Decodable, Encodable, Header};
use alloy_rlp_derive::{RlpDecodable, RlpEncodable};
use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};

#[derive(RlpEncodable, RlpDecodable)]
struct LegacyTx {
    nonce: u64,
    gas_price: u128,
    gas_limit: u64,
    to: [u8; 20],
    value: u128,
    input: Bytes,
    v: u64,
    r: [u8; 32],
    s: [u8; 32],
}

#[derive(RlpEncodable, RlpDecodable)]
struct BlockHeader {
    parent_hash: [u8; 32],
    ommers_hash: [u8; 32],
    beneficiary: [u8; 20],
    state_root: [u8; 32],
    transactions_root: [u8; 32],
    receipts_root: [u8; 32],
    logs_bloom: [u8; 256],
    difficulty: u128,
    number: u64,
    gas_limit: u64,
    gas_used: u64,
    timestamp: u64,
    extra_data: Bytes,
    mix_hash: [u8; 32],
    nonce: [u8; 8],
}

fn legacy_tx() -> LegacyTx {
    LegacyTx {
        nonce: 0x1234,
        gas_price: 30_000_000_000,
        gas_limit: 21_000,
        to: [0xab; 20],
        value: 1_000_000_000_000_000_000,
        input: Bytes::from(vec![0xcd; 68]),
        v: 37,
        r: [0xef; 32],
        s: [0x12; 32],
    }
}

const fn block_header() -> BlockHeader {
    BlockHeader {
        parent_hash: [0x11; 32],
        ommers_hash: [0x22; 32],
        beneficiary: [0x33; 20],
        state_root: [0x44; 32],
        transactions_root: [0x55; 32],
        receipts_root: [0x66; 32],
        logs_bloom: [0x77; 256],
        difficulty: 0,
        number: 18_000_000,
        gas_limit: 30_000_000,
        gas_used: 15_000_000,
        timestamp: 1_700_000_000,
        extra_data: Bytes::from_static(b"alloy-rlp benchmark extra data"),
        mix_hash: [0x88; 32],
        nonce: [0; 8],
    }
}

fn encode_into<T: Encodable + ?Sized>(value: &T, buf: &mut Vec<u8>) {
    buf.clear();
    value.encode(buf);
}

fn bench_encode<T: Encodable + ?Sized>(c: &mut Criterion, name: &str, value: &T) {
    let mut buf = Vec::with_capacity(value.length());
    c.bench_function(&format!("encode/{name}"), |b| {
        b.iter(|| encode_into(black_box(value), &mut buf));
    });
}

fn bench_decode<T: Decodable + Encodable>(c: &mut Criterion, name: &str, value: &T) {
    let encoded = alloy_rlp::encode(value);
    c.bench_function(&format!("decode/{name}"), |b| {
        b.iter(|| T::decode(&mut black_box(encoded.as_slice())).unwrap());
    });
}

fn bench_length<T: Encodable + ?Sized>(c: &mut Criterion, name: &str, value: &T) {
    c.bench_function(&format!("length/{name}"), |b| b.iter(|| black_box(value).length()));
}

fn integers(c: &mut Criterion) {
    macro_rules! int {
        ($($name:literal => $value:expr),+ $(,)?) => {$(
            let value = $value;
            bench_encode(c, $name, &value);
            bench_decode(c, $name, &value);
            bench_length(c, $name, &value);
        )+};
    }

    int! {
        "u8/zero" => 0u8,
        "u8/small" => 0x7fu8,
        "u8/large" => 0xffu8,
        "u64/small" => 0x7fu64,
        "u64/large" => u64::MAX,
        "u128/small" => 0x7fu128,
        "u128/large" => u128::MAX,
    }
}

fn byte_strings(c: &mut Criterion) {
    let mut group = c.benchmark_group("bytes");
    for len in [0usize, 1, 32, 55, 56, 256, 1024, 65536] {
        let value = Bytes::from(vec![0xa5u8; len]);
        let encoded = alloy_rlp::encode(&value);
        let mut buf = Vec::with_capacity(encoded.len());
        group.throughput(Throughput::Bytes(len as u64));
        group.bench_with_input(BenchmarkId::new("encode", len), &value, |b, value| {
            b.iter(|| encode_into(black_box(value), &mut buf));
        });
        group.bench_with_input(BenchmarkId::new("decode", len), &encoded, |b, encoded| {
            b.iter(|| Bytes::decode(&mut black_box(encoded.as_slice())).unwrap());
        });
        group.bench_with_input(BenchmarkId::new("decode_bytes", len), &encoded, |b, encoded| {
            b.iter(|| Header::decode_bytes(&mut black_box(encoded.as_slice()), false).unwrap());
        });
        group.bench_with_input(BenchmarkId::new("length", len), &value, |b, value| {
            b.iter(|| black_box(value).length());
        });
    }
    group.finish();
}

fn headers(c: &mut Criterion) {
    let mut group = c.benchmark_group("header");
    for payload_length in [0usize, 1, 55, 56, 255, 256, 65535, 65536, 1 << 24] {
        for list in [false, true] {
            let kind = if list { "list" } else { "string" };
            let header = Header { list, payload_length };
            let mut encoded = Vec::new();
            header.encode(&mut encoded);
            // `Header::decode` checks that the payload is present.
            encoded.resize(encoded.len() + payload_length, 0);
            // Avoid decoding a one-byte string payload as a non-canonical single byte.
            if !list && payload_length == 1 {
                encoded[1] = 0x80;
            }
            let mut buf = Vec::with_capacity(8);
            let id = format!("{kind}/{payload_length}");
            group.bench_with_input(BenchmarkId::new("encode", &id), &header, |b, header| {
                b.iter(|| {
                    buf.clear();
                    black_box(header).encode(&mut buf);
                });
            });
            group.bench_with_input(BenchmarkId::new("decode", &id), &encoded, |b, encoded| {
                b.iter(|| Header::decode(&mut black_box(encoded.as_slice())).unwrap());
            });
            group.bench_with_input(BenchmarkId::new("length", &id), &header, |b, header| {
                b.iter(|| black_box(header).length());
            });
        }
    }
    group.bench_function("length_of_length", |b| {
        b.iter(|| {
            let mut sum = 0;
            for len in [0usize, 55, 56, 255, 256, 65536, 1 << 24] {
                sum += length_of_length(black_box(len));
            }
            sum
        });
    });
    group.finish();
}

fn lists(c: &mut Criterion) {
    let mut group = c.benchmark_group("list");
    for len in [1usize, 16, 256, 4096] {
        let ints: Vec<u64> =
            (0..len as u64).map(|i| i.wrapping_mul(0x9e37_79b9_7f4a_7c15)).collect();
        let strings: Vec<Bytes> = (0..len).map(|i| Bytes::from(vec![i as u8; 32])).collect();
        bench_list(&mut group, "u64", len, &ints);
        bench_list(&mut group, "bytes32", len, &strings);
    }
    group.finish();
}

fn bench_list<T: Encodable + Decodable>(
    group: &mut criterion::BenchmarkGroup<'_, criterion::measurement::WallTime>,
    name: &str,
    len: usize,
    items: &Vec<T>,
) {
    let encoded = alloy_rlp::encode(items);
    let mut buf = Vec::with_capacity(encoded.len());
    group.throughput(Throughput::Elements(len as u64));
    let id = |op: &str| BenchmarkId::new(format!("{op}/{name}"), len);
    group.bench_with_input(id("encode_list"), items, |b, items| {
        b.iter(|| {
            buf.clear();
            encode_list::<T, T>(black_box(items), &mut buf);
        });
    });
    group.bench_with_input(id("encode_vec"), items, |b, items| {
        b.iter(|| encode_into(black_box(items), &mut buf));
    });
    group.bench_with_input(id("list_length"), items, |b, items| {
        b.iter(|| list_length::<T, T>(black_box(items)));
    });
    group.bench_with_input(id("decode_vec"), &encoded, |b, encoded| {
        b.iter(|| Vec::<T>::decode(&mut black_box(encoded.as_slice())).unwrap());
    });
}

fn structs(c: &mut Criterion) {
    let tx = legacy_tx();
    bench_encode(c, "struct/legacy_tx", &tx);
    bench_decode(c, "struct/legacy_tx", &tx);
    bench_length(c, "struct/legacy_tx", &tx);

    let header = block_header();
    bench_encode(c, "struct/block_header", &header);
    bench_decode(c, "struct/block_header", &header);
    bench_length(c, "struct/block_header", &header);
}

criterion_group!(benches, integers, byte_strings, headers, lists, structs);
criterion_main!(benches);
