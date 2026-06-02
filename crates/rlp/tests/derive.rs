//! Tests for the derive macros.

#![cfg(feature = "derive")]
#![allow(dead_code)]

use alloy_rlp::*;

fn assert_err_kind<T>(result: alloy_rlp::Result<T>, expected: ErrorKind) {
    match result {
        Ok(_) => panic!("expected {expected:?} error"),
        Err(err) => assert_eq!(err.kind(), expected),
    }
}

fn decode<T>(bytes: impl AsRef<[u8]>) -> alloy_rlp::Result<T>
where
    T: for<'de> RlpDecodable<'de>,
{
    alloy_rlp::decode_exact(bytes)
}

fn manual_list(fields: &[Vec<u8>]) -> Vec<u8> {
    let payload_length = fields.iter().map(Vec::len).sum();
    let mut out = Vec::new();
    Header { list: true, payload_length }.encode(&mut Encoder::new(&mut out));
    for field in fields {
        out.extend_from_slice(field);
    }
    out
}

fn assert_manual_list_encoding<T>(value: &T, fields: &[Vec<u8>])
where
    T: RlpEncodable + for<'de> RlpDecodable<'de> + PartialEq + std::fmt::Debug,
{
    let encoded = alloy_rlp::encode(value);
    assert_eq!(encoded, manual_list(fields));

    let decoded = decode::<T>(&encoded).unwrap();
    assert_eq!(&decoded, value);
}

#[test]
fn simple_derive() {
    #[derive(RlpEncodable, RlpDecodable, RlpMaxEncodedLen, PartialEq, Debug)]
    struct MyThing(#[rlp] [u8; 12]);

    let thing = MyThing([0; 12]);

    // roundtrip fidelity
    let mut buf = Vec::new();
    thing.rlp_encode(&mut Encoder::new(&mut buf));
    let decoded = decode::<MyThing>(&buf).unwrap();
    assert_eq!(thing, decoded);

    // does not panic on short input
    assert_err_kind(decode::<MyThing>([0x8c; 11]), ErrorKind::InputTooShort)
}

#[test]
const fn wrapper() {
    #[derive(RlpEncodableWrapper, RlpDecodableWrapper, RlpMaxEncodedLen, PartialEq, Debug)]
    struct Wrapper([u8; 8]);

    #[derive(RlpEncodableWrapper, RlpDecodableWrapper, PartialEq, Debug)]
    struct ConstWrapper<const N: usize>([u8; N]);
}

#[test]
const fn generics() {
    trait LT<'a> {}

    #[derive(RlpEncodable, RlpDecodable, RlpMaxEncodedLen)]
    struct Generic<T, U: for<'a> LT<'a>, V: Default, const N: usize>(T, usize, U, V, [u8; N])
    where
        U: std::fmt::Display;

    #[derive(RlpEncodableWrapper, RlpDecodableWrapper, RlpMaxEncodedLen)]
    struct GenericWrapper<T>(T)
    where
        T: Sized;
}

#[test]
const fn opt() {
    #[derive(RlpEncodable, RlpDecodable)]
    #[rlp(trailing)]
    struct Options<T>(Option<Vec<T>>);

    #[derive(RlpEncodable, RlpDecodable)]
    #[rlp(trailing)]
    struct Options2<T> {
        a: Option<T>,
        #[rlp(default)]
        b: Option<T>,
    }
}

/// Test that multiple attributes can be combined in a single `#[rlp(...)]`.
/// See <https://github.com/alloy-rs/rlp/issues/9>
#[test]
fn multiple_attrs_combined() {
    /// A type that intentionally does NOT implement `RlpEncodable` or `RlpDecodable`.
    /// This verifies that `#[rlp(default, skip)]` works for such types.
    #[derive(PartialEq, Debug, Default)]
    struct Cache(u64);

    // Test `#[rlp(default, skip)]` order
    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    struct Foo {
        pub bar: u64,
        #[rlp(default, skip)]
        pub cache: Cache,
    }

    let foo = Foo { bar: 42, cache: Cache(123) };

    let mut buf = Vec::new();
    foo.rlp_encode(&mut Encoder::new(&mut buf));

    let decoded = decode::<Foo>(&buf).unwrap();
    assert_eq!(decoded.bar, 42);
    assert_eq!(decoded.cache, Cache::default());

    // Test `#[rlp(skip, default)]` reverse order
    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    struct Bar {
        pub baz: u64,
        #[rlp(skip, default)]
        pub cache: Cache,
    }

    let bar = Bar { baz: 99, cache: Cache(456) };

    let mut buf2 = Vec::new();
    bar.rlp_encode(&mut Encoder::new(&mut buf2));

    let decoded2 = decode::<Bar>(&buf2).unwrap();
    assert_eq!(decoded2.baz, 99);
    assert_eq!(decoded2.cache, Cache::default());
}

/// Test that `#[rlp(skip)]` alone works.
#[test]
fn skip_field() {
    #[derive(PartialEq, Debug, Default)]
    struct NotEncodable(u64);

    #[derive(RlpEncodable, PartialEq, Debug)]
    struct WithSkip {
        pub value: u64,
        #[rlp(skip)]
        pub skipped: NotEncodable,
    }

    let s = WithSkip { value: 42, skipped: NotEncodable(123) };

    let mut buf = Vec::new();
    s.rlp_encode(&mut Encoder::new(&mut buf));

    // Decode as a struct without the skipped field to verify it wasn't encoded
    #[derive(RlpDecodable, PartialEq, Debug)]
    struct WithoutSkip {
        pub value: u64,
    }

    let decoded = decode::<WithoutSkip>(&buf).unwrap();
    assert_eq!(decoded.value, 42);
}

#[test]
fn tuple_roundtrips_and_raw_modes() {
    fn check<T>(value: T)
    where
        T: RlpEncodable + for<'de> RlpDecodable<'de> + PartialEq + std::fmt::Debug,
    {
        let encoded = alloy_rlp::encode(&value);
        assert_eq!(encoded.len(), value.rlp_len());
        let decoded = decode::<T>(&encoded).unwrap();
        assert_eq!(decoded, value);

        let mut raw = Vec::new();
        value.rlp_encode_raw(&mut Encoder::new(&mut raw));
        assert_eq!(raw.len(), value.rlp_len_raw());
        let mut raw_decoder = Decoder::new(&raw);
        let decoded_raw = T::rlp_decode_raw(&mut raw_decoder).unwrap();
        assert_eq!(decoded_raw, value);
        assert!(raw_decoder.is_empty());
        assert_ne!(encoded, raw);
    }

    check((1u8,));
    check((1u8, 2u16));
    check((1u8, 2u16, 3u32));
    check((1u8, 2u16, 3u32, 4u64));
    check((1u8, 2u16, 3u32, 4u64, 5usize));
    check((1u8, 2u16, 3u32, 4u64, 5usize, 6u128));
    check((1u8, 2u16, 3u32, 4u64, 5usize, 6u128, true));
    check((1u8, 2u16, 3u32, 4u64, 5usize, 6u128, true, [7u8; 1]));
    check((1u8, 2u16, 3u32, 4u64, 5usize, 6u128, true, [7u8; 1], [8u8; 2]));
    check((1u8, 2u16, 3u32, 4u64, 5usize, 6u128, true, [7u8; 1], [8u8; 2], String::from("nine")));
    check((
        1u8,
        2u16,
        3u32,
        4u64,
        5usize,
        6u128,
        true,
        [7u8; 1],
        [8u8; 2],
        String::from("nine"),
        Bytes::from(vec![10u8]),
    ));
    check((
        1u8,
        2u16,
        3u32,
        4u64,
        5usize,
        6u128,
        true,
        [7u8; 1],
        [8u8; 2],
        String::from("nine"),
        Bytes::from(vec![10u8]),
        BytesMut::from(&b"eleven"[..]),
    ));
}

#[test]
fn tuple_decode_rejects_malformed_lists() {
    let too_few = alloy_rlp::encode((1u8,));
    assert_err_kind(decode::<(u8, u8)>(&too_few), ErrorKind::InputTooShort);

    let extra = alloy_rlp::encode((1u8, 2u8));
    assert_err_kind(decode::<(u8,)>(&extra), ErrorKind::ListLengthMismatch { expected: 2, got: 1 });

    assert_err_kind(decode::<(u8,)>([0x01]), ErrorKind::UnexpectedString);
}

#[test]
fn tuple_raw_decode_leaves_outer_fields() {
    let mut raw = Vec::new();
    (1u8, 2u8).rlp_encode_raw(&mut Encoder::new(&mut raw));
    3u8.rlp_encode(&mut Encoder::new(&mut raw));

    let mut decoder = Decoder::new(&raw);
    let tuple = <(u8, u8)>::rlp_decode_raw(&mut decoder).unwrap();
    let tail = u8::rlp_decode(&mut decoder).unwrap();
    assert_eq!(tuple, (1, 2));
    assert_eq!(tail, 3);
    assert!(decoder.is_empty());
}

#[test]
fn flatten_nested_vs_flat_encoding() {
    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    struct Inner {
        a: u64,
        b: u64,
    }

    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    struct OuterNested {
        x: u64,
        inner: Inner,
    }

    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    struct OuterFlat {
        x: u64,
        #[rlp(flatten)]
        inner: Inner,
    }

    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    struct Equivalent {
        x: u64,
        a: u64,
        b: u64,
    }

    let nested = OuterNested { x: 1, inner: Inner { a: 2, b: 3 } };
    let flat = OuterFlat { x: 1, inner: Inner { a: 2, b: 3 } };
    let equivalent = Equivalent { x: 1, a: 2, b: 3 };

    let nested_encoded = alloy_rlp::encode(&nested);
    let flat_encoded = alloy_rlp::encode(&flat);
    assert_ne!(nested_encoded, flat_encoded);
    assert_eq!(flat_encoded, alloy_rlp::encode(&equivalent));
    assert_eq!(decode::<OuterFlat>(&flat_encoded).unwrap(), flat);
}

#[test]
fn flatten_multiple_and_tuple_fields() {
    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    struct A {
        x: u64,
    }

    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    struct B {
        y: u16,
        z: u64,
    }

    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    struct Combined {
        #[rlp(flatten)]
        a: A,
        #[rlp(flatten)]
        pair: (u8, u16),
        #[rlp(flatten)]
        b: B,
    }

    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    struct Flat {
        x: u64,
        pair_0: u8,
        pair_1: u16,
        y: u16,
        z: u64,
    }

    let value = Combined { a: A { x: 10 }, pair: (11, 12), b: B { y: 20, z: 30 } };
    let flat = Flat { x: 10, pair_0: 11, pair_1: 12, y: 20, z: 30 };

    let encoded = alloy_rlp::encode(&value);
    assert_eq!(encoded, alloy_rlp::encode(&flat));
    assert_eq!(decode::<Combined>(&encoded).unwrap(), value);
}

#[test]
fn flatten_with_skip_default_fields() {
    #[derive(PartialEq, Debug, Default)]
    struct Cache(u64);

    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    struct Inner {
        a: u64,
        #[rlp(default, skip)]
        cache: Cache,
    }

    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    struct Outer {
        #[rlp(flatten)]
        inner: Inner,
        b: u64,
        #[rlp(skip)]
        cache: Cache,
    }

    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    struct Flat {
        a: u64,
        b: u64,
    }

    let value = Outer { inner: Inner { a: 1, cache: Cache(2) }, b: 3, cache: Cache(4) };
    let encoded = alloy_rlp::encode(&value);
    assert_eq!(encoded, alloy_rlp::encode(&Flat { a: 1, b: 3 }));

    let decoded = decode::<Outer>(&encoded).unwrap();
    assert_eq!(decoded.inner.a, 1);
    assert_eq!(decoded.inner.cache, Cache::default());
    assert_eq!(decoded.b, 3);
    assert_eq!(decoded.cache, Cache::default());
}

#[test]
fn trailing_optional_last_field_roundtrips_zero() {
    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    #[rlp(trailing)]
    struct S {
        x: u64,
        y: Option<u64>,
    }

    for value in [S { x: 1, y: None }, S { x: 1, y: Some(0) }, S { x: 1, y: Some(2) }] {
        let encoded = alloy_rlp::encode(&value);
        assert_eq!(decode::<S>(&encoded).unwrap(), value);
    }
}

#[test]
fn flattened_trailing_options_do_not_consume_outer_fields() {
    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    #[rlp(trailing)]
    struct Inner {
        a: u64,
        maybe: Option<u64>,
        later: Option<u64>,
    }

    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    struct Outer {
        #[rlp(flatten)]
        inner: Inner,
        tail: u64,
    }

    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    struct Flat {
        a: u64,
        maybe: u64,
        later: u64,
        tail: u64,
    }

    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    struct FlatWithoutLater {
        a: u64,
        maybe: u64,
        tail: u64,
    }

    let value = Outer { inner: Inner { a: 1, maybe: Some(2), later: Some(4) }, tail: 3 };
    let encoded = alloy_rlp::encode(&value);
    assert_eq!(encoded, alloy_rlp::encode(&Flat { a: 1, maybe: 2, later: 4, tail: 3 }));

    let decoded = decode::<Outer>(&encoded).unwrap();
    assert_eq!(decoded, value);

    let zero_then_tail = Outer { inner: Inner { a: 1, maybe: Some(0), later: None }, tail: 3 };
    let encoded = alloy_rlp::encode(&zero_then_tail);
    assert_eq!(encoded, alloy_rlp::encode(&FlatWithoutLater { a: 1, maybe: 0, tail: 3 }));
    assert_eq!(decode::<Outer>(&encoded).unwrap(), zero_then_tail);

    let sentinel_then_some = Outer { inner: Inner { a: 1, maybe: None, later: Some(2) }, tail: 3 };
    let encoded = alloy_rlp::encode(&sentinel_then_some);
    assert_eq!(encoded, alloy_rlp::encode(&Flat { a: 1, maybe: 0, later: 2, tail: 3 }));
    assert_eq!(decode::<Outer>(&encoded).unwrap(), sentinel_then_some);

    // `None, Some(2)` and `Some(0), Some(2)` have the same raw bytes because `0x80` is both the
    // gap sentinel and the RLP encoding of `0u64`. The bounded rule reserves following fields and
    // treats this shape as the gap form.
    let ambiguous_some_zero_then_some =
        Outer { inner: Inner { a: 1, maybe: Some(0), later: Some(2) }, tail: 3 };
    assert_eq!(alloy_rlp::encode(&ambiguous_some_zero_then_some), encoded);
    assert_eq!(decode::<Outer>(&encoded).unwrap(), sentinel_then_some);
}

#[test]
fn tagged_enum_roundtrips_shapes_and_tags() {
    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    #[rlp(tagged)]
    enum Message {
        Ping,
        Pong(u8, u16),
        Data { a: u8, b: u64 },
    }

    for value in [Message::Ping, Message::Pong(1, 2), Message::Data { a: 3, b: 4 }] {
        let encoded = alloy_rlp::encode(&value);
        assert_eq!(decode::<Message>(&encoded).unwrap(), value);
    }

    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    #[rlp(tagged)]
    enum Discriminants {
        Start = 10,
        Stop = 20,
    }

    assert_eq!(alloy_rlp::encode(&Discriminants::Start), alloy_rlp::encode((10u64,)));
    assert_eq!(alloy_rlp::encode(&Discriminants::Stop), alloy_rlp::encode((20u64,)));
    assert_eq!(decode::<Discriminants>(alloy_rlp::encode((10u64,))).unwrap(), Discriminants::Start);

    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    #[rlp(tagged)]
    enum Custom {
        #[rlp(tag = 0x80)]
        Alpha,
        #[rlp(tag = 0x1234)]
        Beta(u64),
    }

    assert_eq!(alloy_rlp::encode(&Custom::Alpha), alloy_rlp::encode((0x80u64,)));
    let beta = Custom::Beta(99);
    let encoded = alloy_rlp::encode(&beta);
    assert_eq!(decode::<Custom>(&encoded).unwrap(), beta);
}

#[test]
fn tagged_enum_rejects_unknown_tags_and_trailing_payload() {
    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    #[rlp(tagged)]
    enum Command {
        Start = 10,
    }

    assert_err_kind(
        decode::<Command>(alloy_rlp::encode((99u64,))),
        ErrorKind::Custom("unknown variant tag"),
    );
    assert_err_kind(
        decode::<Command>(alloy_rlp::encode((10u64, 1u8))),
        ErrorKind::ListLengthMismatch { expected: 0, got: 1 },
    );
}

#[test]
fn tagged_enum_unknown_tag_reports_tag_bytepos() {
    #[derive(RlpDecodable, PartialEq, Debug)]
    #[rlp(tagged)]
    enum Command {
        Start = 10,
    }

    #[derive(RlpDecodable, PartialEq, Debug)]
    struct Envelope {
        first: u8,
        command: Command,
    }

    let encoded = alloy_rlp::encode((7u8, (99u64,)));
    let err = decode::<Envelope>(&encoded).unwrap_err();
    assert_eq!(err.kind(), ErrorKind::Custom("unknown variant tag"));
    assert_eq!(err.bytepos(), 3);
}

#[test]
fn transparent_structs_encode_as_inner_field() {
    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    #[rlp(transparent)]
    struct Named {
        inner: u64,
    }

    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    #[rlp(transparent)]
    struct Newtype(u64);

    #[derive(PartialEq, Debug, Default)]
    struct Marker;

    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    #[rlp(transparent)]
    struct WithSkip {
        value: u64,
        #[rlp(skip)]
        marker: Marker,
    }

    for encoded in [
        alloy_rlp::encode(Named { inner: 42 }),
        alloy_rlp::encode(Newtype(42)),
        alloy_rlp::encode(WithSkip { value: 42, marker: Marker }),
    ] {
        assert_eq!(encoded, alloy_rlp::encode(42u64));
    }

    assert_eq!(decode::<Named>(alloy_rlp::encode(42u64)).unwrap(), Named { inner: 42 });
    assert_eq!(decode::<Newtype>(alloy_rlp::encode(42u64)).unwrap(), Newtype(42));
    assert_eq!(
        decode::<WithSkip>(alloy_rlp::encode(42u64)).unwrap(),
        WithSkip { value: 42, marker: Marker }
    );
}

#[test]
fn reth_like_eth_payloads_match_manual_list_encoding() {
    #[derive(RlpEncodable, RlpDecodable, Clone, PartialEq, Debug)]
    struct BlockHashNumber {
        hash: [u8; 32],
        number: u64,
    }

    let block_hash_number = BlockHashNumber { hash: [0x11; 32], number: 17 };
    assert_manual_list_encoding(
        &block_hash_number,
        &[alloy_rlp::encode(block_hash_number.hash), alloy_rlp::encode(block_hash_number.number)],
    );

    #[derive(RlpEncodable, RlpDecodable, Clone, PartialEq, Debug)]
    struct LegacyTx {
        nonce: u64,
        gas_price: u128,
        gas_limit: u64,
        to: [u8; 20],
        value: u128,
        input: Bytes,
        v: u64,
        r: u128,
        s: u128,
    }

    let tx = LegacyTx {
        nonce: 7,
        gas_price: 20_000_000_000,
        gas_limit: 21_000,
        to: [0x22; 20],
        value: 1_000_000_000_000_000_000,
        input: Bytes::from_static(b"call-data"),
        v: 37,
        r: 0x1234,
        s: 0x5678,
    };
    assert_manual_list_encoding(
        &tx,
        &[
            alloy_rlp::encode(tx.nonce),
            alloy_rlp::encode(tx.gas_price),
            alloy_rlp::encode(tx.gas_limit),
            alloy_rlp::encode(tx.to),
            alloy_rlp::encode(tx.value),
            alloy_rlp::encode(&tx.input),
            alloy_rlp::encode(tx.v),
            alloy_rlp::encode(tx.r),
            alloy_rlp::encode(tx.s),
        ],
    );

    #[derive(RlpEncodable, RlpDecodable, Clone, PartialEq, Debug)]
    struct MiniHeader {
        parent_hash: [u8; 32],
        ommers_hash: [u8; 32],
        beneficiary: [u8; 20],
        state_root: [u8; 32],
        transactions_root: [u8; 32],
        receipts_root: [u8; 32],
        logs_bloom: Bytes,
        difficulty: u128,
        number: u64,
        gas_limit: u64,
        gas_used: u64,
        timestamp: u64,
        extra_data: Bytes,
        mix_hash: [u8; 32],
        nonce: [u8; 8],
    }

    let header = MiniHeader {
        parent_hash: [0x01; 32],
        ommers_hash: [0x02; 32],
        beneficiary: [0x03; 20],
        state_root: [0x04; 32],
        transactions_root: [0x05; 32],
        receipts_root: [0x06; 32],
        logs_bloom: Bytes::from(vec![0xaa; 256]),
        difficulty: 17_000_000,
        number: 18_000_000,
        gas_limit: 30_000_000,
        gas_used: 12_345_678,
        timestamp: 1_700_000_000,
        extra_data: Bytes::from_static(b"alloy-rlp"),
        mix_hash: [0x07; 32],
        nonce: [0x08; 8],
    };
    assert_manual_list_encoding(
        &header,
        &[
            alloy_rlp::encode(header.parent_hash),
            alloy_rlp::encode(header.ommers_hash),
            alloy_rlp::encode(header.beneficiary),
            alloy_rlp::encode(header.state_root),
            alloy_rlp::encode(header.transactions_root),
            alloy_rlp::encode(header.receipts_root),
            alloy_rlp::encode(&header.logs_bloom),
            alloy_rlp::encode(header.difficulty),
            alloy_rlp::encode(header.number),
            alloy_rlp::encode(header.gas_limit),
            alloy_rlp::encode(header.gas_used),
            alloy_rlp::encode(header.timestamp),
            alloy_rlp::encode(&header.extra_data),
            alloy_rlp::encode(header.mix_hash),
            alloy_rlp::encode(header.nonce),
        ],
    );

    #[derive(RlpEncodable, RlpDecodable, Clone, PartialEq, Debug)]
    struct MiniBlock {
        header: MiniHeader,
        transactions: Vec<LegacyTx>,
        ommers: Vec<MiniHeader>,
    }

    let ommer = MiniHeader { nonce: [0x09; 8], ..header.clone() };
    let block = MiniBlock { header, transactions: vec![tx.clone()], ommers: vec![ommer] };
    assert_manual_list_encoding(
        &block,
        &[
            alloy_rlp::encode(&block.header),
            alloy_rlp::encode(&block.transactions),
            alloy_rlp::encode(&block.ommers),
        ],
    );

    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    struct NewBlock {
        block: MiniBlock,
        td: u128,
    }

    let new_block = NewBlock { block, td: 19_000_000 };
    assert_manual_list_encoding(
        &new_block,
        &[alloy_rlp::encode(&new_block.block), alloy_rlp::encode(new_block.td)],
    );

    #[derive(RlpEncodableWrapper, RlpDecodableWrapper, PartialEq, Debug)]
    struct Transactions(Vec<LegacyTx>);

    let transactions = Transactions(vec![tx]);
    let encoded = alloy_rlp::encode(&transactions);
    assert_eq!(encoded, alloy_rlp::encode(&transactions.0));
    assert_eq!(decode::<Transactions>(&encoded).unwrap(), transactions);
}

#[test]
fn reth_like_p2p_tagged_payloads_match_manual_list_encoding() {
    #[derive(RlpEncodable, RlpDecodable, Clone, PartialEq, Debug)]
    struct Capability {
        name: String,
        version: u64,
    }

    #[derive(RlpEncodable, RlpDecodable, Clone, PartialEq, Debug)]
    struct HelloMessage {
        protocol_version: u64,
        client_version: String,
        capabilities: Vec<Capability>,
        port: u16,
        id: [u8; 32],
    }

    let hello = HelloMessage {
        protocol_version: 5,
        client_version: "reth/v1.0.0".to_string(),
        capabilities: vec![Capability { name: "eth".to_string(), version: 68 }],
        port: 30303,
        id: [0x42; 32],
    };
    assert_manual_list_encoding(
        &hello,
        &[
            alloy_rlp::encode(hello.protocol_version),
            alloy_rlp::encode(&hello.client_version),
            alloy_rlp::encode(&hello.capabilities),
            alloy_rlp::encode(hello.port),
            alloy_rlp::encode(hello.id),
        ],
    );

    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    #[rlp(tagged)]
    enum P2PControl {
        Hello(HelloMessage),
        Disconnect {
            reason: u8,
        },
        #[rlp(tag = 2)]
        Ping,
        #[rlp(tag = 3)]
        Pong,
    }

    let hello_msg = P2PControl::Hello(hello.clone());
    assert_manual_list_encoding(&hello_msg, &[alloy_rlp::encode(0u64), alloy_rlp::encode(&hello)]);

    let disconnect = P2PControl::Disconnect { reason: 8 };
    assert_manual_list_encoding(&disconnect, &[alloy_rlp::encode(1u64), alloy_rlp::encode(8u8)]);

    assert_manual_list_encoding(&P2PControl::Ping, &[alloy_rlp::encode(2u64)]);
    assert_manual_list_encoding(&P2PControl::Pong, &[alloy_rlp::encode(3u64)]);
}
