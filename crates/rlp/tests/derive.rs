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

#[test]
fn simple_derive() {
    #[derive(RlpEncodable, RlpDecodable, RlpMaxEncodedLen, PartialEq, Debug)]
    struct MyThing(#[rlp] [u8; 12]);

    let thing = MyThing([0; 12]);

    // roundtrip fidelity
    let mut buf = Vec::new();
    thing.rlp_encode(&mut Encoder::new(&mut buf));
    let decoded = MyThing::rlp_decode(&mut buf.as_slice()).unwrap();
    assert_eq!(thing, decoded);

    // does not panic on short input
    assert_eq!(
        Err(Error::new(ErrorKind::InputTooShort)),
        MyThing::rlp_decode(&mut [0x8c; 11].as_ref())
    )
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

    let decoded = Foo::rlp_decode(&mut buf.as_slice()).unwrap();
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

    let decoded2 = Bar::rlp_decode(&mut buf2.as_slice()).unwrap();
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

    let decoded = WithoutSkip::rlp_decode(&mut buf.as_slice()).unwrap();
    assert_eq!(decoded.value, 42);
}

#[test]
fn tuple_roundtrips_and_raw_modes() {
    fn check<T>(value: T)
    where
        T: RlpEncodable + RlpDecodable + PartialEq + std::fmt::Debug,
    {
        let encoded = alloy_rlp::encode(&value);
        assert_eq!(encoded.len(), value.rlp_len());
        let decoded = T::rlp_decode(&mut encoded.as_slice()).unwrap();
        assert_eq!(decoded, value);

        let mut raw = Vec::new();
        value.rlp_encode_raw(&mut Encoder::new(&mut raw));
        assert_eq!(raw.len(), value.rlp_len_raw());
        let mut raw_slice = raw.as_slice();
        let decoded_raw = T::rlp_decode_raw(&mut raw_slice).unwrap();
        assert_eq!(decoded_raw, value);
        assert!(raw_slice.is_empty());
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
    assert_err_kind(<(u8, u8)>::rlp_decode(&mut too_few.as_slice()), ErrorKind::InputTooShort);

    let extra = alloy_rlp::encode((1u8, 2u8));
    assert_err_kind(
        <(u8,)>::rlp_decode(&mut extra.as_slice()),
        ErrorKind::ListLengthMismatch { expected: 2, got: 1 },
    );

    assert_err_kind(<(u8,)>::rlp_decode(&mut [0x01].as_slice()), ErrorKind::UnexpectedString);
}

#[test]
fn tuple_raw_decode_leaves_outer_fields() {
    let mut raw = Vec::new();
    (1u8, 2u8).rlp_encode_raw(&mut Encoder::new(&mut raw));
    3u8.rlp_encode(&mut Encoder::new(&mut raw));

    let mut slice = raw.as_slice();
    let tuple = <(u8, u8)>::rlp_decode_raw(&mut slice).unwrap();
    let tail = u8::rlp_decode(&mut slice).unwrap();
    assert_eq!(tuple, (1, 2));
    assert_eq!(tail, 3);
    assert!(slice.is_empty());
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
    assert_eq!(OuterFlat::rlp_decode(&mut flat_encoded.as_slice()).unwrap(), flat);
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
    assert_eq!(Combined::rlp_decode(&mut encoded.as_slice()).unwrap(), value);
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

    let decoded = Outer::rlp_decode(&mut encoded.as_slice()).unwrap();
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
        assert_eq!(S::rlp_decode(&mut encoded.as_slice()).unwrap(), value);
    }
}

#[test]
fn flattened_trailing_options_do_not_consume_outer_fields() {
    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    #[rlp(trailing)]
    struct Inner {
        a: u64,
        maybe: Option<u64>,
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
        tail: u64,
    }

    let value = Outer { inner: Inner { a: 1, maybe: Some(2) }, tail: 3 };
    let encoded = alloy_rlp::encode(&value);
    assert_eq!(encoded, alloy_rlp::encode(&Flat { a: 1, tail: 3 }));

    let decoded = Outer::rlp_decode(&mut encoded.as_slice()).unwrap();
    assert_eq!(decoded, Outer { inner: Inner { a: 1, maybe: None }, tail: 3 });
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
        assert_eq!(Message::rlp_decode(&mut encoded.as_slice()).unwrap(), value);
    }

    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    #[rlp(tagged)]
    enum Discriminants {
        Start = 10,
        Stop = 20,
    }

    assert_eq!(alloy_rlp::encode(&Discriminants::Start), alloy_rlp::encode((10u64,)));
    assert_eq!(alloy_rlp::encode(&Discriminants::Stop), alloy_rlp::encode((20u64,)));
    assert_eq!(
        Discriminants::rlp_decode(&mut alloy_rlp::encode((10u64,)).as_slice()).unwrap(),
        Discriminants::Start
    );

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
    assert_eq!(Custom::rlp_decode(&mut encoded.as_slice()).unwrap(), beta);
}

#[test]
fn tagged_enum_rejects_unknown_tags_and_trailing_payload() {
    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    #[rlp(tagged)]
    enum Command {
        Start = 10,
    }

    assert_err_kind(
        Command::rlp_decode(&mut alloy_rlp::encode((99u64,)).as_slice()),
        ErrorKind::Custom("unknown variant tag"),
    );
    assert_err_kind(
        Command::rlp_decode(&mut alloy_rlp::encode((10u64, 1u8)).as_slice()),
        ErrorKind::ListLengthMismatch { expected: 0, got: 1 },
    );
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

    assert_eq!(
        Named::rlp_decode(&mut alloy_rlp::encode(42u64).as_slice()).unwrap(),
        Named { inner: 42 }
    );
    assert_eq!(Newtype::rlp_decode(&mut alloy_rlp::encode(42u64).as_slice()).unwrap(), Newtype(42));
    assert_eq!(
        WithSkip::rlp_decode(&mut alloy_rlp::encode(42u64).as_slice()).unwrap(),
        WithSkip { value: 42, marker: Marker }
    );
}
