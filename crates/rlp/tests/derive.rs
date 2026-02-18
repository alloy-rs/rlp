//! Tests for the derive macros.

#![cfg(feature = "derive")]
#![allow(dead_code)]

use alloy_rlp::*;

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

/// Test `#[rlp(transparent)]` as a replacement for `RlpEncodableWrapper`/`RlpDecodableWrapper`.
#[test]
fn transparent_basic() {
    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    #[rlp(transparent)]
    struct Wrapper {
        inner: u64,
    }

    let w = Wrapper { inner: 42 };
    let encoded = alloy_rlp::encode(&w);

    // Should encode identically to the inner type (no list header)
    let raw = alloy_rlp::encode(42u64);
    assert_eq!(encoded, raw);

    let decoded = Wrapper::rlp_decode(&mut encoded.as_slice()).unwrap();
    assert_eq!(decoded, w);
}

/// Test `#[rlp(transparent)]` with a skipped field.
#[test]
fn transparent_with_skip() {
    #[derive(PartialEq, Debug, Default)]
    struct NotEncodable;

    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    #[rlp(transparent)]
    struct WithSkip {
        value: u64,
        #[rlp(skip)]
        _marker: NotEncodable,
    }

    let w = WithSkip { value: 99, _marker: NotEncodable };
    let encoded = alloy_rlp::encode(&w);
    assert_eq!(encoded, alloy_rlp::encode(99u64));

    let decoded = WithSkip::rlp_decode(&mut encoded.as_slice()).unwrap();
    assert_eq!(decoded.value, 99);
}

/// Test `#[rlp(transparent)]` with a tuple struct.
#[test]
fn transparent_tuple() {
    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    #[rlp(transparent)]
    struct Wrap(u64);

    let w = Wrap(123);
    let encoded = alloy_rlp::encode(&w);
    assert_eq!(encoded, alloy_rlp::encode(123u64));

    let decoded = Wrap::rlp_decode(&mut encoded.as_slice()).unwrap();
    assert_eq!(decoded, w);
}

/// Test `#[rlp(tagged)]` on an enum with unnamed fields.
#[test]
fn tagged_enum_unnamed() {
    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    #[rlp(tagged)]
    enum FooBar {
        Foo(u64),
        Bar(u16, u64),
    }

    let val = FooBar::Foo(42);
    let encoded = alloy_rlp::encode(&val);
    let decoded = FooBar::rlp_decode(&mut encoded.as_slice()).unwrap();
    assert_eq!(decoded, val);

    let val = FooBar::Bar(7, 42);
    let encoded = alloy_rlp::encode(&val);
    let decoded = FooBar::rlp_decode(&mut encoded.as_slice()).unwrap();
    assert_eq!(decoded, val);
}

/// Test `#[rlp(tagged)]` on an enum with unit variants.
#[test]
fn tagged_enum_unit() {
    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    #[rlp(tagged)]
    enum Signal {
        Ping,
        Pong,
    }

    let val = Signal::Ping;
    let encoded = alloy_rlp::encode(&val);
    let decoded = Signal::rlp_decode(&mut encoded.as_slice()).unwrap();
    assert_eq!(decoded, val);

    let val = Signal::Pong;
    let encoded = alloy_rlp::encode(&val);
    let decoded = Signal::rlp_decode(&mut encoded.as_slice()).unwrap();
    assert_eq!(decoded, val);
}

/// Test `#[rlp(tagged)]` with named fields.
#[test]
fn tagged_enum_named() {
    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    #[rlp(tagged)]
    enum Msg {
        Hello { version: u64 },
        Data { a: u16, b: u64 },
    }

    let val = Msg::Hello { version: 5 };
    let encoded = alloy_rlp::encode(&val);
    let decoded = Msg::rlp_decode(&mut encoded.as_slice()).unwrap();
    assert_eq!(decoded, val);

    let val = Msg::Data { a: 7, b: 42 };
    let encoded = alloy_rlp::encode(&val);
    let decoded = Msg::rlp_decode(&mut encoded.as_slice()).unwrap();
    assert_eq!(decoded, val);
}

/// Test `#[rlp(tagged)]` with explicit discriminant values.
#[test]
fn tagged_enum_discriminant() {
    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    #[rlp(tagged)]
    enum Cmd {
        Start = 10,
        Stop = 20,
    }

    let val = Cmd::Start;
    let encoded = alloy_rlp::encode(&val);
    let decoded = Cmd::rlp_decode(&mut encoded.as_slice()).unwrap();
    assert_eq!(decoded, val);

    let val = Cmd::Stop;
    let encoded = alloy_rlp::encode(&val);
    let decoded = Cmd::rlp_decode(&mut encoded.as_slice()).unwrap();
    assert_eq!(decoded, val);
}

/// Test `#[rlp(tag = <expr>)]` per-variant override.
#[test]
fn tagged_enum_tag_attr() {
    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    #[rlp(tagged)]
    enum Custom {
        #[rlp(tag = 0x80)]
        Alpha,
        #[rlp(tag = 0xFF)]
        Beta(u64),
    }

    let val = Custom::Alpha;
    let encoded = alloy_rlp::encode(&val);
    let decoded = Custom::rlp_decode(&mut encoded.as_slice()).unwrap();
    assert_eq!(decoded, val);

    let val = Custom::Beta(999);
    let encoded = alloy_rlp::encode(&val);
    let decoded = Custom::rlp_decode(&mut encoded.as_slice()).unwrap();
    assert_eq!(decoded, val);
}

/// Test that unknown tags produce an error on decode.
#[test]
fn tagged_enum_unknown_tag() {
    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    #[rlp(tagged)]
    enum OnlyOne {
        A,
    }

    // Encode variant A (tag 0), then mutate tag to 99
    let mut encoded = alloy_rlp::encode(&OnlyOne::A);
    // The encoding is a list [tag]. For tag=0 (RLP: 0x80), the list is [0xC1, 0x80].
    // Change the tag byte to 99 (which is < 0x80, so it's a single-byte RLP)
    encoded[1] = 99;
    let result = OnlyOne::rlp_decode(&mut encoded.as_slice());
    assert!(result.is_err());
    assert_eq!(result.unwrap_err().kind, ErrorKind::Custom("unknown variant tag"));
}

/// Test that `#[rlp(tagged)]` roundtrips match the manual example in examples/enum.rs.
#[test]
fn tagged_enum_matches_manual() {
    // The manual FooBar example encodes Foo(42) as list [0u8, 42u64]
    // Our derived version should produce the same encoding
    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    #[rlp(tagged)]
    enum FooBar {
        Foo(u64),
        Bar(u16, u64),
    }

    let derived_foo = alloy_rlp::encode(FooBar::Foo(42));
    let derived_bar = alloy_rlp::encode(FooBar::Bar(7, 42));

    // Build the expected encoding manually using encode_list
    use alloy_rlp::{encode_list, Encoder};

    let mut expected_foo = Vec::new();
    let enc: [&dyn RlpEncodable; 2] = [&0u8, &42u64];
    encode_list::<_, dyn RlpEncodable>(&enc, &mut Encoder::new(&mut expected_foo));

    let mut expected_bar = Vec::new();
    let enc: [&dyn RlpEncodable; 3] = [&1u8, &7u16, &42u64];
    encode_list::<_, dyn RlpEncodable>(&enc, &mut Encoder::new(&mut expected_bar));

    assert_eq!(derived_foo, expected_foo);
    assert_eq!(derived_bar, expected_bar);
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

/// Test `#[rlp(flatten)]` field attribute.
#[test]
fn flatten_field() {
    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    struct Inner {
        a: u64,
        b: u64,
    }

    // Without flatten: Outer encodes as [x, [a, b]] (nested list)
    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    struct OuterNested {
        x: u64,
        inner: Inner,
    }

    // With flatten: Outer encodes as [x, a, b] (fields inlined)
    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    struct OuterFlat {
        x: u64,
        #[rlp(flatten)]
        inner: Inner,
    }

    let nested = OuterNested { x: 1, inner: Inner { a: 2, b: 3 } };
    let flat = OuterFlat { x: 1, inner: Inner { a: 2, b: 3 } };

    let nested_encoded = alloy_rlp::encode(&nested);
    let flat_encoded = alloy_rlp::encode(&flat);

    // They should be different: nested has [1, [2, 3]], flat has [1, 2, 3]
    assert_ne!(nested_encoded, flat_encoded);

    // Flat should encode/decode as [x, a, b] — same as a 3-field struct
    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    struct ThreeFields {
        x: u64,
        a: u64,
        b: u64,
    }

    let three = ThreeFields { x: 1, a: 2, b: 3 };
    let three_encoded = alloy_rlp::encode(&three);
    assert_eq!(flat_encoded, three_encoded);

    // Roundtrip flat
    let decoded = OuterFlat::rlp_decode(&mut flat_encoded.as_slice()).unwrap();
    assert_eq!(decoded, flat);
}

/// Test `#[rlp(flatten)]` with multiple flattened fields.
#[test]
fn flatten_multiple() {
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
        b: B,
    }

    let val = Combined { a: A { x: 10 }, b: B { y: 20, z: 30 } };
    let encoded = alloy_rlp::encode(&val);

    // Should encode as [10, 20, 30] — same as a flat 3-field struct
    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    struct Flat3 {
        x: u64,
        y: u16,
        z: u64,
    }
    let flat = Flat3 { x: 10, y: 20, z: 30 };
    assert_eq!(encoded, alloy_rlp::encode(&flat));

    let decoded = Combined::rlp_decode(&mut encoded.as_slice()).unwrap();
    assert_eq!(decoded, val);
}

/// Test `#[rlp(flatten)]` with a skipped field alongside.
#[test]
fn flatten_with_skip() {
    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    struct Inner {
        a: u64,
    }

    #[derive(PartialEq, Debug, Default)]
    struct NotRlp;

    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    struct Outer {
        x: u64,
        #[rlp(flatten)]
        inner: Inner,
        #[rlp(default, skip)]
        _cache: NotRlp,
    }

    let val = Outer { x: 1, inner: Inner { a: 2 }, _cache: NotRlp };
    let encoded = alloy_rlp::encode(&val);

    let decoded = Outer::rlp_decode(&mut encoded.as_slice()).unwrap();
    assert_eq!(decoded.x, 1);
    assert_eq!(decoded.inner.a, 2);
}

/// Test tuple encode/decode roundtrip with larger arities.
#[test]
fn tuple_larger_arity() {
    let t5 = (1u8, 2u16, 3u32, 4u64, 5u128);
    let encoded = alloy_rlp::encode(t5);
    let decoded = <(u8, u16, u32, u64, u128)>::rlp_decode(&mut encoded.as_slice()).unwrap();
    assert_eq!(decoded, t5);
}

/// Test tuple decode rejects trailing bytes.
#[test]
fn tuple_decode_trailing_bytes() {
    // Encode (1u64, 2u64) then try to decode as (u64,) — should fail due to extra data
    let data = alloy_rlp::encode((1u64, 2u64));
    let result = <(u64,)>::rlp_decode(&mut data.as_slice());
    assert!(result.is_err());
    assert_eq!(result.unwrap_err().kind, ErrorKind::ListLengthMismatch { expected: 0, got: 1 });
}

/// Test tuple decode rejects too-few elements.
#[test]
fn tuple_decode_too_few() {
    let data = alloy_rlp::encode((1u64,));
    let result = <(u64, u64)>::rlp_decode(&mut data.as_slice());
    assert!(result.is_err());
    assert_eq!(result.unwrap_err().kind, ErrorKind::InputTooShort);
}

/// Last trailing optional field roundtrips values that encode as 0x80.
#[test]
fn option_zero_value_roundtrip() {
    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    #[rlp(trailing)]
    struct S {
        x: u64,
        flag: Option<bool>,
        val: Option<u64>,
    }

    for v in [
        S { x: 1, flag: None, val: None },
        S { x: 1, flag: None, val: Some(0) },
        S { x: 1, flag: None, val: Some(42) },
    ] {
        let encoded = alloy_rlp::encode(&v);
        let decoded = S::rlp_decode(&mut encoded.as_slice()).unwrap();
        assert_eq!(v, decoded);
    }
}

/// Flatten with inner trailing optionals: raw mode skips optional fields.
#[test]
fn flatten_with_inner_trailing_optional() {
    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    #[rlp(trailing)]
    struct Inner {
        a: u64,
        b: Option<u64>,
    }

    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    struct Outer {
        #[rlp(flatten)]
        inner: Inner,
        c: u64,
    }

    let val = Outer { inner: Inner { a: 1, b: None }, c: 3 };
    let encoded = alloy_rlp::encode(&val);
    let decoded = Outer::rlp_decode(&mut encoded.as_slice()).unwrap();
    assert_eq!(decoded, val);

    // Raw encode/decode skip optionals and stay symmetric.
    let s = Inner { a: 42, b: Some(99) };
    let mut raw_buf = Vec::new();
    s.rlp_encode_raw(&mut alloy_rlp::Encoder::new(&mut raw_buf));
    let decoded = Inner::rlp_decode_raw(&mut raw_buf.as_slice()).unwrap();
    assert_eq!(decoded, Inner { a: 42, b: None });
    assert_eq!(s.rlp_len_raw(), raw_buf.len());
}
