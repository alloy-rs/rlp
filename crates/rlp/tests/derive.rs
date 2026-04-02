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
    thing.encode(&mut buf);
    let decoded = MyThing::decode(&mut buf.as_slice()).unwrap();
    assert_eq!(thing, decoded);

    // does not panic on short input
    assert_eq!(Err(Error::InputTooShort), MyThing::decode(&mut [0x8c; 11].as_ref()))
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

#[test]
fn trailing_no_gaps() {
    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    #[rlp(trailing(no_gaps))]
    struct NoGaps {
        required: u64,
        a: Option<[u8; 32]>,
        b: Option<[u8; 32]>,
    }

    let h1 = [1u8; 32];
    let h2 = [2u8; 32];

    // Roundtrip with all fields present.
    let val = NoGaps { required: 1, a: Some(h1), b: Some(h2) };
    let mut buf = Vec::new();
    val.encode(&mut buf);
    let decoded = NoGaps::decode(&mut buf.as_slice()).unwrap();
    assert_eq!(val, decoded);

    // Roundtrip with all optional fields absent.
    let val = NoGaps { required: 1, a: None, b: None };
    buf.clear();
    val.encode(&mut buf);
    assert_eq!(buf, vec![0xc1, 0x01]);
    let decoded = NoGaps::decode(&mut buf.as_slice()).unwrap();
    assert_eq!(val, decoded);

    // Roundtrip with first present, second absent.
    let val = NoGaps { required: 1, a: Some(h1), b: None };
    buf.clear();
    val.encode(&mut buf);
    let decoded = NoGaps::decode(&mut buf.as_slice()).unwrap();
    assert_eq!(val, decoded);

    // With no_gaps, 0x80 in the payload is decoded as Some (attempting to decode the inner
    // type), not as a None placeholder. For [u8; 32] this fails since 0x80 is too short.
    let non_canonical = vec![0xc2, 0x01, 0x80];
    assert!(NoGaps::decode(&mut non_canonical.as_slice()).is_err());
}

#[test]
fn trailing_canonical() {
    #[derive(RlpEncodable, RlpDecodable, PartialEq, Debug)]
    #[rlp(trailing(canonical))]
    struct Canonical {
        required: u64,
        a: Option<[u8; 32]>,
        b: Option<[u8; 32]>,
    }

    let h1 = [1u8; 32];
    let h2 = [2u8; 32];

    // Roundtrip with all fields present.
    let val = Canonical { required: 1, a: Some(h1), b: Some(h2) };
    let mut buf = Vec::new();
    val.encode(&mut buf);
    let decoded = Canonical::decode(&mut buf.as_slice()).unwrap();
    assert_eq!(val, decoded);

    // Roundtrip with all optional fields absent.
    let val = Canonical { required: 1, a: None, b: None };
    buf.clear();
    val.encode(&mut buf);
    assert_eq!(buf, vec![0xc1, 0x01]);
    let decoded = Canonical::decode(&mut buf.as_slice()).unwrap();
    assert_eq!(val, decoded);

    // Roundtrip with first present, second absent.
    let val = Canonical { required: 1, a: Some(h1), b: None };
    buf.clear();
    val.encode(&mut buf);
    let decoded = Canonical::decode(&mut buf.as_slice()).unwrap();
    assert_eq!(val, decoded);

    // Roundtrip with first absent, second present — uses 0x80 placeholder for `a`.
    let val = Canonical { required: 1, a: None, b: Some(h2) };
    buf.clear();
    val.encode(&mut buf);
    assert_eq!(buf[1], 0x01); // required
    assert_eq!(buf[2], 0x80); // None placeholder
    let decoded = Canonical::decode(&mut buf.as_slice()).unwrap();
    assert_eq!(val, decoded);

    // Non-canonical: trailing 0x80 is decoded as Some, which fails for [u8; 32].
    let non_canonical = vec![0xc2, 0x01, 0x80];
    assert!(Canonical::decode(&mut non_canonical.as_slice()).is_err());
}

/// Test that trailing options compile with generics.
#[test]
const fn trailing_opts_compiles() {
    #[derive(RlpEncodable, RlpDecodable)]
    #[rlp(trailing)]
    struct PlainTrailing<T>(Option<Vec<T>>);

    #[derive(RlpEncodable, RlpDecodable)]
    #[rlp(trailing(no_gaps))]
    struct NoGapsTrailing<T>(Option<Vec<T>>);

    #[derive(RlpEncodable, RlpDecodable)]
    #[rlp(trailing(canonical))]
    struct CanonicalTrailing<T>(Option<Vec<T>>);
}

/// Test that multiple attributes can be combined in a single `#[rlp(...)]`.
/// See <https://github.com/alloy-rs/rlp/issues/9>
#[test]
fn multiple_attrs_combined() {
    /// A type that intentionally does NOT implement `Encodable` or `Decodable`.
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
    foo.encode(&mut buf);

    let decoded = Foo::decode(&mut buf.as_slice()).unwrap();
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
    bar.encode(&mut buf2);

    let decoded2 = Bar::decode(&mut buf2.as_slice()).unwrap();
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
    s.encode(&mut buf);

    // Decode as a struct without the skipped field to verify it wasn't encoded
    #[derive(RlpDecodable, PartialEq, Debug)]
    struct WithoutSkip {
        pub value: u64,
    }

    let decoded = WithoutSkip::decode(&mut buf.as_slice()).unwrap();
    assert_eq!(decoded.value, 42);
}
