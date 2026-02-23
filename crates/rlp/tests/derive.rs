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
