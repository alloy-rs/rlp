//! This example demonstrates deriving RlpEncodable/RlpDecodable for enums
//! using `#[rlp(tagged)]`.

use alloy_rlp::{encode, RlpDecodable, RlpEncodable};

#[derive(Debug, PartialEq, RlpEncodable, RlpDecodable)]
#[rlp(tagged)]
enum FooBar {
    Foo(u64),
    Bar(u16, u64),
}

#[derive(Debug, PartialEq, RlpEncodable, RlpDecodable)]
#[rlp(tagged)]
enum WithNamed {
    A { x: u64, y: u16 },
    B { z: u64 },
}

#[derive(Debug, PartialEq, RlpEncodable, RlpDecodable)]
#[rlp(tagged)]
enum WithUnit {
    Empty,
    Value(u64),
}

#[derive(Debug, PartialEq, RlpEncodable, RlpDecodable)]
#[rlp(tagged)]
enum WithCustomTags {
    #[rlp(tag = 10)]
    A(u64),
    #[rlp(tag = 20)]
    B(u16),
}

#[derive(Debug, PartialEq, RlpEncodable, RlpDecodable)]
#[rlp(tagged)]
#[repr(u8)]
enum WithDiscriminant {
    A(u64) = 5,
    B(u16) = 7,
}

fn main() {
    // Unnamed fields (tuple variants)
    let val = FooBar::Foo(42);
    let out = encode(&val);
    assert_eq!(FooBar::rlp_decode(&mut out.as_ref()), Ok(val));

    let val = FooBar::Bar(7, 42);
    let out = encode(&val);
    assert_eq!(FooBar::rlp_decode(&mut out.as_ref()), Ok(val));

    // Named fields
    let val = WithNamed::A { x: 100, y: 200 };
    let out = encode(&val);
    assert_eq!(WithNamed::rlp_decode(&mut out.as_ref()), Ok(val));

    let val = WithNamed::B { z: 999 };
    let out = encode(&val);
    assert_eq!(WithNamed::rlp_decode(&mut out.as_ref()), Ok(val));

    // Unit variants
    let val = WithUnit::Empty;
    let out = encode(&val);
    assert_eq!(WithUnit::rlp_decode(&mut out.as_ref()), Ok(val));

    let val = WithUnit::Value(123);
    let out = encode(&val);
    assert_eq!(WithUnit::rlp_decode(&mut out.as_ref()), Ok(val));

    // Custom tags
    let val = WithCustomTags::A(42);
    let out = encode(&val);
    assert_eq!(WithCustomTags::rlp_decode(&mut out.as_ref()), Ok(val));

    let val = WithCustomTags::B(7);
    let out = encode(&val);
    assert_eq!(WithCustomTags::rlp_decode(&mut out.as_ref()), Ok(val));

    // Discriminant-based tags
    let val = WithDiscriminant::A(42);
    let out = encode(&val);
    assert_eq!(WithDiscriminant::rlp_decode(&mut out.as_ref()), Ok(val));

    let val = WithDiscriminant::B(7);
    let out = encode(&val);
    assert_eq!(WithDiscriminant::rlp_decode(&mut out.as_ref()), Ok(val));

    println!("all enum derive tests passed!");
}
