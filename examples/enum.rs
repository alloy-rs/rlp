//! This example demonstrates how to encode and decode an enum using
//! `alloy_rlp`.

use alloy_rlp::{encode, Decodable, Encodable, Error, Expectation};
use bytes::BufMut;

#[derive(Debug, PartialEq)]
enum FooBar {
    // Treated as an individual value
    Foo(u64),
    // Treated as a list of values
    Bar(u16, u64),
}

impl Encodable for FooBar {
    fn encode_fields(&self, out: &mut dyn BufMut) {
        match self {
            // This is an individual value, so we just pass through
            Self::Foo(x) => {
                x.encode_fields(out);
            }
            // This is a list of values, so we need to encode each entry as its
            // own item
            Self::Bar(x, y) => {
                x.encode(out);
                y.encode(out);
            }
        }
    }

    fn encoded_fields_length(&self) -> usize {
        match self {
            // This is an individual value, so we just pass through
            Self::Foo(x) => x.encoded_fields_length(),
            // This is a list of values, so we need to sum the lengths of the fields
            Self::Bar(x, y) => x.length() + y.length(),
        }
    }

    fn is_string(&self) -> bool {
        match self {
            // This is an individual value, so we just pass through
            Self::Foo(inner) => inner.is_string(),
            // This is a list because it's treated as a list of values
            Self::Bar(_, _) => false,
        }
    }
}

impl Decodable for FooBar {
    fn expected() -> Expectation {
        // No expectation, as the type is data-dependent
        Expectation::None
    }

    fn decode_fields(data: &mut &[u8]) -> Result<Self, Error> {
        // Simple strategy: if we correctly decode a `u64`, then we know it's
        // a `Foo` variant. Otherwise, we assume it's a `Bar` variant.
        let copy = &mut *data;
        if let Ok(val) = u64::decode_fields(copy) {
            *data = *copy;
            return Ok(Self::Foo(val));
        }

        Ok(Self::Bar(u16::decode_fields(data)?, u64::decode_fields(data)?))
    }
}

fn main() {
    let val = FooBar::Foo(42);
    let out = encode(&val);
    assert_eq!(FooBar::decode(&mut out.as_ref()), Ok(val));

    let val = FooBar::Bar(7, 42);
    let out = encode(&val);
    assert_eq!(FooBar::decode(&mut out.as_ref()), Ok(val));

    println!("success!")
}
