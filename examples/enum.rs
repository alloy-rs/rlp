//! This example demonstrates how to encode and decode an enum using
//! `alloy_rlp`.

use alloy_rlp::{encode, BufMut, Decoder, Encoder, Error, ErrorKind, RlpDecodable, RlpEncodable};

#[derive(Debug, PartialEq)]
enum FooBar {
    Foo(u64),
    Bar(u16, u64),
}

impl RlpEncodable for FooBar {
    fn rlp_encode<T: BufMut>(&self, out: &mut Encoder<T>) {
        match self {
            Self::Foo(x) => (0u8, *x).rlp_encode(out),
            Self::Bar(x, y) => (1u8, *x, *y).rlp_encode(out),
        }
    }

    fn rlp_len_raw(&self) -> usize {
        self.rlp_len()
    }
}

impl<'de> RlpDecodable<'de> for FooBar {
    fn rlp_decode(decoder: &mut Decoder<'de>) -> Result<Self, Error> {
        let mut payload = decoder.decode_payload(true)?;
        match u8::rlp_decode(&mut payload)? {
            0 => Ok(Self::Foo(u64::rlp_decode(&mut payload)?)),
            1 => Ok(Self::Bar(u16::rlp_decode(&mut payload)?, u64::rlp_decode(&mut payload)?)),
            _ => Err(ErrorKind::Custom("unknown type").into()),
        }
    }
}

fn main() {
    let val = FooBar::Foo(42);
    let out = encode(&val);
    assert_eq!(alloy_rlp::decode_exact::<FooBar>(&out), Ok(val));

    let val = FooBar::Bar(7, 42);
    let out = encode(&val);
    assert_eq!(alloy_rlp::decode_exact::<FooBar>(&out), Ok(val));

    println!("success!")
}
