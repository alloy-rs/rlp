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
        let tag_bytepos = payload.bytepos();
        let value = match u8::rlp_decode(&mut payload)? {
            0 => Self::Foo(u64::rlp_decode(&mut payload)?),
            1 => Self::Bar(u16::rlp_decode(&mut payload)?, u64::rlp_decode(&mut payload)?),
            _ => return Err(payload.error_at(ErrorKind::Custom("unknown type"), tag_bytepos)),
        };

        if !payload.is_empty() {
            return Err(
                payload.error(ErrorKind::ListLengthMismatch { expected: 0, got: payload.len() })
            );
        }

        Ok(value)
    }
}

fn main() {
    let val = FooBar::Foo(42);
    let out = encode(&val);
    assert_eq!(alloy_rlp::decode_exact::<FooBar>(&out), Ok(val));

    let val = FooBar::Bar(7, 42);
    let out = encode(&val);
    assert_eq!(alloy_rlp::decode_exact::<FooBar>(&out), Ok(val));

    let unknown = encode((2u8,));
    let err = alloy_rlp::decode_exact::<FooBar>(&unknown).unwrap_err();
    assert_eq!(err.kind(), ErrorKind::Custom("unknown type"));
    assert_eq!(err.bytepos(), 1);

    let trailing = encode((0u8, 42u64, 7u8));
    let err = alloy_rlp::decode_exact::<FooBar>(&trailing).unwrap_err();
    assert_eq!(err.kind(), ErrorKind::ListLengthMismatch { expected: 0, got: 1 });

    println!("success!")
}
