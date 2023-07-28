use alloy_rlp::{encode_list, Decodable, Encodable, Error, Header};
use bytes::BufMut;

#[derive(Debug, PartialEq)]
enum FooBar {
    Foo(u64),
    Bar(u16, u64),
}

impl Encodable for FooBar {
    fn encode(&self, out: &mut dyn BufMut) {
        match self {
            Self::Foo(x) => {
                let enc: [&dyn Encodable; 2] = [&0u8, x];
                encode_list::<_, dyn Encodable>(&enc, out);
            }
            Self::Bar(x, y) => {
                let enc: [&dyn Encodable; 3] = [&1u8, x, y];
                encode_list::<_, dyn Encodable>(&enc, out);
            }
        }
    }
}

impl Decodable for FooBar {
    fn decode(data: &mut &[u8]) -> Result<Self, Error> {
        let mut payload = Header::decode_bytes(data, true)?;
        match u8::decode(&mut payload)? {
            0 => {
                let foo = Self::Foo(u64::decode(&mut payload)?);
                Ok(foo)
            }
            1 => {
                let bar = Self::Bar(u16::decode(&mut payload)?, u64::decode(&mut payload)?);
                Ok(bar)
            }
            _ => Err(Error::Custom("unknown type")),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloy_rlp::encode;

    #[test]
    fn foo_roundtrip() {
        let val = FooBar::Foo(42);
        let out = encode(&val);
        assert_eq!(FooBar::decode(&mut out.as_ref()), Ok(val));
    }

    #[test]
    fn bar_roundtrip() {
        let val = FooBar::Bar(7, 42);
        let out = encode(&val);
        assert_eq!(FooBar::decode(&mut out.as_ref()), Ok(val));
    }
}
