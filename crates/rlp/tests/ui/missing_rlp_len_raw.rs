use alloy_rlp::{BufMut, Encoder, RlpEncodable};

struct Bad;

impl RlpEncodable for Bad {
    fn rlp_encode<T: BufMut>(&self, _out: &mut Encoder<T>) {}
}

fn main() {}
