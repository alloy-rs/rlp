use alloy_rlp::{RlpDecodable, RlpEncodable};

#[derive(RlpEncodable, RlpDecodable)]
struct Bad {
    #[rlp(flatten)]
    value: Option<u8>,
}

fn main() {}
