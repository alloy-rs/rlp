use alloy_rlp::RlpEncodable;

#[derive(RlpEncodable)]
#[rlp(transparent)]
struct Bad {
    a: u8,
    b: u8,
}

fn main() {}
