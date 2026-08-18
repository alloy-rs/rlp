#![no_main]

use alloy_rlp::{Decodable, Header};
use libfuzzer_sys::fuzz_target;

/// A zero-sized eager list item. Decoding a `Vec<RawItem>` exercises Alloy's normal list decoder:
/// it pushes one entry for every valid item, while this fuzzer's borrowed reference cursor only
/// validates and advances over the same items.
#[derive(Debug)]
struct RawItem;

impl Decodable for RawItem {
    fn decode(buf: &mut &[u8]) -> alloy_rlp::Result<Self> {
        let raw = *buf;
        let mut remainder = raw;
        let header = Header::decode(&mut remainder)?;
        let header_length = raw.len() - remainder.len();
        *buf = &raw[header_length + header.payload_length..];
        Ok(Self)
    }
}

fn eager(input: &[u8]) -> alloy_rlp::Result<(usize, usize)> {
    let mut buf = input;
    let items = Vec::<RawItem>::decode(&mut buf)?;
    Ok((items.len(), input.len() - buf.len()))
}

/// The pre-API reference cursor. The stacked `RlpList` change replaces this implementation with
/// the public cursor while retaining this differential oracle.
fn borrowed_reference(input: &[u8]) -> alloy_rlp::Result<(usize, usize)> {
    let mut buf = input;
    let mut payload = Header::decode_bytes(&mut buf, true)?;
    let mut count = 0;

    while !payload.is_empty() {
        let raw = payload;
        let mut remainder = raw;
        let header = Header::decode(&mut remainder)?;
        let header_length = raw.len() - remainder.len();
        payload = &raw[header_length + header.payload_length..];
        count += 1;
    }

    Ok((count, input.len() - buf.len()))
}

fuzz_target!(|input: &[u8]| {
    assert_eq!(eager(input), borrowed_reference(input));
});
