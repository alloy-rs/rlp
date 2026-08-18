#![no_main]

use alloy_rlp::{Error, Header, PayloadView, RlpList};
use libfuzzer_sys::fuzz_target;

fn eager(input: &[u8]) -> alloy_rlp::Result<(Vec<&[u8]>, usize)> {
    let mut buf = input;
    let payload = Header::decode_raw(&mut buf)?;
    let PayloadView::List(items) = payload else {
        return Err(Error::UnexpectedString);
    };
    Ok((items, input.len() - buf.len()))
}

fn borrowed(input: &[u8]) -> alloy_rlp::Result<(Vec<&[u8]>, usize)> {
    let mut buf = input;
    let mut list = RlpList::decode(&mut buf)?;
    let mut items = Vec::new();
    while let Some(item) = list.next_raw()? {
        items.push(item);
    }
    Ok((items, input.len() - buf.len()))
}

fn bounded_count(input: &[u8], limit: usize) -> alloy_rlp::Result<usize> {
    let mut buf = input;
    RlpList::decode(&mut buf)?.count_at_most(limit)
}

fn assert_differential(input: &[u8], limit: usize) {
    match (eager(input), borrowed(input)) {
        (Ok((eager_items, eager_consumed)), Ok((borrowed_items, borrowed_consumed))) => {
            assert_eq!(eager_items, borrowed_items);
            assert_eq!(eager_consumed, borrowed_consumed);
            assert_eq!(bounded_count(input, limit).unwrap(), eager_items.len().min(limit + 1));
        }
        (Err(_), Err(_)) => {
            // `count_at_most` is deliberately permitted to succeed once it has found `limit + 1`
            // valid items; it need not inspect a malformed suffix after that bound.
            if let Ok(count) = bounded_count(input, limit) {
                assert_eq!(count, limit + 1);
            }
        }
        (eager, borrowed) => panic!("eager={eager:?}, borrowed={borrowed:?}"),
    }
}

fuzz_target!(|input: &[u8]| {
    assert_differential(input, input.first().copied().unwrap_or_default() as usize);
});
