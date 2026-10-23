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

fn has_more_than(input: &[u8], limit: u64) -> alloy_rlp::Result<bool> {
    let mut buf = input;
    RlpList::decode(&mut buf)?.has_more_than(limit)
}

fn assert_differential(input: &[u8]) {
    match (eager(input), borrowed(input)) {
        (Ok((eager_items, eager_consumed)), Ok((borrowed_items, borrowed_consumed))) => {
            assert_eq!(eager_items, borrowed_items);
            assert_eq!(eager_consumed, borrowed_consumed);

            let count = eager_items.len() as u64;
            for limit in [count.saturating_sub(1), count, count.saturating_add(1)] {
                assert_eq!(has_more_than(input, limit).unwrap(), count > limit);
            }
        }
        (Err(_), Err(_)) => {}
        (eager, borrowed) => panic!("eager={eager:?}, borrowed={borrowed:?}"),
    }
}

fuzz_target!(|input: &[u8]| {
    assert_differential(input);
});
