# alloy-rlp

This crate provides Ethereum RLP (de)serialization functionality. RLP is
commonly used for Ethereum EL datastructures, and its documentation can be
found [at ethereum.org][ref].

[ref]: https://ethereum.org/en/developers/docs/data-structures-and-encoding/rlp/

## Usage

We strongly recommend deriving RLP traits via the `RlpEncodable` and
`RlpDecodable` derive macros.

Trait methods can then be accessed via the `RlpEncodable` and `RlpDecodable` traits.

## Example

```rust
# #[cfg(feature = "derive")] {
use alloy_rlp::{RlpEncodable, RlpDecodable, Encoder};

#[derive(Debug, RlpEncodable, RlpDecodable, PartialEq)]
pub struct MyStruct {
    pub a: u64,
    pub b: Vec<u8>,
}

let my_struct = MyStruct {
    a: 42,
    b: vec![1, 2, 3],
};

let mut buffer = Vec::<u8>::new();
my_struct.rlp_encode(&mut Encoder::new(&mut buffer));
let decoded = MyStruct::rlp_decode(&mut buffer.as_slice()).unwrap();
assert_eq!(my_struct, decoded);
# }
```
