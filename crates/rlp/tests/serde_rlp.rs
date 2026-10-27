//! Tests for the optional Serde adapter's human-readable and binary representations.

#![cfg(feature = "serde")]

use serde::{Deserialize, Serialize};

#[derive(Debug, PartialEq, Serialize, Deserialize)]
struct Record {
    #[serde(with = "alloy_rlp::serde_rlp")]
    field: Vec<u64>,
}

#[derive(Serialize, Deserialize)]
struct EncodedRecord {
    field: Vec<u8>,
}

#[test]
fn preserves_json() {
    let record = Record { field: vec![1, 128, 1024] };
    let json = serde_json::to_string(&record).unwrap();
    assert_eq!(json, r#"{"field":[1,128,1024]}"#);
    assert_eq!(serde_json::from_str::<Record>(&json).unwrap(), record);
}

#[test]
fn binary_uses_rlp_bytes() {
    for field in [vec![], vec![0], vec![1, 128, 1024, u64::MAX]] {
        let record = Record { field };
        let encoded = bincode::serialize(&record).unwrap();
        let raw: EncodedRecord = bincode::deserialize(&encoded).unwrap();
        assert_eq!(raw.field, alloy_rlp::encode(&record.field));
        assert_eq!(bincode::serialize(&raw).unwrap(), encoded);
        assert_eq!(bincode::deserialize::<Record>(&encoded).unwrap(), record);
        assert_eq!(bincode::deserialize_from::<_, Record>(encoded.as_slice()).unwrap(), record);
    }
}

#[test]
fn rejects_invalid_rlp() {
    // Missing input, truncated list payload, scalar instead of a list, and non-canonical integer.
    for field in [vec![], vec![0xc1], vec![0x80], vec![0xc2, 0x81, 0x01]] {
        let encoded = bincode::serialize(&EncodedRecord { field }).unwrap();
        assert!(bincode::deserialize::<Record>(&encoded).is_err());
    }
}

#[test]
fn rejects_trailing_rlp_bytes() {
    let mut field = alloy_rlp::encode(vec![1u64, 128, 1024]);
    field.push(0x80);
    let encoded = bincode::serialize(&EncodedRecord { field }).unwrap();
    assert!(bincode::deserialize::<Record>(&encoded).is_err());
}
