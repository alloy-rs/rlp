//! Serde adapter preserving human-readable values and using RLP bytes in binary formats.
//!
//! Available with the `serde` feature, including in `no_std` builds with `alloc`.
//! Use `#[serde(with = "alloy_rlp::serde_rlp")]` on fields implementing both Serde and RLP
//! serialization. Human-readable formats use the field's normal Serde representation; binary
//! formats use a byte string containing exactly one RLP value. Invalid RLP and trailing bytes
//! are returned as deserialization errors.
//!
//! ```
//! use serde::{Deserialize, Serialize};
//!
//! #[derive(Debug, PartialEq, Serialize, Deserialize)]
//! struct Record {
//!     #[serde(with = "alloy_rlp::serde_rlp")]
//!     field: Vec<u64>,
//! }
//!
//! let record = Record { field: vec![1, 128, 1024] };
//! assert_eq!(serde_json::to_string(&record)?, r#"{"field":[1,128,1024]}"#);
//! let encoded = bincode::serialize(&record)?;
//! assert_eq!(bincode::deserialize::<Record>(&encoded)?, record);
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```

use crate::{Decodable, Encodable};
use core::{fmt, marker::PhantomData};
use serde::{de, Deserialize, Deserializer, Serialize, Serializer};

/// Serialize a value normally in human-readable formats, or as RLP bytes otherwise.
pub fn serialize<T: Serialize + Encodable, S: Serializer>(
    value: &T,
    serializer: S,
) -> Result<S::Ok, S::Error> {
    if serializer.is_human_readable() {
        value.serialize(serializer)
    } else {
        serializer.serialize_bytes(&crate::encode(value))
    }
}

/// Deserialize a human-readable value normally, or decode exactly one RLP value from bytes.
pub fn deserialize<'de, T: Deserialize<'de> + Decodable, D: Deserializer<'de>>(
    deserializer: D,
) -> Result<T, D::Error> {
    if deserializer.is_human_readable() {
        T::deserialize(deserializer)
    } else {
        deserializer.deserialize_bytes(RlpVisitor(PhantomData))
    }
}

struct RlpVisitor<T>(PhantomData<T>);

impl<T: Decodable> de::Visitor<'_> for RlpVisitor<T> {
    type Value = T;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("an RLP-encoded byte string")
    }

    fn visit_bytes<E: de::Error>(self, encoded: &[u8]) -> Result<T, E> {
        crate::decode_exact(encoded).map_err(E::custom)
    }
}
