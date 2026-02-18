use crate::{Error, ErrorKind, Header, Result};
use bytes::{Bytes, BytesMut};
use core::marker::{PhantomData, PhantomPinned};

/// A type that can be decoded from an RLP blob.
pub trait RlpDecodable: Sized {
    /// Decodes the blob into the appropriate type. `buf` must be advanced past
    /// the decoded object.
    fn rlp_decode(buf: &mut &[u8]) -> Result<Self>;

    /// Decodes the type from raw bytes without reading a header.
    ///
    /// This is used for `#[rlp(flatten)]` where the header is handled externally.
    /// The default implementation delegates to [`rlp_decode`](RlpDecodable::rlp_decode).
    fn rlp_decode_raw(buf: &mut &[u8]) -> Result<Self> {
        Self::rlp_decode(buf)
    }
}

/// An active RLP decoder over a payload slice.
///
/// Wraps a byte slice and provides methods for sequentially decoding RLP items, tracking byte
/// position for error reporting.
#[derive(Debug)]
pub struct Decoder<'de> {
    buf: &'de [u8],
    /// The total length of the original payload, used to compute consumed bytes.
    original_len: usize,
    /// An offset added to the consumed-byte count for error reporting.
    start: usize,
}

impl<'de> Decoder<'de> {
    /// Creates a new decoder by reading an RLP list header from the input and
    /// capturing the list payload.
    pub fn new(mut payload: &'de [u8]) -> Result<Self> {
        let payload_view = Header::decode_bytes(&mut payload, true)?;
        let len = payload_view.len();
        Ok(Self { buf: payload_view, original_len: len, start: 0 })
    }

    /// Creates a new decoder from a raw payload slice (without reading a header).
    pub const fn from_raw(buf: &'de [u8]) -> Self {
        let len = buf.len();
        Self { buf, original_len: len, start: 0 }
    }

    /// Creates a new decoder with a specific starting byte position for error reporting.
    pub fn with_start(mut payload: &'de [u8], start: usize) -> Result<Self> {
        let payload_view = Header::decode_bytes(&mut payload, true)?;
        let len = payload_view.len();
        Ok(Self { buf: payload_view, original_len: len, start })
    }

    /// Returns the remaining undecoded bytes.
    pub const fn remaining(&self) -> &'de [u8] {
        self.buf
    }

    /// Returns `true` if there are no more bytes to decode.
    pub const fn is_empty(&self) -> bool {
        self.buf.is_empty()
    }

    /// Returns the current byte position in the input.
    ///
    /// This is `start + (original_len - remaining_len)`, i.e. the number of
    /// bytes consumed so far, offset by the starting position.
    pub const fn bytepos(&self) -> usize {
        self.start.saturating_add(self.original_len - self.buf.len())
    }

    /// Decode the next item from the buffer.
    #[inline]
    pub fn decode_next<T: RlpDecodable>(&mut self) -> Result<Option<T>> {
        if self.buf.is_empty() {
            Ok(None)
        } else {
            T::rlp_decode(&mut self.buf).map(Some)
        }
    }

    /// Decode the next item from the buffer using the raw (headerless) decoder.
    #[inline]
    pub fn decode_next_raw<T: RlpDecodable>(&mut self) -> Result<Option<T>> {
        if self.buf.is_empty() {
            Ok(None)
        } else {
            T::rlp_decode_raw(&mut self.buf).map(Some)
        }
    }

    /// Creates an [`Error`] with the given [`ErrorKind`] at the current byte position.
    pub const fn error(&self, kind: ErrorKind) -> Error {
        Error::with_bytepos(kind, self.bytepos())
    }
}

/// Backwards-compatible alias for [`Decoder`].
#[deprecated(since = "0.4.0", note = "use `Decoder` instead")]
pub type Rlp<'a> = Decoder<'a>;

impl<T: ?Sized> RlpDecodable for PhantomData<T> {
    fn rlp_decode(_buf: &mut &[u8]) -> Result<Self> {
        Ok(Self)
    }
}

impl RlpDecodable for PhantomPinned {
    fn rlp_decode(_buf: &mut &[u8]) -> Result<Self> {
        Ok(Self)
    }
}

impl RlpDecodable for bool {
    #[inline]
    fn rlp_decode(buf: &mut &[u8]) -> Result<Self> {
        Ok(match u8::rlp_decode(buf)? {
            0 => false,
            1 => true,
            _ => return Err(ErrorKind::Custom("invalid bool value, must be 0 or 1").into()),
        })
    }
}

impl<const N: usize> RlpDecodable for [u8; N] {
    #[inline]
    fn rlp_decode(from: &mut &[u8]) -> Result<Self> {
        let bytes = Header::decode_bytes(from, false)?;
        Self::try_from(bytes).map_err(|_| ErrorKind::UnexpectedLength.into())
    }
}

macro_rules! decode_integer {
    ($($t:ty),+ $(,)?) => {$(
        impl RlpDecodable for $t {
            #[inline]
            fn rlp_decode(buf: &mut &[u8]) -> Result<Self> {
                let bytes = Header::decode_bytes(buf, false)?;
                static_left_pad(bytes).map(<$t>::from_be_bytes)
            }
        }
    )+};
}

decode_integer!(u8, u16, u32, u64, usize, u128);

impl RlpDecodable for Bytes {
    #[inline]
    fn rlp_decode(buf: &mut &[u8]) -> Result<Self> {
        Header::decode_bytes(buf, false).map(|x| Self::from(x.to_vec()))
    }
}

impl RlpDecodable for BytesMut {
    #[inline]
    fn rlp_decode(buf: &mut &[u8]) -> Result<Self> {
        Header::decode_bytes(buf, false).map(Self::from)
    }
}

impl RlpDecodable for alloc::string::String {
    #[inline]
    fn rlp_decode(buf: &mut &[u8]) -> Result<Self> {
        Header::decode_str(buf).map(Into::into)
    }
}

impl<T: RlpDecodable> RlpDecodable for alloc::vec::Vec<T> {
    #[inline]
    fn rlp_decode(buf: &mut &[u8]) -> Result<Self> {
        let mut bytes = Header::decode_bytes(buf, true)?;
        let mut vec = Self::new();
        let payload_view = &mut bytes;
        while !payload_view.is_empty() {
            vec.push(T::rlp_decode(payload_view)?);
        }
        Ok(vec)
    }
}

macro_rules! wrap_impl {
    ($($(#[$attr:meta])* [$($gen:tt)*] <$t:ty>::$new:ident($t2:ty)),+ $(,)?) => {$(
        $(#[$attr])*
        impl<$($gen)*> RlpDecodable for $t {
            #[inline]
            fn rlp_decode(buf: &mut &[u8]) -> Result<Self> {
                <$t2 as RlpDecodable>::rlp_decode(buf).map(<$t>::$new)
            }
        }
    )+};
}

wrap_impl! {
    #[cfg(feature = "arrayvec")]
    [const N: usize] <arrayvec::ArrayVec<u8, N>>::from([u8; N]),
    [T: RlpDecodable] <alloc::boxed::Box<T>>::new(T),
    [T: RlpDecodable] <alloc::rc::Rc<T>>::new(T),
    #[cfg(target_has_atomic = "ptr")]
    [T: RlpDecodable] <alloc::sync::Arc<T>>::new(T),
}

macro_rules! tuple_impl {
    ($($ty:ident),+) => {
        impl<$($ty: RlpDecodable),+> RlpDecodable for ($($ty,)+) {
            #[inline]
            fn rlp_decode(buf: &mut &[u8]) -> Result<Self> {
                let b = &mut Header::decode_bytes(buf, true)?;
                let result = ($($ty::rlp_decode(b)?,)+);
                if !b.is_empty() {
                    return Err(ErrorKind::ListLengthMismatch {
                        expected: 0,
                        got: b.len(),
                    }.into());
                }
                Ok(result)
            }
        }
    };
}

tuple_impl!(A);
tuple_impl!(A, B);
tuple_impl!(A, B, C);
tuple_impl!(A, B, C, D);
tuple_impl!(A, B, C, D, E);
tuple_impl!(A, B, C, D, E, F);
tuple_impl!(A, B, C, D, E, F, G);
tuple_impl!(A, B, C, D, E, F, G, H);
tuple_impl!(A, B, C, D, E, F, G, H, I);
tuple_impl!(A, B, C, D, E, F, G, H, I, J);
tuple_impl!(A, B, C, D, E, F, G, H, I, J, K);
tuple_impl!(A, B, C, D, E, F, G, H, I, J, K, L);

impl<T: ?Sized + alloc::borrow::ToOwned> RlpDecodable for alloc::borrow::Cow<'_, T>
where
    T::Owned: RlpDecodable,
{
    #[inline]
    fn rlp_decode(buf: &mut &[u8]) -> Result<Self> {
        T::Owned::rlp_decode(buf).map(Self::Owned)
    }
}

#[cfg(any(feature = "std", feature = "core-net"))]
mod std_impl {
    use super::*;
    #[cfg(all(feature = "core-net", not(feature = "std")))]
    use core::net::{IpAddr, Ipv4Addr, Ipv6Addr};
    #[cfg(feature = "std")]
    use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};

    impl RlpDecodable for IpAddr {
        fn rlp_decode(buf: &mut &[u8]) -> Result<Self> {
            let bytes = Header::decode_bytes(buf, false)?;
            match bytes.len() {
                4 => Ok(Self::V4(Ipv4Addr::from(slice_to_array::<4>(bytes).expect("infallible")))),
                16 => {
                    Ok(Self::V6(Ipv6Addr::from(slice_to_array::<16>(bytes).expect("infallible"))))
                }
                _ => Err(ErrorKind::UnexpectedLength.into()),
            }
        }
    }

    impl RlpDecodable for Ipv4Addr {
        #[inline]
        fn rlp_decode(buf: &mut &[u8]) -> Result<Self> {
            let bytes = Header::decode_bytes(buf, false)?;
            slice_to_array::<4>(bytes).map(Self::from)
        }
    }

    impl RlpDecodable for Ipv6Addr {
        #[inline]
        fn rlp_decode(buf: &mut &[u8]) -> Result<Self> {
            let bytes = Header::decode_bytes(buf, false)?;
            slice_to_array::<16>(bytes).map(Self::from)
        }
    }

    #[inline]
    fn slice_to_array<const N: usize>(slice: &[u8]) -> Result<[u8; N]> {
        slice.try_into().map_err(|_| ErrorKind::UnexpectedLength.into())
    }
}

/// Decodes the entire input, ensuring no trailing bytes remain.
///
/// # Errors
///
/// Returns an error if the encoding is invalid or if data remains after decoding the RLP item.
#[inline]
pub fn decode_exact<T: RlpDecodable>(bytes: impl AsRef<[u8]>) -> Result<T> {
    let mut buf = bytes.as_ref();
    let out = T::rlp_decode(&mut buf)?;

    // check if there are any remaining bytes after decoding
    if !buf.is_empty() {
        // TODO: introduce a new variant TrailingBytes to better distinguish this error
        return Err(ErrorKind::UnexpectedLength.into());
    }

    Ok(out)
}

/// Left-pads a slice to a statically known size array.
///
/// # Errors
///
/// Returns an error if the slice is too long or if the first byte is 0.
#[inline]
pub(crate) fn static_left_pad<const N: usize>(data: &[u8]) -> Result<[u8; N]> {
    if data.len() > N {
        return Err(ErrorKind::Overflow.into());
    }

    let mut v = [0; N];

    // yes, data may empty, e.g. we decode a bool false value
    if data.is_empty() {
        return Ok(v);
    }

    if data[0] == 0 {
        return Err(ErrorKind::LeadingZero.into());
    }

    // SAFETY: length checked above
    unsafe { v.get_unchecked_mut(N - data.len()..) }.copy_from_slice(data);
    Ok(v)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{encode, RlpEncodable};
    use core::fmt::Debug;
    use hex_literal::hex;

    #[allow(unused_imports)]
    use alloc::{string::String, vec::Vec};

    fn check_decode<'a, T, IT>(fixtures: IT)
    where
        T: RlpEncodable + RlpDecodable + PartialEq + Debug,
        IT: IntoIterator<Item = (Result<T>, &'a [u8])>,
    {
        for (expected, mut input) in fixtures {
            if let Ok(expected) = &expected {
                assert_eq!(crate::encode(expected), input, "{expected:?}");
            }

            let orig = input;
            assert_eq!(
                T::rlp_decode(&mut input),
                expected,
                "input: {}{}",
                hex::encode(orig),
                expected.as_ref().map_or_else(
                    |_| String::new(),
                    |expected| format!("; expected: {}", hex::encode(crate::encode(expected)))
                )
            );

            if expected.is_ok() {
                assert_eq!(input, &[]);
            }
        }
    }

    /// Helper to create an `Error` from an `ErrorKind` with bytepos 0.
    fn err(kind: ErrorKind) -> Error {
        Error::new(kind)
    }

    #[test]
    fn rlp_bool() {
        let out = [0x80];
        let val = bool::rlp_decode(&mut &out[..]);
        assert_eq!(Ok(false), val);

        let out = [0x01];
        let val = bool::rlp_decode(&mut &out[..]);
        assert_eq!(Ok(true), val);
    }

    #[test]
    fn rlp_strings() {
        check_decode::<Bytes, _>([
            (Ok(hex!("00")[..].to_vec().into()), &hex!("00")[..]),
            (
                Ok(hex!("6f62636465666768696a6b6c6d")[..].to_vec().into()),
                &hex!("8D6F62636465666768696A6B6C6D")[..],
            ),
            (Err(err(ErrorKind::UnexpectedList)), &hex!("C0")[..]),
        ])
    }

    #[test]
    fn rlp_fixed_length() {
        check_decode([
            (Ok(hex!("6f62636465666768696a6b6c6d")), &hex!("8D6F62636465666768696A6B6C6D")[..]),
            (Err(err(ErrorKind::UnexpectedLength)), &hex!("8C6F62636465666768696A6B6C")[..]),
            (Err(err(ErrorKind::UnexpectedLength)), &hex!("8E6F62636465666768696A6B6C6D6E")[..]),
        ])
    }

    #[test]
    fn rlp_u64() {
        check_decode([
            (Ok(9_u64), &hex!("09")[..]),
            (Ok(0_u64), &hex!("80")[..]),
            (Ok(0x0505_u64), &hex!("820505")[..]),
            (Ok(0xCE05050505_u64), &hex!("85CE05050505")[..]),
            (Err(err(ErrorKind::Overflow)), &hex!("8AFFFFFFFFFFFFFFFFFF7C")[..]),
            (Err(err(ErrorKind::InputTooShort)), &hex!("8BFFFFFFFFFFFFFFFFFF7C")[..]),
            (Err(err(ErrorKind::UnexpectedList)), &hex!("C0")[..]),
            (Err(err(ErrorKind::LeadingZero)), &hex!("00")[..]),
            (Err(err(ErrorKind::NonCanonicalSingleByte)), &hex!("8105")[..]),
            (Err(err(ErrorKind::LeadingZero)), &hex!("8200F4")[..]),
            (Err(err(ErrorKind::NonCanonicalSize)), &hex!("B8020004")[..]),
            (
                Err(err(ErrorKind::Overflow)),
                &hex!("A101000000000000000000000000000000000000008B000000000000000000000000")[..],
            ),
        ])
    }

    #[test]
    fn rlp_vectors() {
        check_decode::<Vec<u64>, _>([
            (Ok(vec![]), &hex!("C0")[..]),
            (Ok(vec![0xBBCCB5_u64, 0xFFC0B5_u64]), &hex!("C883BBCCB583FFC0B5")[..]),
        ])
    }

    #[cfg(feature = "std")]
    #[test]
    fn rlp_ip() {
        use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};

        let localhost4 = Ipv4Addr::new(127, 0, 0, 1);
        let localhost6 = localhost4.to_ipv6_mapped();
        let expected4 = &hex!("847F000001")[..];
        let expected6 = &hex!("9000000000000000000000ffff7f000001")[..];
        check_decode::<Ipv4Addr, _>([(Ok(localhost4), expected4)]);
        check_decode::<Ipv6Addr, _>([(Ok(localhost6), expected6)]);
        check_decode::<IpAddr, _>([
            (Ok(IpAddr::V4(localhost4)), expected4),
            (Ok(IpAddr::V6(localhost6)), expected6),
        ]);
    }

    #[test]
    fn malformed_rlp() {
        check_decode::<Bytes, _>([
            (Err(err(ErrorKind::InputTooShort)), &hex!("C1")[..]),
            (Err(err(ErrorKind::InputTooShort)), &hex!("D7")[..]),
        ]);
        check_decode::<[u8; 5], _>([
            (Err(err(ErrorKind::InputTooShort)), &hex!("C1")[..]),
            (Err(err(ErrorKind::InputTooShort)), &hex!("D7")[..]),
        ]);
        #[cfg(feature = "std")]
        check_decode::<std::net::IpAddr, _>([
            (Err(err(ErrorKind::InputTooShort)), &hex!("C1")[..]),
            (Err(err(ErrorKind::InputTooShort)), &hex!("D7")[..]),
        ]);
        check_decode::<Vec<u8>, _>([
            (Err(err(ErrorKind::InputTooShort)), &hex!("C1")[..]),
            (Err(err(ErrorKind::InputTooShort)), &hex!("D7")[..]),
        ]);
        check_decode::<String, _>([
            (Err(err(ErrorKind::InputTooShort)), &hex!("C1")[..]),
            (Err(err(ErrorKind::InputTooShort)), &hex!("D7")[..]),
        ]);
        check_decode::<String, _>([
            (Err(err(ErrorKind::InputTooShort)), &hex!("C1")[..]),
            (Err(err(ErrorKind::InputTooShort)), &hex!("D7")[..]),
        ]);
        check_decode::<u8, _>([(Err(err(ErrorKind::InputTooShort)), &hex!("82")[..])]);
        check_decode::<u64, _>([(Err(err(ErrorKind::InputTooShort)), &hex!("82")[..])]);
    }

    #[test]
    fn rlp_full() {
        fn check_decode_exact<T: RlpDecodable + RlpEncodable + PartialEq + Debug>(input: T) {
            let encoded = encode(&input);
            assert_eq!(decode_exact::<T>(&encoded), Ok(input));
            assert_eq!(
                decode_exact::<T>([encoded, vec![0x00]].concat()),
                Err(err(ErrorKind::UnexpectedLength))
            );
        }

        check_decode_exact::<String>("".into());
        check_decode_exact::<String>("test1234".into());
        check_decode_exact::<Vec<u64>>(vec![]);
        check_decode_exact::<Vec<u64>>(vec![0; 4]);
    }

    #[test]
    fn decoder_basic() {
        let data = crate::encode(vec![1u64, 2u64, 3u64]);
        let mut decoder = Decoder::new(&data).unwrap();
        assert_eq!(decoder.decode_next::<u64>().unwrap(), Some(1));
        assert_eq!(decoder.decode_next::<u64>().unwrap(), Some(2));
        assert_eq!(decoder.decode_next::<u64>().unwrap(), Some(3));
        assert_eq!(decoder.decode_next::<u64>().unwrap(), None);
        assert!(decoder.is_empty());
    }

    #[test]
    fn decoder_from_raw() {
        // Encode two values without a list header
        let mut raw = Vec::new();
        1u64.rlp_encode(&mut crate::Encoder::new(&mut raw));
        2u64.rlp_encode(&mut crate::Encoder::new(&mut raw));

        let mut decoder = Decoder::from_raw(&raw);
        assert_eq!(decoder.decode_next::<u64>().unwrap(), Some(1));
        assert_eq!(decoder.decode_next::<u64>().unwrap(), Some(2));
        assert!(decoder.is_empty());
    }

    #[test]
    fn decoder_new_rejects_non_list() {
        // A non-list RLP item (string "hello")
        let data = crate::encode("hello");
        let result = Decoder::new(&data);
        assert_eq!(result.unwrap_err().kind, ErrorKind::UnexpectedString);
    }

    #[test]
    fn decoder_with_start() {
        let data = crate::encode(vec![10u64, 20u64]);
        let mut decoder = Decoder::with_start(&data, 100).unwrap();
        assert_eq!(decoder.decode_next::<u64>().unwrap(), Some(10));
        assert_eq!(decoder.decode_next::<u64>().unwrap(), Some(20));
        assert!(decoder.is_empty());
    }

    #[test]
    fn decoder_remaining() {
        let data = crate::encode(vec![1u64, 2u64]);
        let mut decoder = Decoder::new(&data).unwrap();
        let initial_len = decoder.remaining().len();
        assert!(initial_len > 0);

        decoder.decode_next::<u64>().unwrap();
        assert!(decoder.remaining().len() < initial_len);

        decoder.decode_next::<u64>().unwrap();
        assert!(decoder.remaining().is_empty());
    }

    #[test]
    fn decoder_error() {
        let data = crate::encode(vec![1u64]);
        let decoder = Decoder::new(&data).unwrap();
        let e = decoder.error(ErrorKind::Custom("test"));
        assert_eq!(e.kind, ErrorKind::Custom("test"));
        assert_eq!(e.bytepos, decoder.bytepos());
    }

    #[test]
    fn decoder_decode_next_raw() {
        let data = crate::encode(vec![5u64, 6u64]);
        let mut decoder = Decoder::new(&data).unwrap();
        // rlp_decode_raw defaults to rlp_decode, so this should work identically
        assert_eq!(decoder.decode_next_raw::<u64>().unwrap(), Some(5));
        assert_eq!(decoder.decode_next_raw::<u64>().unwrap(), Some(6));
        assert_eq!(decoder.decode_next_raw::<u64>().unwrap(), None);
    }

    #[test]
    fn rlp_decode_raw_default() {
        // rlp_decode_raw delegates to rlp_decode by default
        let encoded = crate::encode(42u64);
        let mut buf = encoded.as_slice();
        let val = u64::rlp_decode_raw(&mut buf).unwrap();
        assert_eq!(val, 42);
        assert!(buf.is_empty());
    }

    #[test]
    fn decoder_new_empty_input() {
        let result = Decoder::new(&[]);
        assert_eq!(result.unwrap_err().kind, ErrorKind::InputTooShort);
    }

    #[test]
    fn decoder_new_empty_list() {
        // 0xC0 is the RLP encoding of an empty list
        let mut decoder = Decoder::new(&[0xC0]).unwrap();
        assert!(decoder.is_empty());
        assert!(decoder.remaining().is_empty());
        assert_eq!(decoder.decode_next::<u64>().unwrap(), None);
    }

    #[test]
    fn decoder_with_start_rejects_non_list() {
        let data = crate::encode("hello");
        let result = Decoder::with_start(&data, 50);
        let e = result.unwrap_err();
        assert_eq!(e.kind, ErrorKind::UnexpectedString);
    }

    #[test]
    fn decoder_from_raw_empty() {
        let mut decoder = Decoder::from_raw(&[]);
        assert!(decoder.is_empty());
        assert!(decoder.remaining().is_empty());
        assert_eq!(decoder.decode_next::<u64>().unwrap(), None);
        assert_eq!(decoder.decode_next_raw::<u64>().unwrap(), None);
    }

    #[test]
    fn decoder_decode_next_error_propagation() {
        // 0xC3 = list of 3 payload bytes
        // 0x82, 0x00, 0xF4 = 2-byte string with leading zero → LeadingZero when decoded as u64
        let corrupt: &[u8] = &[0xC3, 0x82, 0x00, 0xF4];
        let mut decoder = Decoder::new(corrupt).unwrap();
        let result = decoder.decode_next::<u64>();
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().kind, ErrorKind::LeadingZero);
    }

    #[test]
    fn decoder_decode_next_raw_error_propagation() {
        // Same leading-zero corruption via decode_next_raw
        let corrupt: &[u8] = &[0xC3, 0x82, 0x00, 0xF4];
        let mut decoder = Decoder::new(corrupt).unwrap();
        let result = decoder.decode_next_raw::<u64>();
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().kind, ErrorKind::LeadingZero);
    }

    #[test]
    fn decoder_bytepos_advances() {
        let data = crate::encode(vec![1u64, 2u64]);
        let mut decoder = Decoder::new(&data).unwrap();
        assert_eq!(decoder.bytepos(), 0);
        decoder.decode_next::<u64>().unwrap(); // consumes 1 byte (single-byte int 1)
        assert_eq!(decoder.bytepos(), 1);
        decoder.decode_next::<u64>().unwrap(); // consumes 1 byte (single-byte int 2)
        assert_eq!(decoder.bytepos(), 2);
    }

    #[test]
    fn rlp_tuples() {
        // Single-element tuple
        let data = crate::encode((42u64,));
        let decoded = <(u64,)>::rlp_decode(&mut data.as_slice()).unwrap();
        assert_eq!(decoded, (42,));

        // Two-element tuple
        let data = crate::encode((1u64, 2u64));
        let decoded = <(u64, u64)>::rlp_decode(&mut data.as_slice()).unwrap();
        assert_eq!(decoded, (1, 2));

        // Three-element heterogeneous tuple
        let data = crate::encode((1u8, 2u16, 3u64));
        let decoded = <(u8, u16, u64)>::rlp_decode(&mut data.as_slice()).unwrap();
        assert_eq!(decoded, (1, 2, 3));

        // Roundtrip
        let original = (100u64, 200u32, true);
        let data = crate::encode(original);
        let decoded = <(u64, u32, bool)>::rlp_decode(&mut data.as_slice()).unwrap();
        assert_eq!(decoded, original);
    }

    #[test]
    fn decoder_bytepos_with_start_offset() {
        let data = crate::encode(vec![1u64]);
        let mut decoder = Decoder::with_start(&data, 100).unwrap();
        assert_eq!(decoder.bytepos(), 100);
        decoder.decode_next::<u64>().unwrap();
        assert_eq!(decoder.bytepos(), 101);
    }
}
