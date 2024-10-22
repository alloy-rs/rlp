use crate::{header::advance_unchecked, Error, Header, Result};
use bytes::{Buf, Bytes, BytesMut};
use core::marker::{PhantomData, PhantomPinned};

/// The expected type of an RLP header during deserialization. This is used by
/// the [`Decodable`] trait to enforce header correctness during decoding.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Expectation {
    /// Expect a list.
    List,
    /// Expect a bytestring.
    Bytestring,
    /// No expectation. The type has no header, or the header type is data-dependent.
    None,
}

impl Expectation {
    /// Checks if the header matches the expectation.
    pub const fn check(&self, header: &Header) -> Result<()> {
        match self {
            Self::List => {
                if !header.list {
                    return Err(Error::UnexpectedString);
                }
            }
            Self::Bytestring => {
                if header.list {
                    return Err(Error::UnexpectedList);
                }
            }
            _ => {}
        }
        Ok(())
    }
}

/// A type that can be decoded from an RLP blob.
pub trait Decodable: Sized {
    /// Returns the expected header type for this type. Used by
    /// [`Decodable::decode`] to check header correctness during decoding. If
    /// the RLP type is unknown or data-dependent, or if the data is a
    /// single-byte type return [`Expectation::None`].
    fn expected() -> Expectation;

    /// Decode the fields of this type from the blob.
    ///
    /// After this function returns the `buf` MUST be empty.
    fn decode_fields(buf: &mut &[u8]) -> Result<Self>;

    /// Decodes the blob into the appropriate type.
    fn decode(buf: &mut &[u8]) -> Result<Self> {
        let header = Header::decode(buf)?;
        if header.payload_length > buf.len() {
            return Err(Error::InputTooShort);
        }
        Self::expected().check(&header)?;
        let t = Self::decode_fields(buf)?;

        Ok(t)
    }

    /// Decode the blob into the appropriate type, ensuring no trailing bytes
    /// remain.
    fn decode_exact(buf: &mut &[u8]) -> Result<Self> {
        let copy = &mut &**buf;

        // Determine what the appropriate region of the header is
        let header = Header::decode(copy)?;
        let inner_deser_len = header.length_with_payload();

        // Check that the buffer is exact size
        if inner_deser_len > buf.len() {
            return Err(Error::InputTooShort);
        }
        if inner_deser_len < buf.len() {
            return Err(Error::UnexpectedLength);
        }

        // Deserialize using only the appropriate region of the buffer
        let inner_deser = &mut &buf[..inner_deser_len];
        let t = Self::decode(inner_deser)?;
        if !inner_deser.is_empty() {
            // decoding failed to consume the buffer
            return Err(Error::UnexpectedLength);
        }

        // SAFETY: checked above
        unsafe { advance_unchecked(buf, inner_deser_len) };
        Ok(t)
    }
}

/// An active RLP decoder, with a specific slice of a payload.
#[derive(Debug)]
pub struct Rlp<'a> {
    payload_view: &'a [u8],
}

impl<'a> Rlp<'a> {
    /// Instantiate an RLP decoder with a payload slice.
    pub fn new(mut payload: &'a [u8]) -> Result<Self> {
        let payload_view = Header::decode_bytes(&mut payload, true)?;
        Ok(Self { payload_view })
    }

    /// Decode the next item from the buffer.
    #[inline]
    pub fn get_next<T: Decodable>(&mut self) -> Result<Option<T>> {
        if self.payload_view.is_empty() {
            Ok(None)
        } else {
            T::decode(&mut self.payload_view).map(Some)
        }
    }
}

impl<T: ?Sized> Decodable for PhantomData<T> {
    #[inline]
    fn expected() -> Expectation {
        Expectation::None
    }

    #[inline]
    fn decode_fields(_buf: &mut &[u8]) -> Result<Self> {
        Ok(Self)
    }

    #[inline]
    fn decode(_buf: &mut &[u8]) -> Result<Self> {
        Ok(Self)
    }

    #[inline]
    fn decode_exact(_buf: &mut &[u8]) -> Result<Self> {
        Ok(Self)
    }
}

impl Decodable for PhantomPinned {
    #[inline]
    fn expected() -> Expectation {
        Expectation::None
    }

    #[inline]
    fn decode_fields(_buf: &mut &[u8]) -> Result<Self> {
        Ok(Self)
    }

    #[inline]
    fn decode(_buf: &mut &[u8]) -> Result<Self> {
        Ok(Self)
    }

    #[inline]
    fn decode_exact(_buf: &mut &[u8]) -> Result<Self> {
        Ok(Self)
    }
}

impl Decodable for bool {
    #[inline]
    fn expected() -> Expectation {
        Expectation::None
    }

    #[inline]
    fn decode_fields(buf: &mut &[u8]) -> Result<Self> {
        Ok(match u8::decode(buf)? {
            0 => false,
            1 => true,
            _ => return Err(Error::Custom("invalid bool value, must be 0 or 1")),
        })
    }

    #[inline]
    fn decode(buf: &mut &[u8]) -> Result<Self> {
        Self::decode_fields(buf)
    }

    #[inline]
    fn decode_exact(buf: &mut &[u8]) -> Result<Self> {
        if buf.len() != 1 {
            return Err(Error::UnexpectedLength);
        }
        Self::decode_fields(buf)
    }
}

impl<const N: usize> Decodable for [u8; N] {
    #[inline]
    fn expected() -> Expectation {
        Expectation::Bytestring
    }

    #[inline]
    fn decode_fields(buf: &mut &[u8]) -> Result<Self> {
        let mut arr = [0; N];
        arr.copy_from_slice(buf);
        *buf = &[];
        Ok(arr)
    }

    fn decode(buf: &mut &[u8]) -> Result<Self> {
        let header = Header::decode(buf)?;
        if header.payload_length != N {
            return Err(Error::UnexpectedLength);
        }
        if buf.len() < N {
            return Err(Error::InputTooShort);
        }
        Self::expected().check(&header)?;
        let t = Self::decode_fields(buf)?;

        Ok(t)
    }
}

macro_rules! uint_impl {
    ($($t:ty),+ $(,)?) => {$(
        impl Decodable for $t {
            #[inline]
            fn expected() -> Expectation {
                Expectation::None
            }

            #[inline]
            fn decode_fields(buf: &mut &[u8]) -> Result<Self> {
                let first = buf.first().copied().ok_or(Error::InputTooShort)?;
                match first {
                    0 => return Err(Error::LeadingZero),
                    1..crate::EMPTY_STRING_CODE => {
                        buf.advance(1);
                        return Ok(first as $t)
                    },
                    crate::EMPTY_STRING_CODE => {
                        buf.advance(1);
                        return Ok(0)
                    },
                    _ => {
                        let bytes = Header::decode_bytes(buf, false)?;
                        static_left_pad(bytes).map(<$t>::from_be_bytes)
                    }
                }

            }

            #[inline]
            fn decode(buf: &mut &[u8]) -> Result<Self> {
                Self::decode_fields(buf)
            }

            #[inline]
            fn decode_exact(buf: &mut &[u8]) -> Result<Self> {
                let res = Self::decode_fields(buf);
                if !buf.is_empty() {
                    return Err(Error::UnexpectedLength);
                }
                res
            }
        }
    )+};
}

uint_impl!(u8, u16, u32, u64, usize, u128);

impl Decodable for Bytes {
    #[inline]
    fn expected() -> Expectation {
        Expectation::Bytestring
    }

    #[inline]
    fn decode_fields(buf: &mut &[u8]) -> Result<Self> {
        Ok(buf.copy_to_bytes(buf.len()))
    }
}

impl Decodable for BytesMut {
    #[inline]
    fn expected() -> Expectation {
        Expectation::Bytestring
    }

    #[inline]
    fn decode_fields(buf: &mut &[u8]) -> Result<Self> {
        Ok(buf.copy_to_bytes(buf.len()).into())
    }

    #[inline]
    fn decode(buf: &mut &[u8]) -> Result<Self> {
        Header::decode_bytes(buf, false).map(Self::from)
    }
}

impl Decodable for alloc::string::String {
    #[inline]
    fn expected() -> Expectation {
        Expectation::Bytestring
    }

    #[inline]
    fn decode_fields(buf: &mut &[u8]) -> Result<Self> {
        let res = core::str::from_utf8(buf)
            .map_err(|_| Error::Custom("invalid utf8 string"))
            .map(Into::into);
        *buf = &[];
        res
    }

    fn decode(buf: &mut &[u8]) -> Result<Self> {
        let header = Header::decode(buf)?;
        if header.payload_length == 0 {
            if buf.is_empty() {
                return Ok(Self::new());
            } else {
                return Err(Error::UnexpectedLength);
            }
        }
        if header.payload_length > buf.len() {
            return Err(Error::InputTooShort);
        }
        Self::expected().check(&header)?;
        let t = Self::decode_fields(buf)?;

        Ok(t)
    }
}

impl<T: Decodable> Decodable for alloc::vec::Vec<T> {
    #[inline]
    fn expected() -> Expectation {
        Expectation::List
    }

    #[inline]
    fn decode_fields(buf: &mut &[u8]) -> Result<Self> {
        let mut vec = Self::new();
        while !buf.is_empty() {
            vec.push(T::decode(buf)?);
        }
        Ok(vec)
    }
}

macro_rules! wrap_impl {
    ($($(#[$attr:meta])* [$($gen:tt)*] <$t:ty>::$new:ident($t2:ty)),+ $(,)?) => {$(
        $(#[$attr])*
        impl<$($gen)*> Decodable for $t {
            #[inline]
            fn expected() -> Expectation {
                <$t2 as Decodable>::expected()
            }

            #[inline]
            fn decode_fields(buf: &mut &[u8]) -> Result<Self> {
                <$t2 as Decodable>::decode_fields(buf).map(<$t>::$new)
            }

            #[inline]
            fn decode(buf: &mut &[u8]) -> Result<Self> {
                <$t2 as Decodable>::decode(buf).map(<$t>::$new)
            }
        }
    )+};
}

wrap_impl! {
    #[cfg(feature = "arrayvec")]
    [const N: usize] <arrayvec::ArrayVec<u8, N>>::from([u8; N]),
    [T: Decodable] <alloc::boxed::Box<T>>::new(T),
    [T: Decodable] <alloc::rc::Rc<T>>::new(T),
    [T: Decodable] <alloc::sync::Arc<T>>::new(T),
}

impl<T: ?Sized + alloc::borrow::ToOwned> Decodable for alloc::borrow::Cow<'_, T>
where
    T::Owned: Decodable,
{
    #[inline]
    fn expected() -> Expectation {
        T::Owned::expected()
    }

    #[inline]
    fn decode_fields(buf: &mut &[u8]) -> Result<Self> {
        T::Owned::decode_fields(buf).map(Self::Owned)
    }

    #[inline]
    fn decode(buf: &mut &[u8]) -> Result<Self> {
        T::Owned::decode(buf).map(Self::Owned)
    }
}

#[cfg(feature = "std")]
mod std_impl {
    use super::*;
    use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};

    impl Decodable for IpAddr {
        #[inline]
        fn expected() -> Expectation {
            Expectation::Bytestring
        }

        #[inline]
        fn decode_fields(buf: &mut &[u8]) -> Result<Self> {
            if buf.len() == 4 {
                Ipv4Addr::decode_fields(buf).map(Self::V4)
            } else if buf.len() == 16 {
                Ipv6Addr::decode_fields(buf).map(Self::V6)
            } else {
                Err(Error::UnexpectedLength)
            }
        }
    }

    impl Decodable for Ipv4Addr {
        #[inline]
        fn expected() -> Expectation {
            Expectation::Bytestring
        }

        #[inline]
        fn decode_fields(buf: &mut &[u8]) -> Result<Self> {
            let res = slice_to_array::<4>(buf).map(Self::from);
            buf.advance(4);
            res
        }
    }

    impl Decodable for Ipv6Addr {
        #[inline]
        fn expected() -> Expectation {
            Expectation::Bytestring
        }

        #[inline]
        fn decode_fields(buf: &mut &[u8]) -> Result<Self> {
            let res = slice_to_array::<16>(buf).map(Self::from);
            buf.advance(16);
            res
        }
    }
}

/// Decodes the entire input, ensuring no trailing bytes remain.
///
/// # Errors
///
/// Returns an error if the encoding is invalid or if data remains after decoding the RLP item.
#[inline]
pub fn decode_exact<T: Decodable>(bytes: impl AsRef<[u8]>) -> Result<T> {
    T::decode_exact(&mut bytes.as_ref())
}

/// Left-pads a slice to a statically known size array.
///
/// # Errors
///
/// Returns an error if the slice is too long or if the first byte is 0.
#[inline]
pub(crate) fn static_left_pad<const N: usize>(data: &[u8]) -> Result<[u8; N]> {
    if data.len() > N {
        return Err(Error::Overflow);
    }

    let mut v = [0; N];

    // yes, data may empty, e.g. we decode a bool false value
    if data.is_empty() {
        return Ok(v);
    }

    if data[0] == 0 {
        return Err(Error::LeadingZero);
    }

    // SAFETY: length checked above
    unsafe { v.get_unchecked_mut(N - data.len()..) }.copy_from_slice(data);
    Ok(v)
}

#[cfg(feature = "std")]
#[inline]
fn slice_to_array<const N: usize>(slice: &[u8]) -> Result<[u8; N]> {
    slice.try_into().map_err(|_| Error::UnexpectedLength)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{encode, Encodable};
    use core::fmt::Debug;
    use hex_literal::hex;

    #[allow(unused_imports)]
    use alloc::{string::String, vec::Vec};

    fn check_decode<'a, T, IT>(fixtures: IT)
    where
        T: Encodable + Decodable + PartialEq + Debug,
        IT: IntoIterator<Item = (Result<T>, &'a [u8])>,
    {
        for (expected, mut input) in fixtures {
            if let Ok(expected) = &expected {
                assert_eq!(crate::encode(expected), input, "{expected:?}");
            }

            let orig = input;
            assert_eq!(
                T::decode(&mut input),
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

    #[test]
    fn rlp_bool() {
        let out = [0x80];
        let val = bool::decode(&mut &out[..]);
        assert_eq!(Ok(false), val);

        let out = [0x01];
        let val = bool::decode(&mut &out[..]);
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
            (Err(Error::UnexpectedList), &hex!("C0")[..]),
        ])
    }

    #[test]
    fn rlp_fixed_length() {
        check_decode([
            (Ok(hex!("6f62636465666768696a6b6c6d")), &hex!("8D6F62636465666768696A6B6C6D")[..]),
            (Err(Error::UnexpectedLength), &hex!("8C6F62636465666768696A6B6C")[..]),
            (Err(Error::UnexpectedLength), &hex!("8E6F62636465666768696A6B6C6D6E")[..]),
        ])
    }

    #[test]
    fn rlp_u64() {
        check_decode([
            (Ok(9_u64), &hex!("09")[..]),
            (Ok(0_u64), &hex!("80")[..]),
            (Ok(0x0505_u64), &hex!("820505")[..]),
            (Ok(0xCE05050505_u64), &hex!("85CE05050505")[..]),
            (Err(Error::Overflow), &hex!("8AFFFFFFFFFFFFFFFFFF7C")[..]),
            (Err(Error::InputTooShort), &hex!("8BFFFFFFFFFFFFFFFFFF7C")[..]),
            (Err(Error::UnexpectedList), &hex!("C0")[..]),
            (Err(Error::LeadingZero), &hex!("00")[..]),
            (Err(Error::NonCanonicalSingleByte), &hex!("8105")[..]),
            (Err(Error::LeadingZero), &hex!("8200F4")[..]),
            (Err(Error::NonCanonicalSize), &hex!("B8020004")[..]),
            (
                Err(Error::Overflow),
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
            (Err(Error::InputTooShort), &hex!("C1")[..]),
            (Err(Error::InputTooShort), &hex!("D7")[..]),
        ]);
        check_decode::<[u8; 5], _>([
            (Err(Error::InputTooShort), &hex!("C1")[..]),
            (Err(Error::InputTooShort), &hex!("D7")[..]),
        ]);
        #[cfg(feature = "std")]
        check_decode::<std::net::IpAddr, _>([
            (Err(Error::InputTooShort), &hex!("C1")[..]),
            (Err(Error::InputTooShort), &hex!("D7")[..]),
        ]);
        check_decode::<Vec<u8>, _>([
            (Err(Error::InputTooShort), &hex!("C1")[..]),
            (Err(Error::InputTooShort), &hex!("D7")[..]),
        ]);
        check_decode::<String, _>([
            (Err(Error::InputTooShort), &hex!("C1")[..]),
            (Err(Error::InputTooShort), &hex!("D7")[..]),
        ]);
        check_decode::<String, _>([
            (Err(Error::InputTooShort), &hex!("C1")[..]),
            (Err(Error::InputTooShort), &hex!("D7")[..]),
        ]);
        check_decode::<u8, _>([(Err(Error::InputTooShort), &hex!("82")[..])]);
        check_decode::<u64, _>([(Err(Error::InputTooShort), &hex!("82")[..])]);
    }

    #[test]
    fn rlp_full() {
        fn check_decode_exact<T: Decodable + Encodable + PartialEq + Debug>(input: T) {
            let encoded = encode(&input);
            assert_eq!(decode_exact::<T>(&encoded), Ok(input));
            assert_eq!(
                decode_exact::<T>([encoded, vec![0x00]].concat()),
                Err(Error::UnexpectedLength)
            );
        }

        decode_exact::<String>(vec![0x80]).unwrap();

        check_decode_exact::<String>("".into());
        check_decode_exact::<String>("test1234".into());
        check_decode_exact::<Vec<u64>>(vec![]);
        check_decode_exact::<Vec<u64>>(vec![0; 4]);
    }
}
