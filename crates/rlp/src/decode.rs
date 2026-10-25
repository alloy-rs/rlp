use crate::{Error, Header, Result, EMPTY_STRING_CODE};
use bytes::{Bytes, BytesMut};
use core::{
    marker::{PhantomData, PhantomPinned},
    mem::size_of,
    num::{NonZeroU128, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8, NonZeroUsize},
};

const NON_ZERO_INTEGER_ERROR: &str = "non-zero integer cannot be zero";

/// A type that can be decoded from an RLP blob.
pub trait Decodable: Sized {
    /// Decodes the blob into the appropriate type. `buf` must be advanced past
    /// the decoded object.
    fn decode(buf: &mut &[u8]) -> Result<Self>;
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
    fn decode(_buf: &mut &[u8]) -> Result<Self> {
        Ok(Self)
    }
}

impl Decodable for PhantomPinned {
    fn decode(_buf: &mut &[u8]) -> Result<Self> {
        Ok(Self)
    }
}

impl Decodable for bool {
    #[inline]
    fn decode(buf: &mut &[u8]) -> Result<Self> {
        Ok(match u8::decode(buf)? {
            0 => false,
            1 => true,
            _ => return Err(Error::Custom("invalid bool value, must be 0 or 1")),
        })
    }
}

impl<const N: usize> Decodable for [u8; N] {
    #[inline]
    fn decode(from: &mut &[u8]) -> Result<Self> {
        // A canonical short string of exactly `N` bytes: the header is a single known byte.
        if N > 1 && N < 56 {
            if let Some((&b, rest)) = from.split_first() {
                if b == EMPTY_STRING_CODE + N as u8 && rest.len() >= N {
                    let (array, rest) = rest.split_at(N);
                    *from = rest;
                    return Ok(array.try_into().unwrap());
                }
            }
        }

        let bytes = Header::decode_bytes(from, false)?;
        Self::try_from(bytes).map_err(|_| Error::UnexpectedLength)
    }
}

macro_rules! decode_integer {
    ($($t:ty),+ $(,)?) => {$(
        impl Decodable for $t {
            #[inline]
            fn decode(buf: &mut &[u8]) -> Result<Self> {
                const N: usize = size_of::<$t>();

                if let Some(&b) = buf.first() {
                    if b < EMPTY_STRING_CODE {
                        if b == 0 {
                            return Err(Error::LeadingZero);
                        }
                        *buf = &buf[1..];
                        return Ok(b as $t);
                    }

                    let len = (b - EMPTY_STRING_CODE) as usize;
                    if len == 0 {
                        *buf = &buf[1..];
                        return Ok(0);
                    }

                    if len <= N {
                        if let Some(payload) = buf.get(1..=len) {
                            let first = payload[0];
                            if len == 1 {
                                if first < EMPTY_STRING_CODE {
                                    return Err(Error::NonCanonicalSingleByte);
                                }
                            } else if first == 0 {
                                return Err(Error::LeadingZero);
                            }

                            // Load a full `N` bytes and shift out the ones that follow the
                            // payload. At the end of `buf`, fold the payload instead.
                            let value = match buf.get(1..=N).map(<[u8; N]>::try_from) {
                                Some(Ok(word)) => {
                                    <$t>::from_be_bytes(word) >> (<$t>::BITS as usize - 8 * len)
                                }
                                _ => payload.iter().fold(0u128, |v, &x| v << 8 | x as u128) as $t,
                            };
                            *buf = &buf[1 + len..];
                            return Ok(value);
                        }
                    }
                }

                decode_integer_slow::<N>(buf).map(<$t>::from_be_bytes)
            }
        }
    )+};
}

decode_integer!(u8, u16, u32, u64, usize, u128);

/// Decodes the big-endian bytes of an `N`-byte integer through the generic string path.
///
/// Outlined so that the integer fast path stays small enough to inline into callers.
#[inline(never)]
fn decode_integer_slow<const N: usize>(buf: &mut &[u8]) -> Result<[u8; N]> {
    static_left_pad(Header::decode_bytes(buf, false)?)
}

macro_rules! decode_nonzero_integer {
    ($($t:ty => $inner:ty),+ $(,)?) => {$(
        impl Decodable for $t {
            #[inline]
            fn decode(buf: &mut &[u8]) -> Result<Self> {
                <$inner>::decode(buf).and_then(|value| {
                    <$t>::new(value).ok_or(Error::Custom(NON_ZERO_INTEGER_ERROR))
                })
            }
        }
    )+};
}

decode_nonzero_integer! {
    NonZeroU8 => u8,
    NonZeroU16 => u16,
    NonZeroU32 => u32,
    NonZeroU64 => u64,
    NonZeroUsize => usize,
    NonZeroU128 => u128,
}

impl Decodable for Bytes {
    #[inline]
    fn decode(buf: &mut &[u8]) -> Result<Self> {
        Header::decode_bytes(buf, false).map(|x| Self::from(x.to_vec()))
    }
}

impl Decodable for BytesMut {
    #[inline]
    fn decode(buf: &mut &[u8]) -> Result<Self> {
        Header::decode_bytes(buf, false).map(Self::from)
    }
}

impl Decodable for alloc::string::String {
    #[inline]
    fn decode(buf: &mut &[u8]) -> Result<Self> {
        Header::decode_str(buf).map(Into::into)
    }
}

/// Decodes an RLP list and appends each item to the provided vector.
///
/// # Errors
///
/// Returns an error if the input is not a valid RLP list or any item fails to decode.
#[inline]
pub fn decode_append<T: Decodable>(buf: &mut &[u8], out: &mut alloc::vec::Vec<T>) -> Result<()> {
    let mut payload = Header::decode_bytes(buf, true)?;
    while !payload.is_empty() {
        out.push(T::decode(&mut payload)?);
    }
    Ok(())
}

impl<T: Decodable> Decodable for alloc::vec::Vec<T> {
    #[inline]
    fn decode(buf: &mut &[u8]) -> Result<Self> {
        let mut vec = Self::new();
        decode_append(buf, &mut vec)?;
        Ok(vec)
    }
}

macro_rules! wrap_impl {
    ($($(#[$attr:meta])* [$($gen:tt)*] <$t:ty>::$new:ident($t2:ty)),+ $(,)?) => {$(
        $(#[$attr])*
        impl<$($gen)*> Decodable for $t {
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
    #[cfg(target_has_atomic = "ptr")]
    [T: Decodable] <alloc::sync::Arc<T>>::new(T),
}

impl<T: ?Sized + alloc::borrow::ToOwned> Decodable for alloc::borrow::Cow<'_, T>
where
    T::Owned: Decodable,
{
    #[inline]
    fn decode(buf: &mut &[u8]) -> Result<Self> {
        T::Owned::decode(buf).map(Self::Owned)
    }
}

#[cfg(any(feature = "std", feature = "core-net"))]
mod std_impl {
    use super::*;
    #[cfg(all(feature = "core-net", not(feature = "std")))]
    use core::net::{IpAddr, Ipv4Addr, Ipv6Addr};
    #[cfg(feature = "std")]
    use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};

    impl Decodable for IpAddr {
        fn decode(buf: &mut &[u8]) -> Result<Self> {
            let bytes = Header::decode_bytes(buf, false)?;
            match bytes.len() {
                4 => Ok(Self::V4(Ipv4Addr::from(slice_to_array::<4>(bytes).expect("infallible")))),
                16 => {
                    Ok(Self::V6(Ipv6Addr::from(slice_to_array::<16>(bytes).expect("infallible"))))
                }
                _ => Err(Error::UnexpectedLength),
            }
        }
    }

    impl Decodable for Ipv4Addr {
        #[inline]
        fn decode(buf: &mut &[u8]) -> Result<Self> {
            let bytes = Header::decode_bytes(buf, false)?;
            slice_to_array::<4>(bytes).map(Self::from)
        }
    }

    impl Decodable for Ipv6Addr {
        #[inline]
        fn decode(buf: &mut &[u8]) -> Result<Self> {
            let bytes = Header::decode_bytes(buf, false)?;
            slice_to_array::<16>(bytes).map(Self::from)
        }
    }

    #[inline]
    fn slice_to_array<const N: usize>(slice: &[u8]) -> Result<[u8; N]> {
        slice.try_into().map_err(|_| Error::UnexpectedLength)
    }
}

/// Decodes the entire input, ensuring no trailing bytes remain.
///
/// # Errors
///
/// Returns an error if the encoding is invalid or if data remains after decoding the RLP item.
#[inline]
pub fn decode_exact<T: Decodable>(bytes: impl AsRef<[u8]>) -> Result<T> {
    let mut buf = bytes.as_ref();
    let out = T::decode(&mut buf)?;

    // check if there are any remaining bytes after decoding
    if !buf.is_empty() {
        // TODO: introduce a new variant TrailingBytes to better distinguish this error
        return Err(Error::UnexpectedLength);
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{encode, Encodable};
    use core::{
        fmt::Debug,
        num::{NonZeroU128, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8, NonZeroUsize},
    };
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
    fn rlp_fixed_length_followed_by_trailing_bytes() {
        let tail = hex!("ffeeddccbbaa9988");

        let mut buf = &hex!("8D6F62636465666768696A6B6C6Dffeeddccbbaa9988")[..];
        assert_eq!(<[u8; 13]>::decode(&mut buf), Ok(hex!("6f62636465666768696a6b6c6d")));
        assert_eq!(buf, tail);

        let input = &hex!("8D6F62636465666768696A6B6C6Dffeeddccbbaa9988")[..];
        assert_eq!(<[u8; 12]>::decode(&mut &input[..]), Err(Error::UnexpectedLength));
        assert_eq!(<[u8; 14]>::decode(&mut &input[..]), Err(Error::UnexpectedLength));

        assert_eq!(<[u8; 13]>::decode(&mut &hex!("8D6F6263")[..]), Err(Error::InputTooShort));

        let mut buf = &hex!("8105ffeeddccbbaa9988")[..];
        assert_eq!(<[u8; 1]>::decode(&mut buf), Err(Error::NonCanonicalSingleByte));

        let mut buf = &hex!("8180ffeeddccbbaa9988")[..];
        assert_eq!(<[u8; 1]>::decode(&mut buf), Ok([0x80]));
        assert_eq!(buf, tail);
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
    fn rlp_uints_followed_by_trailing_bytes() {
        fn check<T: Decodable + PartialEq + Debug>(input: &[u8], expected: Result<T>, rest: &[u8]) {
            let mut buf = input;
            assert_eq!(T::decode(&mut buf), expected, "input: {}", hex::encode(input));
            if expected.is_ok() {
                assert_eq!(buf, rest, "input: {}", hex::encode(input));
            }
        }

        let tail = hex!("ffeeddccbbaa99887766554433221100");

        for (header, value) in
            [(&hex!("80")[..], 0), (&hex!("09")[..], 9), (&hex!("8180")[..], 0x80)]
        {
            let input = [header, &tail].concat();
            check(&input, Ok(value as u8), &tail);
            check(&input, Ok(value as u16), &tail);
            check(&input, Ok(value as u32), &tail);
            check(&input, Ok(value as u64), &tail);
            check(&input, Ok(value as usize), &tail);
            check(&input, Ok(value as u128), &tail);
        }

        let input = [&hex!("820505")[..], &tail].concat();
        check::<u8>(&input, Err(Error::Overflow), &[]);
        check(&input, Ok(0x0505_u16), &tail);
        check(&input, Ok(0x0505_u32), &tail);
        check(&input, Ok(0x0505_u64), &tail);
        check(&input, Ok(0x0505_usize), &tail);
        check(&input, Ok(0x0505_u128), &tail);

        let input = [&hex!("88ffffffffffffffff")[..], &tail].concat();
        check::<u32>(&input, Err(Error::Overflow), &[]);
        check(&input, Ok(u64::MAX), &tail);
        check(&input, Ok(u64::MAX as usize), &tail);
        check(&input, Ok(u64::MAX as u128), &tail);

        let input = [&hex!("90112233445566778899aabbccddeeff00")[..], &tail].concat();
        check(&input, Ok(0x1122_3344_5566_7788_99aa_bbcc_ddee_ff00_u128), &tail);

        let input = [&hex!("8105")[..], &tail].concat();
        check::<u8>(&input, Err(Error::NonCanonicalSingleByte), &[]);
        check::<u64>(&input, Err(Error::NonCanonicalSingleByte), &[]);
        check::<u128>(&input, Err(Error::NonCanonicalSingleByte), &[]);

        let input = [&hex!("8200f4")[..], &tail].concat();
        check::<u16>(&input, Err(Error::LeadingZero), &[]);
        check::<u64>(&input, Err(Error::LeadingZero), &[]);
        check::<u128>(&input, Err(Error::LeadingZero), &[]);

        let input = [&hex!("00")[..], &tail].concat();
        check::<u8>(&input, Err(Error::LeadingZero), &[]);
        check::<u64>(&input, Err(Error::LeadingZero), &[]);
    }

    #[test]
    fn rlp_nonzero_uints() {
        check_decode([(Ok(NonZeroU8::new(9).unwrap()), &hex!("09")[..])]);
        check_decode([(Ok(NonZeroU16::new(0x0505).unwrap()), &hex!("820505")[..])]);
        check_decode([(Ok(NonZeroU32::new(0xCE0505).unwrap()), &hex!("83CE0505")[..])]);
        check_decode([(Ok(NonZeroU64::new(0xCE05050505).unwrap()), &hex!("85CE05050505")[..])]);
        check_decode([(Ok(NonZeroUsize::new(0x80).unwrap()), &hex!("8180")[..])]);
        check_decode([(
            Ok(NonZeroU128::new(0x10203E405060708090A0B0C0D0E0F2).unwrap()),
            &hex!("8f10203e405060708090a0b0c0d0e0f2")[..],
        )]);
        check_decode::<NonZeroU8, _>([(
            Err(Error::Custom(NON_ZERO_INTEGER_ERROR)),
            &hex!("80")[..],
        )]);
        check_decode::<NonZeroU8, _>([(Err(Error::LeadingZero), &hex!("00")[..])]);
    }

    #[test]
    fn rlp_vectors() {
        check_decode::<Vec<u64>, _>([
            (Ok(vec![]), &hex!("C0")[..]),
            (Ok(vec![0xBBCCB5_u64, 0xFFC0B5_u64]), &hex!("C883BBCCB583FFC0B5")[..]),
        ])
    }

    #[test]
    fn rlp_decode_append_appends_to_existing_vec() {
        let mut input = &hex!("C883BBCCB583FFC0B5")[..];
        let mut values = Vec::with_capacity(4);
        values.push(0x01);
        let capacity = values.capacity();

        decode_append::<u64>(&mut input, &mut values).unwrap();

        assert!(input.is_empty());
        assert_eq!(values, vec![0x01, 0xBBCCB5_u64, 0xFFC0B5_u64]);
        assert_eq!(values.capacity(), capacity);
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

        check_decode_exact::<String>("".into());
        check_decode_exact::<String>("test1234".into());
        check_decode_exact::<Vec<u64>>(vec![]);
        check_decode_exact::<Vec<u64>>(vec![0; 4]);
    }
}
