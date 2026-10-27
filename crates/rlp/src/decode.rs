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

/// A borrowed cursor over the items of an RLP list.
///
/// Unlike [`Rlp`], this cursor can return the original encoding of an item without decoding or
/// allocating it. This is useful for protocols that need to validate an item's position, count,
/// or identifier before materializing its contents.
#[derive(Debug)]
pub struct RlpList<'a> {
    payload: &'a [u8],
}

impl<'a> RlpList<'a> {
    /// Creates a cursor over the next RLP list in `buf`, advancing `buf` past that list.
    #[inline]
    pub fn decode(buf: &mut &'a [u8]) -> Result<Self> {
        Ok(Self { payload: Header::decode_bytes(buf, true)? })
    }

    /// Returns the next complete RLP item without decoding it.
    ///
    /// The returned slice includes the item's RLP header. It aliases the source buffer and no
    /// allocation is performed.
    #[inline]
    pub fn next_raw(&mut self) -> Result<Option<&'a [u8]>> {
        if self.payload.is_empty() {
            return Ok(None);
        }

        let raw = self.payload;
        let mut remainder = raw;
        let header = Header::decode(&mut remainder)?;
        let header_length = raw.len() - remainder.len();
        let item_length = header_length + header.payload_length;

        // `Header::decode` verified that the declared payload is available.
        self.payload = &raw[item_length..];
        Ok(Some(&raw[..item_length]))
    }

    /// Decodes the next item in the list.
    #[inline]
    pub fn next<T: Decodable>(&mut self) -> Result<Option<T>> {
        let Some(mut raw) = self.next_raw()? else {
            return Ok(None);
        };
        let value = T::decode(&mut raw)?;
        if !raw.is_empty() {
            return Err(Error::UnexpectedLength);
        }
        Ok(Some(value))
    }

    /// Returns whether this list contains more than `limit` items.
    ///
    /// Stops as soon as it encounters the first excessive item, without scanning the remainder.
    /// This makes it suitable for enforcing protocol item limits before allocating a decoded
    /// collection.
    #[inline]
    pub fn has_more_than(&mut self, limit: u64) -> Result<bool> {
        for _ in 0..limit {
            if self.next_raw()?.is_none() {
                return Ok(false);
            }
        }
        Ok(self.next_raw()?.is_some())
    }

    /// Returns `true` if the list has no remaining items.
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.payload.is_empty()
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

        // A canonical long string of exactly `N` bytes: `0xB8 N` or `0xB9 N_hi N_lo`.
        if N >= 56 && N <= 0xFFFF {
            let [hi, lo] = (N as u16).to_be_bytes();
            let (header, len) = if N <= 0xFF { ([0xB8, lo, 0], 2) } else { ([0xB9, hi, lo], 3) };
            if let Some(rest) = from.strip_prefix(&header[..len]) {
                if rest.len() >= N {
                    let (array, rest) = rest.split_at(N);
                    *from = rest;
                    return Ok(array.try_into().unwrap());
                }
            }
        }

        decode_array_slow(from)
    }
}

/// Decodes an `N`-byte array through the generic string path.
///
/// Outlined so that the array fast paths stay small enough to inline into callers.
#[inline(never)]
fn decode_array_slow<const N: usize>(from: &mut &[u8]) -> Result<[u8; N]> {
    let bytes = Header::decode_bytes(from, false)?;
    bytes.try_into().map_err(|_| Error::UnexpectedLength)
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
    fn rlp_list_returns_raw_items_without_allocating_a_collection() {
        let mut encoded = &hex!("C501820102C0")[..];
        let mut list = RlpList::decode(&mut encoded).unwrap();

        assert_eq!(list.next_raw().unwrap(), Some(&hex!("01")[..]));
        assert_eq!(list.next_raw().unwrap(), Some(&hex!("820102")[..]));
        assert_eq!(list.next_raw().unwrap(), Some(&hex!("C0")[..]));
        assert_eq!(list.next_raw().unwrap(), None);
        assert!(list.is_empty());
        assert!(encoded.is_empty());
    }

    #[test]
    fn rlp_list_stops_after_the_first_excessive_item() {
        let mut encoded = &hex!("C5C0C0C0C0C0")[..];
        let mut list = RlpList::decode(&mut encoded).unwrap();

        assert!(list.has_more_than(2).unwrap());
        // The cursor stopped at the first excessive item, leaving the remainder untouched.
        assert_eq!(list.next_raw().unwrap(), Some(&hex!("C0")[..]));
    }

    #[test]
    fn rlp_list_accepts_a_u64_limit() {
        let mut encoded = &hex!("C1C0")[..];
        let mut list = RlpList::decode(&mut encoded).unwrap();

        assert!(!list.has_more_than(u64::MAX).unwrap());
    }

    #[test]
    fn rlp_list_does_not_inspect_a_malformed_suffix_after_exceeding_limit() {
        // The third item declares a long string but has no length byte. The second valid item is
        // already sufficient to establish that this list exceeds a limit of one.
        let mut encoded = &hex!("C3C0C0B8")[..];
        let mut list = RlpList::decode(&mut encoded).unwrap();

        assert!(list.has_more_than(1).unwrap());
    }

    #[test]
    fn rlp_list_next_requires_the_decoder_to_consume_the_item() {
        struct DoesNotConsume;

        impl Decodable for DoesNotConsume {
            fn decode(_buf: &mut &[u8]) -> Result<Self> {
                Ok(Self)
            }
        }

        let mut encoded = &hex!("C101")[..];
        let mut list = RlpList::decode(&mut encoded).unwrap();

        assert!(matches!(list.next::<DoesNotConsume>(), Err(Error::UnexpectedLength)));
    }

    #[test]
    fn rlp_list_validates_each_raw_item_before_returning_it() {
        let mut encoded = &hex!("C1B8")[..];
        let mut list = RlpList::decode(&mut encoded).unwrap();

        assert_eq!(list.next_raw(), Err(Error::InputTooShort));
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
    fn rlp_fixed_length_long_strings() {
        fn encode(len: usize, payload: &[u8]) -> Vec<u8> {
            let mut out = Vec::new();
            Header { list: false, payload_length: len }.encode(&mut out);
            out.extend_from_slice(payload);
            out
        }

        fn check<const N: usize>() {
            let payload: Vec<u8> = (0..N).map(|i| i as u8 | 1).collect();
            let array = <[u8; N]>::try_from(&payload[..]).unwrap();
            let tail = hex!("ffeeddcc");

            let encoded = encode(N, &payload);
            let header_len = encoded.len() - N;
            assert_eq!(header_len, if N <= 0xFF { 2 } else { 3 });

            let mut buf = &encoded[..];
            assert_eq!(<[u8; N]>::decode(&mut buf), Ok(array));
            assert!(buf.is_empty());

            let with_tail = [&encoded[..], &tail].concat();
            let mut buf = &with_tail[..];
            assert_eq!(<[u8; N]>::decode(&mut buf), Ok(array));
            assert_eq!(buf, tail);

            for len in [0, 1, header_len, header_len + 1, encoded.len() - 1] {
                let mut buf = &encoded[..len];
                assert_eq!(<[u8; N]>::decode(&mut buf), Err(Error::InputTooShort), "len {len}");
            }

            // The header declares one byte more or fewer than the array holds.
            let longer = encode(N + 1, &[&payload[..], &[1]].concat());
            assert_eq!(<[u8; N]>::decode(&mut &longer[..]), Err(Error::UnexpectedLength));
            let shorter = encode(N - 1, &payload[..N - 1]);
            assert_eq!(<[u8; N]>::decode(&mut &shorter[..]), Err(Error::UnexpectedLength));

            // A list header is not a string.
            let mut list = encoded.clone();
            list[0] += 0x40;
            assert_eq!(<[u8; N]>::decode(&mut &list[..]), Err(Error::UnexpectedList));
        }

        check::<56>();
        check::<255>();
        check::<256>();
        check::<257>();
        check::<0x0102>();
        check::<0xFFFF>();

        // The length bytes are big-endian.
        let buf = [&[0xB9, 0x02, 0x01][..], &[1; 0x0102]].concat();
        assert_eq!(<[u8; 0x0102]>::decode(&mut &buf[..]), Err(Error::InputTooShort));

        // Length-of-length mismatches and leading zeros in the length are not canonical.
        let buf = [&[0xB9, 0x00, 0xFF][..], &[1; 255]].concat();
        assert_eq!(<[u8; 255]>::decode(&mut &buf[..]), Err(Error::LeadingZero));
        let buf = [&[0xB8, 0x37][..], &[1; 55]].concat();
        assert_eq!(<[u8; 55]>::decode(&mut &buf[..]), Err(Error::NonCanonicalSize));
        let buf = [&[0xBA, 0x00, 0x01, 0x00][..], &[1; 256]].concat();
        assert_eq!(<[u8; 256]>::decode(&mut &buf[..]), Err(Error::LeadingZero));
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
        if usize::BITS == 64 {
            check(&input, Ok(u64::MAX as usize), &tail);
        } else {
            check::<usize>(&input, Err(Error::Overflow), &[]);
        }
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
