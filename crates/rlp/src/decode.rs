use crate::{Error, ErrorKind, Header, Result};
use bytes::{Bytes, BytesMut};
use core::{
    marker::{PhantomData, PhantomPinned},
    num::{NonZeroU128, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8, NonZeroUsize},
};

const NON_ZERO_INTEGER_ERROR: &str = "non-zero integer cannot be zero";

/// A type that can be decoded from an RLP blob.
pub trait RlpDecodable<'de>: Sized {
    /// Minimum number of raw RLP items this type needs to decode successfully.
    const MIN_RAW_ITEMS: usize = 1;

    /// Decodes the blob into the appropriate type. `decoder` must be advanced past
    /// the decoded object.
    fn rlp_decode(decoder: &mut Decoder<'de>) -> Result<Self>;

    /// Decodes this value from a buffer that omits the value's outer RLP list header.
    #[inline]
    fn rlp_decode_raw(decoder: &mut Decoder<'de>) -> Result<Self> {
        Self::rlp_decode(decoder)
    }
}

/// An active RLP decoder that tracks byte position while advancing through an input buffer.
#[derive(Clone, Debug)]
pub struct Decoder<'de> {
    buf: &'de [u8],
    bytepos: usize,
    raw_tail_items: usize,
}

impl<'de> Decoder<'de> {
    /// Instantiate an RLP decoder with an input slice.
    #[inline]
    pub const fn new(buf: &'de [u8]) -> Self {
        Self { buf, bytepos: 0, raw_tail_items: 0 }
    }

    /// Instantiate an RLP decoder with an input slice and starting byte position.
    #[inline]
    pub const fn with_bytepos(buf: &'de [u8], bytepos: usize) -> Self {
        Self { buf, bytepos, raw_tail_items: 0 }
    }

    /// Returns the remaining undecoded input.
    #[inline]
    pub const fn as_slice(&self) -> &'de [u8] {
        self.buf
    }

    /// Returns true if the decoder has no remaining input.
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.buf.is_empty()
    }

    /// Returns the number of remaining undecoded bytes.
    #[inline]
    pub const fn len(&self) -> usize {
        self.buf.len()
    }

    /// Returns the current byte position.
    #[inline]
    pub const fn bytepos(&self) -> usize {
        self.bytepos
    }

    /// Returns the raw item count reserved for enclosing flattened fields.
    #[inline]
    pub const fn raw_tail_items(&self) -> usize {
        self.raw_tail_items
    }

    /// Temporarily sets the raw item count reserved for enclosing flattened fields.
    #[inline]
    pub fn with_raw_tail_items<R>(
        &mut self,
        raw_tail_items: usize,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        let previous = self.raw_tail_items;
        self.raw_tail_items = raw_tail_items;
        let result = f(self);
        self.raw_tail_items = previous;
        result
    }

    /// Returns the next undecoded byte without advancing.
    #[inline]
    pub fn peek(&self) -> Option<u8> {
        self.buf.first().copied()
    }

    /// Creates an error at the current byte position.
    #[inline]
    pub const fn error(&self, kind: ErrorKind) -> Error {
        Error::with_bytepos(kind, self.bytepos)
    }

    /// Creates an error at the given byte position.
    #[inline]
    pub const fn error_at(&self, kind: ErrorKind, bytepos: usize) -> Error {
        Error::with_bytepos(kind, bytepos)
    }

    /// Decodes the next RLP header, advancing past the header but not the payload.
    #[inline]
    pub fn decode_header(&mut self) -> Result<Header> {
        let before = self.buf.len();
        match Header::decode_at(&mut self.buf, self.bytepos) {
            Ok(header) => {
                self.advance_bytepos(before);
                Ok(header)
            }
            Err(err) => {
                self.advance_bytepos(before);
                Err(err)
            }
        }
    }

    /// Advances by `cnt` bytes and returns the advanced-over slice.
    #[inline]
    pub fn advance(&mut self, cnt: usize) -> Result<&'de [u8]> {
        if self.buf.len() < cnt {
            return Err(self.error(ErrorKind::InputTooShort));
        }
        let (bytes, rest) = self.buf.split_at(cnt);
        self.buf = rest;
        self.bytepos = self.bytepos.saturating_add(cnt);
        Ok(bytes)
    }

    /// Decodes the next payload from the buffer, advancing past the full item.
    #[inline]
    pub fn decode_bytes(&mut self, is_list: bool) -> Result<&'de [u8]> {
        self.decode_bytes_with_position(is_list).map(|(bytes, _)| bytes)
    }

    #[inline]
    fn decode_bytes_with_position(&mut self, is_list: bool) -> Result<(&'de [u8], usize)> {
        let item_start = self.bytepos;
        let Header { list, payload_length } = self.decode_header()?;

        if list != is_list {
            return Err(Error::with_bytepos(
                if is_list { ErrorKind::UnexpectedString } else { ErrorKind::UnexpectedList },
                item_start,
            ));
        }

        let payload_start = self.bytepos;
        self.advance(payload_length).map(|bytes| (bytes, payload_start))
    }

    /// Decodes the next payload as a nested decoder.
    #[inline]
    pub fn decode_payload(&mut self, is_list: bool) -> Result<Self> {
        let (payload, payload_start) = self.decode_bytes_with_position(is_list)?;
        Ok(Self::with_bytepos(payload, payload_start))
    }

    /// Decodes a string slice from the buffer, advancing past the full item.
    #[inline]
    pub fn decode_str(&mut self) -> Result<&'de str> {
        let (bytes, payload_start) = self.decode_bytes_with_position(false)?;
        core::str::from_utf8(bytes)
            .map_err(|_| Error::with_bytepos(ErrorKind::Custom("invalid string"), payload_start))
    }

    /// Decodes the next item using [`RlpDecodable::rlp_decode`].
    #[inline]
    pub fn decode_next<T: RlpDecodable<'de>>(&mut self) -> Result<T> {
        T::rlp_decode(self)
    }

    /// Decodes the next item using [`RlpDecodable::rlp_decode_raw`].
    #[inline]
    pub fn decode_next_raw<T: RlpDecodable<'de>>(&mut self) -> Result<T> {
        T::rlp_decode_raw(self)
    }

    /// Counts the remaining RLP items without advancing this decoder.
    #[inline]
    pub fn remaining_rlp_items(&self) -> Result<usize> {
        let mut decoder = Self::with_bytepos(self.buf, self.bytepos);
        let mut count = 0usize;
        while !decoder.is_empty() {
            decoder.skip_next()?;
            count = count.saturating_add(1);
        }
        Ok(count)
    }

    /// Skips the next RLP item.
    #[inline]
    pub fn skip_next(&mut self) -> Result<()> {
        let Header { payload_length, .. } = self.decode_header()?;
        self.advance(payload_length)?;
        Ok(())
    }

    #[inline]
    fn advance_bytepos(&mut self, before: usize) {
        self.bytepos = self.bytepos.saturating_add(before.saturating_sub(self.buf.len()));
    }
}

/// An active RLP decoder, with a specific slice of a payload.
#[derive(Debug)]
pub struct Rlp<'a> {
    decoder: Decoder<'a>,
}

impl<'a> Rlp<'a> {
    /// Instantiate an RLP decoder with a payload slice.
    pub fn new(payload: &'a [u8]) -> Result<Self> {
        let mut decoder = Decoder::new(payload);
        let decoder = decoder.decode_payload(true)?;
        Ok(Self { decoder })
    }

    /// Decode the next item from the buffer.
    #[inline]
    pub fn get_next<T: RlpDecodable<'a>>(&mut self) -> Result<Option<T>> {
        if self.decoder.is_empty() {
            Ok(None)
        } else {
            T::rlp_decode(&mut self.decoder).map(Some)
        }
    }
}

impl<'de, T: ?Sized> RlpDecodable<'de> for PhantomData<T> {
    const MIN_RAW_ITEMS: usize = 0;

    fn rlp_decode(_decoder: &mut Decoder<'de>) -> Result<Self> {
        Ok(Self)
    }
}

impl<'de> RlpDecodable<'de> for PhantomPinned {
    const MIN_RAW_ITEMS: usize = 0;

    fn rlp_decode(_decoder: &mut Decoder<'de>) -> Result<Self> {
        Ok(Self)
    }
}

impl<'de> RlpDecodable<'de> for bool {
    #[inline]
    fn rlp_decode(decoder: &mut Decoder<'de>) -> Result<Self> {
        let bytepos = decoder.bytepos();
        Ok(match u8::rlp_decode(decoder)? {
            0 => false,
            1 => true,
            _ => {
                return Err(Error::with_bytepos(
                    ErrorKind::Custom("invalid bool value, must be 0 or 1"),
                    bytepos,
                ))
            }
        })
    }
}

impl<'de, const N: usize> RlpDecodable<'de> for [u8; N] {
    #[inline]
    fn rlp_decode(decoder: &mut Decoder<'de>) -> Result<Self> {
        let (bytes, payload_start) = decoder.decode_bytes_with_position(false)?;
        Self::try_from(bytes)
            .map_err(|_| Error::with_bytepos(ErrorKind::UnexpectedLength, payload_start))
    }
}

macro_rules! decode_integer {
    ($($t:ty),+ $(,)?) => {$(
        impl<'de> RlpDecodable<'de> for $t {
            #[inline]
            fn rlp_decode(decoder: &mut Decoder<'de>) -> Result<Self> {
                let (bytes, payload_start) = decoder.decode_bytes_with_position(false)?;
                static_left_pad(bytes)
                    .map(<$t>::from_be_bytes)
                    .map_err(|err| Error::with_bytepos(err.kind(), payload_start.saturating_add(err.bytepos())))
            }
        }
    )+};
}

decode_integer!(u8, u16, u32, u64, usize, u128);

macro_rules! decode_nonzero_integer {
    ($($t:ty => $inner:ty),+ $(,)?) => {$(
        impl<'de> RlpDecodable<'de> for $t {
            #[inline]
            fn rlp_decode(decoder: &mut Decoder<'de>) -> Result<Self> {
                let bytepos = decoder.bytepos();
                <$inner>::rlp_decode(decoder).and_then(|value| {
                    <$t>::new(value).ok_or_else(|| {
                        Error::with_bytepos(ErrorKind::Custom(NON_ZERO_INTEGER_ERROR), bytepos)
                    })
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

impl<'de> RlpDecodable<'de> for Bytes {
    #[inline]
    fn rlp_decode(decoder: &mut Decoder<'de>) -> Result<Self> {
        decoder.decode_bytes(false).map(|x| Self::from(x.to_vec()))
    }
}

impl<'de> RlpDecodable<'de> for BytesMut {
    #[inline]
    fn rlp_decode(decoder: &mut Decoder<'de>) -> Result<Self> {
        decoder.decode_bytes(false).map(Self::from)
    }
}

impl<'de> RlpDecodable<'de> for alloc::string::String {
    #[inline]
    fn rlp_decode(decoder: &mut Decoder<'de>) -> Result<Self> {
        decoder.decode_str().map(Into::into)
    }
}

impl<'de, T: RlpDecodable<'de>> RlpDecodable<'de> for alloc::vec::Vec<T> {
    #[inline]
    fn rlp_decode(decoder: &mut Decoder<'de>) -> Result<Self> {
        let mut vec = Self::new();
        decode_append(decoder, &mut vec)?;
        Ok(vec)
    }
}

/// Decodes an RLP list and appends each item to the provided vector.
///
/// # Errors
///
/// Returns an error if the input is not a valid RLP list or any item fails to decode.
#[inline]
pub fn decode_append<'de, T: RlpDecodable<'de>>(
    decoder: &mut Decoder<'de>,
    out: &mut alloc::vec::Vec<T>,
) -> Result<()> {
    let mut payload = decoder.decode_payload(true)?;
    while !payload.is_empty() {
        out.push(T::rlp_decode(&mut payload)?);
    }
    Ok(())
}

macro_rules! tuple_impls {
    ($(($($ty:ident),+)),+ $(,)?) => {$(
        impl<'de, $($ty: RlpDecodable<'de>),+> RlpDecodable<'de> for ($($ty,)+) {
            const MIN_RAW_ITEMS: usize = 0usize $(+ <$ty as RlpDecodable<'de>>::MIN_RAW_ITEMS)+;

            #[inline]
            fn rlp_decode(decoder: &mut Decoder<'de>) -> Result<Self> {
                let mut payload = decoder.decode_payload(true)?;
                let started_len = payload.len();

                let this = Self::rlp_decode_raw(&mut payload)?;

                let consumed = started_len.saturating_sub(payload.len());
                if consumed != started_len {
                    return Err(payload.error(ErrorKind::ListLengthMismatch {
                            expected: started_len,
                            got: consumed,
                        }));
                }

                Ok(this)
            }

            #[inline]
            fn rlp_decode_raw(decoder: &mut Decoder<'de>) -> Result<Self> {
                Ok(($(<$ty as RlpDecodable<'de>>::rlp_decode(decoder)?,)+))
            }
        }
    )+};
}

tuple_impls! {
    (A),
    (A, B),
    (A, B, C),
    (A, B, C, D),
    (A, B, C, D, E),
    (A, B, C, D, E, F),
    (A, B, C, D, E, F, G),
    (A, B, C, D, E, F, G, H),
    (A, B, C, D, E, F, G, H, I),
    (A, B, C, D, E, F, G, H, I, J),
    (A, B, C, D, E, F, G, H, I, J, K),
    (A, B, C, D, E, F, G, H, I, J, K, L),
}

macro_rules! wrap_impl {
    ($($(#[$attr:meta])* [$($gen:tt)*] <$t:ty>::$new:ident($t2:ty)),+ $(,)?) => {$(
        $(#[$attr])*
        impl<'de, $($gen)*> RlpDecodable<'de> for $t {
            const MIN_RAW_ITEMS: usize = <$t2 as RlpDecodable<'de>>::MIN_RAW_ITEMS;

            #[inline]
            fn rlp_decode(decoder: &mut Decoder<'de>) -> Result<Self> {
                <$t2 as RlpDecodable<'de>>::rlp_decode(decoder).map(<$t>::$new)
            }
        }
    )+};
}

wrap_impl! {
    #[cfg(feature = "arrayvec")]
    [const N: usize] <arrayvec::ArrayVec<u8, N>>::from([u8; N]),
    [T: RlpDecodable<'de>] <alloc::boxed::Box<T>>::new(T),
    [T: RlpDecodable<'de>] <alloc::rc::Rc<T>>::new(T),
    #[cfg(target_has_atomic = "ptr")]
    [T: RlpDecodable<'de>] <alloc::sync::Arc<T>>::new(T),
}

impl<'de, T: ?Sized + alloc::borrow::ToOwned> RlpDecodable<'de> for alloc::borrow::Cow<'_, T>
where
    T::Owned: RlpDecodable<'de>,
{
    const MIN_RAW_ITEMS: usize = <T::Owned as RlpDecodable<'de>>::MIN_RAW_ITEMS;

    #[inline]
    fn rlp_decode(decoder: &mut Decoder<'de>) -> Result<Self> {
        T::Owned::rlp_decode(decoder).map(Self::Owned)
    }
}

#[cfg(any(feature = "std", feature = "core-net"))]
mod std_impl {
    use super::*;
    #[cfg(all(feature = "core-net", not(feature = "std")))]
    use core::net::{IpAddr, Ipv4Addr, Ipv6Addr};
    #[cfg(feature = "std")]
    use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};

    impl<'de> RlpDecodable<'de> for IpAddr {
        fn rlp_decode(decoder: &mut Decoder<'de>) -> Result<Self> {
            let (bytes, payload_start) = decoder.decode_bytes_with_position(false)?;
            match bytes.len() {
                4 => Ok(Self::V4(Ipv4Addr::from(slice_to_array::<4>(bytes).expect("infallible")))),
                16 => {
                    Ok(Self::V6(Ipv6Addr::from(slice_to_array::<16>(bytes).expect("infallible"))))
                }
                _ => Err(Error::with_bytepos(ErrorKind::UnexpectedLength, payload_start)),
            }
        }
    }

    impl<'de> RlpDecodable<'de> for Ipv4Addr {
        #[inline]
        fn rlp_decode(decoder: &mut Decoder<'de>) -> Result<Self> {
            let (bytes, payload_start) = decoder.decode_bytes_with_position(false)?;
            slice_to_array::<4>(bytes)
                .map(Self::from)
                .map_err(|err| Error::with_bytepos(err.kind(), payload_start))
        }
    }

    impl<'de> RlpDecodable<'de> for Ipv6Addr {
        #[inline]
        fn rlp_decode(decoder: &mut Decoder<'de>) -> Result<Self> {
            let (bytes, payload_start) = decoder.decode_bytes_with_position(false)?;
            slice_to_array::<16>(bytes)
                .map(Self::from)
                .map_err(|err| Error::with_bytepos(err.kind(), payload_start))
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
pub fn decode_exact<T>(bytes: impl AsRef<[u8]>) -> Result<T>
where
    T: for<'de> RlpDecodable<'de>,
{
    let mut decoder = Decoder::new(bytes.as_ref());
    let out = T::rlp_decode(&mut decoder)?;

    // check if there are any remaining bytes after decoding
    if !decoder.is_empty() {
        // TODO: introduce a new variant TrailingBytes to better distinguish this error
        return Err(decoder.error(ErrorKind::UnexpectedLength));
    }

    Ok(out)
}

/// Decodes a raw optional field without consuming items reserved for enclosing fields.
///
/// When another raw optional field follows, `0x80` is interpreted as the `None` gap sentinel.
/// That byte is also the valid RLP encoding of values such as `0`, `false`, and empty strings, so
/// those values are only unambiguous when no later optional raw field is present.
#[doc(hidden)]
#[inline]
pub fn decode_optional_raw<'de, T: RlpDecodable<'de>>(
    decoder: &mut Decoder<'de>,
    min_tail_items: usize,
) -> Result<Option<T>> {
    let reserved_items = decoder.raw_tail_items().saturating_add(min_tail_items);
    let remaining_items = decoder.remaining_rlp_items()?;
    if remaining_items <= reserved_items {
        return Ok(None);
    }

    if remaining_items > reserved_items.saturating_add(1)
        && decoder.peek() == Some(crate::EMPTY_STRING_CODE)
    {
        decoder.advance(1)?;
        Ok(None)
    } else {
        T::rlp_decode(decoder).map(Some)
    }
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
    use crate::{encode, Error, RlpEncodable};
    use core::{
        fmt::Debug,
        num::{NonZeroU128, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8, NonZeroUsize},
    };
    use hex_literal::hex;

    #[allow(unused_imports)]
    use alloc::{string::String, vec::Vec};

    fn err(kind: ErrorKind) -> Error {
        Error::new(kind)
    }

    fn err_at(kind: ErrorKind, bytepos: usize) -> Error {
        Error::with_bytepos(kind, bytepos)
    }

    fn check_decode<'a, T, IT>(fixtures: IT)
    where
        T: RlpEncodable + for<'de> RlpDecodable<'de> + PartialEq + Debug,
        IT: IntoIterator<Item = (Result<T>, &'a [u8])>,
    {
        for (expected, input) in fixtures {
            if let Ok(expected) = &expected {
                assert_eq!(crate::encode(expected), input, "{expected:?}");
            }

            let orig = input;
            let mut decoder = Decoder::new(input);
            assert_eq!(
                T::rlp_decode(&mut decoder),
                expected,
                "input: {}{}",
                hex::encode(orig),
                expected.as_ref().map_or_else(
                    |_| String::new(),
                    |expected| format!("; expected: {}", hex::encode(crate::encode(expected)))
                )
            );

            if expected.is_ok() {
                assert!(decoder.is_empty());
            }
        }
    }

    #[test]
    fn rlp_bool() {
        let out = [0x80];
        let val = bool::rlp_decode(&mut Decoder::new(&out));
        assert_eq!(Ok(false), val);

        let out = [0x01];
        let val = bool::rlp_decode(&mut Decoder::new(&out));
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
            (Err(err_at(ErrorKind::UnexpectedLength, 1)), &hex!("8C6F62636465666768696A6B6C")[..]),
            (
                Err(err_at(ErrorKind::UnexpectedLength, 1)),
                &hex!("8E6F62636465666768696A6B6C6D6E")[..],
            ),
        ])
    }

    #[test]
    fn rlp_u64() {
        check_decode([
            (Ok(9_u64), &hex!("09")[..]),
            (Ok(0_u64), &hex!("80")[..]),
            (Ok(0x0505_u64), &hex!("820505")[..]),
            (Ok(0xCE05050505_u64), &hex!("85CE05050505")[..]),
            (Err(err_at(ErrorKind::Overflow, 1)), &hex!("8AFFFFFFFFFFFFFFFFFF7C")[..]),
            (Err(err_at(ErrorKind::InputTooShort, 1)), &hex!("8BFFFFFFFFFFFFFFFFFF7C")[..]),
            (Err(err(ErrorKind::UnexpectedList)), &hex!("C0")[..]),
            (Err(err(ErrorKind::LeadingZero)), &hex!("00")[..]),
            (Err(err_at(ErrorKind::NonCanonicalSingleByte, 1)), &hex!("8105")[..]),
            (Err(err_at(ErrorKind::LeadingZero, 1)), &hex!("8200F4")[..]),
            (Err(err_at(ErrorKind::NonCanonicalSize, 2)), &hex!("B8020004")[..]),
            (
                Err(err_at(ErrorKind::Overflow, 1)),
                &hex!("A101000000000000000000000000000000000000008B000000000000000000000000")[..],
            ),
        ])
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
            Err(err_at(ErrorKind::Custom(NON_ZERO_INTEGER_ERROR), 0)),
            &hex!("80")[..],
        )]);
        check_decode::<NonZeroU8, _>([(Err(err(ErrorKind::LeadingZero)), &hex!("00")[..])]);
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
        let input = hex!("C883BBCCB583FFC0B5");
        let mut decoder = Decoder::new(&input);
        let mut values = Vec::with_capacity(4);
        values.push(0x01);
        let capacity = values.capacity();

        decode_append::<u64>(&mut decoder, &mut values).unwrap();

        assert!(decoder.is_empty());
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
            (Err(err_at(ErrorKind::InputTooShort, 1)), &hex!("C1")[..]),
            (Err(err_at(ErrorKind::InputTooShort, 1)), &hex!("D7")[..]),
        ]);
        check_decode::<[u8; 5], _>([
            (Err(err_at(ErrorKind::InputTooShort, 1)), &hex!("C1")[..]),
            (Err(err_at(ErrorKind::InputTooShort, 1)), &hex!("D7")[..]),
        ]);
        #[cfg(feature = "std")]
        check_decode::<std::net::IpAddr, _>([
            (Err(err_at(ErrorKind::InputTooShort, 1)), &hex!("C1")[..]),
            (Err(err_at(ErrorKind::InputTooShort, 1)), &hex!("D7")[..]),
        ]);
        check_decode::<Vec<u8>, _>([
            (Err(err_at(ErrorKind::InputTooShort, 1)), &hex!("C1")[..]),
            (Err(err_at(ErrorKind::InputTooShort, 1)), &hex!("D7")[..]),
        ]);
        check_decode::<String, _>([
            (Err(err_at(ErrorKind::InputTooShort, 1)), &hex!("C1")[..]),
            (Err(err_at(ErrorKind::InputTooShort, 1)), &hex!("D7")[..]),
        ]);
        check_decode::<String, _>([
            (Err(err_at(ErrorKind::InputTooShort, 1)), &hex!("C1")[..]),
            (Err(err_at(ErrorKind::InputTooShort, 1)), &hex!("D7")[..]),
        ]);
        check_decode::<u8, _>([(Err(err_at(ErrorKind::InputTooShort, 1)), &hex!("82")[..])]);
        check_decode::<u64, _>([(Err(err_at(ErrorKind::InputTooShort, 1)), &hex!("82")[..])]);
    }

    #[test]
    fn rlp_full() {
        fn check_decode_exact<T: for<'de> RlpDecodable<'de> + RlpEncodable + PartialEq + Debug>(
            input: T,
        ) {
            let encoded = encode(&input);
            let encoded_len = encoded.len();
            assert_eq!(decode_exact::<T>(&encoded), Ok(input));
            assert_eq!(
                decode_exact::<T>([encoded, vec![0x00]].concat()),
                Err(Error::with_bytepos(ErrorKind::UnexpectedLength, encoded_len))
            );
        }

        check_decode_exact::<String>("".into());
        check_decode_exact::<String>("test1234".into());
        check_decode_exact::<Vec<u64>>(vec![]);
        check_decode_exact::<Vec<u64>>(vec![0; 4]);
    }

    #[test]
    fn decoder_advances_bytepos() {
        let mut input = Vec::new();
        1u8.rlp_encode(&mut crate::Encoder::new(&mut input));
        "cat".rlp_encode(&mut crate::Encoder::new(&mut input));

        let mut decoder = Decoder::new(&input);
        assert_eq!(decoder.decode_next::<u8>(), Ok(1));
        assert_eq!(decoder.bytepos(), 1);
        assert_eq!(decoder.decode_str(), Ok("cat"));
        assert_eq!(decoder.bytepos(), input.len());
        assert!(decoder.is_empty());
    }

    #[test]
    fn decoder_reports_error_bytepos() {
        let input = [0x01, 0xC0];
        let mut decoder = Decoder::new(&input);
        assert_eq!(decoder.decode_next::<u8>(), Ok(1));
        let err = decoder.decode_bytes(false).unwrap_err();
        assert_eq!(err.kind(), ErrorKind::UnexpectedList);
        assert_eq!(err.bytepos(), 1);

        let input = [0x01, 0x82];
        let mut decoder = Decoder::new(&input);
        assert_eq!(decoder.decode_next::<u8>(), Ok(1));
        let err = decoder.decode_next::<u16>().unwrap_err();
        assert_eq!(err.kind(), ErrorKind::InputTooShort);
        assert_eq!(err.bytepos(), 2);
    }

    #[test]
    fn decoder_decode_next_raw() {
        let mut input = Vec::new();
        (1u8, 2u8).rlp_encode_raw(&mut crate::Encoder::new(&mut input));
        3u8.rlp_encode(&mut crate::Encoder::new(&mut input));

        let mut decoder = Decoder::new(&input);
        assert_eq!(decoder.decode_next_raw::<(u8, u8)>(), Ok((1, 2)));
        assert_eq!(decoder.bytepos(), 2);
        assert_eq!(decoder.decode_next::<u8>(), Ok(3));
        assert!(decoder.is_empty());
    }
}
