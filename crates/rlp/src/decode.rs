use crate::{Error, ErrorKind, Header, Result};
use bytes::{Bytes, BytesMut};
use core::marker::{PhantomData, PhantomPinned};

/// A type that can be decoded from an RLP blob.
pub trait RlpDecodable: Sized {
    /// Decodes the blob into the appropriate type. `buf` must be advanced past
    /// the decoded object.
    fn rlp_decode(buf: &mut &[u8]) -> Result<Self>;

    /// Decodes this value from a buffer that omits the value's outer RLP list header.
    ///
    /// The default implementation preserves the historical behavior by decoding the value normally.
    /// Structured implementations may override this to read their fields sequentially.
    #[inline]
    fn rlp_decode_raw(buf: &mut &[u8]) -> Result<Self> {
        Self::rlp_decode(buf)
    }
}

/// An active RLP decoder that tracks byte position while advancing through an input buffer.
#[derive(Clone, Debug)]
pub struct Decoder<'de> {
    buf: &'de [u8],
    bytepos: usize,
}

impl<'de> Decoder<'de> {
    /// Instantiate an RLP decoder with an input slice.
    #[inline]
    pub const fn new(buf: &'de [u8]) -> Self {
        Self { buf, bytepos: 0 }
    }

    /// Instantiate an RLP decoder with an input slice and starting byte position.
    #[inline]
    pub const fn with_bytepos(buf: &'de [u8], bytepos: usize) -> Self {
        Self { buf, bytepos }
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

    /// Returns the current byte position.
    #[inline]
    pub const fn bytepos(&self) -> usize {
        self.bytepos
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
        match Header::decode(&mut self.buf) {
            Ok(header) => {
                self.advance_bytepos(before);
                Ok(header)
            }
            Err(err) => {
                let err = self.map_error(before, err);
                self.advance_bytepos(before);
                Err(err)
            }
        }
    }

    /// Decodes the next payload from the buffer, advancing past the full item.
    #[inline]
    pub fn decode_bytes(&mut self, is_list: bool) -> Result<&'de [u8]> {
        let item_start = self.bytepos;
        let Header { list, payload_length } = self.decode_header()?;

        if list != is_list {
            return Err(Error::with_bytepos(
                if is_list { ErrorKind::UnexpectedString } else { ErrorKind::UnexpectedList },
                item_start,
            ));
        }

        if self.buf.len() < payload_length {
            return Err(self.error(ErrorKind::InputTooShort));
        }

        let (payload, rest) = self.buf.split_at(payload_length);
        self.buf = rest;
        self.bytepos = self.bytepos.saturating_add(payload_length);
        Ok(payload)
    }

    /// Decodes a string slice from the buffer, advancing past the full item.
    #[inline]
    pub fn decode_str(&mut self) -> Result<&'de str> {
        let item_start = self.bytepos;
        let bytes = self.decode_bytes(false)?;
        core::str::from_utf8(bytes)
            .map_err(|_| Error::with_bytepos(ErrorKind::Custom("invalid string"), item_start))
    }

    /// Decodes the next item using [`RlpDecodable::rlp_decode`].
    #[inline]
    pub fn decode_next<T: RlpDecodable>(&mut self) -> Result<T> {
        self.decode_with(T::rlp_decode)
    }

    /// Decodes the next item using [`RlpDecodable::rlp_decode_raw`].
    #[inline]
    pub fn decode_next_raw<T: RlpDecodable>(&mut self) -> Result<T> {
        self.decode_with(T::rlp_decode_raw)
    }

    #[inline]
    fn decode_with<T>(&mut self, f: impl FnOnce(&mut &'de [u8]) -> Result<T>) -> Result<T> {
        let before = self.buf.len();
        match f(&mut self.buf) {
            Ok(value) => {
                self.advance_bytepos(before);
                Ok(value)
            }
            Err(err) => {
                let err = self.map_error(before, err);
                self.advance_bytepos(before);
                Err(err)
            }
        }
    }

    #[inline]
    fn advance_bytepos(&mut self, before: usize) {
        self.bytepos = self.bytepos.saturating_add(before.saturating_sub(self.buf.len()));
    }

    #[inline]
    const fn map_error(&self, before: usize, err: Error) -> Error {
        let relative = before.saturating_sub(self.buf.len()).saturating_add(err.bytepos());
        Error::with_bytepos(err.kind(), self.bytepos.saturating_add(relative))
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
    pub fn get_next<T: RlpDecodable>(&mut self) -> Result<Option<T>> {
        if self.payload_view.is_empty() {
            Ok(None)
        } else {
            T::rlp_decode(&mut self.payload_view).map(Some)
        }
    }
}

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

macro_rules! tuple_impls {
    ($(($($ty:ident),+)),+ $(,)?) => {$(
        impl<$($ty: RlpDecodable),+> RlpDecodable for ($($ty,)+) {
            #[inline]
            fn rlp_decode(buf: &mut &[u8]) -> Result<Self> {
                let mut payload = Header::decode_bytes(buf, true)?;
                let started_len = payload.len();

                let this = Self::rlp_decode_raw(&mut payload)?;

                let consumed = started_len - payload.len();
                if consumed != started_len {
                    return Err(ErrorKind::ListLengthMismatch {
                        expected: started_len,
                        got: consumed,
                    }
                    .into());
                }

                Ok(this)
            }

            #[inline]
            fn rlp_decode_raw(buf: &mut &[u8]) -> Result<Self> {
                Ok(($(<$ty as RlpDecodable>::rlp_decode(buf)?,)+))
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
    use crate::{encode, Error, RlpEncodable};
    use core::fmt::Debug;
    use hex_literal::hex;

    #[allow(unused_imports)]
    use alloc::{string::String, vec::Vec};

    /// Helper to create an `Error` from an `ErrorKind` with bytepos 0.
    fn err(kind: ErrorKind) -> Error {
        Error::new(kind)
    }

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
                Err(Error::new(ErrorKind::UnexpectedLength))
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
