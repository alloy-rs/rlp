use crate::{Header, EMPTY_STRING_CODE};
use bytes::{BufMut, Bytes, BytesMut};
use core::{
    borrow::Borrow,
    marker::{PhantomData, PhantomPinned},
};

#[allow(unused_imports)]
use alloc::vec::Vec;

#[cfg(feature = "arrayvec")]
use arrayvec::ArrayVec;

/// A type that can be encoded via RLP.
pub trait Encodable {
    /// Encode the inner fields into the `out` buffer, without a header.
    ///
    /// This is a low-level function that should generally not be called
    /// directly. Use [`encode`] instead.
    fn encode_fields(&self, out: &mut dyn BufMut);

    /// Returns the length of the encoded fields in bytes.
    fn encoded_fields_length(&self) -> usize;

    /// Returns `true` if the type is a string.
    fn is_string(&self) -> bool;

    /// Creates a header for the encoding. For types for which a header is
    /// unnecessary,
    fn header(&self) -> Option<Header> {
        Some(Header { list: !self.is_string(), payload_length: self.encoded_fields_length() })
    }

    /// Encodes the type into the `out` buffer.
    fn encode(&self, out: &mut dyn BufMut) {
        if let Some(h) = self.header() {
            h.encode(out);
        }
        self.encode_fields(out);
    }

    /// Returns the length of the encoding of this type in bytes.
    #[inline]
    fn length(&self) -> usize {
        self.header()
            .map(|h| h.length_with_payload())
            .unwrap_or_else(|| self.encoded_fields_length())
    }
}

// The existence of this function makes the compiler catch if the Encodable
// trait is "object-safe" or not.
fn _assert_trait_object(_b: &dyn Encodable) {}

/// Defines the max length of an [`Encodable`] type as a const generic.
///
/// # Safety
///
/// An invalid value can cause the encoder to panic.
pub unsafe trait MaxEncodedLen<const LEN: usize>: Encodable {}

/// Defines the max length of an [`Encodable`] type as an associated constant.
///
/// # Safety
///
/// An invalid value can cause the encoder to panic.
pub unsafe trait MaxEncodedLenAssoc: Encodable {
    /// The maximum length.
    const LEN: usize;
}

/// Implement [`MaxEncodedLen`] and [`MaxEncodedLenAssoc`] for a type.
///
/// # Safety
///
/// An invalid value can cause the encoder to panic.
#[macro_export]
macro_rules! impl_max_encoded_len {
    ($t:ty, $len:expr) => {
        unsafe impl $crate::MaxEncodedLen<{ $len }> for $t {}
        unsafe impl $crate::MaxEncodedLenAssoc for $t {
            const LEN: usize = $len;
        }
    };
}

macro_rules! to_be_bytes_trimmed {
    ($be:ident, $x:expr) => {{
        $be = $x.to_be_bytes();
        &$be[($x.leading_zeros() / 8) as usize..]
    }};
}
pub(crate) use to_be_bytes_trimmed;

impl Encodable for [u8] {
    #[inline]
    fn encode_fields(&self, out: &mut dyn BufMut) {
        out.put_slice(self);
    }

    #[inline]
    fn encoded_fields_length(&self) -> usize {
        self.len()
    }

    #[inline]
    fn is_string(&self) -> bool {
        true
    }

    #[inline]
    fn header(&self) -> Option<Header> {
        (self.len() != 1 || self[0] >= EMPTY_STRING_CODE)
            .then(|| Header { list: false, payload_length: self.encoded_fields_length() })
    }

    #[inline]
    fn length(&self) -> usize {
        const ESC: usize = EMPTY_STRING_CODE as usize;
        match self.len() {
            ..ESC => 1,
            ESC.. => {
                self.header().expect("encoding rules enforce header presence").length_with_payload()
            }
        }
    }
}

impl<T: ?Sized> Encodable for PhantomData<T> {
    #[inline]
    fn encode_fields(&self, _out: &mut dyn BufMut) {}

    #[inline]
    fn encoded_fields_length(&self) -> usize {
        0
    }

    #[inline]
    fn is_string(&self) -> bool {
        true
    }

    #[inline]
    fn header(&self) -> Option<Header> {
        None
    }

    #[inline]
    fn encode(&self, _out: &mut dyn BufMut) {}

    #[inline]
    fn length(&self) -> usize {
        0
    }
}

impl Encodable for PhantomPinned {
    #[inline]
    fn encode_fields(&self, _out: &mut dyn BufMut) {}

    #[inline]
    fn encoded_fields_length(&self) -> usize {
        0
    }

    #[inline]
    fn is_string(&self) -> bool {
        true
    }

    #[inline]
    fn header(&self) -> Option<Header> {
        None
    }

    #[inline]
    fn encode(&self, _out: &mut dyn BufMut) {}

    #[inline]
    fn length(&self) -> usize {
        0
    }
}

impl<const N: usize> Encodable for [u8; N] {
    #[inline]
    fn encode_fields(&self, out: &mut dyn BufMut) {
        self.as_slice().encode_fields(out);
    }

    #[inline]
    fn encoded_fields_length(&self) -> usize {
        self.as_slice().encoded_fields_length()
    }

    #[inline]
    fn is_string(&self) -> bool {
        true
    }

    #[inline]
    fn header(&self) -> Option<Header> {
        self.as_slice().header()
    }

    #[inline]
    fn length(&self) -> usize {
        self.as_slice().length()
    }

    #[inline]
    fn encode(&self, out: &mut dyn BufMut) {
        self.as_slice().encode(out);
    }
}

unsafe impl<const N: usize> MaxEncodedLenAssoc for [u8; N] {
    const LEN: usize = N + length_of_length(N);
}

impl Encodable for str {
    #[inline]
    fn encode_fields(&self, out: &mut dyn BufMut) {
        self.as_bytes().encode_fields(out);
    }

    #[inline]
    fn encoded_fields_length(&self) -> usize {
        self.as_bytes().encoded_fields_length()
    }

    #[inline]
    fn is_string(&self) -> bool {
        true
    }

    #[inline]
    fn header(&self) -> Option<Header> {
        self.as_bytes().header()
    }

    #[inline]
    fn encode(&self, out: &mut dyn BufMut) {
        self.as_bytes().encode(out);
    }

    #[inline]
    fn length(&self) -> usize {
        self.as_bytes().length()
    }
}

impl Encodable for bool {
    #[inline]
    fn encode_fields(&self, out: &mut dyn BufMut) {
        out.put_u8(if *self { 1 } else { EMPTY_STRING_CODE });
    }

    #[inline]
    fn encoded_fields_length(&self) -> usize {
        1
    }

    #[inline]
    fn is_string(&self) -> bool {
        true
    }

    #[inline]
    fn header(&self) -> Option<Header> {
        None
    }

    #[inline]
    fn length(&self) -> usize {
        // a `bool` is always `< EMPTY_STRING_CODE`
        1
    }

    #[inline]
    fn encode(&self, out: &mut dyn BufMut) {
        self.encode_fields(out);
    }
}

impl_max_encoded_len!(bool, <u8 as MaxEncodedLenAssoc>::LEN);

macro_rules! uint_impl {
    ($($t:ty),+ $(,)?) => {$(
        impl Encodable for $t {

            #[inline]
            fn encode_fields(&self, out: &mut dyn BufMut) {
                const ESC: $t = EMPTY_STRING_CODE as $t;
                match self {
                    0 => out.put_u8(EMPTY_STRING_CODE),
                    1..ESC => out.put_u8(*self as u8),
                    ESC.. => {
                        let be;
                        let be = to_be_bytes_trimmed!(be, *self);
                        out.put_slice(be);
                    }
                }
            }

            #[inline]
            fn encoded_fields_length(&self) -> usize {
                const ESC: $t = EMPTY_STRING_CODE as $t;
                match self {
                    0..ESC => 1,
                    ESC.. => (<$t>::BITS as usize / 8) - (self.leading_zeros() as usize / 8)
                }
            }


            #[inline]
            fn is_string(&self) -> bool {
                true
            }

            #[inline]
            fn header(&self) -> Option<Header> {
                const ESC: $t = EMPTY_STRING_CODE as $t;
                match self {
                    0..ESC => None,
                    ESC.. => {
                        Some(Header { list: false, payload_length: self.encoded_fields_length() })
                    }
                }
            }

            #[inline]
            fn length(&self) -> usize {
                const ESC: $t = EMPTY_STRING_CODE as $t;
                match self {
                    0..ESC => 1,
                    ESC.. => self.header().expect("header presence enforced by encoding rules").length_with_payload()
                }
            }
        }

        impl_max_encoded_len!($t, {
            let bytes = <$t>::BITS as usize / 8;
            bytes + length_of_length(bytes)
        });
    )+};
}

uint_impl!(u8, u16, u32, u64, usize, u128);

impl<T: Encodable> Encodable for Vec<T> {
    #[inline]
    fn encode_fields(&self, out: &mut dyn BufMut) {
        self.iter().for_each(|t| t.encode(out));
    }

    fn encoded_fields_length(&self) -> usize {
        self.iter().map(Encodable::length).sum()
    }

    fn is_string(&self) -> bool {
        false
    }

    #[inline]
    fn encode(&self, out: &mut dyn BufMut) {
        self.header().expect("lists always have headers").encode(out);
        self.encode_fields(out);
    }
}

macro_rules! deref_impl {
    ($($(#[$attr:meta])* [$($gen:tt)*] $t:ty),+ $(,)?) => {$(
        $(#[$attr])*
        impl<$($gen)*> Encodable for $t {

            #[inline]
            fn encode_fields(&self, out: &mut dyn BufMut) {
                (**self).encode_fields(out)
            }

            #[inline]
            fn encoded_fields_length(&self) -> usize {
                (**self).encoded_fields_length()
            }

            #[inline]
            fn is_string(&self) -> bool {
                (**self).is_string()
            }

            #[inline]
            fn header(&self) -> Option<Header> {
                (**self).header()
            }

            #[inline]
            fn length(&self) -> usize {
                (**self).length()
            }

            #[inline]
            fn encode(&self, out: &mut dyn BufMut) {
                (**self).encode(out)
            }
        }
    )+};
}

deref_impl! {
    [] alloc::string::String,
    [] Bytes,
    [] BytesMut,
    #[cfg(feature = "arrayvec")]
    [const N: usize] ArrayVec<u8, N>,
    [T: ?Sized + Encodable] &T,
    [T: ?Sized + Encodable] &mut T,
    [T: ?Sized + Encodable] alloc::boxed::Box<T>,
    [T: ?Sized + alloc::borrow::ToOwned + Encodable] alloc::borrow::Cow<'_, T>,
    [T: ?Sized + Encodable] alloc::rc::Rc<T>,
    [T: ?Sized + Encodable] alloc::sync::Arc<T>,
}

#[cfg(feature = "std")]
mod std_support {
    use super::*;
    use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};

    impl Encodable for IpAddr {
        fn encode_fields(&self, out: &mut dyn BufMut) {
            match self {
                Self::V4(ip) => ip.encode_fields(out),
                Self::V6(ip) => ip.encode_fields(out),
            }
        }

        fn encoded_fields_length(&self) -> usize {
            match self {
                Self::V4(ip) => ip.encoded_fields_length(),
                Self::V6(ip) => ip.encoded_fields_length(),
            }
        }

        fn is_string(&self) -> bool {
            match self {
                Self::V4(ip) => ip.is_string(),
                Self::V6(ip) => ip.is_string(),
            }
        }

        fn header(&self) -> Option<Header> {
            match self {
                Self::V4(ip) => ip.header(),
                Self::V6(ip) => ip.header(),
            }
        }

        #[inline]
        fn length(&self) -> usize {
            match self {
                Self::V4(ip) => ip.length(),
                Self::V6(ip) => ip.length(),
            }
        }

        #[inline]
        fn encode(&self, out: &mut dyn BufMut) {
            match self {
                Self::V4(ip) => ip.encode(out),
                Self::V6(ip) => ip.encode(out),
            }
        }
    }

    impl Encodable for Ipv4Addr {
        #[inline]
        fn encode_fields(&self, out: &mut dyn BufMut) {
            self.octets().encode_fields(out)
        }

        #[inline]
        fn encoded_fields_length(&self) -> usize {
            self.octets().encoded_fields_length()
        }

        #[inline]
        fn is_string(&self) -> bool {
            self.octets().is_string()
        }

        #[inline]
        fn header(&self) -> Option<Header> {
            self.octets().header()
        }

        #[inline]
        fn length(&self) -> usize {
            self.octets().length()
        }

        #[inline]
        fn encode(&self, out: &mut dyn BufMut) {
            self.octets().encode(out)
        }
    }

    impl Encodable for Ipv6Addr {
        #[inline]
        fn encode_fields(&self, out: &mut dyn BufMut) {
            self.octets().encode_fields(out)
        }

        #[inline]
        fn encoded_fields_length(&self) -> usize {
            self.octets().encoded_fields_length()
        }

        #[inline]
        fn is_string(&self) -> bool {
            self.octets().is_string()
        }

        #[inline]
        fn header(&self) -> Option<Header> {
            self.octets().header()
        }

        #[inline]
        fn length(&self) -> usize {
            self.octets().length()
        }

        #[inline]
        fn encode(&self, out: &mut dyn BufMut) {
            self.octets().encode(out)
        }
    }
}

/// Encode a value.
///
/// Prefer using [`encode_fixed_size`] if a type implements [`MaxEncodedLen`].
#[inline]
pub fn encode<T: Encodable>(value: T) -> Vec<u8> {
    let mut out = Vec::with_capacity(value.length());
    value.encode(&mut out);
    out
}

/// Encode a type with a known maximum size.
#[cfg(feature = "arrayvec")]
#[inline]
pub fn encode_fixed_size<T: MaxEncodedLen<LEN>, const LEN: usize>(value: &T) -> ArrayVec<u8, LEN> {
    let mut vec = ArrayVec::<u8, LEN>::new();

    // SAFETY: We're casting uninitalized memory to a slice of bytes to be written into.
    let mut out = unsafe { core::slice::from_raw_parts_mut(vec.as_mut_ptr(), LEN) };
    value.encode(&mut out);
    let written = LEN - out.len();

    // SAFETY: `written <= LEN` and all bytes are initialized.
    unsafe { vec.set_len(written) };
    vec
}

/// Calculate the length of a list.
#[inline]
pub fn list_length<B, T>(list: &[B]) -> usize
where
    B: Borrow<T>,
    T: ?Sized + Encodable,
{
    let payload_length = rlp_list_header(list).payload_length;
    payload_length + length_of_length(payload_length)
}

/// Encode a list of items.
#[inline]
pub fn encode_list<B, T>(values: &[B], out: &mut dyn BufMut)
where
    B: Borrow<T>,
    T: ?Sized + Encodable,
{
    rlp_list_header(values).encode(out);
    for value in values {
        value.borrow().encode(out);
    }
}

/// Encode all items from an iterator.
///
/// This clones the iterator. Prefer [`encode_list`] if possible.
#[inline]
pub fn encode_iter<I, B, T>(values: I, out: &mut dyn BufMut)
where
    I: Iterator<Item = B> + Clone,
    B: Borrow<T>,
    T: ?Sized + Encodable,
{
    let mut h = Header { list: true, payload_length: 0 };
    for t in values.clone() {
        h.payload_length += t.borrow().length();
    }

    h.encode(out);
    for value in values {
        value.borrow().encode(out);
    }
}

/// Determine the length in bytes of the length prefix of an RLP item.
#[inline]
pub const fn length_of_length(payload_length: usize) -> usize {
    if payload_length < 56 {
        1
    } else {
        1 + (usize::BITS as usize / 8) - payload_length.leading_zeros() as usize / 8
    }
}

#[inline]
fn rlp_list_header<B, T>(values: &[B]) -> Header
where
    B: Borrow<T>,
    T: ?Sized + Encodable,
{
    let mut h = Header { list: true, payload_length: 0 };
    for value in values {
        h.payload_length += value.borrow().length();
    }
    h
}

#[cfg(test)]
mod tests {
    use super::*;
    use hex_literal::hex;

    fn encoded_list<T: Encodable + Clone>(t: &[T]) -> BytesMut {
        let mut out1 = BytesMut::new();
        encode_list(t, &mut out1);

        let v = t.to_vec();
        assert_eq!(out1.len(), v.length());

        let mut out2 = BytesMut::new();
        v.encode(&mut out2);
        assert_eq!(out1, out2);

        out1
    }

    fn encoded_iter<T: Encodable>(iter: impl Iterator<Item = T> + Clone) -> BytesMut {
        let mut out = BytesMut::new();
        encode_iter(iter, &mut out);
        out
    }

    #[test]
    fn rlp_str() {
        assert_eq!(encode("")[..], hex!("80")[..]);
        assert_eq!(encode("{")[..], hex!("7b")[..]);
        assert_eq!(encode("test str")[..], hex!("887465737420737472")[..]);
    }

    #[test]
    fn rlp_strings() {
        assert_eq!(encode(hex!(""))[..], hex!("80")[..]);
        assert_eq!(encode(hex!("7B"))[..], hex!("7b")[..]);
        assert_eq!(encode(hex!("80"))[..], hex!("8180")[..]);
        assert_eq!(encode(hex!("ABBA"))[..], hex!("82abba")[..]);
    }

    #[test]
    fn rlp_bool() {
        assert_eq!(encode(true), hex!("01"));
        assert_eq!(encode(false), hex!("80"));
    }

    fn c<T, U: From<T>>(
        it: impl IntoIterator<Item = (T, &'static [u8])>,
    ) -> impl Iterator<Item = (U, &'static [u8])> {
        it.into_iter().map(|(k, v)| (k.into(), v))
    }

    fn u8_fixtures() -> impl IntoIterator<Item = (u8, &'static [u8])> {
        vec![
            (0, &hex!("80")[..]),
            (1, &hex!("01")[..]),
            (0x7F, &hex!("7F")[..]),
            (0x80, &hex!("8180")[..]),
        ]
    }

    fn u16_fixtures() -> impl IntoIterator<Item = (u16, &'static [u8])> {
        c(u8_fixtures()).chain(vec![(0x400, &hex!("820400")[..])])
    }

    fn u32_fixtures() -> impl IntoIterator<Item = (u32, &'static [u8])> {
        c(u16_fixtures())
            .chain(vec![(0xFFCCB5, &hex!("83ffccb5")[..]), (0xFFCCB5DD, &hex!("84ffccb5dd")[..])])
    }

    fn u64_fixtures() -> impl IntoIterator<Item = (u64, &'static [u8])> {
        c(u32_fixtures()).chain(vec![
            (0xFFCCB5DDFF, &hex!("85ffccb5ddff")[..]),
            (0xFFCCB5DDFFEE, &hex!("86ffccb5ddffee")[..]),
            (0xFFCCB5DDFFEE14, &hex!("87ffccb5ddffee14")[..]),
            (0xFFCCB5DDFFEE1483, &hex!("88ffccb5ddffee1483")[..]),
        ])
    }

    fn u128_fixtures() -> impl IntoIterator<Item = (u128, &'static [u8])> {
        c(u64_fixtures()).chain(vec![(
            0x10203E405060708090A0B0C0D0E0F2,
            &hex!("8f10203e405060708090a0b0c0d0e0f2")[..],
        )])
    }

    macro_rules! uint_rlp_test {
        ($fixtures:expr) => {
            for (input, output) in $fixtures {
                let encoded = encode(input);
                assert_eq!(input.length(), encoded.len(), "length({input})");
                assert_eq!(encoded, output, "encode({input})");

                #[cfg(feature = "arrayvec")]
                assert_eq!(&encode_fixed_size(&input)[..], output, "encode_fixed_size({input})");
            }
        };
    }

    #[test]
    fn rlp_uints() {
        uint_rlp_test!(u8_fixtures());
        uint_rlp_test!(u16_fixtures());
        uint_rlp_test!(u32_fixtures());
        uint_rlp_test!(u64_fixtures());
        uint_rlp_test!(u128_fixtures());
        // #[cfg(feature = "ethnum")]
        // uint_rlp_test!(u256_fixtures());
    }

    /*
    #[cfg(feature = "ethnum")]
    fn u256_fixtures() -> impl IntoIterator<Item = (ethnum::U256, &'static [u8])> {
        c(u128_fixtures()).chain(vec![(
            ethnum::U256::from_str_radix(
                "0100020003000400050006000700080009000A0B4B000C000D000E01",
                16,
            )
            .unwrap(),
            &hex!("9c0100020003000400050006000700080009000a0b4b000c000d000e01")[..],
        )])
    }

    #[cfg(feature = "ethereum-types")]
    fn eth_u64_fixtures() -> impl IntoIterator<Item = (ethereum_types::U64, &'static [u8])> {
        c(u64_fixtures()).chain(vec![
            (
                ethereum_types::U64::from_str_radix("FFCCB5DDFF", 16).unwrap(),
                &hex!("85ffccb5ddff")[..],
            ),
            (
                ethereum_types::U64::from_str_radix("FFCCB5DDFFEE", 16).unwrap(),
                &hex!("86ffccb5ddffee")[..],
            ),
            (
                ethereum_types::U64::from_str_radix("FFCCB5DDFFEE14", 16).unwrap(),
                &hex!("87ffccb5ddffee14")[..],
            ),
            (
                ethereum_types::U64::from_str_radix("FFCCB5DDFFEE1483", 16).unwrap(),
                &hex!("88ffccb5ddffee1483")[..],
            ),
        ])
    }

    fn eth_u128_fixtures() -> impl IntoIterator<Item = (ethereum_types::U128, &'static [u8])> {
        c(u128_fixtures()).chain(vec![(
            ethereum_types::U128::from_str_radix("10203E405060708090A0B0C0D0E0F2", 16).unwrap(),
            &hex!("8f10203e405060708090a0b0c0d0e0f2")[..],
        )])
    }

    fn eth_u256_fixtures() -> impl IntoIterator<Item = (ethereum_types::U256, &'static [u8])> {
        c(u128_fixtures()).chain(vec![(
            ethereum_types::U256::from_str_radix(
                "0100020003000400050006000700080009000A0B4B000C000D000E01",
                16,
            )
            .unwrap(),
            &hex!("9c0100020003000400050006000700080009000a0b4b000c000d000e01")[..],
        )])
    }

    #[cfg(feature = "ethereum-types")]
    fn eth_u512_fixtures() -> impl IntoIterator<Item = (ethereum_types::U512, &'static [u8])> {
        c(eth_u256_fixtures()).chain(vec![(
            ethereum_types::U512::from_str_radix(
                "0100020003000400050006000700080009000A0B4B000C000D000E010100020003000400050006000700080009000A0B4B000C000D000E01",
                16,
            )
            .unwrap(),
            &hex!("b8380100020003000400050006000700080009000A0B4B000C000D000E010100020003000400050006000700080009000A0B4B000C000D000E01")[..],
        )])
    }

    #[cfg(feature = "ethereum-types")]
    #[test]
    fn rlp_eth_uints() {
        uint_rlp_test!(eth_u64_fixtures());
        uint_rlp_test!(eth_u128_fixtures());
        uint_rlp_test!(eth_u256_fixtures());
        uint_rlp_test!(eth_u512_fixtures());
    }
    */

    #[test]
    fn rlp_list() {
        assert_eq!(encoded_list::<u64>(&[]), &hex!("c0")[..]);
        assert_eq!(encoded_list::<u8>(&[0x00u8]), &hex!("c180")[..]);
        assert_eq!(encoded_list(&[0xFFCCB5_u64, 0xFFC0B5_u64]), &hex!("c883ffccb583ffc0b5")[..]);
    }

    #[test]
    fn rlp_iter() {
        assert_eq!(encoded_iter::<u64>([].into_iter()), &hex!("c0")[..]);
        assert_eq!(
            encoded_iter([0xFFCCB5_u64, 0xFFC0B5_u64].iter()),
            &hex!("c883ffccb583ffc0b5")[..]
        );
    }

    #[test]
    fn to_be_bytes_trimmed() {
        macro_rules! test_to_be_bytes_trimmed {
            ($($x:expr => $expected:expr),+ $(,)?) => {$(
                let be;
                assert_eq!(to_be_bytes_trimmed!(be, $x), $expected);
            )+};
        }

        test_to_be_bytes_trimmed! {
            0u8 => [],
            0u16 => [],
            0u32 => [],
            0u64 => [],
            0usize => [],
            0u128 => [],

            1u8 => [1],
            1u16 => [1],
            1u32 => [1],
            1u64 => [1],
            1usize => [1],
            1u128 => [1],

            u8::MAX => [0xff],
            u16::MAX => [0xff, 0xff],
            u32::MAX => [0xff, 0xff, 0xff, 0xff],
            u64::MAX => [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff],
            u128::MAX => [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff],

            1u8 => [1],
            255u8 => [255],
            256u16 => [1, 0],
            65535u16 => [255, 255],
            65536u32 => [1, 0, 0],
            65536u64 => [1, 0, 0],
        }
    }
}
