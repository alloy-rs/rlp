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

/// An RLP encoder wrapping a [`BufMut`].
pub struct Encoder<'a> {
    out: &'a mut dyn BufMut,
}

impl core::fmt::Debug for Encoder<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Encoder").finish_non_exhaustive()
    }
}

impl<'a> Encoder<'a> {
    /// Creates a new encoder wrapping the given buffer.
    #[inline]
    pub fn new(out: &'a mut dyn BufMut) -> Self {
        Self { out }
    }

    /// Writes a single byte to the buffer.
    #[inline]
    pub fn put_u8(&mut self, n: u8) {
        self.out.put_u8(n)
    }

    /// Writes a byte slice to the buffer.
    #[inline]
    pub fn put_slice(&mut self, src: &[u8]) {
        self.out.put_slice(src)
    }
}

/// A type that can be encoded via RLP.
pub trait RlpEncodable {
    /// Encodes the type into the `out` buffer.
    fn rlp_encode(&self, out: &mut Encoder<'_>);

    /// Returns the length of the encoding of this type in bytes.
    ///
    /// The default implementation computes this by encoding the type.
    /// When possible, we recommend implementers override this with a
    /// specialized implementation.
    #[inline]
    fn rlp_len(&self) -> usize {
        let mut out = Vec::new();
        self.rlp_encode(&mut Encoder::new(&mut out));
        out.len()
    }
}

// The existence of this function makes the compiler catch if the RlpEncodable
// trait is "object-safe" or not.
fn _assert_trait_object(_b: &dyn RlpEncodable) {}

/// Defines the max length of an [`RlpEncodable`] type as a const generic.
///
/// # Safety
///
/// An invalid value can cause the encoder to panic.
pub unsafe trait MaxEncodedLen<const LEN: usize>: RlpEncodable {}

/// Defines the max length of an [`RlpEncodable`] type as an associated constant.
///
/// # Safety
///
/// An invalid value can cause the encoder to panic.
pub unsafe trait MaxEncodedLenAssoc: RlpEncodable {
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

impl RlpEncodable for [u8] {
    #[inline]
    fn rlp_len(&self) -> usize {
        let mut len = self.len();
        if len != 1 || self[0] >= EMPTY_STRING_CODE {
            len += length_of_length(len);
        }
        len
    }

    #[inline]
    fn rlp_encode(&self, out: &mut Encoder<'_>) {
        if self.len() != 1 || self[0] >= EMPTY_STRING_CODE {
            Header { list: false, payload_length: self.len() }.encode(out);
        }
        out.put_slice(self);
    }
}

impl<T: ?Sized> RlpEncodable for PhantomData<T> {
    #[inline]
    fn rlp_len(&self) -> usize {
        0
    }

    #[inline]
    fn rlp_encode(&self, _out: &mut Encoder<'_>) {}
}

impl RlpEncodable for PhantomPinned {
    #[inline]
    fn rlp_len(&self) -> usize {
        0
    }

    #[inline]
    fn rlp_encode(&self, _out: &mut Encoder<'_>) {}
}

impl<const N: usize> RlpEncodable for [u8; N] {
    #[inline]
    fn rlp_len(&self) -> usize {
        self[..].rlp_len()
    }

    #[inline]
    fn rlp_encode(&self, out: &mut Encoder<'_>) {
        self[..].rlp_encode(out);
    }
}

unsafe impl<const N: usize> MaxEncodedLenAssoc for [u8; N] {
    const LEN: usize = N + length_of_length(N);
}

impl RlpEncodable for str {
    #[inline]
    fn rlp_len(&self) -> usize {
        self.as_bytes().rlp_len()
    }

    #[inline]
    fn rlp_encode(&self, out: &mut Encoder<'_>) {
        self.as_bytes().rlp_encode(out)
    }
}

impl RlpEncodable for bool {
    #[inline]
    fn rlp_len(&self) -> usize {
        // a `bool` is always `< EMPTY_STRING_CODE`
        1
    }

    #[inline]
    fn rlp_encode(&self, out: &mut Encoder<'_>) {
        // inlined `(*self as u8).rlp_encode(out)`
        out.put_u8(if *self { 1 } else { EMPTY_STRING_CODE });
    }
}

impl_max_encoded_len!(bool, <u8 as MaxEncodedLenAssoc>::LEN);

macro_rules! uint_impl {
    ($($t:ty),+ $(,)?) => {$(
        impl RlpEncodable for $t {
            #[inline]
            fn rlp_len(&self) -> usize {
                let x = *self;
                if x < EMPTY_STRING_CODE as $t {
                    1
                } else {
                    1 + (<$t>::BITS as usize / 8) - (x.leading_zeros() as usize / 8)
                }
            }

            #[inline]
            fn rlp_encode(&self, out: &mut Encoder<'_>) {
                let x = *self;
                if x == 0 {
                    out.put_u8(EMPTY_STRING_CODE);
                } else if x < EMPTY_STRING_CODE as $t {
                    out.put_u8(x as u8);
                } else {
                    let be;
                    let be = to_be_bytes_trimmed!(be, x);
                    out.put_u8(EMPTY_STRING_CODE + be.len() as u8);
                    out.put_slice(be);
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

impl<T: RlpEncodable> RlpEncodable for Vec<T> {
    #[inline]
    fn rlp_len(&self) -> usize {
        list_length(self)
    }

    #[inline]
    fn rlp_encode(&self, out: &mut Encoder<'_>) {
        encode_list(self, out)
    }
}

macro_rules! deref_impl {
    ($($(#[$attr:meta])* [$($gen:tt)*] $t:ty),+ $(,)?) => {$(
        $(#[$attr])*
        impl<$($gen)*> RlpEncodable for $t {
            #[inline]
            fn rlp_len(&self) -> usize {
                (**self).rlp_len()
            }

            #[inline]
            fn rlp_encode(&self, out: &mut Encoder<'_>) {
                (**self).rlp_encode(out)
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
    [T: ?Sized + RlpEncodable] &T,
    [T: ?Sized + RlpEncodable] &mut T,
    [T: ?Sized + RlpEncodable] alloc::boxed::Box<T>,
    [T: ?Sized + alloc::borrow::ToOwned + RlpEncodable] alloc::borrow::Cow<'_, T>,
    [T: ?Sized + RlpEncodable] alloc::rc::Rc<T>,
    #[cfg(target_has_atomic = "ptr")]
    [T: ?Sized + RlpEncodable] alloc::sync::Arc<T>,
}

#[cfg(any(feature = "std", feature = "core-net"))]
mod std_support {
    use super::*;
    #[cfg(all(feature = "core-net", not(feature = "std")))]
    use core::net::{IpAddr, Ipv4Addr, Ipv6Addr};
    #[cfg(feature = "std")]
    use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};

    impl RlpEncodable for IpAddr {
        #[inline]
        fn rlp_len(&self) -> usize {
            match self {
                Self::V4(ip) => ip.rlp_len(),
                Self::V6(ip) => ip.rlp_len(),
            }
        }

        #[inline]
        fn rlp_encode(&self, out: &mut Encoder<'_>) {
            match self {
                Self::V4(ip) => ip.rlp_encode(out),
                Self::V6(ip) => ip.rlp_encode(out),
            }
        }
    }

    impl RlpEncodable for Ipv4Addr {
        #[inline]
        fn rlp_len(&self) -> usize {
            self.octets().rlp_len()
        }

        #[inline]
        fn rlp_encode(&self, out: &mut Encoder<'_>) {
            self.octets().rlp_encode(out)
        }
    }

    impl RlpEncodable for Ipv6Addr {
        #[inline]
        fn rlp_len(&self) -> usize {
            self.octets().rlp_len()
        }

        #[inline]
        fn rlp_encode(&self, out: &mut Encoder<'_>) {
            self.octets().rlp_encode(out)
        }
    }
}

/// Encode a value.
///
/// Prefer using [`encode_fixed_size`] if a type implements [`MaxEncodedLen`].
#[inline]
pub fn encode<T: RlpEncodable>(value: T) -> Vec<u8> {
    let mut out = Vec::with_capacity(value.rlp_len());
    value.rlp_encode(&mut Encoder::new(&mut out));
    out
}

/// Encode a type with a known maximum size.
#[cfg(feature = "arrayvec")]
#[inline]
pub fn encode_fixed_size<T: MaxEncodedLen<LEN>, const LEN: usize>(value: &T) -> ArrayVec<u8, LEN> {
    let mut vec = ArrayVec::<u8, LEN>::new();

    // SAFETY: We're casting uninitalized memory to a slice of bytes to be written into.
    let mut out = unsafe { core::slice::from_raw_parts_mut(vec.as_mut_ptr(), LEN) };
    {
        let mut encoder = Encoder::new(&mut out);
        value.rlp_encode(&mut encoder);
    }
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
    T: ?Sized + RlpEncodable,
{
    let payload_length = rlp_list_header(list).payload_length;
    payload_length + length_of_length(payload_length)
}

/// Encode a list of items.
#[inline]
pub fn encode_list<B, T>(values: &[B], out: &mut Encoder<'_>)
where
    B: Borrow<T>,
    T: ?Sized + RlpEncodable,
{
    rlp_list_header(values).encode(out);
    for value in values {
        value.borrow().rlp_encode(out);
    }
}

/// Encode all items from an iterator.
///
/// This clones the iterator. Prefer [`encode_list`] if possible.
#[inline]
pub fn encode_iter<I, B, T>(values: I, out: &mut Encoder<'_>)
where
    I: Iterator<Item = B> + Clone,
    B: Borrow<T>,
    T: ?Sized + RlpEncodable,
{
    let mut h = Header { list: true, payload_length: 0 };
    for t in values.clone() {
        h.payload_length += t.borrow().rlp_len();
    }

    h.encode(out);
    for value in values {
        value.borrow().rlp_encode(out);
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
    T: ?Sized + RlpEncodable,
{
    let mut h = Header { list: true, payload_length: 0 };
    for value in values {
        h.payload_length += value.borrow().rlp_len();
    }
    h
}

#[cfg(test)]
mod tests {
    use super::*;
    use hex_literal::hex;

    fn encoded_list<T: RlpEncodable + Clone>(t: &[T]) -> BytesMut {
        let mut out1 = BytesMut::new();
        encode_list(t, &mut Encoder::new(&mut out1));

        let v = t.to_vec();
        assert_eq!(out1.len(), v.rlp_len());

        let mut out2 = BytesMut::new();
        v.rlp_encode(&mut Encoder::new(&mut out2));
        assert_eq!(out1, out2);

        out1
    }

    fn encoded_iter<T: RlpEncodable>(iter: impl Iterator<Item = T> + Clone) -> BytesMut {
        let mut out = BytesMut::new();
        encode_iter(iter, &mut Encoder::new(&mut out));
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
                assert_eq!(encode(input), output, "encode({input})");
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
