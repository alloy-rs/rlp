use crate::{
    decode::static_left_pad, Encoder, Error, ErrorKind, Result, EMPTY_LIST_CODE, EMPTY_STRING_CODE,
};
use bytes::{Buf, BufMut};
use core::hint::unreachable_unchecked;

/// The header of an RLP item.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Header {
    /// True if list, false otherwise.
    pub list: bool,
    /// Length of the payload in bytes.
    pub payload_length: usize,
}

impl Header {
    /// Decodes an RLP header from the given buffer.
    ///
    /// # Errors
    ///
    /// Returns an error if the buffer is too short or the header is invalid.
    #[inline]
    pub fn decode(buf: &mut &[u8]) -> Result<Self> {
        Self::decode_at(buf, 0)
    }

    /// Decodes an RLP header from the given buffer using `bytepos` as the absolute
    /// byte position of the first byte in `buf`.
    ///
    /// # Errors
    ///
    /// Returns an error if the buffer is too short or the header is invalid.
    #[inline]
    pub fn decode_at(buf: &mut &[u8], bytepos: usize) -> Result<Self> {
        let started_len = buf.len();
        let payload_length;
        let mut list = false;
        match get_next_byte(buf, started_len, bytepos)? {
            0..=0x7F => payload_length = 1,

            b @ EMPTY_STRING_CODE..=0xB7 => {
                buf.advance(1);
                payload_length = (b - EMPTY_STRING_CODE) as usize;
                if payload_length == 1
                    && get_next_byte(buf, started_len, bytepos)? < EMPTY_STRING_CODE
                {
                    return Err(error_at(
                        ErrorKind::NonCanonicalSingleByte,
                        buf,
                        started_len,
                        bytepos,
                    ));
                }
            }

            b @ (0xB8..=0xBF | 0xF8..=0xFF) => {
                buf.advance(1);

                list = b >= 0xF8; // second range
                let code = if list { 0xF7 } else { 0xB7 };

                // SAFETY: `b - code` is always in the range `1..=8` in the current match arm.
                // The compiler/LLVM apparently cannot prove this because of the `|` pattern +
                // the above `if`, since it can do it in the other arms with only 1 range.
                let len_of_len = unsafe { b.checked_sub(code).unwrap_unchecked() } as usize;
                if len_of_len == 0 || len_of_len > 8 {
                    unsafe { unreachable_unchecked() }
                }

                if buf.len() < len_of_len {
                    return Err(error_at(ErrorKind::InputTooShort, buf, started_len, bytepos));
                }
                // SAFETY: length checked above
                let len = unsafe { buf.get_unchecked(..len_of_len) };
                let len_bytepos = current_bytepos(buf, started_len, bytepos);
                buf.advance(len_of_len);

                let len = u64::from_be_bytes(static_left_pad(len).map_err(|err| {
                    Error::with_bytepos(err.kind(), len_bytepos.saturating_add(err.bytepos()))
                })?);
                payload_length = usize::try_from(len).map_err(|_| {
                    Error::with_bytepos(ErrorKind::Custom("Input too big"), len_bytepos)
                })?;
                if payload_length < 56 {
                    return Err(error_at(ErrorKind::NonCanonicalSize, buf, started_len, bytepos));
                }
            }

            b @ EMPTY_LIST_CODE..=0xF7 => {
                buf.advance(1);
                list = true;
                payload_length = (b - EMPTY_LIST_CODE) as usize;
            }
        }

        if buf.remaining() < payload_length {
            return Err(error_at(ErrorKind::InputTooShort, buf, started_len, bytepos));
        }

        Ok(Self { list, payload_length })
    }

    /// Decodes the next payload from the given buffer, advancing it.
    ///
    /// # Errors
    ///
    /// Returns an error if the buffer is too short or the header is invalid.
    #[inline]
    pub fn decode_bytes<'a>(buf: &mut &'a [u8], is_list: bool) -> Result<&'a [u8]> {
        Self::decode_bytes_at(buf, is_list, 0)
    }

    /// Decodes the next payload from the given buffer using `bytepos` as the absolute
    /// byte position of the first byte in `buf`.
    ///
    /// # Errors
    ///
    /// Returns an error if the buffer is too short or the header is invalid.
    #[inline]
    pub fn decode_bytes_at<'a>(
        buf: &mut &'a [u8],
        is_list: bool,
        bytepos: usize,
    ) -> Result<&'a [u8]> {
        let Self { list, payload_length } = Self::decode_at(buf, bytepos)?;

        if list != is_list {
            return Err(Error::with_bytepos(
                if is_list { ErrorKind::UnexpectedString } else { ErrorKind::UnexpectedList },
                bytepos,
            ));
        }

        // SAFETY: this is already checked in `decode`
        let bytes = unsafe { advance_unchecked(buf, payload_length) };
        Ok(bytes)
    }

    /// Decodes a string slice from the given buffer, advancing it.
    ///
    /// # Errors
    ///
    /// Returns an error if the buffer is too short or the header is invalid.
    #[inline]
    pub fn decode_str<'a>(buf: &mut &'a [u8]) -> Result<&'a str> {
        Self::decode_str_at(buf, 0)
    }

    /// Decodes a string slice from the given buffer using `bytepos` as the absolute
    /// byte position of the first byte in `buf`.
    ///
    /// # Errors
    ///
    /// Returns an error if the buffer is too short, the header is invalid, or the
    /// decoded bytes are not valid UTF-8.
    #[inline]
    pub fn decode_str_at<'a>(buf: &mut &'a [u8], bytepos: usize) -> Result<&'a str> {
        let started_len = buf.len();
        let bytes = Self::decode_bytes_at(buf, false, bytepos)?;
        let consumed = started_len.saturating_sub(buf.len());
        let payload_bytepos = bytepos.saturating_add(consumed.saturating_sub(bytes.len()));
        core::str::from_utf8(bytes)
            .map_err(|_| Error::with_bytepos(ErrorKind::Custom("invalid string"), payload_bytepos))
    }

    /// Extracts the next payload from the given buffer, advancing it.
    ///
    /// The returned `PayloadView` provides a structured view of the payload, allowing for efficient
    /// parsing of nested items without unnecessary allocations.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The buffer is too short
    /// - The header is invalid
    /// - Any nested headers (for list items) are invalid
    #[inline]
    pub fn decode_raw<'a>(buf: &mut &'a [u8]) -> Result<PayloadView<'a>> {
        Self::decode_raw_at(buf, 0)
    }

    /// Extracts the next payload from the given buffer using `bytepos` as the absolute
    /// byte position of the first byte in `buf`.
    ///
    /// The returned `PayloadView` provides a structured view of the payload, allowing for efficient
    /// parsing of nested items without unnecessary allocations.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The buffer is too short
    /// - The header is invalid
    /// - Any nested headers (for list items) are invalid
    #[inline]
    pub fn decode_raw_at<'a>(buf: &mut &'a [u8], bytepos: usize) -> Result<PayloadView<'a>> {
        let started_len = buf.len();
        let Self { list, payload_length } = Self::decode_at(buf, bytepos)?;
        let payload_bytepos = bytepos.saturating_add(started_len.saturating_sub(buf.len()));
        // SAFETY: this is already checked in `decode`
        let mut payload = unsafe { advance_unchecked(buf, payload_length) };

        if !list {
            return Ok(PayloadView::String(payload));
        }

        let mut items = alloc::vec::Vec::new();
        let mut item_bytepos = payload_bytepos;
        while !payload.is_empty() {
            // store the start of the current item for later slice creation
            let item_start = payload;

            // decode the header of the next RLP item, advancing the payload
            let Self { payload_length, .. } = Self::decode_at(&mut payload, item_bytepos)?;
            // SAFETY: this is already checked in `decode`
            unsafe { advance_unchecked(&mut payload, payload_length) };

            // calculate the total length of the item (header + payload) by subtracting the
            // remaining payload length from the initial length
            let item_length = item_start.len() - payload.len();
            items.push(&item_start[..item_length]);
            item_bytepos = item_bytepos.saturating_add(item_length);
        }

        Ok(PayloadView::List(items))
    }

    /// Encodes the header into the `out` buffer.
    #[inline]
    pub fn encode<T: BufMut>(&self, out: &mut Encoder<T>) {
        if self.payload_length < 56 {
            let code = if self.list { EMPTY_LIST_CODE } else { EMPTY_STRING_CODE };
            out.put_u8(code + self.payload_length as u8);
        } else {
            let len_be;
            let len_be = crate::encode::to_be_bytes_trimmed!(len_be, self.payload_length);
            let code = if self.list { 0xF7 } else { 0xB7 };
            out.put_u8(code + len_be.len() as u8);
            out.put_slice(len_be);
        }
    }

    /// Returns the length of the encoded header.
    #[inline]
    pub const fn length(&self) -> usize {
        crate::length_of_length(self.payload_length)
    }

    /// Returns the total length of the encoded header and payload.
    pub const fn length_with_payload(&self) -> usize {
        self.length() + self.payload_length
    }
}

/// Structured representation of an RLP payload.
#[derive(Debug)]
pub enum PayloadView<'a> {
    /// Payload is a byte string.
    String(&'a [u8]),
    /// Payload is a list of RLP encoded data.
    List(alloc::vec::Vec<&'a [u8]>),
}

/// Same as `buf.first().ok_or(ErrorKind::InputTooShort)`.
#[inline(always)]
fn get_next_byte(buf: &[u8], started_len: usize, bytepos: usize) -> Result<u8> {
    if buf.is_empty() {
        return Err(error_at(ErrorKind::InputTooShort, &buf, started_len, bytepos));
    }
    // SAFETY: length checked above
    Ok(*unsafe { buf.get_unchecked(0) })
}

#[inline(always)]
const fn error_at(kind: ErrorKind, buf: &&[u8], started_len: usize, bytepos: usize) -> Error {
    Error::with_bytepos(kind, current_bytepos(buf, started_len, bytepos))
}

#[inline(always)]
const fn current_bytepos(buf: &&[u8], started_len: usize, bytepos: usize) -> usize {
    bytepos.saturating_add(started_len.saturating_sub(buf.len()))
}

/// Same as `let (bytes, rest) = buf.split_at(cnt); *buf = rest; bytes`.
#[inline(always)]
unsafe fn advance_unchecked<'a>(buf: &mut &'a [u8], cnt: usize) -> &'a [u8] {
    if buf.remaining() < cnt {
        unreachable_unchecked()
    }
    let bytes = &buf[..cnt];
    buf.advance(cnt);
    bytes
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::RlpEncodable;
    use alloc::vec::Vec;
    use core::fmt::Debug;

    fn check_decode_raw_list<T: RlpEncodable + Debug>(input: Vec<T>) {
        let encoded = crate::encode(&input);
        let expected: Vec<_> = input.iter().map(crate::encode).collect();
        let mut buf = encoded.as_slice();
        assert!(
            matches!(Header::decode_raw(&mut buf), Ok(PayloadView::List(v)) if v == expected),
            "input: {input:?}, expected list: {expected:?}",
        );
        assert!(buf.is_empty(), "buffer was not advanced");
    }

    fn check_decode_raw_string(input: &str) {
        let encoded = crate::encode(input);
        let expected = Header::decode_bytes(&mut &encoded[..], false).unwrap();
        let mut buf = encoded.as_slice();
        assert!(
            matches!(Header::decode_raw(&mut buf), Ok(PayloadView::String(v)) if v == expected),
            "input: {input}, expected string: {expected:?}",
        );
        assert!(buf.is_empty(), "buffer was not advanced");
    }

    #[test]
    fn decode_raw() {
        // empty list
        check_decode_raw_list(Vec::<u64>::new());
        // list of an empty RLP list
        check_decode_raw_list(vec![Vec::<u64>::new()]);
        // list of an empty RLP string
        check_decode_raw_list(vec![""]);
        // list of two RLP strings
        check_decode_raw_list(vec![0xBBCCB5_u64, 0xFFC0B5_u64]);
        // list of three RLP lists of various lengths
        check_decode_raw_list(vec![vec![0u64], vec![1u64, 2u64], vec![3u64, 4u64, 5u64]]);
        // list of four empty RLP strings
        check_decode_raw_list(vec![0u64; 4]);
        // list of all one-byte strings, some will have an RLP header and some won't
        check_decode_raw_list((0u64..0xFF).collect());

        // strings of various lengths
        check_decode_raw_string("");
        check_decode_raw_string(" ");
        check_decode_raw_string("test1234");
    }

    #[test]
    fn decode_at_reports_absolute_byte_positions() {
        let mut input = &[0x82][..];
        let err = Header::decode_at(&mut input, 7).unwrap_err();
        assert_eq!(err.kind(), ErrorKind::InputTooShort);
        assert_eq!(err.bytepos(), 8);

        let mut input = &[0xc0][..];
        let err = Header::decode_bytes_at(&mut input, false, 11).unwrap_err();
        assert_eq!(err.kind(), ErrorKind::UnexpectedList);
        assert_eq!(err.bytepos(), 11);

        let mut input = &[0x81, 0xff][..];
        let err = Header::decode_str_at(&mut input, 13).unwrap_err();
        assert_eq!(err.kind(), ErrorKind::Custom("invalid string"));
        assert_eq!(err.bytepos(), 14);

        let mut input = &[0xc2, 0x01, 0x82][..];
        let err = Header::decode_raw_at(&mut input, 17).unwrap_err();
        assert_eq!(err.kind(), ErrorKind::InputTooShort);
        assert_eq!(err.bytepos(), 20);
    }
}
