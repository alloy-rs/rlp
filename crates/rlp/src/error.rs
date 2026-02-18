use core::fmt;

/// RLP result type.
pub type Result<T, E = Error> = core::result::Result<T, E>;

/// RLP error with byte position context.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Error {
    /// The byte position in the input where the error occurred.
    pub bytepos: usize,
    /// The kind of error.
    pub kind: ErrorKind,
}

impl Error {
    /// Creates a new error with the given kind and byte position 0.
    #[inline]
    pub const fn new(kind: ErrorKind) -> Self {
        Self { bytepos: 0, kind }
    }

    /// Creates a new error with the given kind and byte position.
    #[inline]
    pub const fn with_bytepos(kind: ErrorKind, bytepos: usize) -> Self {
        Self { bytepos, kind }
    }
}

impl From<ErrorKind> for Error {
    #[inline]
    fn from(kind: ErrorKind) -> Self {
        Self::new(kind)
    }
}

#[cfg(all(feature = "core-error", not(feature = "std")))]
impl core::error::Error for Error {}
#[cfg(feature = "std")]
impl std::error::Error for Error {}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} (at byte {})", self.kind, self.bytepos)
    }
}

/// RLP error type.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ErrorKind {
    /// Numeric Overflow.
    Overflow,
    /// Leading zero disallowed.
    LeadingZero,
    /// Overran input while decoding.
    InputTooShort,
    /// Expected single byte, but got invalid value.
    NonCanonicalSingleByte,
    /// Expected size, but got invalid value.
    NonCanonicalSize,
    /// Expected a payload of a specific size, got an unexpected size.
    UnexpectedLength,
    /// Expected another type, got a string instead.
    UnexpectedString,
    /// Expected another type, got a list instead.
    UnexpectedList,
    /// Got an unexpected number of items in a list.
    ListLengthMismatch {
        /// Expected length.
        expected: usize,
        /// Actual length.
        got: usize,
    },
    /// Custom error.
    Custom(&'static str),
}

#[cfg(all(feature = "core-error", not(feature = "std")))]
impl core::error::Error for ErrorKind {}
#[cfg(feature = "std")]
impl std::error::Error for ErrorKind {}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Overflow => f.write_str("overflow"),
            Self::LeadingZero => f.write_str("leading zero"),
            Self::InputTooShort => f.write_str("input too short"),
            Self::NonCanonicalSingleByte => f.write_str("non-canonical single byte"),
            Self::NonCanonicalSize => f.write_str("non-canonical size"),
            Self::UnexpectedLength => f.write_str("unexpected length"),
            Self::UnexpectedString => f.write_str("unexpected string"),
            Self::UnexpectedList => f.write_str("unexpected list"),
            Self::ListLengthMismatch { got, expected } => {
                write!(f, "unexpected list length (got {got}, expected {expected})")
            }
            Self::Custom(err) => f.write_str(err),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn error_new() {
        let e = Error::new(ErrorKind::Overflow);
        assert_eq!(e.bytepos, 0);
        assert_eq!(e.kind, ErrorKind::Overflow);
    }

    #[test]
    fn error_with_bytepos() {
        let e = Error::with_bytepos(ErrorKind::InputTooShort, 42);
        assert_eq!(e.bytepos, 42);
        assert_eq!(e.kind, ErrorKind::InputTooShort);
    }

    #[test]
    fn error_from_error_kind() {
        let e: Error = ErrorKind::LeadingZero.into();
        assert_eq!(e.bytepos, 0);
        assert_eq!(e.kind, ErrorKind::LeadingZero);
    }

    #[test]
    fn error_display() {
        let e = Error::with_bytepos(ErrorKind::Overflow, 10);
        assert_eq!(e.to_string(), "overflow (at byte 10)");
    }

    #[test]
    fn error_display_list_length_mismatch() {
        let e = Error::new(ErrorKind::ListLengthMismatch { expected: 3, got: 5 });
        assert_eq!(e.to_string(), "unexpected list length (got 5, expected 3) (at byte 0)");
    }

    #[test]
    fn error_display_custom() {
        let e = Error::new(ErrorKind::Custom("bad data"));
        assert_eq!(e.to_string(), "bad data (at byte 0)");
    }

    #[test]
    fn error_eq_distinguishes_bytepos() {
        let a = Error::with_bytepos(ErrorKind::Overflow, 0);
        let b = Error::with_bytepos(ErrorKind::Overflow, 1);
        assert_ne!(a, b);
    }

    #[test]
    fn error_clone_copy() {
        let e = Error::with_bytepos(ErrorKind::LeadingZero, 5);
        let cloned = e.clone();
        let copied = e;
        assert_eq!(e, cloned);
        assert_eq!(e, copied);
    }
}
