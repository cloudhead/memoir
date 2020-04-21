//! Parser result types.

use std::fmt;

/// Result of applying a `Parser` to an input.
pub type Result<'a, T> = std::result::Result<(T, &'a str), (Error, &'a str)>;

/// A parser error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Error {
    msg: String,
    cause: Option<Box<Error>>,
}

impl Error {
    /// Create a new parser error from a message.
    pub fn new<S: Into<String>>(msg: S) -> Self {
        Self {
            msg: msg.into(),
            cause: None,
        }
    }

    /// Create a new parser error from a message, and another error.
    pub fn from<S: Into<String>>(msg: S, cause: Error) -> Self {
        Self {
            msg: msg.into(),
            cause: Some(Box::new(cause)),
        }
    }

    /// Create an error based on an actual and expected.
    pub fn expect(expected: &str, actual: &str) -> Error {
        if actual.is_empty() {
            return Self::new(format!("expected {}, but reached end of input", expected));
        }

        let (actual, overflow) = if actual.len() > 8 {
            (&actual[..8], "..")
        } else {
            (actual, "")
        };
        Self::new(format!(
            "expected {}, got `{}{}`",
            expected, actual, overflow
        ))
    }
}

impl std::error::Error for Error {}

impl From<String> for Error {
    fn from(input: String) -> Self {
        Error::new(input)
    }
}

impl From<&str> for Error {
    fn from(input: &str) -> Self {
        Error::new(input)
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.msg.fmt(f)
    }
}
