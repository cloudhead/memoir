//! Parser errors.

use std::fmt;

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
}

impl std::error::Error for Error {}

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
