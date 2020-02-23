#![deny(missing_docs)]
//! Memoir is a library of self-describing, reflective parser-combinators.
//! Parsers are represented as reified objects that can print themselves
//! as documentation.
//!
//! For most purposes, memoir's *prelude* should be imported.
//!
//! ```
//! use memoir::prelude::*;
//!
//! let parser =
//!     (string("set"), optional(symbol('!')))
//!     .then(whitespace())
//!     .then(either(string("on"), string("off")));
//!
//! assert_eq!(parser.describe(), "set[!] on/off");
//! assert!(parser.parse("set on").is_ok());
//! ```

pub mod error;
pub mod parsers;
pub mod prelude;
