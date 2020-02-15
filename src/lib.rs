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
//!     (keyword("set"), optional(symbol('!')))
//!     .then(whitespace())
//!     .then(either(keyword("on"), keyword("off")));
//!
//! assert_eq!(parser.describe(), "set[!] on/off");
//! assert!(parser.parse("set on").is_ok());
//! ```

pub mod error;
pub mod parsers;
pub mod prelude;
