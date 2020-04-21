#![deny(missing_docs)]
#![allow(clippy::type_complexity)]

//! Memoir is a library of self-describing, reflective parser-combinators.
//! Parsers are represented as reified objects that can print themselves
//! as documentation.
//!
//! For most purposes, memoir's *prelude* should be imported.
//!
//! ```
//! use memoir::*;
//!
//! let parser =
//!     string("set").then(optional(symbol('!')))
//!     .then(whitespace())
//!     .then(either(string("on"), string("off")));
//!
//! assert_eq!(parser.label, r#""set" '!'? <whitespace> "on" | "off""#);
//! assert!(parser.parse("set on").is_ok());
//! ```
pub mod ops;
pub mod parsers;
pub mod result;
pub mod traits;

pub use parsers::*;
