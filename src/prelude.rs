//! Exports all the common parser combinators.

pub use crate::parsers::Parser;
pub use crate::parsers::{
    any, between, choice, digit, either, keyword, letter, list, many, optional, satisfy, symbol,
    whitespace, word,
};
