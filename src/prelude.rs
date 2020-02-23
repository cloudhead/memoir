//! Exports all the common parser combinators.

pub use crate::parsers::Parser;
pub use crate::parsers::{
    any, between, character, choice, digit, either, fail, keyword, letter, linefeed, list, many,
    optional, satisfy, string, symbol, whitespace, word,
};
