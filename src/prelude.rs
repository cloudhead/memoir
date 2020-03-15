//! Exports all the common parser combinators.

pub use crate::parsers::Parser;
pub use crate::parsers::{
    any, apply, between, case, cases, character, choice, digit, either, fail, integer, keyword,
    letter, linefeed, list, many, natural, optional, rational, satisfy, string, symbol, whitespace,
    word,
};
