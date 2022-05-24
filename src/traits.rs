//! Parser traits.
use crate::parsers::Parser;
use crate::result::*;

/// Types that can be parsed from strings.
pub trait Parse: Sized + 'static {
    /// Return a parser for this type.
    fn parser() -> Parser<Self>;

    /// Parse a string into this type.
    fn parse(input: &str) -> Result<'_, Self> {
        Self::parser().parse(input)
    }
}
