//! Core parser types. Import to construct new parsers.

use nonempty::NonEmpty;

use std::fmt;
use std::result;

use crate::error::Error;

/// Either left or right. Used for parsers that can return
/// either of two types of output.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Either<L, R> {
    Left(L),
    Right(R),
}

/// Result of applying a `Parser` to an input.
pub type Result<'a, T> = result::Result<(T, &'a str), Error>;

/// A self-describing parser combinator.
pub trait Parser<'a>: Clone {
    /// The output of the parser, in case of success.
    type Output;

    /// Parse an input string and return a result, On success, returns an output, and any leftover
    /// input. Otherwise, returns an error.
    fn parse(&self, input: &'a str) -> Result<'a, Self::Output>;

    /// Describe this parser as a string.
    fn describe(&self) -> String;

    /// Describe this parser when it fails.
    fn describe_err(&self) -> Error {
        Error::new(format!("expected `{}`", self.describe()))
    }

    /// Sequence this parser with the next one.
    fn then<P: Parser<'a>>(self, next: P) -> (Self, P) {
        (self, next)
    }

    /// If this parser fails, try another one.
    fn or<P: Parser<'a>>(self, other: P) -> Alternative<Self, P> {
        Alternative(self, other)
    }

    /// Overwrite this parser's description with the given string.
    /// This is useful in particular when using one of the provideed parsers,
    /// and the built-in description is not adequate.
    fn label(self, label: &'a str) -> Label<'a, Self> {
        Label(self, label)
    }

    /// Provide a custom error message in case this parser fails.
    /// This is useful for more complex parsers, or when the default
    /// error is not adequate.
    fn label_err(self, err: &'a str) -> LabelErr<'a, Self> {
        LabelErr(self, err)
    }
}

/// A parser that always fails with a message. Useful to create custom
/// error messages.
#[derive(Clone)]
pub struct Fail<'a>(&'a str);
impl<'a> Parser<'a> for Fail<'a> {
    type Output = ();

    fn parse(&self, _: &'a str) -> Result<'a, Self::Output> {
        Err(Error::new(self.0))
    }

    fn describe(&self) -> String {
        self.0.to_owned()
    }
}

/// A transparent parser that overwrites that provides a description
/// for the underlying parser.
#[derive(Clone)]
pub struct Label<'a, P>(P, &'a str);
impl<'a, P> Parser<'a> for Label<'a, P>
where
    P: Parser<'a>,
{
    type Output = P::Output;

    fn parse(&self, input: &'a str) -> Result<'a, Self::Output> {
        self.0.parse(input)
    }

    fn describe(&self) -> String {
        self.1.to_owned()
    }
}

/// A transparent parser that just adds a label in case the parser fails.
#[derive(Clone)]
pub struct LabelErr<'a, P>(P, &'a str);
impl<'a, P> Parser<'a> for LabelErr<'a, P>
where
    P: Parser<'a>,
{
    type Output = P::Output;

    fn parse(&self, input: &'a str) -> Result<'a, Self::Output> {
        self.0.parse(input).map_err(|e| Error::from(self.1, e))
    }

    fn describe(&self) -> String {
        self.0.describe()
    }
}

/// Tries to apply the underlying parser, and if it fails, returns
/// an unmodified input.
///
/// Returns the output as an `Option`.
#[derive(Clone)]
pub struct Optional<P>(P);
impl<'a, P> Parser<'a> for Optional<P>
where
    P: Parser<'a>,
{
    type Output = Option<P::Output>;

    fn parse(&self, input: &'a str) -> Result<'a, Self::Output> {
        match self.0.parse(input) {
            Ok((out, rest)) => Ok((Some(out), rest)),
            Err(_) => Ok((None, input)),
        }
    }

    fn describe(&self) -> String {
        self.to_string()
    }
}

impl<'a, P> fmt::Display for Optional<P>
where
    P: Parser<'a>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}]", self.0.describe())
    }
}

/// Parses if the predicate returns `true` on the input's next `char`.
#[derive(Clone)]
pub struct Satisfy<'a, F>(F, &'a str);
impl<'a, F> Parser<'a> for Satisfy<'a, F>
where
    F: Fn(char) -> bool + Clone,
{
    type Output = char;

    fn parse(&self, input: &'a str) -> Result<'a, Self::Output> {
        let predicate = &self.0;

        match input.chars().next() {
            Some(c) if predicate(c) => Ok((c, input.get(c.len_utf8()..).unwrap_or_default())),
            _ => Err(self.describe_err()),
        }
    }

    fn describe(&self) -> String {
        self.1.to_owned()
    }
}

/// Applies the underlying parser zero or more times. Never fails.
/// Returns the outputs as a vector.
#[derive(Clone)]
pub struct Any<P>(P);
impl<'a, P> Parser<'a> for Any<P>
where
    P: Parser<'a>,
{
    type Output = Vec<P::Output>;

    fn parse(&self, input: &'a str) -> Result<'a, Self::Output> {
        let mut input = input;
        let mut outs = Vec::new();

        while let Ok((out, rest)) = self.0.parse(input) {
            outs.push(out);
            input = rest;
        }
        Ok((outs, input))
    }

    fn describe(&self) -> String {
        self.to_string()
    }
}

impl<'a, P> fmt::Display for Any<P>
where
    P: Parser<'a>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}]..", self.0.describe())
    }
}

/// Applies the underlying parser at least once.
/// Returns the outputs as a non-empty vector.
#[derive(Clone)]
pub struct Many<P>(P);
impl<'a, P> Parser<'a> for Many<P>
where
    P: Parser<'a>,
{
    type Output = NonEmpty<P::Output>;

    fn parse(&self, input: &'a str) -> Result<'a, Self::Output> {
        (self.0.clone(), Any(self.0.clone()))
            .parse(input)
            .map(|(out, rest)| (out.into(), rest))
    }

    fn describe(&self) -> String {
        self.to_string()
    }
}

impl<'a, P> fmt::Display for Many<P>
where
    P: Parser<'a>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}..", self.0.describe())
    }
}

/// Tries to apply the first parser, and if it fails, applies
/// the second one. On success, returns an `Either` with either
/// the output of the first or second parser.
#[derive(Clone)]
pub struct Alternative<P, Q>(P, Q);
impl<'a, P, Q> Parser<'a> for Alternative<P, Q>
where
    P: Parser<'a>,
    Q: Parser<'a>,
{
    type Output = Either<P::Output, Q::Output>;

    fn parse(&self, input: &'a str) -> Result<'a, Self::Output> {
        if let Ok((out, rest)) = self.0.parse(input) {
            Ok((Either::Left(out), rest))
        } else {
            match self.1.parse(input) {
                Ok((out, rest)) => Ok((Either::Right(out), rest)),
                Err(err) => Err(err),
            }
        }
    }

    fn describe(&self) -> String {
        self.to_string()
    }
}

impl<'a, P, Q> fmt::Display for Alternative<P, Q>
where
    P: Parser<'a>,
    Q: Parser<'a>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}/{}", self.0.describe(), self.1.describe())
    }
}

/// Applies the parsers in the underlying vector until one succeeds.
#[derive(Clone)]
pub struct Choice<P>(Vec<P>);
impl<'a, P> Parser<'a> for Choice<P>
where
    P: Parser<'a>,
{
    type Output = P::Output;

    fn parse(&self, input: &'a str) -> Result<'a, Self::Output> {
        for p in self.0.iter() {
            if let Ok(result) = p.parse(input) {
                return Ok(result);
            }
        }
        Err(self.describe_err())
    }

    fn describe(&self) -> String {
        self.to_string()
    }
}

impl<'a, P> fmt::Display for Choice<P>
where
    P: Parser<'a>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0
            .iter()
            .map(|p| p.describe())
            .collect::<Vec<_>>()
            .join(" | ")
            .fmt(f)
    }
}

/// Tries to parse a single character.
#[derive(Clone)]
pub struct Symbol(char);
impl<'a> Parser<'a> for Symbol {
    type Output = char;

    fn parse(&self, input: &'a str) -> Result<'a, Self::Output> {
        match input.chars().next() {
            Some(c) if c == self.0 => Ok((c, input.get(c.len_utf8()..).unwrap_or_default())),
            _ => Err(self.describe_err()),
        }
    }

    fn describe(&self) -> String {
        self.to_string()
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

/// Tries to parse a string literal.
#[derive(Clone)]
pub struct Keyword(&'static str);
impl<'a> Parser<'a> for Keyword {
    type Output = &'static str;

    fn parse(&self, input: &'a str) -> Result<'a, Self::Output> {
        match input.get(..self.0.len()) {
            Some(word) if word == self.0 => {
                Ok((self.0, input.get(word.len()..).unwrap_or_default()))
            }
            _ => Err(self.describe_err()),
        }
    }

    fn describe(&self) -> String {
        self.to_string()
    }
}

impl fmt::Display for Keyword {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

/// Applies the first parser and if it succeeds, the second.
impl<'a, P, Q> Parser<'a> for (P, Q)
where
    P: Parser<'a>,
    Q: Parser<'a>,
{
    type Output = (P::Output, Q::Output);

    fn parse(&self, input: &'a str) -> Result<'a, Self::Output> {
        self.0
            .parse(input)
            .and_then(|(out0, rest)| self.1.parse(rest).map(|(out1, rest)| ((out0, out1), rest)))
    }

    fn describe(&self) -> String {
        format!("{}{}", self.0.describe(), self.1.describe())
    }
}

impl<'a, P, Q, R> Parser<'a> for (P, Q, R)
where
    P: Parser<'a>,
    Q: Parser<'a>,
    R: Parser<'a>,
{
    type Output = (P::Output, Q::Output, R::Output);

    fn parse(&self, input: &'a str) -> Result<'a, Self::Output> {
        self.0.parse(input).and_then(|(out0, rest)| {
            self.1.parse(rest).and_then(|(out1, rest)| {
                self.2
                    .parse(rest)
                    .map(|(out2, rest)| ((out0, out1, out2), rest))
            })
        })
    }

    fn describe(&self) -> String {
        format!(
            "{}{}{}",
            self.0.describe(),
            self.1.describe(),
            self.1.describe()
        )
    }
}

/// Applies the parsers in the slice until one succeeds.
#[inline]
pub fn choice<'a, P: Parser<'a>>(parsers: &[P]) -> Choice<P> {
    Choice(parsers.to_vec())
}

/// Applies the parser any number of times.
#[inline]
pub fn any<'a, P: Parser<'a>>(parser: P) -> Any<P> {
    Any(parser)
}

/// Applies the parser at least once.
#[inline]
pub fn many<'a, P: Parser<'a>>(parser: P) -> Many<P> {
    Many(parser)
}

/// Applies the parser at least once, separating subsequent applications
/// with a separator.
#[inline]
pub fn list<'a, P: Parser<'a>>(parser: P, separator: impl Parser<'a>) -> impl Parser<'a> {
    parser.clone().then(Any(separator.then(parser)))
}

/// Tries to apply the parser. If it fails, returns the unmodified input.
/// Outputs an `Option` with `None` if it failed to apply the parser
/// and `Some` if it succeeded.
#[inline]
pub fn optional<'a, P: Parser<'a>>(parser: P) -> Optional<P> {
    Optional(parser)
}

/// Parses a single character.
#[inline]
pub fn symbol(sym: char) -> Symbol {
    Symbol(sym)
}

/// Parses a string literal.
#[inline]
pub fn keyword(kw: &'static str) -> Keyword {
    Keyword(kw)
}

/// Applies the first parser, and if it fails, applies the second one.
/// Outputs an `Either` on success.
#[inline]
pub fn either<'a, P, Q>(left: P, right: Q) -> Alternative<P, Q>
where
    P: Parser<'a>,
    Q: Parser<'a>,
{
    Alternative(left, right)
}

/// Apply *open*, then *between*, then *close*.
///
/// ```
/// use memoir::prelude::*;
///
/// let parser = between(symbol('{'), symbol('}'), any(letter()));
///
/// assert!(parser.parse("{acme}").is_ok());
/// ```
#[inline]
pub fn between<'a, P, Q>(open: P, close: P, between: Q) -> impl Parser<'a>
where
    P: Parser<'a>,
    Q: Parser<'a>,
{
    open.then(between).then(close)
}

#[inline]
pub fn satisfy<'a, F>(predicate: F, description: &'a str) -> Satisfy<'a, F> {
    Satisfy(predicate, description)
}

/// Parses a single letter.
///
/// ```
/// use memoir::prelude::*;
///
/// let letter = satisfy(char::is_alphabetic, "a-Z");
/// ```
#[inline]
pub fn letter<'a>() -> Satisfy<'a, fn(char) -> bool> {
    satisfy(char::is_alphabetic, "a-Z")
}

/// Parses a single base ten digit.
///
/// ```
/// use memoir::prelude::*;
///
/// let digit = satisfy(|c: char| c.is_digit(10), "0-9");
/// ```
#[inline]
pub fn digit<'a>() -> Satisfy<'a, fn(char) -> bool> {
    satisfy(|c: char| c.is_digit(10), "0-9")
}

/// Parses a single word.
///
/// ```
/// use memoir::prelude::*;
///
/// assert!(word().parse("fj20_a1").is_ok());
/// ```
#[inline]
pub fn word<'a>() -> impl Parser<'a> {
    many(satisfy(|c: char| c.is_alphabetic() || c == '_', "a-Z | _")).label("<word>")
}

/// Parses a single whitespace character.
///
/// ```
/// use memoir::prelude::*;
///
/// let whitespace = satisfy(char::is_whitespace, " ");
/// ```
#[inline]
pub fn whitespace<'a>() -> Satisfy<'a, fn(char) -> bool> {
    satisfy(char::is_whitespace, " ")
}

/// Fail with a message.
///
/// ```
/// use memoir::prelude::*;
/// use memoir::error::Error;
///
/// let parser = symbol('!').or(fail("only `!` is allowed"));
///
/// assert_eq!(parser.parse("?").err(), Some(Error::new("only `!` is allowed")));
/// ```
#[inline]
pub fn fail<'a>(msg: &'a str) -> Fail<'a> {
    Fail(msg)
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_optional() {
        let p = Optional(Symbol('?'));

        assert_eq!(p.to_string(), "[?]");

        assert!(p.parse("?").is_ok());
        assert!(p.parse("").is_ok());
    }

    #[test]
    fn test_choice() {
        let p = Choice(vec![Symbol('?'), Symbol('!'), Symbol('.')]);

        assert_eq!(p.to_string(), "? | ! | .");

        assert_eq!(p.parse("?").ok(), Some(('?', "")));
        assert_eq!(p.parse("!").ok(), Some(('!', "")));
        assert_eq!(p.parse(".").ok(), Some(('.', "")));

        assert!(p.parse("@").is_err());
        assert!(p.parse(",").is_err());
        assert!(p.parse("").is_err());
    }

    #[test]
    fn test_any() {
        let p = Any(Symbol('?'));

        assert_eq!(p.to_string(), "[?]..");

        assert!(p.parse("").is_ok());
        assert!(p.parse("?").is_ok());
        assert!(p.parse("???").is_ok());
        assert!(p.parse("??????").is_ok());
    }

    #[test]
    fn test_keyword() {
        let p = Keyword("set");

        assert_eq!(p.to_string(), "set");

        assert!(p.parse("set").is_ok());
        assert!(p.parse("get").is_err());
        assert!(p.parse("").is_err());
    }

    #[test]
    fn test_many() {
        let p = Many(Symbol('!'));

        assert_eq!(p.to_string(), "!..");

        assert!(p.parse("!").is_ok());
        assert!(p.parse("!!").is_ok());
        assert!(p.parse("!!!").is_ok());
        assert!(p.parse("").is_err());
    }

    #[test]
    fn test_tuple1() {
        let p = (Many(Symbol('!')), Many(Symbol('?')));

        assert_eq!(p.describe(), "!..?..");
        assert!(p.parse("!!!!???").is_ok());
    }

    #[test]
    fn test_tuple2() {
        let p = (
            Keyword("switch"),
            (
                Symbol(' '),
                (
                    Symbol('='),
                    (Symbol(' '), Choice(vec![Keyword("on"), Keyword("off")])),
                ),
            ),
        );

        assert_eq!(p.describe(), "switch = on | off");

        assert!(p.parse("switch = on").is_ok());
        assert!(p.parse("switch = off").is_ok());
    }

    #[test]
    fn test_then() {
        let p = Keyword("set").then(Symbol(' ')).then(Symbol('!'));

        assert_eq!(p.describe(), "set !");
    }

    #[test]
    fn test_satisfy() {
        let p = Many(Satisfy(char::is_alphabetic, "[a-Z]"));

        assert_eq!(p.describe(), "[a-Z]..");

        assert!(p.parse("abcdefg").is_ok());
        assert!(p.parse("aBcDe").is_ok());
        assert_eq!(p.parse("___").err(), Some(Error::new("expected `[a-Z]`")));
    }

    #[test]
    fn test_label_err() {
        let p = LabelErr(Keyword("set"), "want `set`");

        assert_eq!(p.describe(), "set");

        assert!(p.parse("set").is_ok());
        assert_eq!(p.parse("get").unwrap_err().to_string(), "want `set`");
    }

    #[test]
    fn test_label() {
        let p = Label(Keyword("set"), "<set>");

        assert_eq!(p.describe(), "<set>");
        assert!(p.parse("set").is_ok());
    }

    #[test]
    fn test_labels() {
        let p1 = Label(LabelErr(Keyword("set"), "want `set`"), "<set>");
        let p2 = LabelErr(Label(Keyword("set"), "<set>"), "want `set`");

        assert_eq!(p1.describe(), "<set>");
        assert!(p1.parse("set").is_ok());
        assert_eq!(p1.parse("get").unwrap_err().to_string(), "want `set`");

        assert_eq!(p2.describe(), "<set>");
        assert!(p2.parse("set").is_ok());
        assert_eq!(p2.parse("get").unwrap_err().to_string(), "want `set`");
    }

    #[test]
    fn test_list() {
        let p = list(Keyword("moo"), Symbol('-'));

        assert!(p.parse("moo-moo-moo").is_ok());
        assert!(p.parse("moo").is_ok());
        assert!(p.parse("foo").is_err());
    }
}
