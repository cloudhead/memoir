//! Core parser types.

use std::fmt;
use std::iter::FromIterator;
use std::num::{ParseFloatError, ParseIntError};
use std::rc::Rc;

use crate::result::{Error, Result};

/// Either left or right. Used for parsers that can return
/// either of two types of output.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Either<L, R> {
    /// The left case.
    Left(L),
    /// The right case.
    Right(R),
}

/// A self-describing parser combinator.
#[derive(Clone)]
pub struct Parser<O: 'static> {
    /// The label or description of this parser.
    pub label: String,

    parse: Rc<dyn for<'a> Fn(&'a str) -> Result<'a, O>>,
}

impl<O> Parser<O> {
    /// Create a new parser from a function and a label.
    pub fn new<F, S>(f: F, label: S) -> Self
    where
        F: 'static + Fn(&str) -> Result<O>,
        S: Into<String>,
    {
        Parser {
            parse: Rc::new(f),
            label: label.into(),
        }
    }

    /// Sequence this parser with the next one.
    ///
    /// ```
    /// use memoir::*;
    ///
    /// let p = string("moo").then(symbol('!')).then(symbol('?'));
    /// assert_eq!(p.label, "\"moo\" '!' '?'");
    /// ```
    pub fn then<U: 'static>(self, next: Parser<U>) -> Parser<(O, U)> {
        let label = format!("{} {}", self.label, next.label);

        Parser::new(
            move |input: &str| {
                (*self.parse)(input).and_then(|(out0, rest)| {
                    (*next.parse)(rest).map(|(out1, rest)| ((out0, out1), rest))
                })
            },
            label,
        )
    }

    /// Fail this parser if the predicate fails.
    ///
    /// ```
    /// use memoir::*;
    ///
    /// let p = string("moo").followed_by(|c| c == Some('.'));
    /// assert_eq!(p.parse("moo."), Ok(("moo".to_owned(), ".")));
    /// assert!(p.parse("moo").is_err());
    /// ```
    pub fn followed_by<F>(self, f: F) -> Parser<O>
    where
        F: 'static + Fn(Option<char>) -> bool,
    {
        let label = self.label.clone();

        Parser::new(
            move |input| match (*self.parse)(input) {
                Ok((out, rest)) => {
                    let c = rest.chars().next();

                    if f(c) {
                        Ok((out, rest))
                    } else {
                        Err((
                            Error::new(format!(
                                "expected {:?} not to be followed by {:?}",
                                self.label,
                                c.map(|c| c.to_string())
                                    .as_deref()
                                    .unwrap_or("<end of input>")
                            )),
                            rest,
                        ))
                    }
                }
                Err(err) => Err(err),
            },
            label,
        )
    }

    /// If this parser fails without any consuming input, try another one.
    ///
    /// ```
    /// use memoir::*;
    ///
    /// let p = symbol('!').or(symbol('?'));
    ///
    /// assert_eq!(p.parse("?"), Ok(('?', "")));
    /// ```
    pub fn or(self, other: Parser<O>) -> Parser<O> {
        let label = format!("{} | {}", self.label, other.label);

        Parser::new(
            move |input| match (*self.parse)(input) {
                Ok(result) => Ok(result),
                Err((err, rest)) if rest != input => Err((err, rest)),
                Err((_err, _rest)) => match (*other.parse)(input) {
                    Ok((out, rest)) => Ok((out, rest)),
                    // TODO: Combine error messages.
                    Err(err) => Err(err),
                },
            },
            label,
        )
    }

    /// Apply this parser, then try to apply the other parser.
    /// Only the output from this parser is returned.
    ///
    /// ```
    /// use memoir::*;
    ///
    /// let p = symbol('X').skip(symbol('Y')).then(symbol('Z'));
    ///
    /// assert_eq!(p.parse("XYZ"), Ok((('X', 'Z'), "")));
    /// assert!(p.parse("XZ").is_err());
    ///
    /// let p = symbol('X').skip(optional(symbol('Y'))).then(symbol('Z'));
    ///
    /// assert_eq!(p.parse("XYZ"), Ok((('X', 'Z'), "")));
    /// assert_eq!(p.parse("XZ"), Ok((('X', 'Z'), "")));
    /// ```
    pub fn skip<U>(self, skip: Parser<U>) -> Parser<O>
    where
        Self: Sized,
    {
        let label = self.label.clone();

        Parser::new(
            move |input| match (*self.parse)(input) {
                Ok((out, rest)) => match (*skip.parse)(rest) {
                    Ok((_, skipped)) => Ok((out, skipped)),
                    Err(err) => Err(err),
                },
                Err(err) => Err(err),
            },
            label,
        )
    }

    /// Modify the parser output if it succeeds, with the provided function.
    ///
    /// ```
    /// use memoir::*;
    ///
    /// let p = symbol('X').map(|out| (out, out));
    ///
    /// assert_eq!(p.parse("X"), Ok((('X', 'X'), "")));
    /// ```
    pub fn map<U: 'static, F>(self, f: F) -> Parser<U>
    where
        F: 'static + Fn(O) -> U,
    {
        let label = self.label.clone();

        Parser::new(
            move |input| (*self.parse)(input).map(|(out, rest)| (f(out), rest)),
            label,
        )
    }

    /// Modify the parser output if it succeeds, with the provided function
    /// that can fail.
    ///
    /// ```
    /// use memoir::*;
    ///
    /// let p = symbol('X').try_map::<String, _, _>(|out| Err(format!("failed to parse {}", out)));
    ///
    /// assert!(p.parse("X").is_err())
    /// ```
    pub fn try_map<'a, U: 'static, S, F>(self, f: F) -> Parser<U>
    where
        F: 'static + Fn(O) -> std::result::Result<U, S>,
        S: Into<String>,
    {
        let label = self.label.clone();

        Parser::new(
            move |input| {
                (*self.parse)(input).and_then(|(out, rest)| match f(out) {
                    Ok(result) => Ok((result, rest)),
                    Err(err) => Err((Error::new(err.into()), rest)),
                })
            },
            label,
        )
    }

    /// Modify the parser output if it succeeds, with the provided value.
    ///
    /// ```
    /// use memoir::*;
    ///
    /// let p = symbol('X').value('Y');
    ///
    /// assert_eq!(p.parse("X"), Ok(('Y', "")));
    /// ```
    pub fn value<U: Clone + 'static>(self, val: U) -> Parser<U> {
        let label = self.label.clone();

        Parser::new(
            move |input| (*self.parse)(input).map(|(_, rest)| (val.clone(), rest)),
            label,
        )
    }

    /// Overwrite this parser's description with the given string.
    /// This is useful in particular when using one of the provideed parsers,
    /// and the built-in description is not adequate.
    pub fn label(self, l: impl Into<String>) -> Parser<O> {
        Parser {
            parse: self.parse,
            label: l.into(),
        }
    }

    /// Parse an input string and return a result. On success, returns an output, and any leftover
    /// input. Otherwise, returns an error.
    pub fn parse<'a>(&self, input: &'a str) -> Result<'a, O> {
        (*self.parse)(input)
    }

    /// Try to convert the output of the parser from a string to the specified type.
    ///
    /// ```
    /// use memoir::*;
    ///
    /// let p = many::<_, String>(digit()).from_str::<u64, _>();
    ///
    /// assert_eq!(p.parse("12345"), Ok((12345, "")));
    /// assert!(p.parse("abcde").is_err());
    ///
    /// ```
    pub fn from_str<U, E>(self) -> Parser<U>
    where
        O: AsRef<str>,
        U: std::str::FromStr<Err = E>,
        E: std::fmt::Display,
    {
        let label = self.label.clone();

        Parser::new(
            move |input| match (*self.parse)(input) {
                Ok((out, rest)) => match out.as_ref().parse::<U>() {
                    Ok(o) => Ok((o, rest)),
                    Err(e) => Err((
                        Error::new(format!("conversion from string failed: {}", e)),
                        rest,
                    )),
                },
                Err(err) => Err(err),
            },
            label,
        )
    }

    /// Apply the parser until the other parser succeeds, or the
    /// end of the input is reached.
    ///
    /// ```
    /// use memoir::*;
    ///
    /// let p = character().until::<String, _>(symbol('!'));
    /// let (out, rest) = p.parse("Hello World!").unwrap();
    ///
    /// assert_eq!(out, String::from("Hello World"),);
    /// assert_eq!(rest, "!");
    /// ```
    pub fn until<U, V>(self, other: Parser<V>) -> Parser<U>
    where
        U: FromIterator<O>,
    {
        let label = format!("(-{} {})*", other.label, self.label);

        Parser::new(
            move |input| {
                let mut input = input;
                let mut outs = Vec::new();

                while (*other.parse)(input).is_err() && !input.is_empty() {
                    match (*self.parse)(input) {
                        Ok((out, rest)) => {
                            outs.push(out);
                            input = rest;
                        }
                        Err(err) => return Err(err),
                    }
                }
                Ok((outs.into_iter().collect::<U>(), input))
            },
            label,
        )
    }
}

impl<O> fmt::Display for Parser<O> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.label)
    }
}

impl From<char> for Parser<char> {
    fn from(c: char) -> Self {
        symbol(c)
    }
}

impl From<&'static str> for Parser<String> {
    fn from(s: &'static str) -> Self {
        string(s)
    }
}

/// Types that can be parsed from strings.
pub trait Parse: Sized {
    /// Parse a string into this type.
    fn parse(input: &str) -> Result<Self>;

    /// Describe this type.
    fn label() -> &'static str;
}

/// Create a parser out of an instance of `Parse`.
pub fn parser<O: Parse>() -> Parser<O> {
    Parser::new(O::parse, O::label())
}

/// Fail with a message.
///
/// ```
/// use memoir::*;
/// use memoir::result::Error;
///
/// let parser = symbol('!').or(fail("only `!` is allowed"));
///
/// assert_eq!(parser.parse("?").err(), Some((Error::new("only `!` is allowed"), "?")));
/// ```
pub fn fail<S: Into<String>, U>(err: S) -> Parser<U> {
    let err = err.into();

    Parser::new(move |input| Err((Error::new(err.clone()), input)), "<fail>")
}

/// Call the given predicate on the next character. If it returns `true`,
/// consume the character.
pub fn satisfy<F, S>(predicate: F, label: S) -> Parser<char>
where
    F: 'static + Fn(char) -> bool,
    S: Into<String>,
{
    let label: String = label.into();
    let expected = label.clone();

    Parser::new(
        move |input: &str| match input.chars().next() {
            Some(c) if predicate(c) => Ok((c, input.get(c.len_utf8()..).unwrap_or_default())),
            _ => Err((Error::expect(&expected, input), input)),
        },
        label,
    )
}

/// Call a function on the input, and if it returns `false`,
/// throw an error.
pub fn expect<F>(f: F, token: &'static str) -> Parser<()>
where
    F: 'static + Fn(&str) -> bool,
{
    Parser::new(
        move |input| {
            if !f(input) {
                Err((Error::expect(token, input), input))
            } else {
                Ok(((), input))
            }
        },
        token,
    )
}

/// Apply *open*, then *between*, then *close*.
///
/// ```
/// use memoir::*;
///
/// let parser = between(symbol('{'), symbol('}'), any::<_, String>(letter()));
///
/// assert!(parser.parse("{acme}").is_ok());
/// assert_eq!(parser.parse("{acme}"), Ok(("acme".to_owned(), "")));
/// ```
pub fn between<U: 'static, V: 'static, O>(
    open: impl Into<Parser<U>>,
    close: impl Into<Parser<V>>,
    between: Parser<O>,
) -> Parser<O> {
    open.into()
        .then(between)
        .then(close.into())
        .map(|((_, body), _)| body)
}

/// Tries to apply the parser. If it fails, returns the unmodified input.
/// Outputs an `Option` with `None` if it failed to apply the parser
/// and `Some` if it succeeded.
pub fn optional<O: 'static>(p: impl Into<Parser<O>>) -> Parser<Option<O>> {
    let p = p.into();
    let label = format!("{}?", p.label);

    Parser::new(
        move |input: &str| match (*p.parse)(input) {
            Ok((out, rest)) => Ok((Some(out), rest)),
            Err(_) => Ok((None, input)),
        },
        label,
    )
}

/// Parses a single character.
pub fn symbol(c: char) -> Parser<char> {
    satisfy(move |input: char| input == c, format!("{:?}", c))
}

/// Parses a single letter.
///
/// ```
/// use memoir::*;
///
/// let letter = satisfy(char::is_alphabetic, "a-Z");
/// ```
pub fn letter() -> Parser<char> {
    satisfy(char::is_alphabetic, "a-Z")
}

/// Parses any character. Always succeeds.
pub fn character() -> Parser<char> {
    satisfy(|_| true, "<character>")
}

/// Applies the parser any number of times.
///
/// ```
/// use memoir::*;
///
/// let p = any(symbol('?'));
///
/// assert_eq!(p.to_string(), "'?'*");
/// assert_eq!(p.parse("???"), Ok((String::from("???"), "")));
///
/// assert!(p.parse("").is_ok());
/// assert!(p.parse("?").is_ok());
/// assert!(p.parse("??????").is_ok());
/// ```
pub fn any<O, U>(p: Parser<O>) -> Parser<U>
where
    O: 'static,
    U: 'static + FromIterator<O>,
{
    let label = format!("{}*", &p.label);

    Parser::new(
        move |input| {
            let mut input = input;
            let mut outs = Vec::new();

            while let Ok((out, rest)) = (*p.parse)(input) {
                outs.push(out);
                input = rest;
            }
            Ok((outs.into_iter().collect::<U>(), input))
        },
        label,
    )
}

/// Applies the parser one or more times.
///
/// ```
/// use memoir::*;
///
/// let p = many::<_, String>(symbol('!'));
///
/// assert_eq!(p.to_string(), "'!'+");
///
/// assert!(p.parse("!").is_ok());
/// assert!(p.parse("!!").is_ok());
/// assert!(p.parse("!!!").is_ok());
/// assert!(p.parse("").is_err());
/// ```
pub fn many<O, U>(p: Parser<O>) -> Parser<U>
where
    O: 'static,
    U: 'static + FromIterator<O>,
{
    let label = format!("{}+", &p.label);

    Parser::new(
        move |input| {
            let mut input = input;
            let mut outs = Vec::new();

            let (out, rest) = (*p.parse)(input)?;
            outs.push(out);
            input = rest;

            while let Ok((out, rest)) = (*p.parse)(input) {
                outs.push(out);
                input = rest;
            }
            Ok((outs.into_iter().collect::<U>(), input))
        },
        label,
    )
}

/// Applies the parsers in the slice until one succeeds.
///
/// ```
/// use memoir::*;
///
/// let p = choice(vec![symbol('?'), symbol('!'), symbol('.')]);
///
/// assert_eq!(p.to_string(), "'?' | '!' | '.'");
///
/// assert_eq!(p.parse("?").ok(), Some(('?', "")));
/// assert_eq!(p.parse("!").ok(), Some(('!', "")));
/// assert_eq!(p.parse(".").ok(), Some(('.', "")));
///
/// assert!(p.parse("@").is_err());
/// assert!(p.parse(",").is_err());
/// assert!(p.parse("").is_err());
/// ```
pub fn choice<O>(choices: Vec<Parser<O>>) -> Parser<O>
where
    O: 'static + Clone,
{
    let label = choices
        .iter()
        .map(|p| p.label.clone())
        .collect::<Vec<_>>()
        .join(" | ");
    let expected = label.clone();

    Parser::new(
        move |input| {
            for p in choices.iter() {
                match (*p.parse)(input) {
                    Ok(result) => return Ok(result),
                    Err((err, rest)) if rest != input => return Err((err, rest)),
                    Err(_) => continue,
                }
            }
            Err((Error::expect(&expected, input), input))
        },
        label,
    )
}

/// Parses a string literal.
///
/// ```
/// use memoir::*;
/// use memoir::result::Error;
///
/// let p = keyword::<String>("set");
///
/// assert_eq!(p.to_string(), "\"set\"");
///
/// assert!(p.parse("set").is_ok());
/// assert!(p.parse("").is_err());
///
/// assert_eq!(p.parse("get").err(), Some((Error::new("expected \"set\", got `get`"), "get")));
///
/// let p = keyword::<bool>("true");
/// assert_eq!(p.parse("true!"), Ok((true, "!")));
/// ```
pub fn keyword<O: std::str::FromStr + 'static>(s: &'static str) -> Parser<O> {
    let label = format!("{:?}", s);
    let expected = label.clone();

    Parser::new(
        move |input| match input.get(..s.len()) {
            Some(word) if word == s => match O::from_str(s) {
                Ok(out) => Ok((out, input.get(word.len()..).unwrap_or_default())),
                Err(_) => Err((Error::new("couldn't convert keyword"), input)),
            },
            _ => Err((Error::expect(&expected, input), input)),
        },
        label,
    )
}

/// Like `keyword`, but constrained to `String` outputs.
pub fn string(s: &'static str) -> Parser<String> {
    keyword::<String>(s)
}

/// Spaces.
///
/// ```
/// use memoir::*;
///
/// let p = whitespace();
///
/// assert!(p.parse(" ").is_ok());
/// assert!(p.parse("   ").is_ok());
/// assert!(p.parse("\t \t").is_ok());
/// assert!(p.parse("").is_err());
/// ```
pub fn whitespace() -> Parser<String> {
    many::<_, String>(satisfy(char::is_whitespace, "<whitespace>"))
        .label("<whitespace>")
        .from_str::<String, _>()
}

/// Parses a single line-feed token.
///
/// ```
/// use memoir::*;
///
/// let p = linefeed();
/// assert_eq!(p.parse("\n"), Ok((String::from("\n"), "")));
/// assert_eq!(p.parse("\r\n"), Ok((String::from("\r\n"), "")));
/// ```
pub fn linefeed() -> Parser<String> {
    symbol('\n').map(|_| String::from("\n")).or(string("\r\n"))
}

/// Parses a single base ten digit.
///
/// ```
/// use memoir::*;
///
/// let digit = satisfy(|c: char| c.is_digit(10), "0-9");
/// ```
pub fn digit() -> Parser<char> {
    satisfy(|c: char| c.is_digit(10), "0-9")
}

/// Natural number.
///
/// ```
/// use memoir::*;
///
/// let p = natural::<u64>();
///
/// assert!(p.parse("0").is_ok());
/// assert!(p.parse("123").is_ok());
/// assert!(p.parse("043").is_ok());
/// assert!(p.parse("-55").is_err());
/// ```
pub fn natural<O: std::str::FromStr<Err = ParseIntError>>() -> Parser<O> {
    many::<_, String>(digit()).from_str::<O, _>()
}

/// Positive or negative integer.
///
/// ```
/// use memoir::*;
///
/// let p = integer::<i64>();
///
/// assert!(p.parse("0").is_ok());
/// assert!(p.parse("123").is_ok());
/// assert!(p.parse("043").is_ok());
/// assert!(p.parse("-55").is_ok());
/// ```
pub fn integer<O: std::str::FromStr<Err = ParseIntError>>() -> Parser<O> {
    optional(symbol('-'))
        .then(many::<_, String>(digit()))
        .map(|(neg, num)| match neg {
            Some(_) => format!("-{}", num),
            None => num,
        })
        .from_str::<O, _>()
}

/// Rational number.
///
/// ```
/// use memoir::*;
///
/// let p = rational::<f64>();
///
/// assert!(p.parse("0").is_ok());
/// assert!(p.parse("123.456").is_ok());
/// assert!(p.parse("-1.944").is_ok());
/// assert!(p.parse("42").is_ok());
///
/// assert_eq!(p.parse(".42"), Ok((0.42, "")));
/// assert_eq!(p.parse("-.42"), Ok((-0.42, "")));
/// assert_eq!(p.parse("42."), Ok((42., "")));
/// assert_eq!(p.parse("42-"), Ok((42., "-")));
/// ```
pub fn rational<O: std::str::FromStr<Err = ParseFloatError>>() -> Parser<O> {
    optional(symbol('-'))
        .then(many::<_, String>(digit().or(symbol('.'))))
        .map(|(neg, num)| match neg {
            Some(_) => format!("-{}", num),
            None => num,
        })
        .from_str::<O, _>()
}

/// Applies the first parser, and if it fails, applies the second one.
/// Outputs an `Either` on success.
pub fn either<U, V>(left: Parser<U>, right: Parser<V>) -> Parser<Either<U, V>>
where
    U: 'static,
    V: 'static,
{
    let label = format!("{} | {}", left.label, right.label);

    Parser::new(
        move |input| {
            if let Ok((out, rest)) = (*left.parse)(input) {
                Ok((Either::Left(out), rest))
            } else {
                match (*right.parse)(input) {
                    Ok((out, rest)) => Ok((Either::Right(out), rest)),
                    Err(err) => Err(err),
                }
            }
        },
        label,
    )
}

/// Apply the given parser, and if it fails, don't consume any input.
///
/// ```
/// use memoir::*;
///
/// let p = choice(vec![
///     peek(string("leave").skip(whitespace()).then(string("england"))),
///     peek(string("leave").skip(whitespace()).then(string("france"))),
/// ]);
///
/// assert!(p.parse("leave england").is_ok());
/// assert!(p.parse("leave france").is_ok());
/// ```
pub fn peek<O>(p: Parser<O>) -> Parser<O> {
    let label = p.label.clone();

    Parser::new(
        move |input| (*p.parse)(input).map_err(|(err, _)| (err, input)),
        label,
    )
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_choice_backtracking() {
        let p = choice(vec![
            string("leave").skip(whitespace()).then(string("england")),
            string("learn").skip(whitespace()).then(string("english")),
            string("leave").skip(whitespace()).then(string("britain")),
        ]);

        assert!(p.parse("learn english").is_ok());
        assert!(p.parse("leave england").is_ok());
        assert!(p.parse("leave britain").is_err());

        let (err, rest) = p.parse("leave english").err().unwrap();
        assert_eq!(rest, "english");
        assert_eq!(err.to_string(), "expected \"england\", got `english`");
    }

    #[test]
    fn test_or_backtracing() {
        let p = string("leave")
            .skip(whitespace())
            .then(string("england"))
            .or(string("learn").skip(whitespace()).then(string("english")))
            .or(string("leave").skip(whitespace()).then(string("britain")));

        assert!(p.parse("learn english").is_ok());
        assert!(p.parse("leave england").is_ok());
        assert!(p.parse("leave britain").is_err());

        let (err, rest) = p.parse("leave english").err().unwrap();
        assert_eq!(rest, "english");
        assert_eq!(err.to_string(), "expected \"england\", got `english`");
    }
}
