//! Core parser types.
use std::fmt;
use std::iter::FromIterator;
use std::num::{ParseFloatError, ParseIntError};
use std::rc::Rc;
use std::str::FromStr;

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
    /// let p = string("moo").followed_by(symbol('.'));
    /// assert_eq!(p.parse("moo."), Ok(("moo".to_owned(), ".")));
    /// assert!(p.parse("moo").is_err());
    /// ```
    pub fn followed_by<U>(self, p: Parser<U>) -> Parser<O> {
        let label = self.label.clone();

        Parser::new(
            move |input| match (*self.parse)(input) {
                Ok((out, rest)) => {
                    if (*p.parse)(rest).is_ok() {
                        Ok((out, rest))
                    } else {
                        Err((
                            Error::new(format!(
                                "expected `{}` to be followed by {}, got `{}`",
                                input, p.label, rest,
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
    pub fn try_map<U: 'static, S, F>(self, f: F) -> Parser<U>
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

    /// Expect the end of input.
    pub fn end(self) -> Parser<O> {
        self.skip(Parser::new(
            |input| {
                if !input.is_empty() {
                    Err((
                        format!("extraneous input found: {}", pretty(input)).into(),
                        input,
                    ))
                } else {
                    Ok(((), input))
                }
            },
            "<end>",
        ))
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
        U: FromStr<Err = E>,
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

/// Tries to apply the parser.  Outputs an `Option` with `None` if it failed to apply the parser
/// and no input was consumed, and `Some` if it succeeded. Outputs an error if some but not all
/// input was consumed.
pub fn optional<O: 'static>(p: impl Into<Parser<O>>) -> Parser<Option<O>> {
    let p = p.into();
    let label = format!("[{}]", p.label);

    Parser::new(
        move |input: &str| match (*p.parse)(input) {
            Ok((out, rest)) => Ok((Some(out), rest)),
            Err((_, rest)) if rest == input => Ok((None, input)),
            Err(err) => Err(err),
        },
        label,
    )
}

/// Apply the parser until the other parser succeeds.
///
/// ```
/// use memoir::*;
///
/// let p = until(symbol('!'));
/// let (out, rest) = p.parse("Hello World!").unwrap();
///
/// assert_eq!(out, String::from("Hello World"),);
/// assert_eq!(rest, "!");
///
/// assert!(p.parse("!").is_ok());
/// assert!(p.parse("Hello World").is_err());
/// ```
pub fn until<V>(p: Parser<V>) -> Parser<String> {
    let label = format!("(-{})*", p.label);

    Parser::new(
        move |mut input| {
            let mut chars = input.chars();
            let mut out = String::new();

            loop {
                if (*p.parse)(input).is_ok() {
                    return Ok((out, input));
                }

                if let Some(c) = chars.next() {
                    out.push(c);
                    input = &input[c.len_utf8()..];
                } else {
                    break;
                }
            }
            Err((Error::new("reached end of input"), input))
        },
        label,
    )
}

/// Succeeds when the input is empty.
///
/// ```
/// use memoir::{end, until};
///
/// end().parse("").is_ok();
/// end().parse("#").is_err();
///
/// let (out, rest) = until(end()).parse("Hello World!").unwrap();
/// assert_eq!(out, String::from("Hello World!"));
/// assert_eq!(rest, "");
/// ```
pub fn end() -> Parser<()> {
    Parser::new(
        |input| {
            if input.is_empty() {
                Ok(((), input))
            } else {
                Err((Error::expect("end of input", input), input))
            }
        },
        "<end>",
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
/// let p = choice([symbol('?'), symbol('!'), symbol('.')]);
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
pub fn choice<O>(choices: impl AsRef<[Parser<O>]> + 'static) -> Parser<O>
where
    O: 'static + Clone,
{
    let label = choices
        .as_ref()
        .iter()
        .map(|p| p.label.clone())
        .collect::<Vec<_>>()
        .join(" | ");
    let expected = label.clone();

    Parser::new(
        move |input| {
            for p in choices.as_ref().iter() {
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

/// Applies all the given parsers and picks the one which consumes the most input.
/// Doesn't consume any input on partial failure.
///
/// ```
/// use memoir::*;
///
/// let p = greediest([string("he"), string("hello")]);
///
/// assert_eq!(p.parse("hello").ok(), Some(("hello".to_owned(), "")));
/// assert_eq!(p.parse("he").ok(), Some(("he".to_owned(), "")));
/// ```
pub fn greediest<'a, O>(choices: impl AsRef<[Parser<O>]> + 'static) -> Parser<O>
where
    O: 'static + Clone,
{
    let label = choices
        .as_ref()
        .iter()
        .map(|p| p.label.clone())
        .collect::<Vec<_>>()
        .join(" | ");
    let expected = label.clone();

    Parser::new(
        move |input| {
            let mut greediest: Option<(O, &str)> = None;

            for p in choices.as_ref().iter() {
                match (*p.parse)(input) {
                    Ok((out, rest)) => match greediest {
                        Some((_, greediest_rest)) if rest.len() < greediest_rest.len() => {
                            greediest = Some((out, rest));
                        }
                        Some(_) => {}
                        None => {
                            greediest = Some((out, rest));
                        }
                    },
                    Err(_) => continue,
                }
            }
            if let Some(result) = greediest {
                Ok(result)
            } else {
                Err((Error::expect(&expected, input), input))
            }
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
pub fn keyword<O: FromStr + 'static>(s: &'static str) -> Parser<O> {
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
pub fn natural<O: FromStr<Err = ParseIntError>>() -> Parser<O> {
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
pub fn integer<O: FromStr<Err = ParseIntError>>() -> Parser<O> {
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
pub fn rational<O: FromStr<Err = ParseFloatError>>() -> Parser<O> {
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
/// let p = choice([
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

/// Silence a parser. Discard its output and return `()` instead.
pub fn hush<O>(p: Parser<O>) -> Parser<()> {
    p.value(())
}

/// Pretty print an input string.
pub fn pretty(s: &str) -> String {
    if s.chars().all(|c| c.is_whitespace()) {
        format!("`{}`", s)
    } else {
        s.to_owned()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_choice_backtracking() {
        let p = choice([
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
    fn test_choice_backtracking_skip() {
        let p = choice([
            string("leave").skip(whitespace()).skip(string("england")),
            string("leave/england"),
        ]);

        assert!(p.parse("leave england").is_ok());
        assert!(p.parse("leave/england").is_err());

        let p = choice([
            peek(string("leave").skip(whitespace())).skip(string("england")),
            string("leave/england"),
        ]);

        assert!(p.parse("leave england").is_ok());
        assert!(p.parse("leave/england").is_ok());
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

    #[test]
    fn test_greediest() {
        let p = greediest([
            natural::<u32>().value("<natural>"),
            rational::<f32>().value("<rational>"),
        ]);

        assert_eq!(p.parse("42").ok(), Some(("<natural>", "")));
        assert_eq!(p.parse("42.0").ok(), Some(("<rational>", "")));

        let p = choice([
            natural::<u32>().value("<natural>"),
            rational::<f32>().value("<rational>"),
        ]);

        assert_eq!(p.parse("42").ok(), Some(("<natural>", "")));
        assert_eq!(p.parse("42.0").ok(), Some(("<natural>", ".0")));

        let p = greediest([symbol('!').then(symbol('?')), symbol('!').then(symbol('.'))]);

        let (_, rest) = p.parse("!!").unwrap_err();
        assert_eq!(rest, "!!", "doesn't consume any input on failure");

        let p = choice([symbol('!').then(symbol('?')), symbol('!').then(symbol('.'))]);

        let (_, rest) = p.parse("!!").unwrap_err();
        assert_eq!(rest, "!", "consumes input on failure");
    }
}
