use memoir::parsers::Parser;
use memoir::prelude::*;

#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    Bool(bool),
    U32(u32),
    U32Tuple(u32, u32),
    F64(f64),
    F64Tuple(f64, f64),
    Str(String),
    Ident(String),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Command {
    Edit(Vec<String>),
    EditFrames(Vec<String>),
    ForceQuit,
    ForceQuitAll,
    Quit,
    QuitAll,
    Set(String, Value),
    WriteFrames(Option<String>),
    Write(Option<String>),
    WriteQuit,
}

pub fn identifier<'a>() -> impl Parser<'a, Output = String> + Clone {
    many::<_, String>(satisfy(
        |c: char| {
            (c.is_ascii_alphabetic()
                || c.is_ascii_digit()
                || [':', '/', '_', '+', '-', '!', '?'].contains(&c))
        },
        "<identifier>",
    ))
}

pub fn command<'a>(cmd: &'static str) -> impl Parser<'a, Output = String> {
    string(cmd).skip(whitespace())
}

pub fn value<'a>() -> impl Parser<'a, Output = Value> {
    let uint = many::<_, String>(digit()).from_str::<u32>();
    let float = many::<_, String>(digit().or('.').or('-')).from_str::<f64>();

    let str_val = quoted().map(|s| Value::Str(s));
    let u32_tuple_val = uint
        .clone()
        .skip(whitespace())
        .then(uint.clone())
        .map(|(x, y)| Value::U32Tuple(x, y));
    let u32_val = uint.clone().map(|u| Value::U32(u));
    let f64_tuple_val = float
        .clone()
        .skip(whitespace())
        .then(float.clone())
        .map(|(x, y)| Value::F64Tuple(x, y));
    let f64_val = float.map(|f| Value::F64(f));
    let bool_val = string("on")
        .map(|_| true)
        .or(string("off").map(|_| false))
        .map(|b| Value::Bool(b));
    let ident_val = identifier().map(|id| Value::Ident(id));

    str_val
        .or(f64_tuple_val)
        .or(u32_tuple_val)
        .or(f64_val)
        .or(u32_val)
        .or(bool_val)
        .or(ident_val)
}

pub fn quoted<'a>() -> impl Parser<'a, Output = String> {
    between('"', '"', any(character()).until('"'))
}

fn main() {
    let quit = command("q").map(|_| Command::Quit);
    let quit_all = command("qa").map(|_| Command::QuitAll);
    let force_quit = command("q!").map(|_| Command::ForceQuit);
    let force_quit_all = command("qa!").map(|_| Command::ForceQuitAll);
    let set = command("set")
        .then(identifier())
        .skip(optional(whitespace()))
        .then(optional(
            symbol('=').skip(optional(whitespace())).then(value()),
        ))
        .map(|((_, k), v): ((_, String), _)| match v {
            Some((_, v)) => Command::Set(k.to_owned(), v),
            None => Command::Set(k.to_owned(), Value::Bool(true)),
        });

    let parser = quit.or(quit_all).or(force_quit).or(force_quit_all).or(set);

    assert_eq!(
        parser.parse("set key = value"),
        Ok((
            Command::Set(String::from("key"), Value::Ident(String::from("value"))),
            ""
        ))
    );

    assert_eq!(
        parser.parse("set key"),
        Ok((Command::Set(String::from("key"), Value::Bool(true)), ""))
    );
}
