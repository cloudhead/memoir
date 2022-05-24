//! Operators.

use std::ops;

use crate::parsers::Parser;

impl<O> ops::Div for Parser<O> {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        self.or(rhs)
    }
}

impl<O, U> ops::Add<Parser<U>> for Parser<O> {
    type Output = Parser<(O, U)>;

    fn add(self, rhs: Parser<U>) -> Self::Output {
        self.then(rhs)
    }
}

impl<O, U: 'static, F> ops::Shr<F> for Parser<O>
where
    F: 'static + Fn(O) -> U,
{
    type Output = Parser<U>;

    fn shr(self, rhs: F) -> Self::Output {
        self.map(rhs)
    }
}
