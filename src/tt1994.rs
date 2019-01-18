//! Tofte and Talpin. POPL 1994.
//! “Implementation of the typed call-by-value λ-calculus using a stack of regions.”

use std::collections::HashMap;
use std::convert::{TryFrom, TryInto};
use std::fmt;
use std::result;

use failure::Fail;

/// A region variable.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RVar(usize);

/// A region name.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct RName(usize);

impl fmt::Display for RName {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "region name<{}>", self.0)
    }
}

/// A store.
pub struct Store(HashMap<RName, Region>);

/// A place, either a region variable or a region name.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Place {
    Var(RVar),
    Name(RName),
}

/// An ordinary variable.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Var(usize);

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "var<{}>", self.0)
    }
}

/// A letrec variable.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FVar(usize);

impl fmt::Display for FVar {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "letrec var<{}>", self.0)
    }
}

/// A term.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    /// A variable.
    Var(Var),

    /// A lambda abstraction.
    Abs(Box<Term>, Place),

    /// An application of a function.
    App(Box<Term>, Box<Term>),

    /// A let-expression.
    Let(Box<Term>, Box<Term>),

    /// A letrec-expression.
    LetRec(usize, Place, Box<Term>, Box<Term>),

    /// An instantiation.
    Inst(FVar, Vec<Place>, Place),

    /// A letregion-expression.
    LetRegion(Box<Term>),
}

/// A region.
pub struct Region(Vec<SValue>);

/// A storable value.
#[derive(Clone, Debug, PartialEq)]
pub enum SValue {
    Int(isize),
    Closure(Closure),
}

/// A closure, either a plain closure or a region closure.
#[derive(Clone, Debug, PartialEq)]
pub enum Closure {
    Plain(Term, VEnv),
    Region(usize, Term, VEnv),
}

/// A variable environment.
#[derive(Clone, Debug, PartialEq)]
pub struct VEnv(Vec<Address>);

/// An address.
#[derive(Clone, Debug, PartialEq)]
pub struct Address {
    region: RName,
    offset: Offset,
}

/// A region offset.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Offset(usize);

impl fmt::Display for Offset {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// An error.
#[derive(Debug, Fail, PartialEq)]
pub enum RError {
    #[fail(display = "unbound region name: {}", name)]
    UnboundRegionName { name: RName },

    #[fail(display = "unbound offset: {}", offset)]
    UnboundOffset { offset: Offset },

    #[fail(display = "unbound variable: {}", var)]
    UnboundVariable { var: Var },

    #[fail(display = "unbound letrec variable: {}", var)]
    UnboundLetrecVariable { var: FVar },

    #[fail(display = "not closure: {:?}", value)]
    NotClosure { value: SValue },
}

type Result<T> = result::Result<T, RError>;

impl TryFrom<SValue> for Closure {
    type Error = RError;

    fn try_from(sv: SValue) -> result::Result<Self, Self::Error> {
        match sv {
            SValue::Closure(c) => Ok(c),
            _ => Err(RError::NotClosure { value: sv }),
        }
    }
}

impl Address {
    fn new(region: RName, offset: Offset) -> Address {
        Address { region, offset }
    }
}

impl VEnv {
    pub fn get(&self, v: &Var) -> Result<&Address> {
        self.0
            .get(v.0)
            .ok_or_else(|| RError::UnboundVariable { var: v.clone() })
    }

    pub fn get_letrec(&self, v: &FVar) -> Result<&Address> {
        self.0
            .get(v.0)
            .ok_or_else(|| RError::UnboundLetrecVariable { var: v.clone() })
    }
}

type Value = Address;

impl Store {
    pub fn new() -> Store {
        Store(HashMap::new())
    }

    pub fn get(&self, name: &RName) -> Result<&Region> {
        self.0
            .get(name)
            .ok_or_else(|| RError::UnboundRegionName { name: name.clone() })
    }

    pub fn lookup(&self, addr: &Address) -> Result<&SValue> {
        self.get(&addr.region)?.get(&addr.offset)
    }

    pub fn reduce(&mut self, t: Term, env: &mut VEnv) -> Result<Value> {
        use Term::*;
        match t {
            Var(v) => Ok(env.get(&v)?.clone()),
            _ => unimplemented!(),
        }
    }
}

impl Region {
    pub fn get(&self, offset: &Offset) -> Result<&SValue> {
        self.0
            .get(offset.0)
            .ok_or(RError::UnboundOffset { offset: *offset })
    }
}

impl Term {
    /// Creates an n-ary letregion-expression.
    pub fn letregion(n: usize, t: Term) -> Term {
        (0..n).fold(t, |t, _| Term::LetRegion(Box::new(t)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! assert_reduce_err {
        ($t:expr, $v:expr, $e:expr) => {{
            let mut s = Store::new();
            assert_eq!(s.reduce($t, &mut VEnv($v)), Err($e))
        }};
    }

    macro_rules! assert_reduce_ok {
        ($t:expr, $v:expr, $a:expr) => {{
            let mut s = Store::new();
            assert_eq!(s.reduce($t, &mut VEnv($v)), Ok($a))
        }};
    }

    #[test]
    fn test_reduce() {
        assert_reduce_err!(
            Term::Var(Var(0)),
            vec![],
            RError::UnboundVariable { var: Var(0) }
        );

        assert_reduce_ok!(
            Term::Var(Var(0)),
            vec![Address::new(RName(0), Offset(0))],
            Address::new(RName(0), Offset(0))
        );
    }
}
