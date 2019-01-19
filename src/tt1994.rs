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
#[derive(Default)]
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

impl Place {
    fn shift(self, d: usize) -> Place {
        use Place::*;
        match self {
            Var(v) => Var(RVar(v.0 + d)),
            Name(_) => self,
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
        self.get(&addr.region)?.get(addr.offset)
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
    pub fn get(&self, offset: Offset) -> Result<&SValue> {
        self.0.get(offset.0).ok_or(RError::UnboundOffset { offset })
    }
}

impl Term {
    /// Creates an n-ary letregion-expression.
    pub fn letregion(n: usize, t: Term) -> Term {
        (0..n).fold(t, |t, _| Term::LetRegion(Box::new(t)))
    }

    fn var(n: usize) -> Term {
        Term::Var(Var(n))
    }

    fn abs(t: Term, p: Place) -> Term {
        Term::Abs(Box::new(t), p)
    }

    fn app(t1: Term, t2: Term) -> Term {
        Term::App(Box::new(t1), Box::new(t2))
    }

    fn let_(t1: Term, t2: Term) -> Term {
        Term::Let(Box::new(t1), Box::new(t2))
    }

    fn letrec(n: usize, p: Place, t1: Term, t2: Term) -> Term {
        Term::LetRec(n, p, Box::new(t1), Box::new(t2))
    }

    fn map<F>(self, f: &F, c: usize) -> Term
    where
        F: Fn(usize, Place) -> Place,
    {
        use Term::*;
        match self {
            Var(v) => Var(v),
            Abs(t, p) => Term::abs(t.map(f, c), f(c, p)),
            App(t1, t2) => Term::app(t1.map(f, c), t2.map(f, c)),
            Let(t1, t2) => Term::let_(t1.map(f, c), t2.map(f, c)),
            LetRec(n, p, t1, t2) => Term::letrec(n, f(c, p), t1.map(f, c + n), t2.map(f, c)),
            Inst(v, ps, p) => Inst(v, ps.into_iter().map(|p| f(c, p)).collect(), f(c, p)),
            LetRegion(t) => Term::letregion(1, t.map(f, c + 1)),
        }
    }

    pub fn shift_above(self, c: usize, d: isize) -> Term {
        use Place::*;
        let f = |c, p| match p {
            Name(_) => p,
            Var(ref v) => {
                if c <= v.0 {
                    Var(RVar((v.0 as isize + d) as usize))
                } else {
                    p
                }
            }
        };
        self.map(&f, c)
    }

    pub fn shift(self, d: isize) -> Term {
        self.shift_above(0, d)
    }

    pub fn subst(self, j: usize, q: Place) -> Term {
        use Place::*;
        let f = |c, p| match p {
            Name(_) => p,
            Var(ref v) => {
                if j + c == v.0 {
                    q.clone().shift(c)
                } else {
                    p
                }
            }
        };
        self.map(&f, 0)
    }

    pub fn subst_top(self, q: Place) -> Term {
        self.subst(0, q.shift(1)).shift(-1)
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

    macro_rules! shift_id {
        ($t:expr, $n:expr) => {
            assert_eq!($t.shift($n), $t)
        };
    }

    #[test]
    fn test_shift() {
        shift_id!(Term::Var(Var(0)), 0);
        shift_id!(Term::Var(Var(0)), 1);

        shift_id!(Term::abs(Term::Var(Var(0)), Place::Var(RVar(0))), 0);

        assert_eq!(
            Term::abs(Term::Var(Var(0)), Place::Var(RVar(0))).shift(1),
            Term::abs(Term::Var(Var(0)), Place::Var(RVar(1)))
        );

        assert_eq!(
            Term::abs(Term::Var(Var(3)), Place::Var(RVar(34))).shift(780),
            Term::abs(Term::Var(Var(3)), Place::Var(RVar(814)))
        );

        assert_eq!(
            Term::letregion(1, Term::abs(Term::Var(Var(2)), Place::Var(RVar(0)))).shift(29),
            Term::letregion(1, Term::abs(Term::Var(Var(2)), Place::Var(RVar(0))))
        );

        assert_eq!(
            Term::letregion(1, Term::abs(Term::Var(Var(2)), Place::Var(RVar(1)))).shift(29),
            Term::letregion(1, Term::abs(Term::Var(Var(2)), Place::Var(RVar(30))))
        );

        assert_eq!(
            Term::letregion(1, Term::abs(Term::Var(Var(2)), Place::Var(RVar(4)))).shift(68),
            Term::letregion(1, Term::abs(Term::Var(Var(2)), Place::Var(RVar(72))))
        );

        assert_eq!(
            Term::letrec(
                1,
                Place::Var(RVar(0)),
                Term::abs(Term::Var(Var(1)), Place::Var(RVar(0))),
                Term::abs(Term::Var(Var(1)), Place::Var(RVar(0)))
            )
            .shift(1),
            Term::letrec(
                1,
                Place::Var(RVar(1)),
                Term::abs(Term::Var(Var(1)), Place::Var(RVar(0))),
                Term::abs(Term::Var(Var(1)), Place::Var(RVar(1)))
            )
        );

        assert_eq!(
            Term::letrec(
                3,
                Place::Var(RVar(12)),
                Term::abs(Term::Var(Var(1024)), Place::Var(RVar(3))),
                Term::abs(Term::Var(Var(0)), Place::Var(RVar(32)))
            )
            .shift(9),
            Term::letrec(
                3,
                Place::Var(RVar(21)),
                Term::abs(Term::Var(Var(1024)), Place::Var(RVar(12))),
                Term::abs(Term::Var(Var(0)), Place::Var(RVar(41)))
            )
        );
    }
}
