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
#[derive(Debug, Default, PartialEq)]
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
#[derive(Debug, Default, PartialEq)]
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
#[derive(Clone, Debug, Default, PartialEq)]
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

    #[fail(display = "expected {}, but got {}", expect, got)]
    ArityMismatch { expect: usize, got: usize },

    #[fail(display = "not region name: {:?}", place)]
    NotRegionName { place: Place },

    #[fail(display = "not region closure: {:?}", closure)]
    NotRegionClosure { closure: Closure },

    #[fail(display = "not plain closure: {:?}", closure)]
    NotPlainClosure { closure: Closure },
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

impl TryFrom<Closure> for (usize, Term, VEnv) {
    type Error = RError;

    fn try_from(c: Closure) -> result::Result<Self, Self::Error> {
        match c {
            Closure::Region(n, t, env) => Ok((n, t, env)),
            _ => Err(RError::NotRegionClosure { closure: c }),
        }
    }
}

impl TryFrom<Closure> for (Term, VEnv) {
    type Error = RError;

    fn try_from(c: Closure) -> result::Result<Self, Self::Error> {
        match c {
            Closure::Plain(t, env) => Ok((t, env)),
            _ => Err(RError::NotPlainClosure { closure: c }),
        }
    }
}

impl Place {
    pub fn var(n: usize) -> Place {
        Place::Var(RVar(n))
    }

    pub fn name(n: usize) -> Place {
        Place::Name(RName(n))
    }

    fn shift(self, d: usize) -> Place {
        use Place::*;
        match self {
            Var(v) => Var(RVar(v.0 + d)),
            Name(_) => self,
        }
    }
}

impl TryFrom<Place> for RName {
    type Error = RError;

    fn try_from(p: Place) -> result::Result<Self, Self::Error> {
        match p {
            Place::Name(name) => Ok(name),
            _ => Err(RError::NotRegionName { place: p }),
        }
    }
}

impl Address {
    fn new(region: RName, offset: Offset) -> Address {
        Address { region, offset }
    }
}

impl VEnv {
    pub fn new() -> Self {
        VEnv(vec![])
    }

    fn insert(&mut self, addr: Address) {
        self.0.push(addr)
    }

    fn pop(&mut self) {
        self.0.pop().expect("VEnv::pop: expect non-empty");
    }

    pub fn get(&self, v: &Var) -> Result<&Address> {
        let l = self.0.len();
        l.checked_sub(v.0 + 1)
            .and_then(|n| self.0.get(n))
            .ok_or_else(|| RError::UnboundVariable { var: v.clone() })
    }

    pub fn get_letrec(&self, v: &FVar) -> Result<&Address> {
        let l = self.0.len();
        l.checked_sub(v.0 + 1)
            .and_then(|n| self.0.get(n))
            .ok_or_else(|| RError::UnboundLetrecVariable { var: v.clone() })
    }
}

type Value = Address;

impl Store {
    pub fn new() -> Store {
        Store(HashMap::new())
    }

    pub fn from_vec(v: Vec<(RName, Region)>) -> Self {
        Store(v.into_iter().collect())
    }

    fn new_offset(&self, name: &RName) -> Result<Offset> {
        Ok(self.get(name)?.new_offset())
    }

    pub fn get(&self, name: &RName) -> Result<&Region> {
        self.0
            .get(name)
            .ok_or_else(|| RError::UnboundRegionName { name: name.clone() })
    }

    pub fn lookup(&self, addr: &Address) -> Result<&SValue> {
        self.get(&addr.region)?.get(addr.offset)
    }

    fn put(&mut self, addr: Address, sv: SValue) {
        let offset = addr.offset;
        self.0.entry(addr.region).and_modify(|r| r.put(offset, sv));
    }

    pub fn reduce(&mut self, t: Term, env: &mut VEnv) -> Result<Value> {
        use Term::*;
        match t {
            Var(v) => Ok(env.get(&v)?.clone()),
            Inst(fv, ps, p) => {
                let addr = env.get_letrec(&fv)?;
                let sv = self.lookup(addr)?.clone();
                let name = RName::try_from(p)?;
                let (n, t, env) = Closure::try_from(sv)?.try_into()?;
                if ps.len() != n {
                    return Err(RError::ArityMismatch {
                        expect: n,
                        got: ps.len(),
                    });
                }
                let t = ps
                    .into_iter()
                    .enumerate()
                    .fold(t, |t, (i, p)| t.subst(i, p.shift(n)))
                    .shift(-(n as isize));
                let sv = SValue::Closure(Closure::Plain(t, env));
                let offset = self.new_offset(&name)?;
                let addr = Address::new(name, offset);
                self.put(addr.clone(), sv);
                Ok(addr)
            }
            Abs(t, p) => {
                let name = p.try_into()?;
                let offset = self.new_offset(&name)?;
                let addr = Address::new(name, offset);
                let sv = SValue::Closure(Closure::Plain(*t, env.clone()));
                self.put(addr.clone(), sv);
                Ok(addr)
            }
            App(t1, t2) => {
                let addr = self.reduce(*t1, env)?;
                let (t, mut env0) = Closure::try_from(self.lookup(&addr)?.clone())?.try_into()?;
                let v = self.reduce(*t2, env)?;
                env0.insert(v);
                self.reduce(t, &mut env0)
            }
            Let(t1, t2) => {
                let v = self.reduce(*t1, env)?;
                env.insert(v);
                let r = self.reduce(*t2, env);
                env.pop();
                r
            }
            _ => unimplemented!(),
        }
    }
}

impl Region {
    pub fn new() -> Self {
        Region(vec![])
    }

    fn new_offset(&self) -> Offset {
        Offset(self.0.len())
    }

    pub fn get(&self, offset: Offset) -> Result<&SValue> {
        self.0.get(offset.0).ok_or(RError::UnboundOffset { offset })
    }

    fn put(&mut self, offset: Offset, sv: SValue) {
        self.0.insert(offset.0, sv)
    }
}

impl Term {
    /// Creates an n-ary letregion-expression.
    pub fn letregion(n: usize, t: Term) -> Term {
        (0..n).fold(t, |t, _| Term::LetRegion(Box::new(t)))
    }

    pub fn var(n: usize) -> Term {
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

    macro_rules! subst_top_id {
        ($t:expr, $p:expr) => {
            assert_eq!($t.subst_top($p), $t)
        };
    }

    #[test]
    fn test_subst_top() {
        subst_top_id!(Term::var(0), Place::var(0));
        subst_top_id!(Term::var(1), Place::var(0));

        subst_top_id!(
            Term::abs(Term::var(1), Place::Name(RName(100))),
            Place::var(0)
        );
        subst_top_id!(
            Term::abs(Term::var(0), Place::Name(RName(100))),
            Place::var(1)
        );

        assert_eq!(
            Term::abs(Term::var(0), Place::var(0)).subst_top(Place::var(77)),
            Term::abs(Term::var(0), Place::var(77))
        );

        assert_eq!(
            Term::abs(Term::var(0), Place::var(1)).subst_top(Place::var(96)),
            Term::abs(Term::var(0), Place::var(0))
        );

        assert_eq!(
            Term::abs(Term::var(0), Place::var(8)).subst_top(Place::var(96)),
            Term::abs(Term::var(0), Place::var(7))
        );

        subst_top_id!(
            Term::letregion(1, Term::abs(Term::var(0), Place::var(0))),
            Place::var(44)
        );

        assert_eq!(
            Term::letregion(1, Term::abs(Term::var(0), Place::var(1))).subst_top(Place::var(44)),
            Term::letregion(1, Term::abs(Term::var(0), Place::var(45)))
        );

        subst_top_id!(
            Term::letregion(2, Term::abs(Term::var(0), Place::var(1))),
            Place::var(44)
        );

        assert_eq!(
            Term::letregion(6, Term::abs(Term::var(0), Place::var(7))).subst_top(Place::var(408)),
            Term::letregion(6, Term::abs(Term::var(0), Place::var(6)))
        );

        assert_eq!(
            Term::letregion(6, Term::abs(Term::var(0), Place::var(8))).subst_top(Place::var(408)),
            Term::letregion(6, Term::abs(Term::var(0), Place::var(7)))
        );

        assert_eq!(
            Term::letregion(6, Term::abs(Term::var(0), Place::var(20))).subst_top(Place::var(408)),
            Term::letregion(6, Term::abs(Term::var(0), Place::var(19)))
        );

        assert_eq!(
            Term::letregion(6, Term::abs(Term::var(0), Place::var(6))).subst_top(Place::var(408)),
            Term::letregion(6, Term::abs(Term::var(0), Place::var(414)))
        );

        assert_eq!(
            Term::letrec(
                0,
                Place::var(0),
                Term::abs(Term::var(0), Place::var(0)),
                Term::abs(Term::var(0), Place::var(0))
            )
            .subst_top(Place::var(28)),
            Term::letrec(
                0,
                Place::var(28),
                Term::abs(Term::var(0), Place::var(28)),
                Term::abs(Term::var(0), Place::var(28))
            )
        );

        assert_eq!(
            Term::letrec(
                1,
                Place::var(0),
                Term::abs(Term::var(0), Place::var(0)),
                Term::abs(Term::var(0), Place::var(0))
            )
            .subst_top(Place::var(28)),
            Term::letrec(
                1,
                Place::var(28),
                Term::abs(Term::var(0), Place::var(0)),
                Term::abs(Term::var(0), Place::var(28))
            )
        );

        assert_eq!(
            Term::letrec(
                1,
                Place::var(0),
                Term::letrec(
                    1,
                    Place::var(0),
                    Term::abs(Term::var(0), Place::var(0)),
                    Term::abs(Term::var(0), Place::var(0)),
                ),
                Term::abs(Term::var(0), Place::var(0))
            )
            .subst_top(Place::var(28)),
            Term::letrec(
                1,
                Place::var(28),
                Term::letrec(
                    1,
                    Place::var(0),
                    Term::abs(Term::var(0), Place::var(0)),
                    Term::abs(Term::var(0), Place::var(0)),
                ),
                Term::abs(Term::var(0), Place::var(28))
            )
        );
    }

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

    macro_rules! assert_reduce_store_err {
        ($s:expr, $t:expr, $v:expr, $e:expr) => {{
            let mut s = $s;
            assert_eq!(s.reduce($t, &mut VEnv($v)), Err($e))
        }};
    }

    macro_rules! assert_reduce_store_ok {
        ($s:expr, $t:expr, $v:expr, $a:expr, $sr:expr) => {{
            let mut s = $s;
            assert_eq!(s.reduce($t, &mut VEnv($v)), Ok($a));
            assert_eq!(s, $sr);
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

        assert_reduce_ok!(
            Term::Var(Var(0)),
            vec![
                Address::new(RName(0), Offset(0)),
                Address::new(RName(11), Offset(9)),
            ],
            Address::new(RName(11), Offset(9))
        );

        assert_reduce_err!(
            Term::Inst(FVar(0), vec![], Place::var(0)),
            vec![],
            RError::UnboundLetrecVariable { var: FVar(0) }
        );

        assert_reduce_err!(
            Term::Inst(FVar(0), vec![], Place::var(0)),
            vec![Address::new(RName(0), Offset(0))],
            RError::UnboundRegionName { name: RName(0) }
        );

        assert_reduce_store_err!(
            Store::from_vec(vec![(RName(0), Region(vec![]))]),
            Term::Inst(FVar(0), vec![], Place::var(0)),
            vec![Address::new(RName(0), Offset(0))],
            RError::UnboundOffset { offset: Offset(0) }
        );

        assert_reduce_store_err!(
            Store::from_vec(vec![(RName(0), Region(vec![SValue::Int(55)]))]),
            Term::Inst(FVar(0), vec![], Place::var(0)),
            vec![Address::new(RName(0), Offset(0))],
            RError::NotRegionName {
                place: Place::var(0)
            }
        );

        assert_reduce_store_err!(
            Store::from_vec(vec![(RName(0), Region(vec![SValue::Int(55)]))]),
            Term::Inst(FVar(0), vec![], Place::name(0)),
            vec![Address::new(RName(0), Offset(0))],
            RError::NotClosure {
                value: SValue::Int(55)
            }
        );

        assert_reduce_store_err!(
            Store::from_vec(vec![(
                RName(0),
                Region(vec![SValue::Closure(Closure::Plain(
                    Term::var(0),
                    VEnv::new(),
                ))]),
            )]),
            Term::Inst(FVar(0), vec![], Place::name(0)),
            vec![Address::new(RName(0), Offset(0))],
            RError::NotRegionClosure {
                closure: Closure::Plain(Term::var(0), VEnv::new())
            }
        );

        assert_reduce_store_err!(
            Store::from_vec(vec![(
                RName(0),
                Region(vec![SValue::Closure(Closure::Region(
                    1,
                    Term::var(0),
                    VEnv::new(),
                ))]),
            )]),
            Term::Inst(FVar(0), vec![], Place::name(0)),
            vec![Address::new(RName(0), Offset(0))],
            RError::ArityMismatch { expect: 1, got: 0 }
        );

        assert_reduce_store_ok!(
            Store::from_vec(vec![(
                RName(0),
                Region(vec![SValue::Closure(Closure::Region(
                    0,
                    Term::var(0),
                    VEnv::new(),
                ))]),
            )]),
            Term::Inst(FVar(0), vec![], Place::name(0)),
            vec![Address::new(RName(0), Offset(0))],
            Address::new(RName(0), Offset(1)),
            Store::from_vec(vec![(
                RName(0),
                Region(vec![
                    SValue::Closure(Closure::Region(0, Term::var(0), VEnv::new())),
                    SValue::Closure(Closure::Plain(Term::var(0), VEnv::new()))
                ])
            )])
        );

        assert_reduce_store_ok!(
            Store::from_vec(vec![(
                RName(0),
                Region(vec![SValue::Closure(Closure::Region(
                    1,
                    Term::var(0),
                    VEnv::new(),
                ))]),
            )]),
            Term::Inst(FVar(0), vec![Place::var(73)], Place::name(0)),
            vec![Address::new(RName(0), Offset(0))],
            Address::new(RName(0), Offset(1)),
            Store::from_vec(vec![(
                RName(0),
                Region(vec![
                    SValue::Closure(Closure::Region(1, Term::var(0), VEnv::new())),
                    SValue::Closure(Closure::Plain(Term::var(0), VEnv::new()))
                ])
            )])
        );

        assert_reduce_store_ok!(
            Store::from_vec(vec![(
                RName(0),
                Region(vec![SValue::Closure(Closure::Region(
                    2,
                    Term::abs(Term::abs(Term::var(0), Place::var(1)), Place::var(0)),
                    VEnv::new(),
                ))]),
            )]),
            Term::Inst(
                FVar(0),
                vec![Place::var(73), Place::name(686)],
                Place::name(0)
            ),
            vec![Address::new(RName(0), Offset(0))],
            Address::new(RName(0), Offset(1)),
            Store::from_vec(vec![(
                RName(0),
                Region(vec![
                    SValue::Closure(Closure::Region(
                        2,
                        Term::abs(Term::abs(Term::var(0), Place::var(1)), Place::var(0)),
                        VEnv::new(),
                    )),
                    SValue::Closure(Closure::Plain(
                        Term::abs(Term::abs(Term::var(0), Place::name(686)), Place::var(73)),
                        VEnv::new(),
                    ))
                ])
            )])
        );

        assert_reduce_err!(
            Term::abs(Term::var(0), Place::var(0)),
            vec![],
            RError::NotRegionName {
                place: Place::var(0)
            }
        );

        assert_reduce_err!(
            Term::abs(Term::var(0), Place::name(0)),
            vec![],
            RError::UnboundRegionName { name: RName(0) }
        );

        assert_reduce_store_ok!(
            Store::from_vec(vec![(RName(0), Region::new())]),
            Term::abs(Term::var(0), Place::name(0)),
            vec![],
            Address::new(RName(0), Offset(0)),
            Store::from_vec(vec![(
                RName(0),
                Region(vec![SValue::Closure(Closure::Plain(
                    Term::var(0),
                    VEnv::new()
                ))])
            )])
        );

        assert_reduce_store_ok!(
            Store::from_vec(vec![(RName(0), Region(vec![SValue::Int(4004)]))]),
            Term::abs(Term::var(0), Place::name(0)),
            vec![],
            Address::new(RName(0), Offset(1)),
            Store::from_vec(vec![(
                RName(0),
                Region(vec![
                    SValue::Int(4004),
                    SValue::Closure(Closure::Plain(Term::var(0), VEnv::new()))
                ])
            )])
        );

        assert_reduce_store_ok!(
            Store::from_vec(vec![(RName(0), Region(vec![SValue::Int(4004)]))]),
            Term::app(Term::abs(Term::var(0), Place::name(0)), Term::var(0)),
            vec![Address::new(RName(39), Offset(24))],
            Address::new(RName(39), Offset(24)),
            Store::from_vec(vec![(
                RName(0),
                Region(vec![
                    SValue::Int(4004),
                    SValue::Closure(Closure::Plain(
                        Term::var(0),
                        VEnv(vec![Address::new(RName(39), Offset(24))])
                    ))
                ])
            )])
        );

        assert_reduce_store_ok!(
            Store::from_vec(vec![(RName(0), Region(vec![SValue::Int(4004)]))]),
            Term::let_(Term::abs(Term::var(0), Place::name(0)), Term::var(0)),
            vec![],
            Address::new(RName(0), Offset(1)),
            Store::from_vec(vec![(
                RName(0),
                Region(vec![
                    SValue::Int(4004),
                    SValue::Closure(Closure::Plain(Term::var(0), VEnv(vec![])))
                ])
            )])
        );
    }
}
