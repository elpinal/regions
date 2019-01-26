//! The target language.

use super::*;

use std::collections::btree_set;
use std::collections::BTreeSet;
use std::collections::HashSet;
use std::iter::FromIterator;

use basis::Basis;

pub mod basis;

/// A region variable.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct RegVar(usize);

/// A typed region-annotated term.
pub enum RegExp {
    Var(Var),
    Inst(Var, InstList, RegVar),
    Abs(PType, Triple),
    App(Triple, Triple),
    LetRec(Scheme, RegVar, Triple, Triple),
    LetRegion(Basis, Triple),
}

/// A target triple.
pub struct Triple {
    e: Box<RegExp>,
    ty: Box<PType>,
    eff: Effect,
}

/// An effect variable.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct EffVar(usize);

/// An atomic effect.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum AtEff {
    Reg(RegVar),
    Eff(EffVar),
}

/// An effect
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct Effect(BTreeSet<AtEff>);

/// An arrow effect.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ArrEff {
    handle: EffVar,
    latent: Effect,
}

/// A type.
pub enum Type {
    Int,
    Var(TyVar),
    Arrow(Box<PType>, ArrEff, Box<PType>),
}

/// A type with a place.
pub struct PType {
    ty: Type,
    reg: RegVar,
}

/// A type scheme.
pub struct Scheme {
    types: usize,
    rvars: usize,
    evars: usize,
    body: Type,
}

/// An instantiation list.
pub struct InstList {
    types: Vec<Type>,
    rvars: Vec<RegVar>,
    arr_effs: Vec<ArrEff>,
}

/// Free region variables.
pub trait FRV<'a, Output: IntoIterator<Item = &'a RegVar> = HashSet<&'a RegVar>> {
    fn frv(&'a self) -> Output;
}

/// Free effect variables.
pub trait FEV<'a, Output: IntoIterator<Item = &'a EffVar> = HashSet<&'a EffVar>> {
    fn fev(&'a self) -> Output;
}

impl<'a> FRV<'a> for AtEff {
    fn frv(&self) -> HashSet<&RegVar> {
        match *self {
            AtEff::Reg(ref rv) => Some(rv).into_iter().collect(),
            AtEff::Eff(_) => Default::default(),
        }
    }
}

impl<'a> FEV<'a> for AtEff {
    fn fev(&self) -> HashSet<&EffVar> {
        match *self {
            AtEff::Reg(_) => Default::default(),
            AtEff::Eff(ref ev) => Some(ev).into_iter().collect(),
        }
    }
}

impl<'a> FRV<'a> for Effect {
    fn frv(&self) -> HashSet<&RegVar> {
        self.0.iter().map(|a| a.frv()).flatten().collect()
    }
}

impl<'a> FEV<'a> for Effect {
    fn fev(&self) -> HashSet<&EffVar> {
        self.0.iter().map(|a| a.fev()).flatten().collect()
    }
}

impl<'a> FRV<'a> for ArrEff {
    fn frv(&self) -> HashSet<&RegVar> {
        self.latent.frv()
    }
}

impl<'a> FEV<'a> for ArrEff {
    fn fev(&self) -> HashSet<&EffVar> {
        let mut s = self.latent.fev();
        s.insert(&self.handle);
        s
    }
}

impl<'a> FRV<'a> for PType {
    fn frv(&self) -> HashSet<&RegVar> {
        let mut s = self.ty.frv();
        s.insert(&self.reg);
        s
    }
}

impl<'a> FEV<'a> for PType {
    fn fev(&self) -> HashSet<&EffVar> {
        self.ty.fev()
    }
}

impl<'a> FRV<'a> for Type {
    fn frv(&self) -> HashSet<&RegVar> {
        use Type::*;
        match *self {
            Int | Var(_) => Default::default(),
            Arrow(ref pt1, ref ae, ref pt2) => {
                let mut s1 = pt1.frv();
                s1.extend(pt2.frv());
                s1.extend(ae.frv());
                s1
            }
        }
    }
}

impl<'a> FEV<'a> for Type {
    fn fev(&self) -> HashSet<&EffVar> {
        use Type::*;
        match *self {
            Int | Var(_) => Default::default(),
            Arrow(ref pt1, ref ae, ref pt2) => {
                let mut s1 = pt1.fev();
                s1.extend(pt2.fev());
                s1.extend(ae.fev());
                s1
            }
        }
    }
}

impl FromIterator<AtEff> for Effect {
    fn from_iter<I: IntoIterator<Item = AtEff>>(iter: I) -> Self {
        Effect(iter.into_iter().collect())
    }
}

impl<'a> IntoIterator for &'a Effect {
    type Item = &'a AtEff;
    type IntoIter = btree_set::Iter<'a, AtEff>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl<'a> From<&'a AtEff> for Option<&'a EffVar> {
    fn from(ae: &'a AtEff) -> Self {
        match *ae {
            AtEff::Eff(ref ev) => Some(ev),
            _ => None,
        }
    }
}

impl AtEff {
    fn reg(n: usize) -> Self {
        AtEff::Reg(RegVar(n))
    }

    fn eff(n: usize) -> Self {
        AtEff::Eff(EffVar(n))
    }
}

impl Effect {
    pub fn new() -> Self {
        Effect(BTreeSet::new())
    }

    fn iter(&self) -> btree_set::Iter<AtEff> {
        self.0.iter()
    }
}

impl ArrEff {
    fn new(handle: EffVar, latent: Effect) -> Self {
        ArrEff { handle, latent }
    }
}

#[cfg(test)]
mod tests {
    #![warn(dead_code)]

    use super::*;

    #[test]
    fn test_arrow_effect_equality() {
        assert_eq!(
            ArrEff::new(EffVar(0), Effect::new()),
            ArrEff::new(EffVar(0), Effect::new())
        );

        assert_eq!(
            ArrEff::new(EffVar(0), Effect::from_iter(vec![AtEff::reg(0)])),
            ArrEff::new(EffVar(0), Effect::from_iter(vec![AtEff::reg(0)]))
        );

        assert_eq!(
            ArrEff::new(
                EffVar(0),
                Effect::from_iter(vec![AtEff::reg(0), AtEff::eff(8)])
            ),
            ArrEff::new(
                EffVar(0),
                Effect::from_iter(vec![AtEff::eff(8), AtEff::reg(0)])
            )
        );

        assert_eq!(
            ArrEff::new(EffVar(0), Effect::from_iter(vec![AtEff::reg(0)])),
            ArrEff::new(
                EffVar(0),
                Effect::from_iter(vec![AtEff::reg(0), AtEff::reg(0)])
            )
        );

        assert_ne!(
            ArrEff::new(
                EffVar(0),
                Effect::from_iter(vec![AtEff::reg(0), AtEff::eff(8)])
            ),
            ArrEff::new(
                EffVar(0),
                Effect::from_iter(vec![AtEff::eff(0), AtEff::reg(0)])
            )
        );

        assert_ne!(
            ArrEff::new(EffVar(0), Effect::from_iter(vec![AtEff::reg(0)])),
            ArrEff::new(
                EffVar(0),
                Effect::from_iter(vec![AtEff::reg(0), AtEff::reg(1)])
            )
        );
    }
}
