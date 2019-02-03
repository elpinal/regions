//! The target language.

use super::*;
use crate::tb1998::ml::MLType;

use std::collections::btree_set;
use std::collections::BTreeSet;
use std::collections::HashSet;
use std::iter::FromIterator;

use failure::Fail;

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
#[derive(Clone)]
pub enum Type {
    Int,
    Var(TyVar),
    Arrow(Box<PType>, ArrEff, Box<PType>),
}

/// A type with a place.
#[derive(Clone)]
pub struct PType {
    ty: Type,
    reg: RegVar,
}

/// A type scheme.
pub struct Scheme {
    tvars: usize,
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

/// Free type variables.
pub trait FTV<'a, Output: IntoIterator<Item = &'a TyVar> = HashSet<&'a TyVar>> {
    fn ftv(&'a self) -> Output;
}

/// Free region variables.
pub trait FRV<'a, Output: IntoIterator<Item = &'a RegVar> = HashSet<&'a RegVar>> {
    fn frv(&'a self) -> Output;
}

/// Free effect variables.
pub trait FEV<'a, Output: IntoIterator<Item = &'a EffVar> = HashSet<&'a EffVar>> {
    fn fev(&'a self) -> Output;
}

/// Primary free region variables.
pub trait PFRV<'a, Output: IntoIterator<Item = &'a RegVar> = HashSet<&'a RegVar>> {
    fn pfrv(&'a self) -> Output;
}

/// Primary free effect variables.
pub trait PFEV<'a, Output: IntoIterator<Item = &'a EffVar> = HashSet<&'a EffVar>> {
    fn pfev(&'a self) -> Output;
}

/// Secondary free region variables.
pub trait SFRV<'a, Output: IntoIterator<Item = &'a RegVar> = HashSet<&'a RegVar>> {
    fn sfrv(&'a self) -> Output;
}

/// Secondary free effect variables.
pub trait SFEV<'a, Output: IntoIterator<Item = &'a EffVar> = HashSet<&'a EffVar>> {
    fn sfev(&'a self) -> Output;
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

impl<'a> FTV<'a> for PType {
    fn ftv(&self) -> HashSet<&TyVar> {
        self.ty.ftv()
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

impl<'a> PFRV<'a> for PType {
    fn pfrv(&self) -> HashSet<&RegVar> {
        let mut s = self.ty.pfrv();
        s.insert(&self.reg);
        s
    }
}

impl<'a> PFEV<'a> for PType {
    fn pfev(&self) -> HashSet<&EffVar> {
        self.ty.pfev()
    }
}

impl<'a> FTV<'a> for Type {
    fn ftv(&self) -> HashSet<&TyVar> {
        use Type::*;
        match *self {
            Int => Default::default(),
            Var(ref tv) => HashSet::from_iter(Some(tv)),
            Arrow(ref pt1, _, ref pt2) => {
                let mut s1 = pt1.ftv();
                s1.extend(pt2.ftv());
                s1
            }
        }
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

impl<'a> PFRV<'a> for Type {
    fn pfrv(&self) -> HashSet<&RegVar> {
        use Type::*;
        match *self {
            Int | Var(_) => Default::default(),
            Arrow(ref pt1, _, ref pt2) => {
                let mut s1 = pt1.pfrv();
                s1.extend(pt2.pfrv());
                s1
            }
        }
    }
}

impl<'a> PFEV<'a> for Type {
    fn pfev(&self) -> HashSet<&EffVar> {
        use Type::*;
        match *self {
            Int | Var(_) => Default::default(),
            Arrow(ref pt1, ref ae, ref pt2) => {
                let mut s1 = pt1.pfev();
                s1.extend(pt2.pfev());
                s1.insert(&ae.handle);
                s1
            }
        }
    }
}

impl<'a> FTV<'a> for Scheme {
    fn ftv(&self) -> HashSet<&TyVar> {
        let s = self.body.ftv();
        s.into_iter().filter(|&tv| tv.0 >= self.tvars).collect()
    }
}

impl<'a, T: FRV<'a> + PFRV<'a>> SFRV<'a> for T {
    fn sfrv(&'a self) -> HashSet<&RegVar> {
        self.frv().difference(&self.pfrv()).cloned().collect()
    }
}

impl<'a, T: FEV<'a> + PFEV<'a>> SFEV<'a> for T {
    fn sfev(&'a self) -> HashSet<&EffVar> {
        self.fev().difference(&self.pfev()).cloned().collect()
    }
}

trait ArrowEffects {
    fn arrow_effects(&self) -> BTreeSet<&ArrEff>;
}

impl ArrowEffects for PType {
    fn arrow_effects(&self) -> BTreeSet<&ArrEff> {
        self.ty.arrow_effects()
    }
}

impl ArrowEffects for Type {
    fn arrow_effects(&self) -> BTreeSet<&ArrEff> {
        use Type::*;
        match *self {
            Int | Var(_) => Default::default(),
            Arrow(ref pt1, ref ae, ref pt2) => {
                let mut s = pt1.arrow_effects();
                s.extend(pt2.arrow_effects());
                s.insert(ae);
                s
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

impl From<Type> for MLType {
    fn from(ty: Type) -> Self {
        use Type::*;
        match ty {
            Int => MLType::Int,
            Var(v) => MLType::Var(v),
            Arrow(pt1, _, pt2) => MLType::arrow((*pt1).into(), (*pt2).into()),
        }
    }
}

impl From<PType> for MLType {
    fn from(pt: PType) -> Self {
        MLType::from(pt.ty)
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

impl Type {
    pub fn arrow(pt1: PType, ae: ArrEff, pt2: PType) -> Self {
        Type::Arrow(Box::new(pt1), ae, Box::new(pt2))
    }
}

#[derive(Debug, Fail, PartialEq)]
pub enum StructuralError {
    #[fail(display = "not structural quantification missing {:?}", _0)]
    Region(RegVar),

    #[fail(display = "not structural quantification missing {:?}", _0)]
    Effect(EffVar),

    #[fail(display = "not structural quantification missing {:?}", _0)]
    Type(TyVar),
}

impl Scheme {
    fn has_structural_quantification(&self) -> Result<(), StructuralError> {
        let rvs = self.body.pfrv();
        for i in 0..self.rvars {
            if !rvs.contains(&RegVar(i)) {
                return Err(StructuralError::Region(RegVar(i)));
            }
        }

        let evs = self.body.pfev();
        for i in 0..self.evars {
            if !evs.contains(&EffVar(i)) {
                return Err(StructuralError::Effect(EffVar(i)));
            }
        }

        let tvs = self.body.ftv();
        for i in 0..self.tvars {
            if !tvs.contains(&TyVar(i)) {
                return Err(StructuralError::Type(TyVar(i)));
            }
        }

        Ok(())
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

    #[test]
    fn structural_quantification() {
        assert_eq!(
            Scheme {
                tvars: 0,
                rvars: 0,
                evars: 0,
                body: Type::Int,
            }
            .has_structural_quantification(),
            Ok(())
        );

        assert_eq!(
            Scheme {
                tvars: 0,
                rvars: 0,
                evars: 1,
                body: Type::Int,
            }
            .has_structural_quantification(),
            Err(StructuralError::Effect(EffVar(0)))
        );

        assert_eq!(
            Scheme {
                tvars: 0,
                rvars: 0,
                evars: 1,
                body: Type::arrow(
                    PType {
                        ty: Type::Int,
                        reg: RegVar(0),
                    },
                    ArrEff::new(EffVar(0), Effect::default()),
                    PType {
                        ty: Type::Int,
                        reg: RegVar(0),
                    }
                ),
            }
            .has_structural_quantification(),
            Ok(())
        );

        assert_eq!(
            Scheme {
                tvars: 0,
                rvars: 1,
                evars: 2,
                body: Type::arrow(
                    PType {
                        ty: Type::Int,
                        reg: RegVar(0),
                    },
                    ArrEff::new(EffVar(0), Effect::from_iter(vec![AtEff::eff(1)])),
                    PType {
                        ty: Type::Int,
                        reg: RegVar(0),
                    }
                ),
            }
            .has_structural_quantification(),
            Err(StructuralError::Effect(EffVar(1)))
        );

        assert_eq!(
            Scheme {
                tvars: 0,
                rvars: 1,
                evars: 2,
                body: Type::arrow(
                    PType {
                        ty: Type::Int,
                        reg: RegVar(0),
                    },
                    ArrEff::new(EffVar(0), Effect::from_iter(vec![AtEff::eff(1)])),
                    PType {
                        ty: Type::arrow(
                            PType {
                                ty: Type::Int,
                                reg: RegVar(1011),
                            },
                            ArrEff::new(EffVar(1), Effect::default()),
                            PType {
                                ty: Type::Int,
                                reg: RegVar(1032),
                            }
                        ),
                        reg: RegVar(0),
                    }
                ),
            }
            .has_structural_quantification(),
            Ok(())
        );
    }
}
