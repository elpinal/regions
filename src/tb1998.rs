//! Tofte and Birkedal. TOPLAS 1998.
//! “A region inference algorithm.”

#![allow(dead_code)]

/// A program variable.
pub struct Var(usize);

/// A type variable.
pub struct TyVar(usize);

/// The source language.
pub mod ml {
    use super::*;

    /// A type.
    pub enum MLType {
        Int,
        Var(TyVar),
        Arrow(Box<MLType>, Box<MLType>),
    }

    /// A type scheme.
    pub struct MLTypeScheme {
        body: MLType,
    }

    /// An explicitly typed source expression.
    pub enum Exp {
        Inst(Var, Vec<MLType>),
        Abs(MLType, Box<Exp>),
        App(Box<Exp>, Box<Exp>),
        LetRec(MLTypeScheme, Box<Exp>, Box<Exp>),
    }

    struct MLTypeEnv(Vec<MLTypeScheme>);
}

/// The target language.
pub mod region {
    use super::*;

    use std::collections::BTreeSet;

    use basis::Basis;

    pub mod basis {
        //! An implementation of bases.

        use super::*;

        use std::collections::BTreeSet;
        use std::collections::HashSet;

        /// A basis.
        pub struct Basis {
            q: HashSet<RegVar>,
            e: BTreeSet<ArrEff>,
        }

        /// Free region variables.
        pub trait FRV<'a, Output: IntoIterator<Item = &'a RegVar> = HashSet<&'a RegVar>> {
            fn frv(&'a self) -> Output;
        }

        impl<'a> FRV<'a> for AtEff {
            fn frv(&'a self) -> HashSet<&'a RegVar> {
                match *self {
                    AtEff::Reg(ref rv) => Some(rv).into_iter().collect(),
                    AtEff::Eff(_) => Default::default(),
                }
            }
        }

        impl<'a> FRV<'a> for Effect {
            fn frv(&'a self) -> HashSet<&'a RegVar> {
                self.0.iter().map(|a| a.frv()).flatten().collect()
            }
        }

        impl<'a> FRV<'a> for ArrEff {
            fn frv(&'a self) -> HashSet<&'a RegVar> {
                self.latent.frv()
            }
        }

        impl<'a> FRV<'a> for PType {
            fn frv(&'a self) -> HashSet<&'a RegVar> {
                let mut s = self.ty.frv();
                s.insert(&self.reg);
                s
            }
        }

        impl<'a> FRV<'a> for Type {
            fn frv(&'a self) -> HashSet<&'a RegVar> {
                use Type::*;
                match *self {
                    Int => Default::default(),
                    Var(_) => Default::default(),
                    Arrow(ref pt1, ref ae, ref pt2) => {
                        let mut s1 = pt1.frv();
                        s1.extend(pt2.frv());
                        s1.extend(ae.frv());
                        s1
                    }
                }
            }
        }
    }

    /// A region variable.
    #[derive(Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
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
    #[derive(Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
    pub struct EffVar(usize);

    /// An atomic effect.
    #[derive(Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
    pub enum AtEff {
        Reg(RegVar),
        Eff(EffVar),
    }

    /// An effect
    #[derive(Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
    pub struct Effect(BTreeSet<AtEff>);

    /// An arrow effect.
    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
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

        fn from_vec(v: Vec<AtEff>) -> Self {
            Effect(v.into_iter().collect())
        }
    }

    impl ArrEff {
        fn new(handle: EffVar, latent: Effect) -> Self {
            ArrEff { handle, latent }
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_arrow_effect_equality() {
            assert_eq!(
                ArrEff::new(EffVar(0), Effect::new()),
                ArrEff::new(EffVar(0), Effect::new())
            );

            assert_eq!(
                ArrEff::new(EffVar(0), Effect::from_vec(vec![AtEff::reg(0)])),
                ArrEff::new(EffVar(0), Effect::from_vec(vec![AtEff::reg(0)]))
            );

            assert_eq!(
                ArrEff::new(
                    EffVar(0),
                    Effect::from_vec(vec![AtEff::reg(0), AtEff::eff(8)])
                ),
                ArrEff::new(
                    EffVar(0),
                    Effect::from_vec(vec![AtEff::eff(8), AtEff::reg(0)])
                )
            );

            assert_eq!(
                ArrEff::new(EffVar(0), Effect::from_vec(vec![AtEff::reg(0)])),
                ArrEff::new(
                    EffVar(0),
                    Effect::from_vec(vec![AtEff::reg(0), AtEff::reg(0)])
                )
            );

            assert_ne!(
                ArrEff::new(
                    EffVar(0),
                    Effect::from_vec(vec![AtEff::reg(0), AtEff::eff(8)])
                ),
                ArrEff::new(
                    EffVar(0),
                    Effect::from_vec(vec![AtEff::eff(0), AtEff::reg(0)])
                )
            );

            assert_ne!(
                ArrEff::new(EffVar(0), Effect::from_vec(vec![AtEff::reg(0)])),
                ArrEff::new(
                    EffVar(0),
                    Effect::from_vec(vec![AtEff::reg(0), AtEff::reg(1)])
                )
            );
        }
    }
}
