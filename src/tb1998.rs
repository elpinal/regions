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
    use std::collections::HashSet;
    use std::iter::FromIterator;

    use basis::Basis;

    pub mod basis {
        //! An implementation of bases.

        use super::*;

        use std::collections::BTreeSet;
        use std::collections::{HashMap, HashSet};

        use failure::Fail;

        /// A set of arrow effects.
        #[derive(Default)]
        pub struct ArrEffSet(BTreeSet<ArrEff>);

        /// A basis.
        #[derive(Default)]
        pub struct Basis {
            q: HashSet<RegVar>,
            e: ArrEffSet,
        }

        impl<'a> FRV<'a> for ArrEffSet {
            fn frv(&self) -> HashSet<&RegVar> {
                self.0.iter().map(|ae| ae.frv()).flatten().collect()
            }
        }

        impl<'a> FEV<'a> for ArrEffSet {
            fn fev(&self) -> HashSet<&EffVar> {
                self.0.iter().map(|ae| ae.fev()).flatten().collect()
            }
        }

        impl<'a> FRV<'a> for Basis {
            fn frv(&self) -> HashSet<&RegVar> {
                let mut s = self.e.frv();
                s.extend(&self.q);
                s
            }
        }

        impl<'a> FEV<'a> for Basis {
            fn fev(&self) -> HashSet<&EffVar> {
                self.e.fev()
            }
        }

        /// Detects a not *functional* set of arrow effects.
        #[derive(Fail, Debug)]
        #[fail(display = "not functional: duplicate effect variable: {:?}", duplicate)]
        pub struct NotFunctionalError {
            duplicate: EffVar,
        }

        impl ArrEffSet {
            /// Gets the effect map of a *functional* set of arrow effects.
            pub fn get_effect_map(&self) -> Result<HashMap<&EffVar, &Effect>, NotFunctionalError> {
                let mut m = HashMap::new();
                for ae in self.0.iter() {
                    if m.insert(&ae.handle, &ae.latent).is_some() {
                        return Err(NotFunctionalError {
                            duplicate: ae.handle.clone(),
                        });
                    }
                }
                Ok(m)
            }
        }

        impl Basis {
            fn new<Q, E>(q: Q, e: E) -> Self
            where
                Q: IntoIterator<Item = RegVar>,
                E: IntoIterator<Item = ArrEff>,
            {
                Basis {
                    q: q.into_iter().collect(),
                    e: ArrEffSet(e.into_iter().collect()),
                }
            }

            fn fresh_reg_var(&self) -> RegVar {
                let rvs = self.frv();
                if !rvs.is_empty() {
                    let len = rvs.len();
                    for i in 0..=len {
                        if !rvs.contains(&RegVar(i)) {
                            return RegVar(i);
                        }
                    }
                }
                RegVar(0)
            }

            fn fresh_eff_var(&self) -> EffVar {
                let evs = self.fev();
                if !evs.is_empty() {
                    let len = evs.len();
                    for i in 0..=len {
                        if !evs.contains(&EffVar(i)) {
                            return EffVar(i);
                        }
                    }
                }
                EffVar(0)
            }
        }

        #[cfg(test)]
        mod tests {
            use super::*;

            #[test]
            fn basis_frv() {
                assert_eq!(Basis::default().frv(), HashSet::new());

                assert_eq!(
                    Basis::new(vec![RegVar(0)], None).frv(),
                    vec![&RegVar(0)].into_iter().collect()
                );

                assert_eq!(
                    Basis::new(vec![RegVar(0)], vec![ArrEff::new(EffVar(0), Effect::new())]).frv(),
                    vec![&RegVar(0)].into_iter().collect()
                );

                assert_eq!(
                    Basis::new(
                        vec![RegVar(0)],
                        vec![ArrEff::new(
                            EffVar(0),
                            Effect::from_iter(vec![AtEff::reg(3)])
                        )]
                    )
                    .frv(),
                    vec![&RegVar(0), &RegVar(3)].into_iter().collect()
                );
            }

            #[test]
            fn fresh_reg_var() {
                assert_eq!(Basis::default().fresh_reg_var(), RegVar(0));
                assert_eq!(Basis::new(vec![RegVar(0)], None).fresh_reg_var(), RegVar(1));
                assert_eq!(Basis::new(vec![RegVar(1)], None).fresh_reg_var(), RegVar(0));
                assert_eq!(
                    Basis::new(vec![RegVar(0), RegVar(1)], None).fresh_reg_var(),
                    RegVar(2)
                );
                assert_eq!(
                    Basis::new(vec![RegVar(0), RegVar(1), RegVar(2)], None).fresh_reg_var(),
                    RegVar(3)
                );
                assert_eq!(
                    Basis::new(vec![RegVar(0), RegVar(1), RegVar(3)], None).fresh_reg_var(),
                    RegVar(2)
                );

                assert_eq!(
                    Basis::new(
                        vec![RegVar(0), RegVar(1), RegVar(3)],
                        vec![ArrEff::new(
                            EffVar(4),
                            Effect::from_iter(vec![AtEff::reg(2)])
                        )]
                    )
                    .fresh_reg_var(),
                    RegVar(4)
                );

                assert_eq!(
                    Basis::new(
                        vec![RegVar(0), RegVar(4), RegVar(3)],
                        vec![ArrEff::new(
                            EffVar(4),
                            Effect::from_iter(vec![AtEff::reg(2)])
                        )]
                    )
                    .fresh_reg_var(),
                    RegVar(1)
                );
            }

            #[test]
            fn fresh_eff_var() {
                assert_eq!(Basis::default().fresh_eff_var(), EffVar(0));
                assert_eq!(Basis::new(vec![RegVar(0)], None).fresh_eff_var(), EffVar(0));
                assert_eq!(Basis::new(vec![RegVar(1)], None).fresh_eff_var(), EffVar(0));
                assert_eq!(
                    Basis::new(vec![RegVar(0), RegVar(1)], None).fresh_eff_var(),
                    EffVar(0)
                );
                assert_eq!(
                    Basis::new(None, vec![ArrEff::new(EffVar(0), Effect::new())]).fresh_eff_var(),
                    EffVar(1)
                );

                assert_eq!(
                    Basis::new(
                        vec![RegVar(0)],
                        vec![ArrEff::new(
                            EffVar(0),
                            Effect::from_iter(vec![
                                AtEff::eff(1),
                                AtEff::eff(2),
                                AtEff::eff(3),
                                AtEff::reg(4),
                                AtEff::reg(5),
                                AtEff::eff(6),
                            ])
                        )]
                    )
                    .fresh_eff_var(),
                    EffVar(4)
                );

                assert_eq!(
                    Basis::new(
                        vec![RegVar(0)],
                        vec![ArrEff::new(
                            EffVar(1),
                            Effect::from_iter(vec![
                                AtEff::eff(1),
                                AtEff::eff(3),
                                AtEff::reg(4),
                                AtEff::eff(6),
                            ])
                        )]
                    )
                    .fresh_eff_var(),
                    EffVar(0)
                );

                assert_eq!(
                    Basis::new(
                        vec![RegVar(0), RegVar(4)],
                        vec![ArrEff::new(
                            EffVar(1),
                            Effect::from_iter(vec![
                                AtEff::eff(1),
                                AtEff::eff(3),
                                AtEff::reg(2),
                                AtEff::eff(6),
                                AtEff::eff(0),
                            ])
                        )]
                    )
                    .fresh_eff_var(),
                    EffVar(2)
                );
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
    #[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
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
}
