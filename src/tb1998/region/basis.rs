//! An implementation of bases.

use super::*;

use std::collections::BTreeSet;
use std::collections::{HashMap, HashSet};

use failure;
use failure::Fail;

/// A set of arrow effects.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct ArrEffSet(BTreeSet<ArrEff>);

/// A basis.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Basis {
    q: HashSet<RegVar>,
    e: ArrEffSet,
}

trait Consistent {
    type Error;

    fn is_consistent(&self, basis: &Basis) -> Result<(), Self::Error>;
}

#[derive(Debug, Fail, PartialEq)]
enum ConsistenceError {
    #[fail(display = "inconsistence basis")]
    InconsistentBasis,

    #[fail(display = "unbound region variable: {:?}", _0)]
    UnboundRegionVariable(RegVar),

    #[fail(display = "unbound region variables")]
    UnboundRegionVariables,

    #[fail(display = "unbound effect variable: {:?}", _0)]
    UnboundEffectVariable(EffVar),

    #[fail(display = "unbound arrow effect: {:?}", _0)]
    UnboundArrowEffect(ArrEff),

    #[fail(display = "missing effects which {:?} denotes", _0)]
    MissingDenotation(EffVar),
}

impl Consistent for RegVar {
    type Error = ConsistenceError;

    fn is_consistent(&self, basis: &Basis) -> Result<(), Self::Error> {
        if !basis.is_consistent() {
            return Err(ConsistenceError::InconsistentBasis);
        }
        if basis.q.contains(self) {
            return Ok(());
        }
        Err(ConsistenceError::UnboundRegionVariable(self.clone()))
    }
}

impl Consistent for ArrEff {
    type Error = ConsistenceError;

    fn is_consistent(&self, basis: &Basis) -> Result<(), Self::Error> {
        if !basis.is_consistent() {
            return Err(ConsistenceError::InconsistentBasis);
        }
        if basis.e.0.contains(self) {
            return Ok(());
        }
        Err(ConsistenceError::UnboundArrowEffect(self.clone()))
    }
}

impl Consistent for PType {
    type Error = ConsistenceError;

    fn is_consistent(&self, basis: &Basis) -> Result<(), Self::Error> {
        self.ty.is_consistent(basis)?;
        self.reg.is_consistent(basis)?;
        Ok(())
    }
}

impl Consistent for Type {
    type Error = ConsistenceError;

    fn is_consistent(&self, basis: &Basis) -> Result<(), Self::Error> {
        use Type::*;
        match *self {
            Int | Var(_) => {
                if !basis.is_consistent() {
                    return Err(ConsistenceError::InconsistentBasis);
                }
            }
            Arrow(ref pt1, ref ae, ref pt2) => {
                pt1.is_consistent(basis)?;
                ae.is_consistent(basis)?;
                pt2.is_consistent(basis)?;
            }
        }
        Ok(())
    }
}

impl Consistent for Effect {
    type Error = failure::Error;

    fn is_consistent(&self, basis: &Basis) -> Result<(), Self::Error> {
        if !basis.is_consistent() {
            Err(ConsistenceError::InconsistentBasis)?;
        }
        if !self.frv().is_subset(&basis.q.iter().collect()) {
            Err(ConsistenceError::UnboundRegionVariables)?;
        }
        let map = basis.e.get_effect_map()?;
        for ev in self.iter().filter_map(Option::<&EffVar>::from) {
            if let Some(eff) = map.get(ev) {
                if !eff.0.is_subset(&self.0) {
                    Err(ConsistenceError::MissingDenotation(ev.clone()))?;
                }
            } else {
                Err(ConsistenceError::UnboundEffectVariable(ev.clone()))?;
            }
        }
        Ok(())
    }
}

impl FromIterator<ArrEff> for ArrEffSet {
    fn from_iter<I: IntoIterator<Item = ArrEff>>(iter: I) -> Self {
        ArrEffSet(BTreeSet::from_iter(iter))
    }
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
    /// Creates an empty set of arrow effects.
    pub fn new() -> Self {
        ArrEffSet(BTreeSet::new())
    }

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

    fn get(&self, ev: &EffVar) -> BTreeSet<&AtEff> {
        self.0
            .iter()
            .filter_map(|ae| {
                if &ae.handle == ev {
                    Some(&ae.latent)
                } else {
                    None
                }
            })
            .flatten()
            .collect()
    }

    fn is_functional(&self) -> bool {
        self.get_effect_map().is_ok()
    }

    fn is_closed(&self) -> bool {
        for ae in self.0.iter() {
            for eff in ae.latent.iter() {
                if let AtEff::Eff(ref ev) = *eff {
                    if !self.0.iter().any(|ae| &ae.handle == ev) {
                        return false;
                    }
                }
            }
        }
        true
    }

    fn is_transitive(&self) -> bool {
        for ae in self.0.iter() {
            let evs = ae.latent.iter().map(Option::from).flatten();
            for ev in evs {
                if !self.get(ev).is_subset(&ae.latent.0.iter().collect()) {
                    return false;
                }
            }
        }
        true
    }

    fn is_consistent(&self) -> bool {
        self.is_functional() && self.is_closed() && self.is_transitive()
    }

    /// Gets the domain of a *functional* set of arrow effects.
    ///
    /// # Panics
    ///
    /// Panics if not *functional*.
    fn domain(&self) -> HashSet<&EffVar> {
        self.get_effect_map()
            .unwrap()
            .into_iter()
            .map(|x| x.0)
            .collect()
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

    fn is_consistent(&self) -> bool {
        self.e.frv().is_subset(&self.q.iter().collect()) && self.e.is_consistent()
    }

    /// Gets the domain of a basis whose set of arrow effects is *functional*.
    ///
    /// # Panics
    ///
    /// Panics if not *functional*.
    fn domain(&self) -> (HashSet<&RegVar>, HashSet<&EffVar>) {
        (self.q.iter().collect(), self.e.domain())
    }

    fn union(&self, another: &Basis) -> Basis {
        Basis {
            q: self.q.union(&another.q).cloned().collect(),
            e: ArrEffSet(self.e.0.union(&another.e.0).cloned().collect()),
        }
    }

    fn disjoint_union(&self, another: &Basis) -> Option<Basis> {
        let u = self.union(another);
        if u.is_consistent()
            && self.q.is_disjoint(&another.q)
            && self.e.domain().is_disjoint(&another.e.domain())
        {
            return Some(u);
        }
        None
    }

    fn observe(&self, e: Effect) -> Effect {
        let rvs = self.frv();
        let evs = self.fev();
        Effect(
            e.0.into_iter()
                .filter(|ae| match ae {
                    AtEff::Reg(rv) => rvs.contains(&rv),
                    AtEff::Eff(ev) => evs.contains(&ev),
                })
                .collect(),
        )
    }

    fn is_subset(&self, another: &Self) -> bool {
        self.q.is_subset(&another.q) && self.e.0.is_subset(&another.e.0)
    }
}

#[cfg(test)]
mod tests {
    #![warn(dead_code)]

    use super::*;

    use quickcheck::quickcheck;
    use quickcheck::Arbitrary;
    use quickcheck::Gen;

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

    #[test]
    fn is_functional() {
        assert!(ArrEffSet::default().is_functional());

        assert!(
            ArrEffSet::from_iter(vec![ArrEff::new(EffVar(0), Effect::default())]).is_functional()
        );

        assert!(ArrEffSet::from_iter(vec![
            ArrEff::new(EffVar(0), Effect::default()),
            ArrEff::new(EffVar(0), Effect::default())
        ])
        .is_functional());

        assert!(!ArrEffSet::from_iter(vec![
            ArrEff::new(EffVar(0), Effect::default()),
            ArrEff::new(EffVar(0), Effect::from_iter(vec![AtEff::reg(0)]))
        ])
        .is_functional());

        assert!(ArrEffSet::from_iter(vec![
            ArrEff::new(EffVar(0), Effect::default()),
            ArrEff::new(EffVar(1), Effect::from_iter(vec![AtEff::reg(0)]))
        ])
        .is_functional());

        assert!(ArrEffSet::from_iter(vec![
            ArrEff::new(EffVar(6), Effect::from_iter(vec![AtEff::reg(0)])),
            ArrEff::new(EffVar(2), Effect::from_iter(vec![AtEff::reg(0)]))
        ])
        .is_functional());
    }

    #[test]
    fn is_closed() {
        assert!(ArrEffSet::default().is_closed());

        assert!(ArrEffSet::from_iter(vec![ArrEff::new(EffVar(0), Effect::default())]).is_closed());

        assert!(ArrEffSet::from_iter(vec![ArrEff::new(
            EffVar(0),
            Effect::from_iter(vec![AtEff::reg(0)])
        )])
        .is_closed());

        assert!(ArrEffSet::from_iter(vec![ArrEff::new(
            EffVar(0),
            Effect::from_iter(vec![AtEff::eff(0)])
        )])
        .is_closed());

        assert!(!ArrEffSet::from_iter(vec![ArrEff::new(
            EffVar(0),
            Effect::from_iter(vec![AtEff::eff(1)])
        )])
        .is_closed());

        assert!(ArrEffSet::from_iter(vec![
            ArrEff::new(EffVar(0), Effect::from_iter(vec![AtEff::eff(1)])),
            ArrEff::new(EffVar(1), Effect::new())
        ])
        .is_closed());

        assert!(!ArrEffSet::from_iter(vec![
            ArrEff::new(EffVar(0), Effect::from_iter(vec![AtEff::eff(1)])),
            ArrEff::new(EffVar(2), Effect::new())
        ])
        .is_closed());

        assert!(!ArrEffSet::from_iter(vec![
            ArrEff::new(EffVar(0), Effect::from_iter(vec![AtEff::eff(1)])),
            ArrEff::new(EffVar(0), Effect::from_iter(vec![AtEff::eff(2)])),
            ArrEff::new(EffVar(2), Effect::new())
        ])
        .is_closed());

        assert!(ArrEffSet::from_iter(vec![
            ArrEff::new(EffVar(0), Effect::from_iter(vec![AtEff::eff(1)])),
            ArrEff::new(EffVar(1), Effect::from_iter(vec![AtEff::eff(2)])),
            ArrEff::new(EffVar(2), Effect::new())
        ])
        .is_closed());

        assert!(ArrEffSet::from_iter(vec![
            ArrEff::new(
                EffVar(0),
                Effect::from_iter(vec![AtEff::eff(1), AtEff::reg(2), AtEff::eff(5)])
            ),
            ArrEff::new(EffVar(1), Effect::from_iter(vec![AtEff::eff(5)])),
            ArrEff::new(EffVar(5), Effect::new())
        ])
        .is_closed());

        assert!(ArrEffSet::from_iter(vec![
            ArrEff::new(
                EffVar(0),
                Effect::from_iter(vec![AtEff::eff(1), AtEff::reg(2), AtEff::eff(5)])
            ),
            ArrEff::new(EffVar(1), Effect::from_iter(vec![AtEff::eff(5)])),
            ArrEff::new(EffVar(5), Effect::from_iter(vec![AtEff::eff(7)])),
            ArrEff::new(EffVar(5), Effect::from_iter(vec![AtEff::eff(6)])),
            ArrEff::new(EffVar(6), Effect::from_iter(vec![AtEff::eff(1)])),
            ArrEff::new(EffVar(7), Effect::from_iter(vec![AtEff::eff(0)]))
        ])
        .is_closed());

        assert!(!ArrEffSet::from_iter(vec![
            ArrEff::new(
                EffVar(0),
                Effect::from_iter(vec![AtEff::eff(1), AtEff::reg(2), AtEff::eff(5)])
            ),
            ArrEff::new(EffVar(1), Effect::from_iter(vec![AtEff::eff(5)])),
            ArrEff::new(EffVar(5), Effect::from_iter(vec![AtEff::eff(7)])),
            ArrEff::new(EffVar(5), Effect::from_iter(vec![AtEff::eff(6)])),
            ArrEff::new(EffVar(6), Effect::from_iter(vec![AtEff::eff(3)])),
            ArrEff::new(EffVar(7), Effect::from_iter(vec![AtEff::eff(0)]))
        ])
        .is_closed());
    }

    #[test]
    fn arr_eff_set_get() {
        assert_eq!(ArrEffSet::default().get(&EffVar(0)), BTreeSet::new());

        assert_eq!(
            ArrEffSet::from_iter(vec![ArrEff::new(EffVar(0), Effect::new())]).get(&EffVar(0)),
            BTreeSet::new()
        );

        assert_eq!(
            ArrEffSet::from_iter(vec![ArrEff::new(
                EffVar(0),
                Effect::from_iter(vec![AtEff::eff(1)])
            )])
            .get(&EffVar(0)),
            BTreeSet::from_iter(vec![&AtEff::eff(1)])
        );

        assert_eq!(
            ArrEffSet::from_iter(vec![
                ArrEff::new(EffVar(0), Effect::from_iter(vec![AtEff::eff(1)])),
                ArrEff::new(EffVar(0), Effect::from_iter(vec![AtEff::eff(2)])),
                ArrEff::new(EffVar(1), Effect::from_iter(vec![AtEff::eff(3)])),
            ])
            .get(&EffVar(0)),
            BTreeSet::from_iter(vec![&AtEff::eff(1), &AtEff::eff(2)])
        );
    }

    #[test]
    fn is_transitive() {
        assert!(ArrEffSet::default().is_transitive());

        assert!(
            ArrEffSet::from_iter(vec![ArrEff::new(EffVar(0), Effect::default())]).is_transitive()
        );

        assert!(ArrEffSet::from_iter(vec![ArrEff::new(
            EffVar(0),
            Effect::from_iter(vec![AtEff::eff(0)])
        )])
        .is_transitive());

        assert!(ArrEffSet::from_iter(vec![ArrEff::new(
            EffVar(0),
            Effect::from_iter(vec![AtEff::eff(0), AtEff::eff(1)])
        )])
        .is_transitive());

        assert!(!ArrEffSet::from_iter(vec![
            ArrEff::new(EffVar(0), Effect::from_iter(vec![AtEff::eff(0)])),
            ArrEff::new(
                EffVar(0),
                Effect::from_iter(vec![AtEff::eff(0), AtEff::eff(1)])
            )
        ])
        .is_transitive());

        assert!(ArrEffSet::from_iter(vec![
            ArrEff::new(
                EffVar(0),
                Effect::from_iter(vec![AtEff::eff(1), AtEff::eff(0)])
            ),
            ArrEff::new(
                EffVar(1),
                Effect::from_iter(vec![AtEff::eff(0), AtEff::eff(1)])
            )
        ])
        .is_transitive());

        assert!(ArrEffSet::from_iter(vec![
            ArrEff::new(EffVar(0), Effect::from_iter(vec![AtEff::eff(1)])),
            ArrEff::new(EffVar(1), Effect::from_iter(vec![AtEff::eff(1)]))
        ])
        .is_transitive());

        assert!(!ArrEffSet::from_iter(vec![
            ArrEff::new(EffVar(0), Effect::from_iter(vec![AtEff::eff(1)])),
            ArrEff::new(EffVar(1), Effect::from_iter(vec![AtEff::eff(2)])),
            ArrEff::new(EffVar(2), Effect::from_iter(vec![AtEff::eff(3)])),
        ])
        .is_transitive());

        assert!(!ArrEffSet::from_iter(vec![
            ArrEff::new(
                EffVar(0),
                Effect::from_iter(vec![AtEff::eff(1), AtEff::eff(2), AtEff::eff(3)])
            ),
            ArrEff::new(EffVar(1), Effect::from_iter(vec![AtEff::eff(2)])),
            ArrEff::new(EffVar(2), Effect::from_iter(vec![AtEff::eff(3)])),
        ])
        .is_transitive());

        assert!(ArrEffSet::from_iter(vec![
            ArrEff::new(
                EffVar(0),
                Effect::from_iter(vec![AtEff::eff(1), AtEff::eff(2), AtEff::eff(3)])
            ),
            ArrEff::new(
                EffVar(1),
                Effect::from_iter(vec![AtEff::eff(2), AtEff::eff(3)])
            ),
            ArrEff::new(EffVar(2), Effect::from_iter(vec![AtEff::eff(3)])),
        ])
        .is_transitive());

        assert!(!ArrEffSet::from_iter(vec![
            ArrEff::new(
                EffVar(0),
                Effect::from_iter(vec![AtEff::eff(1), AtEff::eff(2), AtEff::eff(3)])
            ),
            ArrEff::new(
                EffVar(1),
                Effect::from_iter(vec![AtEff::eff(2), AtEff::eff(3)])
            ),
            ArrEff::new(
                EffVar(2),
                Effect::from_iter(vec![AtEff::eff(3), AtEff::reg(88)])
            ),
        ])
        .is_transitive());

        assert!(ArrEffSet::from_iter(vec![
            ArrEff::new(
                EffVar(0),
                Effect::from_iter(vec![
                    AtEff::eff(1),
                    AtEff::eff(2),
                    AtEff::eff(3),
                    AtEff::reg(88),
                ])
            ),
            ArrEff::new(
                EffVar(1),
                Effect::from_iter(vec![AtEff::eff(2), AtEff::eff(3), AtEff::reg(88)])
            ),
            ArrEff::new(
                EffVar(2),
                Effect::from_iter(vec![AtEff::eff(3), AtEff::reg(88)])
            ),
        ])
        .is_transitive());

        assert!(!ArrEffSet::from_iter(vec![
            ArrEff::new(
                EffVar(0),
                Effect::from_iter(vec![
                    AtEff::eff(1),
                    AtEff::eff(2),
                    AtEff::eff(9),
                    AtEff::reg(88),
                    AtEff::reg(48),
                    AtEff::reg(3),
                ])
            ),
            ArrEff::new(
                EffVar(1),
                Effect::from_iter(vec![
                    AtEff::eff(2),
                    AtEff::eff(3),
                    AtEff::reg(1006),
                    AtEff::reg(88),
                ])
            ),
            ArrEff::new(
                EffVar(2),
                Effect::from_iter(vec![AtEff::eff(3), AtEff::reg(88)])
            ),
        ])
        .is_transitive());

        assert!(ArrEffSet::from_iter(vec![
            ArrEff::new(
                EffVar(0),
                Effect::from_iter(vec![
                    AtEff::eff(1),
                    AtEff::reg(1006),
                    AtEff::eff(2),
                    AtEff::eff(9),
                    AtEff::reg(88),
                    AtEff::reg(48),
                    AtEff::eff(3),
                    AtEff::reg(3),
                ])
            ),
            ArrEff::new(
                EffVar(1),
                Effect::from_iter(vec![
                    AtEff::eff(2),
                    AtEff::eff(3),
                    AtEff::reg(1006),
                    AtEff::reg(88),
                ])
            ),
            ArrEff::new(
                EffVar(2),
                Effect::from_iter(vec![AtEff::eff(3), AtEff::reg(88)])
            ),
        ])
        .is_transitive());
    }

    #[test]
    fn union_closed() {
        assert!(!Basis::new(
            vec![RegVar(0)],
            vec![ArrEff::new(
                EffVar(0),
                Effect::from_iter(vec![AtEff::reg(88), AtEff::eff(999), AtEff::eff(1)])
            )]
        )
        .union(&Basis::new(
            vec![RegVar(88)],
            vec![ArrEff::new(
                EffVar(1),
                Effect::from_iter(vec![AtEff::reg(88), AtEff::eff(1)])
            )]
        ))
        .e
        .is_closed());

        assert!(Basis::new(
            vec![RegVar(0)],
            vec![ArrEff::new(
                EffVar(0),
                Effect::from_iter(vec![AtEff::reg(88), AtEff::eff(999), AtEff::eff(1)])
            )]
        )
        .union(&Basis::new(
            vec![RegVar(88)],
            vec![
                ArrEff::new(
                    EffVar(1),
                    Effect::from_iter(vec![AtEff::reg(88), AtEff::eff(1)])
                ),
                ArrEff::new(EffVar(999), Effect::default()),
            ]
        ))
        .e
        .is_closed());
    }

    impl Arbitrary for RegVar {
        fn arbitrary<G: Gen>(g: &mut G) -> Self {
            RegVar(usize::arbitrary(g))
        }

        fn shrink(&self) -> Box<Iterator<Item = Self>> {
            Box::new(self.0.shrink().map(RegVar))
        }
    }

    impl Arbitrary for EffVar {
        fn arbitrary<G: Gen>(g: &mut G) -> Self {
            EffVar(usize::arbitrary(g))
        }

        fn shrink(&self) -> Box<Iterator<Item = Self>> {
            Box::new(self.0.shrink().map(EffVar))
        }
    }

    impl Arbitrary for AtEff {
        fn arbitrary<G: Gen>(g: &mut G) -> Self {
            use rand::Rng;
            if g.gen() {
                AtEff::eff(Arbitrary::arbitrary(g))
            } else {
                AtEff::reg(Arbitrary::arbitrary(g))
            }
        }

        fn shrink(&self) -> Box<Iterator<Item = Self>> {
            use AtEff::*;
            match *self {
                Eff(ref x) => Box::new(x.shrink().map(Eff)),
                Reg(ref x) => Box::new(x.shrink().map(Reg)),
            }
        }
    }

    impl Arbitrary for Effect {
        fn arbitrary<G: Gen>(g: &mut G) -> Self {
            Effect(Arbitrary::arbitrary(g))
        }

        fn shrink(&self) -> Box<Iterator<Item = Self>> {
            Box::new(self.0.shrink().map(Effect))
        }
    }

    impl Arbitrary for ArrEff {
        fn arbitrary<G: Gen>(g: &mut G) -> Self {
            ArrEff {
                handle: Arbitrary::arbitrary(g),
                latent: Arbitrary::arbitrary(g),
            }
        }

        fn shrink(&self) -> Box<Iterator<Item = Self>> {
            Box::new(
                (self.handle.clone(), self.latent.clone())
                    .shrink()
                    .map(|(handle, latent)| ArrEff { handle, latent }),
            )
        }
    }

    impl Arbitrary for ArrEffSet {
        fn arbitrary<G: Gen>(g: &mut G) -> Self {
            ArrEffSet(Arbitrary::arbitrary(g))
        }

        fn shrink(&self) -> Box<Iterator<Item = Self>> {
            Box::new(self.0.shrink().map(ArrEffSet))
        }
    }

    impl Arbitrary for Basis {
        fn arbitrary<G: Gen>(g: &mut G) -> Self {
            Basis {
                q: Arbitrary::arbitrary(g),
                e: Arbitrary::arbitrary(g),
            }
        }

        fn shrink(&self) -> Box<Iterator<Item = Self>> {
            Box::new(
                (self.q.clone(), self.e.clone())
                    .shrink()
                    .map(|(q, e)| Basis { q, e }),
            )
        }
    }

    quickcheck! {
        fn prop_disjoint_union_right_empty(b: Basis) -> bool {
            b.disjoint_union(&Basis::default()).map_or(true, |b0| b0 == b)
        }
    }

    #[test]
    fn disjoint_union() {
        assert_eq!(
            Basis::default().disjoint_union(&Basis::default()),
            Some(Basis::default())
        );

        assert_eq!(
            Basis::new(vec![RegVar(0)], None).disjoint_union(&Basis::default()),
            Some(Basis::new(vec![RegVar(0)], None))
        );

        assert_eq!(
            Basis::new(
                None,
                vec![ArrEff::new(
                    EffVar(0),
                    Effect::from_iter(vec![AtEff::Eff(EffVar(1))])
                )]
            )
            .disjoint_union(&Basis::default()),
            None
        );

        assert_eq!(
            Basis::new(
                None,
                vec![ArrEff::new(
                    EffVar(0),
                    Effect::from_iter(vec![AtEff::Eff(EffVar(1))])
                )]
            )
            .disjoint_union(&Basis::new(
                None,
                vec![ArrEff::new(
                    EffVar(0),
                    Effect::from_iter(vec![AtEff::Eff(EffVar(1))])
                )]
            )),
            None
        );

        assert_eq!(
            Basis::new(
                None,
                vec![ArrEff::new(
                    EffVar(0),
                    Effect::from_iter(vec![AtEff::Eff(EffVar(1))])
                )]
            )
            .disjoint_union(&Basis::new(
                None,
                vec![ArrEff::new(
                    EffVar(1),
                    Effect::from_iter(vec![AtEff::Eff(EffVar(1))])
                )]
            )),
            Some(Basis::new(
                None,
                vec![
                    ArrEff::new(EffVar(0), Effect::from_iter(vec![AtEff::Eff(EffVar(1))])),
                    ArrEff::new(EffVar(1), Effect::from_iter(vec![AtEff::Eff(EffVar(1))])),
                ]
            ))
        );

        assert_eq!(
            Basis::new(
                vec![RegVar(0)],
                vec![ArrEff::new(
                    EffVar(0),
                    Effect::from_iter(vec![AtEff::reg(88), AtEff::eff(999), AtEff::eff(1)])
                )]
            )
            .disjoint_union(&Basis::new(
                vec![RegVar(88)],
                vec![
                    ArrEff::new(
                        EffVar(1),
                        Effect::from_iter(vec![AtEff::reg(88), AtEff::eff(1)])
                    ),
                    ArrEff::new(EffVar(999), Effect::default()),
                ]
            )),
            Some(Basis::new(
                vec![RegVar(0), RegVar(88)],
                vec![
                    ArrEff::new(
                        EffVar(0),
                        Effect::from_iter(vec![
                            AtEff::reg(88),
                            AtEff::eff(999),
                            AtEff::Eff(EffVar(1))
                        ])
                    ),
                    ArrEff::new(
                        EffVar(1),
                        Effect::from_iter(vec![AtEff::reg(88), AtEff::Eff(EffVar(1))])
                    ),
                    ArrEff::new(EffVar(999), Effect::default()),
                ]
            ))
        );
    }

    quickcheck! {
        fn prop_observe_empty(e: Effect) -> bool {
            Basis::default().observe(e) == Effect::default()
        }
    }

    #[test]
    fn observe() {
        assert_eq!(
            Basis::default().observe(Effect::default()),
            Effect::default()
        );

        assert_eq!(
            Basis::new(vec![RegVar(0)], None).observe(Effect::default()),
            Effect::default()
        );

        assert_eq!(
            Basis::new(vec![RegVar(0)], None).observe(Effect::from_iter(vec![AtEff::reg(0)])),
            Effect::from_iter(vec![AtEff::reg(0)])
        );

        assert_eq!(
            Basis::new(vec![RegVar(0)], None).observe(Effect::from_iter(vec![AtEff::reg(1)])),
            Effect::default()
        );

        assert_eq!(
            Basis::new(
                vec![RegVar(0)],
                vec![ArrEff::new(EffVar(0), Effect::default())]
            )
            .observe(Effect::from_iter(vec![
                AtEff::eff(0),
                AtEff::eff(1),
                AtEff::reg(0),
            ])),
            Effect::from_iter(vec![AtEff::eff(0), AtEff::reg(0)])
        );

        assert_eq!(
            Basis::new(
                vec![RegVar(0)],
                vec![ArrEff::new(
                    EffVar(0),
                    Effect::from_iter(vec![
                        AtEff::reg(0),
                        AtEff::reg(1),
                        AtEff::eff(1),
                        AtEff::eff(2),
                    ])
                )]
            )
            .observe(Effect::from_iter(vec![
                AtEff::eff(0),
                AtEff::eff(1),
                AtEff::reg(0),
                AtEff::reg(1),
                AtEff::reg(2),
                AtEff::eff(2),
                AtEff::eff(3),
            ])),
            Effect::from_iter(vec![
                AtEff::eff(0),
                AtEff::eff(1),
                AtEff::reg(0),
                AtEff::reg(1),
                AtEff::eff(2),
            ])
        );
    }

    #[test]
    fn consistency() {
        assert_eq!(
            RegVar(0).is_consistent(&Basis::default()),
            Err(ConsistenceError::UnboundRegionVariable(RegVar(0)))
        );

        assert!(RegVar(0)
            .is_consistent(&Basis::new(vec![RegVar(0)], None))
            .is_ok());

        assert_eq!(
            RegVar(1).is_consistent(&Basis::new(vec![RegVar(0)], None)),
            Err(ConsistenceError::UnboundRegionVariable(RegVar(1)))
        );

        assert_eq!(
            ArrEff::new(EffVar(0), Effect::default()).is_consistent(&Basis::default()),
            Err(ConsistenceError::UnboundArrowEffect(ArrEff::new(
                EffVar(0),
                Effect::default()
            )))
        );

        assert!(ArrEff::new(EffVar(0), Effect::default())
            .is_consistent(&Basis::new(
                None,
                vec![ArrEff::new(EffVar(0), Effect::default())]
            ))
            .is_ok());

        assert_eq!(
            ArrEff::new(EffVar(0), Effect::from_iter(vec![AtEff::reg(0)])).is_consistent(
                &Basis::new(None, vec![ArrEff::new(EffVar(0), Effect::default())])
            ),
            Err(ConsistenceError::UnboundArrowEffect(ArrEff::new(
                EffVar(0),
                Effect::from_iter(vec![AtEff::reg(0)])
            )))
        );

        assert_eq!(
            ArrEff::new(EffVar(0), Effect::from_iter(vec![AtEff::reg(0)])).is_consistent(
                &Basis::new(
                    None,
                    vec![ArrEff::new(
                        EffVar(0),
                        Effect::from_iter(vec![AtEff::eff(1)])
                    )]
                )
            ),
            Err(ConsistenceError::InconsistentBasis)
        );

        assert!(Effect::default().is_consistent(&Basis::default()).is_ok());

        assert_eq!(
            Effect::from_iter(vec![AtEff::reg(0)])
                .is_consistent(&Basis::default())
                .unwrap_err()
                .as_fail()
                .downcast_ref(),
            Some(&ConsistenceError::UnboundRegionVariables)
        );

        assert!(Effect::from_iter(vec![AtEff::reg(0)])
            .is_consistent(&Basis::new(vec![RegVar(0)], None))
            .is_ok());

        assert!(Effect::from_iter(vec![AtEff::eff(0)])
            .is_consistent(&Basis::new(
                None,
                vec![ArrEff::new(EffVar(0), Effect::default())]
            ))
            .is_ok());

        assert!(Effect::from_iter(vec![AtEff::eff(0), AtEff::reg(0)])
            .is_consistent(&Basis::new(
                vec![RegVar(0)],
                vec![ArrEff::new(
                    EffVar(0),
                    Effect::from_iter(vec![AtEff::reg(0)])
                )]
            ))
            .is_ok());

        assert_eq!(
            Effect::from_iter(vec![AtEff::eff(0)])
                .is_consistent(&Basis::new(
                    vec![RegVar(0)],
                    vec![ArrEff::new(
                        EffVar(0),
                        Effect::from_iter(vec![AtEff::reg(0)])
                    )]
                ))
                .unwrap_err()
                .as_fail()
                .downcast_ref(),
            Some(&ConsistenceError::MissingDenotation(EffVar(0)))
        );
    }
}
