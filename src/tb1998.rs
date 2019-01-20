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

    use std::collections::HashSet;

    /// A region variable.
    pub struct RegVar(usize);

    /// An untyped region-annotated term.
    pub enum RegExp {
        Var(Var),
        Inst(Var, Vec<RegVar>, RegVar),
        Abs(Box<RegExp>, RegVar),
        App(Box<RegExp>, Box<RegExp>),
        LetRec(usize, RegVar, Box<RegExp>, Box<RegExp>),
        LetRegion(Box<RegExp>),
    }

    /// An effect variable.
    pub struct EffVar(usize);

    /// An atomic effect.
    pub enum AtEff {
        Reg(RegVar),
        Eff(EffVar),
    }

    /// An effect
    pub struct Effect(HashSet<AtEff>);

    /// An arrow effect.
    pub struct ArrEff {
        handle: EffVar,
        latent: Effect,
    }

    /// A type.
    pub enum Type {
        Int,
        Var(TyVar),
        Arrow(Box<PType>, Box<PType>),
    }

    /// A type with a place.
    pub struct PType {
        ty: Type,
        reg: RegVar,
    }
}
