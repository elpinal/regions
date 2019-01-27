//! The source language.

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

impl MLType {
    pub fn arrow(ty1: MLType, ty2: MLType) -> Self {
        MLType::Arrow(Box::new(ty1), Box::new(ty2))
    }
}
