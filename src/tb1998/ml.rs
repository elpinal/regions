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
