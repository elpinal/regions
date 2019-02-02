//! Tofte and Birkedal. TOPLAS 1998.
//! “A region inference algorithm.”

#![allow(dead_code)]

/// A program variable.
pub struct Var(usize);

/// A type variable.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TyVar(usize);

pub mod ml;
pub mod region;
