//! Port of Kodkod / Pardinus (reference/alloy-java/org.alloytools.pardinus.core/src/main/java/kodkod).
//!
//! Module map (port source in parentheses):
//!   ast        (kodkod/ast)            Expr, Formula, Decl, Const, Quantifier, Multiplicity
//!   instance   (kodkod/instance)       Universe, TupleSet, Bounds, Instance
//!   bool       (engine/bool, Bool2CNF) BoolFactory: hash-consed gates, eager Tseitin into SAT
//!   translate  (engine/fol2sat, Solver) FOL2Bool over BoolMatrix, primary variables, solve + decode
//!
//! Not yet ported: integers (bit-vectors), symmetry breaking, skolemization, temporal (LTL), evaluator.
//! The SAT backend comes from the `satsolver` crate.

pub mod ast;
pub mod bool;
pub mod instance;
pub mod translate;

pub use satsolver;
