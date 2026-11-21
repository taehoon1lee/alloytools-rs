//! Port of Kodkod / Pardinus (reference/alloy-java/org.alloytools.pardinus.core/src/main/java/kodkod).
//!
//! Planned module layout (create files as you port; keep this map up to date):
//!   ast        <- kodkod/ast            Relation, Variable, Expression, Formula, IntExpression, Decls
//!   instance   <- kodkod/instance       Universe, Tuple, TupleSet, TupleFactory, Bounds, Instance
//!   bool       <- kodkod/engine/bool    BooleanFactory, BooleanMatrix, BooleanValue, Int, TwosComplementInt
//!   fol2sat    <- kodkod/engine/fol2sat Translator, FOL2BoolTranslator, Skolemizer, SymmetryBreaker,
//!                                        Bool2CNFTranslator, LeafInterpreter, FormulaFlattener
//!   ltl2fol    <- kodkod/engine/ltl2fol LTL2FOLTranslator, TemporalTranslator, TemporalBoundsExpander
//!   engine     <- kodkod/engine         Solver/PardinusSolver/TemporalPardinusSolver, Solution, Evaluator
//!   util       <- kodkod/util/ints      IntSet, IntVector, SparseSequence (use Rust std/bitsets where simpler)
//!
//! The SAT backend comes from the `satsolver` crate.

pub use satsolver;
