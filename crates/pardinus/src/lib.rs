//! Pure-MIT port of the Pardinus/Kodkod pipeline:
//! Kodkod problem (formula DAG + bounds) -> boolean circuit -> CNF -> BatSat portfolio -> instance.
//! See docs/EXACT_PORT.md. Java sources: reference/alloy-java/org.alloytools.pardinus.core/src/main/java/kodkod.

pub mod annotate;
pub mod ast;
pub mod bool;
pub mod cnf;
pub mod fol2bool;
pub mod instance;
pub mod kkwrite;
pub mod replace;
pub mod symmetry;
pub mod temporal;
pub mod translator;
