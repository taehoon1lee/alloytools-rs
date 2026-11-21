//! Alloy front-end. Port of the Java packages:
//!   edu.mit.csail.sdg.alloy4   (Pos, Err*, utilities)      -> `error`
//!   edu.mit.csail.sdg.parser   (Alloy.lex, Alloy.cup, CompModule, CompUtil) -> `lexer`, `parser`, `module`
//!   edu.mit.csail.sdg.ast      (Expr*, Sig, Func, Command, Type)           -> `ast`
//!
//! Public contract used by the CLI (do not break the signatures, extend them):
//!   * [`parse_everything_from_file`]  ~ `CompUtil.parseEverything_fromFile`
//!   * [`World::commands`]             ~ `CompModule.getAllCommands`

pub mod error;
pub mod stdlib;

pub use error::{AlloyError, ErrorKind, Pos};

use std::path::Path;

/// Everything the CLI needs to know about one command before solving.
/// Field meaning is identical to `edu.mit.csail.sdg.ast.Command`.
#[derive(Debug, Clone)]
pub struct CommandInfo {
    pub label: String,
    pub check: bool,
    pub expects: i32,
    /// Exactly `Command.toString()` of Java, e.g. `Run run$1 for 5 int` / `Check A for 3 but exactly 2 X`.
    pub scope_string: String,
    pub overall: i32,
    pub bitwidth: i32,
    pub maxseq: i32,
    pub minprefix: i32,
    pub maxprefix: i32,
}

/// A fully parsed, resolved and type-checked root module plus all opened modules
/// (equivalent of the Java `CompModule` returned by `parseEverything_fromFile`).
#[derive(Debug, Default)]
pub struct World {
    pub commands: Vec<CommandInfo>,
    // TODO(M1/M2): modules, sigs, fields, funcs, facts, resolved command formulas ...
}

impl World {
    pub fn commands(&self) -> &[CommandInfo] {
        &self.commands
    }
}

/// Parse `path` (and every module it opens, including the embedded `util/*` library),
/// resolve names and type-check. Mirrors `CompUtil.parseEverything_fromFile`.
pub fn parse_everything_from_file(path: &Path) -> Result<World, AlloyError> {
    let _src = std::fs::read_to_string(path)
        .map_err(|e| AlloyError::new(ErrorKind::Other, None, format!("cannot read {}: {e}", path.display())))?;
    Err(AlloyError::unsupported("parser not implemented yet (milestone M1)"))
}
