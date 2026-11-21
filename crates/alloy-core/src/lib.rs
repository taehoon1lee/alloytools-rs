//! Alloy front-end. Port of the Java packages:
//!   edu.mit.csail.sdg.alloy4   (Pos, Err*, utilities)      -> `error`
//!   edu.mit.csail.sdg.parser   (Alloy.lex, Alloy.cup, CompModule, CompUtil) -> `lexer`, `parser`, `module`
//!   edu.mit.csail.sdg.ast      (Expr*, Sig, Func, Command, Type)           -> `ast`
//!
//! Public contract used by the CLI (do not break the signatures, extend them):
//!   * [`parse_everything_from_file`]  ~ `CompUtil.parseEverything_fromFile`
//!   * [`World::commands`]             ~ `CompModule.getAllCommands`

pub mod error;
pub mod lexer;
pub mod parser;
pub mod stdlib;
pub mod syntax;

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
///
/// Currently only the root file is parsed (modules/`open` are M2.1) and `CommandInfo` is filled from the
/// parsed commands with Java's defaults; `scope_string` is still empty (M2.3: `Command.toString()`).
pub fn parse_everything_from_file(path: &Path) -> Result<World, AlloyError> {
    let src = std::fs::read_to_string(path)
        .map_err(|e| AlloyError::new(ErrorKind::Other, None, format!("cannot read {}: {e}", path.display())))?;
    let module = parser::parse_module(&path.display().to_string(), &src)?;
    Ok(World {
        commands: command_infos(&module),
    })
}

/// `CommandInfo` for every command of the root module, in source order.
/// Java: `CompModule.addCommand` (anonymous labels `run$N`/`check$N`, N = 1 + commands before it).
fn command_infos(module: &syntax::Module) -> Vec<CommandInfo> {
    let mut out = Vec::new();
    for p in &module.paragraphs {
        let syntax::Paragraph::Command(c) = p else { continue };
        let n = out.len() + 1;
        let label = match (&c.label, &c.target) {
            (Some(l), _) => l.clone(),
            (None, syntax::CommandTarget::Name(name)) => name.clone(),
            (None, syntax::CommandTarget::Block(_)) => {
                format!("{}${n}", if c.check { "check" } else { "run" })
            }
        };
        let steps = c.scopes.steps;
        out.push(CommandInfo {
            label,
            check: c.check,
            expects: c.expect.unwrap_or(-1),
            scope_string: String::new(),
            overall: c.scopes.overall.unwrap_or(-1),
            bitwidth: c.scopes.bitwidth.unwrap_or(-1),
            maxseq: c.scopes.maxseq.unwrap_or(-1),
            minprefix: steps.and_then(|s| s.min).unwrap_or(-1),
            maxprefix: steps.map_or(-1, |s| s.max),
        });
    }
    out
}
