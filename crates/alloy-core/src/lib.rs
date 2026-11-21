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
pub mod loader;
pub mod parser;
pub mod sema;
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
    /// Root module first, then every opened module instance (`loader::load_root`).
    pub modules: Vec<loader::LoadedModule>,
    // TODO(M3): sigs, fields, funcs, facts, resolved command formulas ...
}

impl World {
    pub fn commands(&self) -> &[CommandInfo] {
        &self.commands
    }
}

/// Parse `path` (and every module it opens, including the embedded `util/*` library),
/// resolve names and type-check. Mirrors `CompUtil.parseEverything_fromFile`.
///
/// Loads the root file and its opens (M2.1); `CommandInfo` comes from the root module's commands.
pub fn parse_everything_from_file(path: &Path) -> Result<World, AlloyError> {
    let modules = loader::load_root(path)?;
    Ok(World {
        commands: command_infos(&modules[0].module),
        modules,
    })
}

/// `CommandInfo` for every command of the root module, in source order.
/// Java: `CompModule.addCommand` (anonymous labels `run$N`/`check$N`, N = 1 + commands before it) and
/// `CompModule.addDefaultCommand` (a module without commands gets `Run Default` with formula TRUE).
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
        let mut info = CommandInfo {
            label,
            check: c.check,
            expects: c.expect.unwrap_or(-1),
            scope_string: String::new(),
            overall: c.scopes.overall.unwrap_or(-1),
            bitwidth: c.scopes.bitwidth.unwrap_or(-1),
            maxseq: c.scopes.maxseq.unwrap_or(-1),
            minprefix: steps.and_then(|s| s.min).unwrap_or(-1),
            maxprefix: steps.map_or(-1, |s| s.max),
        };
        info.scope_string = command_to_string(&info, &c.scopes.typescopes);
        out.push(info);
    }
    if out.is_empty() {
        let mut info = CommandInfo {
            label: "Default".into(),
            check: false,
            expects: -1,
            scope_string: String::new(),
            overall: -1,
            bitwidth: -1,
            maxseq: -1,
            minprefix: -1,
            maxprefix: -1,
        };
        info.scope_string = command_to_string(&info, &[]);
        out.push(info);
    }
    out
}

/// Java `Command.toString()`: `Run|Check label [for N [but]] [bits int] [N seq] [steps] [scopes] [expect N]`.
fn command_to_string(c: &CommandInfo, scopes: &[syntax::TypeScope]) -> String {
    let others = c.bitwidth >= 0 || c.maxseq >= 0 || !scopes.is_empty() || c.minprefix >= 0 || c.maxprefix >= 0;
    let mut s = format!("{} {}", if c.check { "Check" } else { "Run" }, c.label);
    if c.overall >= 0 && others {
        s += &format!(" for {} but", c.overall);
    } else if c.overall >= 0 {
        s += &format!(" for {}", c.overall);
    } else if others {
        s += " for";
    }
    let mut first = true;
    if c.bitwidth >= 0 {
        s += &format!(" {} int", c.bitwidth);
        first = false;
    }
    if c.maxseq >= 0 {
        s += &format!("{}{} seq", if first { " " } else { ", " }, c.maxseq);
        first = false;
    }
    if c.maxprefix >= 0 {
        s.push(' ');
        if c.minprefix >= 0 {
            s += &format!("{}..", c.minprefix);
        }
        if c.maxprefix != i32::MAX {
            s += &c.maxprefix.to_string();
        }
        s += " steps";
        first = false;
    }
    for t in scopes {
        s += if first { " " } else { ", " };
        s += &scope_entry_to_string(t);
        first = false;
    }
    if c.expects >= 0 {
        s += &format!(" expect {}", c.expects);
    }
    s
}

/// Java `CommandScope.toString()`: `[exactly ]start[..end][:increment] sig`.
fn scope_entry_to_string(t: &syntax::TypeScope) -> String {
    let mut s = String::new();
    if t.exactly {
        s += "exactly ";
    }
    s += &t.start.to_string();
    if t.end != t.start {
        s += &format!("..{}", t.end);
    }
    if t.increment > 1 {
        s += &format!(":{}", t.increment);
    }
    // Java `Util.tail`: the part after the last '/'.
    let sig = t.sig.rsplit('/').next().unwrap_or(&t.sig);
    format!("{s} {sig}")
}
