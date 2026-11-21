//! Port of the module-loading part of `CORE/parser/CompUtil.java` (`parseRecursively`,
//! `computeModulePath`, `up`) and of the alias rules of `CORE/parser/CompModule.java` (`addOpen`,
//! and the `$`-alias renaming pass after the opens are collected).
//!
//! Every `open` is loaded again per use, as Java does (`CompUtil.parse` is called for each `Open`),
//! so module parameters can later be instantiated per open. Cycles are detected along the open chain
//! (`thispath` in Java). Modules that are not found next to the opening file come from the embedded
//! library (`stdlib`, Java's `models/` resource folder).

use std::path::Path;

use crate::error::{AlloyError, ErrorKind, Pos};
use crate::parser::parse_module;
use crate::stdlib;
use crate::syntax::{Loc, Module, Open, Paragraph};

/// One parsed module instance (Java `CompModule`). Index 0 of the loaded list is the root.
#[derive(Debug)]
pub struct LoadedModule {
    /// Header name (`module a/b`), or "" when there is no header.
    pub name: String,
    /// File path used for relative lookup; embedded library modules use `models/<name>.als`.
    pub path: String,
    pub module: Module,
    /// Resolved `open` declarations in source order.
    pub opens: Vec<ResolvedOpen>,
}

/// An `open` after loading: which module instance it refers to and under which alias.
#[derive(Debug, Clone, PartialEq)]
pub struct ResolvedOpen {
    pub loc: Loc,
    pub is_private: bool,
    /// Alias (explicit `as`, or Java's default name).
    pub alias: String,
    /// Index of the opened module instance in the loaded list.
    pub target: usize,
}

/// Loads the root file and, recursively, every module it opens.
pub fn load_root(root: &Path) -> Result<Vec<LoadedModule>, AlloyError> {
    let key = root.display().to_string();
    let src = std::fs::read_to_string(root).map_err(|e| {
        AlloyError::new(
            ErrorKind::Other,
            None,
            format!("cannot read {}: {e}", root.display()),
        )
    })?;
    let mut out = Vec::new();
    let mut chain = vec![key.clone()];
    load_one(&key, &src, &mut chain, &mut out)?;
    Ok(out)
}

/// Parses one file and loads its opens. Returns the index of the new module instance.
fn load_one(
    path: &str,
    src: &str,
    chain: &mut Vec<String>,
    out: &mut Vec<LoadedModule>,
) -> Result<usize, AlloyError> {
    let module = parse_module(path, src)?;
    let name = module
        .header
        .as_ref()
        .map(|h| h.name.clone())
        .unwrap_or_default();
    check_open_order(path, &module)?;
    let opens: Vec<Open> = module
        .paragraphs
        .iter()
        .filter_map(|p| match p {
            Paragraph::Open(o) => Some(o.clone()),
            _ => None,
        })
        .collect();

    let idx = out.len();
    out.push(LoadedModule {
        name: name.clone(),
        path: path.to_string(),
        module,
        opens: Vec::new(),
    });

    let mut resolved = Vec::new();
    for o in &opens {
        let (child_path, child_src) = find_module(&o.name, &name, path)?;
        if chain.contains(&child_path) {
            return Err(AlloyError::new(
                ErrorKind::Syntax,
                Some(Pos {
                    file: path.to_string(),
                    line: o.loc.line,
                    col: o.loc.col,
                }),
                format!(
                    "Circular dependency in module import. The file \"{}\" is imported infinitely often.",
                    base_name(&child_path)
                ),
            ));
        }
        chain.push(child_path.clone());
        let target = load_one(&child_path, &child_src, chain, out)?;
        chain.pop();
        resolved.push(ResolvedOpen {
            loc: o.loc,
            is_private: o.is_private,
            alias: o.alias.clone().unwrap_or_default(),
            target,
        });
    }
    default_aliases(&opens, &mut resolved);
    out[idx].opens = resolved;
    Ok(idx)
}

/// Java `CompModule.addOpen`: an `open` must come before any sig/fact/pred/fun/assert/macro/command.
fn check_open_order(path: &str, module: &Module) -> Result<(), AlloyError> {
    let mut seen_decl = false;
    for p in &module.paragraphs {
        match p {
            Paragraph::Open(o) if seen_decl => {
                return Err(AlloyError::syntax(
                    Pos {
                        file: path.to_string(),
                        line: o.loc.line,
                        col: o.loc.col,
                    },
                    "The \"open\" declaration must occur before any\nsig/pred/fun/fact/assert/check/run command.",
                ));
            }
            Paragraph::Open(_) | Paragraph::Enum(_) => {}
            _ => seen_decl = true,
        }
    }
    Ok(())
}

/// Java default alias of an `open` without `as`: the module's last path segment when it is a plain
/// identifier and there are no arguments, else `open$N`, renamed afterwards to that last segment
/// when it does not clash (CompModule `addOpen` + the `$` pass of its alias map).
fn default_aliases(opens: &[Open], resolved: &mut [ResolvedOpen]) {
    for (i, o) in opens.iter().enumerate() {
        if o.alias.is_some() {
            continue;
        }
        let plain = o.args.is_empty() && is_identifier(&o.name);
        resolved[i].alias = if plain {
            o.name.clone()
        } else {
            format!("open${}", i + 1)
        };
    }
    for i in 0..resolved.len() {
        if !resolved[i].alias.contains('$') {
            continue;
        }
        let last = opens[i].name.rsplit('/').next().unwrap_or(&opens[i].name).to_string();
        let taken = resolved.iter().any(|r| r.alias == last);
        if is_identifier(&last) && !taken {
            resolved[i].alias = last;
        }
    }
}

/// `[a-zA-Z][a-zA-Z0-9_'"]*` (the Java alias check for a plain name).
fn is_identifier(s: &str) -> bool {
    let mut chars = s.chars();
    match chars.next() {
        Some(c) if c.is_ascii_alphabetic() => {}
        _ => return false,
    }
    chars.all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '\'' || c == '"')
}

/// Finds the file of `target` as Java does: relative to the opening file (`computeModulePath`),
/// else the embedded library. Returns `(key, source)`.
fn find_module(target: &str, module_name: &str, file: &str) -> Result<(String, String), AlloyError> {
    let rel = compute_module_path(module_name, file, target);
    if let Ok(src) = std::fs::read_to_string(&rel) {
        return Ok((rel, src));
    }
    if let Some(src) = stdlib::lookup(target) {
        return Ok((format!("models/{target}.als"), src.to_string()));
    }
    Err(AlloyError::new(
        ErrorKind::Syntax,
        None,
        format!("File cannot be found.\n{target}.als"),
    ))
}

/// Java `CompUtil.computeModulePath`: strip the common module-name prefix of the opening module
/// and the opened name, then go up from the file by the depth of the opening module.
fn compute_module_path(module_a: &str, file_a: &str, module_b: &str) -> String {
    let module_a_full = if module_a.is_empty() {
        "anything"
    } else {
        module_a
    };
    let mut a = module_a_full;
    let mut b = module_b;
    while !a.is_empty() && !b.is_empty() {
        let (ia, ib) = (a.find('/'), b.find('/'));
        let head_a = ia.map_or(a, |i| &a[..i]);
        let head_b = ib.map_or(b, |i| &b[..i]);
        if head_a != head_b || ia.is_none() || ib.is_none() {
            // Java counts the slashes of the *current* moduleA (it is reassigned in the loop).
            let slashes = a.matches('/').count();
            return format!("{}/{}.als", up(file_a, slashes + 1), b);
        }
        a = &a[ia.unwrap_or(0) + 1..];
        b = &b[ib.unwrap_or(0) + 1..];
    }
    String::new()
}

/// Java `CompUtil.up`: drop `steps` trailing path components (`\` or `/`).
fn up(path: &str, mut steps: usize) -> String {
    let mut p = path.to_string();
    while steps > 0 {
        steps -= 1;
        match p.rfind(['/', '\\']) {
            Some(i) if i > 0 => p.truncate(i),
            _ => return String::new(),
        }
    }
    p
}

fn base_name(path: &str) -> &str {
    path.rsplit(['/', '\\']).next().unwrap_or(path)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn module_path_is_relative_to_the_opening_file() {
        // Root `main.als` (no header) opening `util/integer` looks next to itself.
        assert_eq!(compute_module_path("", "D:\\m\\main.als", "util/integer"), "D:\\m/util/integer.als");
        // A module `util/integer` (in `models/util/integer.als`) opening `util/ordering` goes up 2.
        assert_eq!(
            compute_module_path("util/integer", "models/util/integer.als", "util/ordering"),
            "models/util/ordering.als"
        );
        // Same depth: `a/b` opens `a/c` -> `dir/a/c.als` after stripping `a`.
        assert_eq!(compute_module_path("a/b", "x/a/b.als", "a/c"), "x/a/c.als");
    }

    #[test]
    fn up_drops_components() {
        assert_eq!(up("a/b/c.als", 1), "a/b");
        assert_eq!(up("a/b/c.als", 2), "a");
        assert_eq!(up("c.als", 1), "");
    }

    #[test]
    fn default_alias_rules() {
        assert!(is_identifier("ordering"));
        assert!(!is_identifier("util/ordering"));
        assert!(!is_identifier("1abc"));
    }

    #[test]
    fn embedded_library_is_loaded_for_open_util_ordering() {
        let dir = std::env::temp_dir().join("alloy_loader_test_ordering");
        std::fs::create_dir_all(&dir).unwrap();
        let root = dir.join("m.als");
        std::fs::write(&root, "module m\nopen util/ordering[S] as ord\nopen util/boolean\nsig S {}\n").unwrap();
        let mods = load_root(&root).unwrap();
        assert_eq!(mods[0].name, "m");
        let aliases: Vec<&str> = mods[0].opens.iter().map(|o| o.alias.as_str()).collect();
        assert_eq!(aliases, vec!["ord", "boolean"]);
        assert!(mods.len() >= 3, "ordering and boolean (and what they open) are loaded");
    }

    #[test]
    fn open_after_a_sig_is_a_syntax_error() {
        let dir = std::env::temp_dir().join("alloy_loader_test_order");
        std::fs::create_dir_all(&dir).unwrap();
        let root = dir.join("m.als");
        std::fs::write(&root, "sig S {}\nopen util/boolean\n").unwrap();
        let e = load_root(&root).unwrap_err();
        assert_eq!(e.kind, ErrorKind::Syntax);
    }
}
