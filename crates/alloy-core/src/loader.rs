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
    /// Index of the `Paragraph::Open` in the module, or `None` for the implicit `open util/integer as integer`
    /// that Java adds to every module (it is what makes `minus[a, b]` resolve without an `open`).
    pub paragraph: Option<usize>,
}

/// Alias of the implicit integer library open.
pub const IMPLICIT_INTEGER_ALIAS: &str = "integer";

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
    Ok(merge_instances(out))
}

/// Canonical identity of a sig: (module instance, name).
type SigKey = (usize, String);

/// Java `CompModule.resolveModules`: two module instances of the same file instantiated with the same
/// (resolved) sig arguments are one module. E.g. `open util/ordering[Tick]` in two files yields a single
/// ordering. Instances are loaded in pre-order, so an opener always precedes the modules it opens.
fn merge_instances(mods: Vec<LoadedModule>) -> Vec<LoadedModule> {
    let n = mods.len();
    // parent[i] = (opener, paragraph index of the open) for every non-root instance
    let mut parent: Vec<Option<(usize, usize)>> = vec![None; n];
    for (o, m) in mods.iter().enumerate() {
        for r in &m.opens {
            if let Some(k) = r.paragraph {
                if parent[r.target].is_none() {
                    parent[r.target] = Some((o, k));
                }
            }
        }
    }
    let declares = |m: &LoadedModule, name: &str| {
        m.module.paragraphs.iter().any(|p| match p {
            Paragraph::Sig(s) => s.names.iter().any(|x| x == name),
            Paragraph::Enum(e) => e.name == name,
            _ => false,
        })
    };
    let mut rep: Vec<usize> = (0..n).collect();
    // actual parameters of each instance, canonical
    let mut actuals: Vec<Option<Vec<SigKey>>> = vec![None; n];
    actuals[0] = Some(Vec::new());
    let mut seen: Vec<(String, Vec<SigKey>, usize)> = Vec::new();
    for i in 1..n {
        let Some((o, k)) = parent[i] else {
            // the implicit integer open (no paragraph) and any unparented instance: keyed by path only
            let key = (mods[i].path.clone(), Vec::new());
            match seen.iter().find(|(p, a, _)| *p == key.0 && *a == key.1) {
                Some(&(_, _, j)) => rep[i] = j,
                None => seen.push((key.0, key.1, i)),
            }
            actuals[i] = Some(Vec::new());
            continue;
        };
        let o = rep[o];
        let Paragraph::Open(open) = &mods[o].module.paragraphs[k] else { continue };
        let mut args: Option<Vec<SigKey>> = Some(Vec::new());
        for a in &open.args {
            let crate::syntax::ExprKind::Name(nm) = &a.kind else {
                args = None;
                break;
            };
            let key = canonical_sig(&mods, &rep, &actuals, &declares, o, nm);
            match (key, args.as_mut()) {
                (Some(k2), Some(v)) => v.push(k2),
                _ => {
                    args = None;
                    break;
                }
            }
        }
        match args {
            Some(a) => {
                match seen.iter().find(|(p, a2, _)| *p == mods[i].path && *a2 == a) {
                    Some(&(_, _, j)) => rep[i] = j,
                    None => seen.push((mods[i].path.clone(), a.clone(), i)),
                }
                actuals[i] = Some(a);
            }
            None => actuals[i] = None,
        }
    }
    if rep.iter().enumerate().all(|(i, &r)| i == r) {
        return mods;
    }
    // keep representatives only, renumbered
    let mut new_idx = vec![usize::MAX; n];
    let mut next = 0;
    for i in 0..n {
        if rep[i] == i {
            new_idx[i] = next;
            next += 1;
        }
    }
    let mut out = Vec::with_capacity(next);
    for (i, mut m) in mods.into_iter().enumerate() {
        if rep[i] != i {
            continue;
        }
        for r in &mut m.opens {
            r.target = new_idx[rep[r.target]];
        }
        out.push(m);
    }
    out
}

/// Resolves a module argument name written in module `o` to a canonical sig identity.
fn canonical_sig(
    mods: &[LoadedModule],
    rep: &[usize],
    actuals: &[Option<Vec<SigKey>>],
    declares: &dyn Fn(&LoadedModule, &str) -> bool,
    o: usize,
    name: &str,
) -> Option<SigKey> {
    // a parameter of the opener
    let header = mods[o].module.header.as_ref();
    if let Some(h) = header {
        if let Some(pos) = h.params.iter().position(|p| p == name) {
            return actuals[o].as_ref()?.get(pos).cloned();
        }
    }
    if let Some((prefix, base)) = name.rsplit_once('/') {
        // `alias/.../Name`: follow the aliases
        let mut cur = o;
        for seg in prefix.split('/') {
            if seg == "this" {
                continue;
            }
            let r = mods[cur].opens.iter().find(|r| r.alias == seg)?;
            cur = rep[r.target];
        }
        return canonical_in(mods, rep, actuals, declares, cur, base);
    }
    if declares(&mods[o], name) {
        return Some((o, name.to_string()));
    }
    // unqualified: a sig of some opened module
    let mut stack: Vec<usize> = mods[o].opens.iter().map(|r| rep[r.target]).collect();
    let mut visited = vec![o];
    while let Some(m) = stack.pop() {
        if visited.contains(&m) {
            continue;
        }
        visited.push(m);
        if let Some(k) = canonical_in(mods, rep, actuals, declares, m, name) {
            return Some(k);
        }
        stack.extend(mods[m].opens.iter().map(|r| rep[r.target]));
    }
    None
}

fn canonical_in(
    mods: &[LoadedModule],
    rep: &[usize],
    actuals: &[Option<Vec<SigKey>>],
    declares: &dyn Fn(&LoadedModule, &str) -> bool,
    m: usize,
    name: &str,
) -> Option<SigKey> {
    let _ = rep;
    if declares(&mods[m], name) {
        return Some((m, name.to_string()));
    }
    let h = mods[m].module.header.as_ref()?;
    let pos = h.params.iter().position(|p| p == name)?;
    actuals[m].as_ref()?.get(pos).cloned()
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
    let open_at: Vec<(usize, Open)> = module
        .paragraphs
        .iter()
        .enumerate()
        .filter_map(|(k, p)| match p {
            Paragraph::Open(o) => Some((k, o.clone())),
            _ => None,
        })
        .collect();
    let opens: Vec<Open> = open_at.iter().map(|(_, o)| o.clone()).collect();
    // Java: an explicit `open ... as integer` clashes with the implicit integer library.
    let implicit = name != "util/integer";
    if implicit {
        if let Some((_, o)) = open_at.iter().find(|(_, o)| o.alias.as_deref() == Some(IMPLICIT_INTEGER_ALIAS)) {
            return Err(AlloyError::syntax(
                Pos {
                    file: path.to_string(),
                    line: o.loc.line,
                    col: o.loc.col,
                },
                "You cannot import two different modules\nusing the same alias.",
            ));
        }
    }

    let idx = out.len();
    out.push(LoadedModule {
        name: name.clone(),
        path: path.to_string(),
        module,
        opens: Vec::new(),
    });

    let mut resolved = Vec::new();
    if implicit {
        let (child_path, child_src) = find_module("util/integer", &name, path)?;
        chain.push(child_path.clone());
        let target = load_one(&child_path, &child_src, chain, out)?;
        chain.pop();
        resolved.push(ResolvedOpen {
            loc: Loc { line: 1, col: 1 },
            is_private: true,
            alias: IMPLICIT_INTEGER_ALIAS.to_string(),
            target,
            paragraph: None,
        });
    }
    let first_explicit = resolved.len();
    for (o, (k, _)) in opens.iter().zip(open_at.iter()) {
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
            paragraph: Some(*k),
        });
    }
    default_aliases(&opens, &mut resolved[first_explicit..]);
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
        // The implicit `integer` open comes first (Java adds it to every module).
        assert_eq!(aliases, vec!["integer", "ord", "boolean"]);
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
