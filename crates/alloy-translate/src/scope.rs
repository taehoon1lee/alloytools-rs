//! Port of `CORE/translator/ScopeComputer.java` (scope derivation, `computeLowerBound` atom creation)
//! and the sig part of `BoundsComputer.java` (upper/lower atom sets of every sig).
//!
//! Atoms are named exactly like Java: `Sig$i`, with `i` counting from 0 inside one creation step.
//! A top-level sig with scope `n` creates `n - (atoms its children must have)` atoms; exact sigs
//! (`one`, `exactly`) create their own atoms too; plain subsigs share the parent's atoms.

use alloy_core::error::{AlloyError, ErrorKind, Pos};
use alloy_core::sema::{Model, RCommand, SigId, SigKind, SIG_STRING};
use alloy_core::syntax::Mult;

/// Atom layout of one command.
#[derive(Debug, Clone)]
pub struct Layout {
    /// Universe atoms in creation order (their names are the Java atom names).
    pub atoms: Vec<String>,
    /// Scope of every user sig (`None` for builtins / subset sigs without atoms).
    pub scope: Vec<Option<i32>>,
    /// Java `isExact` (exactly `n` atoms).
    pub exact: Vec<bool>,
    /// Atom range `[start, end)` created in the sig's subtree (ScopeComputer's `computeLowerBound`).
    range: Vec<(u32, u32)>,
    parent: Vec<Option<SigId>>,
    children: Vec<Vec<SigId>>,
    is_subset: Vec<bool>,
    model_sigs_len: usize,
    /// Atom range `[start, end)` of the `String` sig (string literals, padded to the `String` scope).
    pub string_range: (u32, u32),
    /// Atom range of the time atoms of a temporal problem (`(0, 0)` when static).
    pub time_range: (u32, u32),
    /// The sig whose computeLowerBound step created each sig atom (exact pipeline renames atoms Java's way).
    pub atom_sig: Vec<SigId>,
}

impl Layout {
    /// Atoms a sig may take (Java `BoundsComputer` upper bound).
    pub fn upper(&self, s: SigId) -> Vec<u32> {
        let i = s as usize;
        if i >= self.model_sigs_len {
            return Vec::new();
        }
        if self.is_subset[i] {
            return Vec::new();
        }
        if self.exact[i] {
            let (a, b) = self.range[i];
            return (a..b).collect();
        }
        match self.parent[i] {
            Some(p) => self.upper(p),
            None => {
                let (a, b) = self.range[i];
                (a..b).collect()
            }
        }
    }

    /// Atoms a sig must take (exact sigs only).
    pub fn lower(&self, s: SigId) -> Vec<u32> {
        let i = s as usize;
        if i >= self.model_sigs_len || !self.exact[i] {
            return Vec::new();
        }
        let (a, b) = self.range[i];
        (a..b).collect()
    }

    pub fn children(&self, s: SigId) -> &[SigId] {
        &self.children[s as usize]
    }

    pub fn parent(&self, s: SigId) -> Option<SigId> {
        self.parent[s as usize]
    }
}

fn err<T>(model: &Model, cmd: &RCommand, msg: String) -> Result<T, AlloyError> {
    let _ = (model, cmd);
    Err(AlloyError::new(
        ErrorKind::Syntax,
        Some(Pos {
            file: String::new(),
            line: 1,
            col: 1,
        }),
        msg,
    ))
}

/// Computes scopes and atoms for `cmd` (Java `ScopeComputer.compute`).
pub fn compute_scopes(model: &Model, cmd: &RCommand) -> Result<Layout, AlloyError> {
    let n = model.sigs.len();
    let mut parent = vec![None; n];
    let mut children = vec![Vec::new(); n];
    let mut is_subset = vec![false; n];
    for (i, s) in model.sigs.iter().enumerate() {
        if s.kind == SigKind::User {
            parent[i] = s.parent;
            if let Some(p) = s.parent {
                children[p as usize].push(i as SigId);
            }
            is_subset[i] = !s.subset_of.is_empty();
        }
    }
    let mut maxstring: Option<i32> = None;
    let mut scope: Vec<Option<i32>> = vec![None; n];
    let mut exact = vec![false; n];
    let is_user = |i: usize| model.sigs[i].kind == SigKind::User;

    // 1. explicit scopes of the command (`for N but ...`)
    for rs in &cmd.scopes {
        if rs.sig == SIG_STRING {
            maxstring = Some(rs.start);
            continue;
        }
        let i = rs.sig as usize;
        if !is_user(i) {
            return err(
                model,
                cmd,
                format!("You cannot set a scope on \"{}\".", model.sigs[i].label),
            );
        }
        scope[i] = Some(rs.start);
        exact[i] = rs.exact;
    }
    // `module m[exactly A]` parameters are forced exact (Java `cmd.additionalExactScopes`).
    let forced_exact: Vec<usize> = model.exact_sigs.iter().map(|&s| s as usize).collect();
    // `one` sigs have exactly one atom; `lone` sigs at most one (unless their scope is 0).
    for i in 0..n {
        if !is_user(i) {
            continue;
        }
        match model.sigs[i].mult {
            Some(Mult::One) => {
                if let Some(sc) = scope[i] {
                    if sc != 1 {
                        return err(
                            model,
                            cmd,
                            format!(
                                "Sig \"{}\" has the multiplicity of \"one\", so its scope must be 1, and cannot be {sc}",
                                model.sigs[i].name
                            ),
                        );
                    }
                }
                scope[i] = Some(1);
                exact[i] = true;
            }
            Some(Mult::Lone) if scope[i] != Some(0) => scope[i] = Some(1),
            _ => {}
        }
    }
    // 1b. Java `derive_abstract_scope`: an abstract sig's scope is the sum of its children's scopes
    // (or, if one child is unscoped and the parent is scoped, the remainder).
    let mut changed = true;
    while changed {
        changed = false;
        for i in 0..n {
            if !is_user(i) || !model.sigs[i].is_abstract || children[i].is_empty() {
                continue;
            }
            let mut sum = 0;
            let mut missing = Vec::new();
            for &c in &children[i] {
                match scope[c as usize] {
                    Some(v) => sum += v,
                    None => missing.push(c as usize),
                }
            }
            if missing.len() > 1 {
                continue;
            }
            match (scope[i], missing.first()) {
                (None, None) => {
                    scope[i] = Some(sum);
                    changed = true;
                }
                (Some(sn), Some(&m)) => {
                    scope[m] = Some(if sn < sum { 0 } else { sn - sum });
                    changed = true;
                }
                _ => {}
            }
        }
    }
    // 2. implicit scopes: top-level sigs get the overall scope (3 when nothing was given)
    let overall = if cmd.overall.is_none() && cmd.scopes.is_empty() {
        Some(3)
    } else {
        cmd.overall
    };
    for i in 0..n {
        if !is_user(i) || parent[i].is_some() || is_subset[i] || scope[i].is_some() {
            continue;
        }
        if model.sigs[i].is_enum {
            scope[i] = Some(0);
            continue;
        }
        if model.sigs[i].mult == Some(Mult::One) {
            continue;
        }
        match overall {
            Some(o) => scope[i] = Some(o),
            None => {
                return err(
                    model,
                    cmd,
                    format!(
                        "You must specify a scope for sig \"{}\"",
                        model.sigs[i].name
                    ),
                )
            }
        }
    }
    // 3. subsigs without a scope take their parent's scope (fixpoint over the tree)
    let mut changed = true;
    while changed {
        changed = false;
        for i in 0..n {
            if !is_user(i) || scope[i].is_some() {
                continue;
            }
            if let Some(p) = parent[i] {
                if let Some(ps) = scope[p as usize] {
                    scope[i] = Some(ps);
                    changed = true;
                }
            }
        }
    }
    for i in 0..n {
        if is_user(i) && scope[i].is_none() && !is_subset[i] {
            scope[i] = Some(0);
        }
    }

    for &i in &forced_exact {
        if is_user(i) && model.sigs[i].subset_of.is_empty() {
            exact[i] = true;
        }
    }

    // 4. atoms (computeLowerBound), from every top-level PrimSig
    let mut layout = Layout {
        atoms: Vec::new(),
        scope: scope.clone(),
        exact: exact.clone(),
        range: vec![(0, 0); n],
        parent: parent.clone(),
        children: children.clone(),
        is_subset: is_subset.clone(),
        model_sigs_len: n,
        string_range: (0, 0),
        time_range: (0, 0),
        atom_sig: Vec::new(),
    };
    let mut atoms = Vec::new();
    let mut range = vec![(0u32, 0u32); n];
    let mut used = std::collections::HashSet::new();
    let mut atom_sig = Vec::new();
    for i in 0..n {
        if is_user(i) && parent[i].is_none() && !is_subset[i] {
            lower_bound(
                model,
                i,
                &scope,
                &exact,
                &children,
                &mut atoms,
                &mut range,
                &mut used,
                &mut atom_sig,
            );
        }
    }
    layout.atom_sig = atom_sig;
    layout.atoms = atoms;
    layout.range = range;
    // String atoms: the literals (named with their quotes), padded with `"String0"`, ... up to the String scope.
    let s0 = layout.atoms.len() as u32;
    layout.atoms.extend(java_string_atoms(model, cmd, maxstring.unwrap_or(-1)));
    layout.string_range = (s0, layout.atoms.len() as u32);
    Ok(layout)
}

/// Java `ScopeComputer.computeLowerBound`: returns the number of atoms the sig's subtree has.
fn lower_bound(
    model: &Model,
    s: usize,
    scope: &[Option<i32>],
    exact: &[bool],
    children: &[Vec<SigId>],
    atoms: &mut Vec<String>,
    range: &mut [(u32, u32)],
    used: &mut std::collections::HashSet<String>,
    atom_sig: &mut Vec<SigId>,
) -> i32 {
    let start = atoms.len() as u32;
    let mut lower: i32 = 0;
    for &c in &children[s] {
        lower += lower_bound(
            model, c as usize, scope, exact, children, atoms, range, used, atom_sig,
        );
    }
    let mut nsc = scope[s].unwrap_or(0);
    if nsc < lower {
        nsc = lower;
    }
    let top = model.sigs[s].parent.is_none();
    if nsc > lower && (exact[s] || top) {
        let k = nsc - lower;
        // Java `UniqueNameGenerator.make`: a clashing base name gets primes (`Ord`, `Ord'`, ...).
        let mut name = model.sigs[s].name.clone();
        while !used.insert(name.clone()) {
            name.push('\'');
        }
        for i in 0..k {
            atoms.push(format!("{name}${i}"));
            atom_sig.push(s as SigId);
        }
        lower = nsc;
    }
    range[s] = (start, atoms.len() as u32);
    lower
}

/// Java `Command.getAllStringConstants` + `ScopeComputer.compute`: the string literals reached from the facts and
/// the command formula (a call contributes its body, then its arguments), then from every sig's facts and field
/// bounds, padded with `"String<i>"` up to the String scope; Java keeps them in a `HashSet`, so the atoms come in
/// `HashSet` iteration order.
fn java_string_atoms(model: &Model, cmd: &RCommand, maxstring: i32) -> Vec<String> {
    use alloy_core::sema::RExpr;
    fn walk(model: &Model, e: &RExpr, out: &mut Vec<String>, seen: &mut Vec<u32>) {
        match e {
            RExpr::Str(t) => {
                let q = format!("\"{t}\"");
                if !out.contains(&q) {
                    out.push(q);
                }
            }
            RExpr::Sig(_) | RExpr::Field(_) | RExpr::Local(_) | RExpr::Const(_) | RExpr::Num(_) => {}
            RExpr::Un(_, x) => walk(model, x, out, seen),
            RExpr::Bin(_, a, b) => {
                walk(model, a, out, seen);
                walk(model, b, out, seen);
            }
            RExpr::Quant(_, ds, b) | RExpr::Compr(ds, b) => {
                for d in ds {
                    walk(model, &d.bound, out, seen);
                }
                walk(model, b, out, seen);
            }
            RExpr::Ite(c, a, b) => {
                walk(model, c, out, seen);
                walk(model, a, out, seen);
                walk(model, b, out, seen);
            }
            RExpr::Let(bs, b) => {
                for (_, x) in bs {
                    walk(model, x, out, seen);
                }
                walk(model, b, out, seen);
            }
            RExpr::Call(f, args) => {
                if !seen.contains(f) {
                    seen.push(*f);
                    walk(model, &model.funcs[*f as usize].body, out, seen);
                }
                for a in args {
                    walk(model, a, out, seen);
                }
            }
            RExpr::Block(xs) | RExpr::Disj(xs) | RExpr::TotalOrder(xs) | RExpr::Choice(xs) => {
                for x in xs {
                    walk(model, x, out, seen);
                }
            }
        }
    }
    let mut out = Vec::new();
    let mut seen = Vec::new();
    for f in &model.facts {
        walk(model, &f.body, &mut out, &mut seen);
    }
    walk(model, &cmd.formula, &mut out, &mut seen);
    for (s, sig) in model.sigs.iter().enumerate() {
        for (x, b) in &model.sig_facts {
            if *x as usize == s {
                walk(model, b, &mut out, &mut seen);
            }
        }
        for &f in &sig.fields {
            walk(model, &model.fields[f as usize].decl, &mut out, &mut seen);
        }
    }
    let mut i = 0;
    while (out.len() as i64) < maxstring as i64 {
        let x = format!("\"String{i}\"");
        if !out.contains(&x) {
            out.push(x);
        }
        i += 1;
    }
    java_hashset_order(out)
}

/// Iteration order of a `java.util.HashSet<String>` filled in the given order (bucket = spread hash & (cap - 1),
/// insertion order inside a bucket; the table doubles from 16 whenever it is more than 3/4 full).
fn java_hashset_order(v: Vec<String>) -> Vec<String> {
    let mut cap = 16usize;
    while v.len() > cap * 3 / 4 {
        cap *= 2;
    }
    let mut keyed: Vec<(usize, usize)> = v
        .iter()
        .enumerate()
        .map(|(i, s)| {
            let mut h: i32 = 0;
            for c in s.encode_utf16() {
                h = h.wrapping_mul(31).wrapping_add(c as i32);
            }
            let h = h as u32;
            (((h ^ (h >> 16)) as usize) & (cap - 1), i)
        })
        .collect();
    keyed.sort_unstable();
    keyed.into_iter().map(|(_, i)| v[i].clone()).collect()
}
