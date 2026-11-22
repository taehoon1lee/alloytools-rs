//! Exact (Java-identical) Alloy -> Kodkod translation into the `pardinus` AST.
//! Port of `edu.mit.csail.sdg.translator.{TranslateAlloyToKodkod, BoundsComputer, Simplifier}` and the bounds /
//! formula parts of `A4Solution` (constructor, addRel, addSig, addField, query, addSymbolicBound, solve prologue),
//! plus the parts of `ast.Type` they need (field types, `fold`). See docs/EXACT_PORT.md.
//! The node shapes and creation order follow the Java visitor, so the resulting problem serializes to exactly the
//! `.kk` text that tools/exact/KKDump writes for Java.

use crate::scope::{compute_scopes, Layout};
use alloy_core::error::{AlloyError, ErrorKind};
use alloy_core::sema::{
    FieldId, FuncId, LocalId, Model, RCommand, RDecl, RExpr, SigId, SigKind, SIG_INT, SIG_NONE,
    SIG_SEQINT, SIG_STRING, SIG_UNIV,
};
use alloy_core::syntax::{BinOp, Const, Mult as AMult, Quant as AQuant, UnOp};
use pardinus::ast::{
    Ast, CastOp, CmpOp, ConstE, EOp, FOp, ICmpOp, IOp, Mult, Node, Quant, RelInfo, N,
};
use pardinus::instance::{Bounds, Options as KOptions, Problem, TupleSet};
use std::collections::HashMap;

fn unsupported(msg: impl Into<String>) -> AlloyError {
    AlloyError::unsupported(msg.into())
}
fn fatal(msg: impl Into<String>) -> AlloyError {
    AlloyError::new(ErrorKind::Other, None, msg.into())
}

// ================================================================================================ Java Type

/// `ast.Type` restricted to relational product types (`entries` order matters for symbolic bounds).
#[derive(Clone, Debug, PartialEq, Default)]
pub struct JType {
    pub entries: Vec<Vec<SigId>>,
}

/// The prim-sig hierarchy as Java sees it (UNIV is the parent of every top-level sig, Int and String).
pub struct Hier<'a> {
    pub model: &'a Model,
}

impl Hier<'_> {
    fn parent(&self, s: SigId) -> Option<SigId> {
        match s {
            SIG_UNIV | SIG_NONE => None,
            SIG_INT | SIG_STRING => Some(SIG_UNIV),
            SIG_SEQINT => Some(SIG_INT),
            _ => Some(self.model.sigs[s as usize].parent.unwrap_or(SIG_UNIV)),
        }
    }
    fn is_abstract(&self, s: SigId) -> bool {
        s > SIG_SEQINT && self.model.sigs[s as usize].is_abstract
    }
    /// `PrimSig.children()` (declaration order)
    fn children(&self, s: SigId) -> Vec<SigId> {
        (0..self.model.sigs.len() as SigId)
            .filter(|&c| {
                c > SIG_SEQINT
                    && self.model.sigs[c as usize].subset_of.is_empty()
                    && self.model.sigs[c as usize].parent == Some(s)
            })
            .collect()
    }
    /// `PrimSig.isSameOrDescendentOf`
    fn same_or_desc(&self, a: SigId, b: SigId) -> bool {
        if a == SIG_NONE || a == b || b == SIG_UNIV {
            return true;
        }
        if a == SIG_UNIV || b == SIG_NONE {
            return false;
        }
        let mut me = Some(a);
        while let Some(x) = me {
            if x == b {
                return true;
            }
            me = self.parent(x);
        }
        false
    }
    fn isect(&self, a: SigId, b: SigId) -> SigId {
        if self.same_or_desc(a, b) {
            a
        } else if self.same_or_desc(b, a) {
            b
        } else {
            SIG_NONE
        }
    }
    fn is_empty_pt(p: &[SigId]) -> bool {
        p.is_empty() || p[0] == SIG_NONE
    }
    fn subtype(&self, x: &[SigId], y: &[SigId]) -> bool {
        (0..x.len()).rev().all(|i| self.same_or_desc(x[i], y[i]))
    }
    /// `Type.add(entries, arities, x)`
    fn add(&self, ee: &mut Vec<Vec<SigId>>, x: Vec<SigId>) {
        if x.is_empty() {
            return;
        }
        let arity = x.len();
        let mut n = ee.len();
        let mut i = ee.len();
        while i > 0 {
            i -= 1;
            if ee[i].len() != arity {
                continue;
            }
            if self.subtype(&x, &ee[i]) {
                return;
            }
            if self.subtype(&ee[i], &x) {
                n -= 1;
                ee.swap(i, n);
                ee.truncate(n);
            }
        }
        ee.push(x);
    }
    pub fn make(&self, s: SigId) -> JType {
        JType {
            entries: vec![vec![s]],
        }
    }
    pub fn product(&self, a: &JType, b: &JType) -> JType {
        let mut ee = Vec::new();
        for x in &a.entries {
            for y in &b.entries {
                let n = x.len() + y.len();
                let p = if Self::is_empty_pt(x) || Self::is_empty_pt(y) {
                    vec![SIG_NONE; n]
                } else {
                    let mut v = x.clone();
                    v.extend(y.iter().copied());
                    v
                };
                self.add(&mut ee, p);
            }
        }
        JType { entries: ee }
    }
    /// `Type.unionWithCommonArity`
    pub fn union(&self, a: &JType, b: &JType) -> JType {
        let has = |t: &JType, n: usize| t.entries.iter().any(|e| e.len() == n);
        let mut ee = Vec::new();
        if !a.entries.is_empty() && !b.entries.is_empty() {
            for x in &a.entries {
                if has(b, x.len()) {
                    self.add(&mut ee, x.clone());
                }
            }
            for x in &b.entries {
                if has(a, x.len()) {
                    self.add(&mut ee, x.clone());
                }
            }
        }
        JType { entries: ee }
    }
    pub fn intersect(&self, a: &JType, b: &JType) -> JType {
        let mut ee = Vec::new();
        for x in &a.entries {
            for y in &b.entries {
                if x.len() == y.len() {
                    let p = if Self::is_empty_pt(x) {
                        x.clone()
                    } else if Self::is_empty_pt(y) {
                        y.clone()
                    } else {
                        let mut v: Vec<SigId> = x
                            .iter()
                            .zip(y.iter())
                            .map(|(&p, &q)| self.isect(p, q))
                            .collect();
                        if v.contains(&SIG_NONE) {
                            v = vec![SIG_NONE; x.len()];
                        }
                        v
                    };
                    self.add(&mut ee, p);
                }
            }
        }
        JType { entries: ee }
    }
    pub fn join(&self, a: &JType, b: &JType) -> JType {
        let mut ee = Vec::new();
        for x in &a.entries {
            for y in &b.entries {
                if x.len() > 1 || y.len() > 1 {
                    let n = x.len() + y.len() - 2;
                    let c = self.isect(*x.last().unwrap(), y[0]);
                    let p = if c == SIG_NONE {
                        vec![SIG_NONE; n]
                    } else {
                        let mut v = x[..x.len() - 1].to_vec();
                        v.extend(y[1..].iter().copied());
                        v
                    };
                    self.add(&mut ee, p);
                }
            }
        }
        JType { entries: ee }
    }
    pub fn transpose(&self, a: &JType) -> JType {
        let mut ee = Vec::new();
        for x in &a.entries {
            if x.len() == 2 {
                self.add(&mut ee, vec![x[1], x[0]]);
            }
        }
        JType { entries: ee }
    }
    pub fn closure(&self, a: &JType) -> JType {
        let mut ans = JType {
            entries: a.entries.iter().filter(|e| e.len() == 2).cloned().collect(),
        };
        let u = ans.clone();
        let mut uu = u.clone();
        loop {
            uu = self.join(&uu, &u);
            let old = ans.clone();
            ans = self.union(&ans, &uu);
            if old == ans {
                break;
            }
        }
        ans
    }
    /// `Type.fold()`
    pub fn fold(&self, t: &JType) -> Vec<Vec<SigId>> {
        let mut e: Vec<Vec<SigId>> = Vec::new();
        for xx in &t.entries {
            let mut x = xx.clone();
            loop {
                let n = x.len();
                let mut changed = false;
                let mut i: isize = 0;
                while (i as usize) < n {
                    let bt = x[i as usize];
                    if let Some(p) = self.parent(bt) {
                        if p != SIG_UNIV && self.is_abstract(p) {
                            if let Some(f) = self.fold1(&mut e, &x, i as usize) {
                                x = f;
                                changed = true;
                                i -= 1;
                            }
                        }
                    }
                    i += 1;
                }
                if !changed {
                    break;
                }
            }
            e.push(x);
        }
        e
    }
    fn fold1(&self, entries: &mut Vec<Vec<SigId>>, a: &[SigId], i: usize) -> Option<Vec<SigId>> {
        let parent = self.parent(a[i])?;
        let mut subs = self.children(parent);
        let mut to_delete: Vec<Vec<SigId>> = Vec::new();
        for bi in (0..entries.len()).rev() {
            let b = &entries[bi];
            if b.len() == a.len() {
                let mut ok = true;
                for j in 0..b.len() {
                    let (bt1, bt2) = (a[j], b[j]);
                    if i == j && self.parent(bt2) != Some(parent) {
                        ok = false;
                        break;
                    }
                    if i != j && bt2 != bt1 {
                        ok = false;
                        break;
                    }
                }
                if ok {
                    to_delete.push(b.clone());
                    if let Some(p) = subs.iter().position(|&s| s == b[i]) {
                        subs.remove(p);
                    }
                }
            }
        }
        if let Some(p) = subs.iter().position(|&s| s == a[i]) {
            subs.remove(p);
        }
        if !subs.is_empty() {
            return None;
        }
        entries.retain(|x| !to_delete.contains(x));
        if let Some(p) = entries.iter().position(|x| x == a) {
            entries.remove(p);
        }
        let mut v = a.to_vec();
        v[i] = parent;
        Some(v)
    }
}

mod bounds;
mod facts;
mod instance;
mod resolve;
mod simplify;
mod visit;

/// Java module paths (`CompModule.path`): root "", an opened instance `parent/alias` (first DFS visit).
pub fn java_paths(world: &alloy_core::World) -> Vec<String> {
    // Every instantiation of a module has the path `opener path/alias` (CompUtil.parseRecursively); merged
    // instantiations keep the smallest path by (contains '$', Util.slashComparator) (CompModule.resolveModules).
    let n = world.modules.len();
    if n == 0 {
        return Vec::new();
    }
    let mut cands: Vec<Vec<String>> = vec![Vec::new(); n];
    cands[0].push(String::new());
    // modules are loaded in pre-order, so an opener precedes what it opens; repeat until stable for safety
    for _ in 0..n {
        let mut changed = false;
        for m in 0..n {
            let prefixes = cands[m].clone();
            for o in &world.modules[m].opens {
                if o.target == 0 {
                    continue;
                }
                for pm in &prefixes {
                    let c = if pm.is_empty() { o.alias.clone() } else { format!("{pm}/{}", o.alias) };
                    if !cands[o.target].contains(&c) && cands[o.target].len() < 64 {
                        cands[o.target].push(c);
                        changed = true;
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }
    cands
        .into_iter()
        .enumerate()
        .map(|(i, c)| {
            if i == 0 {
                return String::new();
            }
            c.into_iter().min_by(|a, b| (a.contains('$'), 0).cmp(&(b.contains('$'), 0)).then_with(|| slash_cmp(a, b))).unwrap_or_default()
        })
        .collect()
}

/// Java `Util.slashComparator`.
pub fn slash_cmp(a: &str, b: &str) -> std::cmp::Ordering {
    use std::cmp::Ordering;
    if a == b {
        return Ordering::Equal;
    }
    for special in ["extends", "in"] {
        if a == special {
            return Ordering::Less;
        }
        if b == special {
            return Ordering::Greater;
        }
    }
    match (a.starts_with("this/"), b.starts_with("this/")) {
        (true, false) => return Ordering::Less,
        (false, true) => return Ordering::Greater,
        _ => {}
    }
    let (sa, sb) = (a.matches('/').count(), b.matches('/').count());
    if sa != sb {
        return sa.cmp(&sb);
    }
    let r = a.to_lowercase().cmp(&b.to_lowercase());
    if r != Ordering::Equal {
        return r;
    }
    a.cmp(b)
}

/// Java label of every sig of the model.
pub fn java_labels(world: &alloy_core::World, model: &Model) -> Vec<String> {
    let paths = java_paths(world);
    model
        .sigs
        .iter()
        .map(|s| {
            if s.kind != SigKind::User {
                return s.label.clone();
            }
            let p = paths.get(s.module).cloned().unwrap_or_default();
            if p.is_empty() {
                format!("this/{}", s.name)
            } else {
                format!("{p}/{}", s.name)
            }
        })
        .collect()
}

/// Builds the Kodkod problem Java Alloy would hand to `PardinusSolver.solveAll` for command `idx`.
pub use instance::{solve_first, ExactOutcome};

pub fn build(
    world: &alloy_core::World,
    model: &Model,
    idx: usize,
) -> Result<(Problem, ExactInfo), AlloyError> {
    let (cx, p) = prepare(world, model, idx)?;
    let info = ExactInfo {
        sig_expr: cx.a2k_sig.clone(),
        field_expr: cx.a2k_field.clone(),
        int_min: cx.min,
        int_max: cx.max,
        n_sig_atoms: cx.int_atom0,
        string_atoms: Vec::new(),
        var_types: cx.var_types.clone(),
    };
    Ok((p, info))
}

/// The Kodkod problem of a command (and the translation state, for the instance output).
fn prepare<'a>(
    world: &alloy_core::World,
    model: &'a Model,
    idx: usize,
) -> Result<(Cx<'a>, Problem), AlloyError> {
    if model.temporal {
        return Err(unsupported(
            "temporal models are not supported by the exact pipeline yet",
        ));
    }
    let cmd = model
        .commands
        .get(idx)
        .ok_or_else(|| fatal("no such command"))?;
    let expects = world.commands.get(idx).map(|c| c.expects).unwrap_or(-1);
    let labels = java_labels(world, model);
    let mut cx = Cx::new(model, cmd, labels)?;
    cx.compute_bounds()?;
    cx.make_facts()?;
    // A4Solution.solve: Simplifier (inferPartialInstance), then `r = r` for every relation, then Formula.and(formulas)
    if !cx.formulas.is_empty() && !cx.simplify() {
        let f = cx.ast.fls();
        cx.add_formula(f);
    }
    let rels = cx.bounds.relations();
    for r in rels {
        let f = cx.ast.eq(r, r);
        cx.formulas.push(f);
    }
    let fs = cx.formulas.clone();
    let goal = cx.ast.and_all(&fs);
    // A4Solution: symmetry 0 when the command expects 1 (an instance must exist)
    let options = KOptions {
        bitwidth: cx.bitwidth,
        symmetry: if expects == 1 { 0 } else { 20 },
        ..Default::default()
    };
    let ast = std::mem::take(&mut cx.ast);
    let bounds = std::mem::take(&mut cx.bounds);
    Ok((
        cx,
        Problem {
            ast,
            bounds,
            options,
            goal,
        },
    ))
}

// ================================================================================================ translation state

/// A translated Alloy expression (`visitThis` result): Kodkod formula, expression or int expression.
#[derive(Clone, Copy, Debug, PartialEq)]
enum V {
    F(N),
    E(N),
    I(N),
}

/// Information the instance output needs besides the problem itself.
pub struct ExactInfo {
    pub sig_expr: Vec<Option<N>>,
    pub field_expr: Vec<Option<N>>,
    pub int_min: i32,
    pub int_max: i32,
    pub n_sig_atoms: u32,
    pub string_atoms: Vec<String>,
    /// Kodkod variable -> Alloy type (A4Solution.decl2type) for skolem typing
    pub var_types: HashMap<N, JType>,
}

pub struct Cx<'a> {
    model: &'a Model,
    cmd: &'a RCommand,
    /// Java labels (`this/A`, `ord/Ord`) of every sig
    labels: Vec<String>,
    pub ast: Ast,
    pub bounds: Bounds,
    formulas: Vec<N>,
    a2k_sig: Vec<Option<N>>,
    a2k_field: Vec<Option<N>>,
    univ: N,
    kk_next: N,
    kk_zero: N,
    kk_seqidx: N,
    kk_string: N,
    s2k: HashMap<String, N>,
    lay: Layout,
    int_atom0: u32,
    min: i32,
    max: i32,
    bitwidth: i32,
    sigint: Vec<u32>,
    seqidx: Vec<u32>,
    strings: Vec<u32>,
    cnt: u32,
    env: Vec<(LocalId, V)>,
    /// macro parameters: the argument expression, translated again at every use (Java Macro.instantiate)
    lazy: Vec<(LocalId, RExpr)>,
    /// Kodkod variables with an Alloy type (A4Solution.decl2type)
    typed_vars: std::collections::HashSet<N>,
    current_function: Vec<FuncId>,
    const_cache: HashMap<FuncId, V>,
    ftypes: HashMap<FieldId, JType>,
    var_types: HashMap<N, JType>,
    /// reachable sigs in Java order (builtins excluded)
    sigs: Vec<SigId>,
    /// A4Solution.sigs: user sigs in addSig (allocation) order, used by makeFacts
    alloc_order: Vec<SigId>,
    /// atom-level types of the locals in scope (overload resolution)
    ltypes: Vec<(LocalId, kodkod::instance::TupleSet)>,
    ty_memo: Vec<Option<kodkod::instance::TupleSet>>,
    ub: HashMap<SigId, Vec<u32>>,
    lb: HashMap<SigId, Vec<u32>>,
}

fn ts(arity: u32, v: Vec<u32>) -> TupleSet {
    TupleSet::new(arity, v)
}

impl<'a> Cx<'a> {
    fn hier(&self) -> Hier<'a> {
        Hier { model: self.model }
    }
    fn is_user(&self, s: SigId) -> bool {
        self.model.sigs[s as usize].kind == SigKind::User
    }
    fn is_prim(&self, s: SigId) -> bool {
        !self.is_user(s) || self.model.sigs[s as usize].subset_of.is_empty()
    }
    fn is_top(&self, s: SigId) -> bool {
        self.is_user(s)
            && self.model.sigs[s as usize].subset_of.is_empty()
            && self.model.sigs[s as usize].parent.is_none()
    }
    fn is_one(&self, s: SigId) -> bool {
        self.is_user(s) && self.model.sigs[s as usize].mult == Some(AMult::One)
    }
    fn label(&self, s: SigId) -> &str {
        &self.labels[s as usize]
    }

    // ---------------------------------------------------------------- A4Solution helpers

    fn rel(&mut self, name: &str, arity: u32, var: bool) -> N {
        self.ast.add(Node::Rel(RelInfo {
            name: name.to_string(),
            arity,
            var,
            atom: false,
            skolem: false,
        }))
    }
    /// `addRel(label, lower, upper)` (`lower == None` = empty)
    fn add_rel(
        &mut self,
        label: &str,
        lower: Option<Vec<u32>>,
        upper: Vec<u32>,
        arity: u32,
        var: bool,
    ) -> N {
        let r = self.rel(label, arity, var);
        let lo = ts(arity, lower.unwrap_or_default());
        self.bounds.bound(r, lo, ts(arity, upper));
        r
    }
    fn add_formula(&mut self, f: N) {
        if let Some(&first) = self.formulas.first() {
            if matches!(self.ast.get(first), Node::ConstF(false)) {
                return;
            }
        }
        if matches!(self.ast.get(f), Node::ConstF(false)) {
            self.formulas.clear();
        }
        self.formulas.push(f);
    }
    fn add_sig(&mut self, s: SigId, e: N) {
        if self.a2k_sig[s as usize].is_some() {
            return;
        }
        self.a2k_sig[s as usize] = Some(e);
        self.alloc_order.push(s);
        if self.is_top(s) {
            let u = self.univ;
            self.univ = self.ast.union(u, e);
        }
    }
    fn a2k(&self, s: SigId) -> N {
        match s {
            SIG_UNIV => self.univ,
            _ => self.a2k_sig[s as usize].expect("sig not allocated"),
        }
    }
    /// `A4Solution.query(findUpper, expr, ...)`: atoms (tuple indices) of a bound expression.
    fn query(&self, upper: bool, e: N) -> Result<Vec<u32>, AlloyError> {
        let n = self.bounds.universe_size();
        Ok(match self.ast.get(e).clone() {
            Node::ConstE(ConstE::None) => Vec::new(),
            Node::ConstE(ConstE::Ints) => self.sigint.clone(),
            Node::Rel(_) => {
                if e == self.kk_seqidx {
                    return Ok(self.seqidx.clone());
                }
                if e == self.kk_string {
                    return Ok(self.strings.clone());
                }
                if let Some(&(_, lo, hi)) = self.bounds.symb.iter().find(|x| x.0 == e) {
                    return self.query(upper, if upper { hi } else { lo });
                }
                let t = if upper {
                    self.bounds.upper.get(&e)
                } else {
                    self.bounds.lower.get(&e)
                };
                t.map(|t| t.idx.clone()).ok_or_else(|| {
                    fatal("Unknown expression encountered during bounds computation")
                })?
            }
            Node::BinE(EOp::Union, a, b) => {
                let mut x = self.query(upper, a)?;
                x.extend(self.query(upper, b)?);
                x.sort_unstable();
                x.dedup();
                x
            }
            Node::BinE(EOp::Product, a, b) => {
                let ar = self.ast.arity(b);
                let xa = self.query(upper, a)?;
                let xb = self.query(upper, b)?;
                let m = n.pow(ar);
                let mut v = Vec::with_capacity(xa.len() * xb.len());
                for &p in &xa {
                    for &q in &xb {
                        v.push(p * m + q);
                    }
                }
                v.sort_unstable();
                v
            }
            _ => {
                return Err(fatal(
                    "Unknown expression encountered during bounds computation",
                ))
            }
        })
    }
}
