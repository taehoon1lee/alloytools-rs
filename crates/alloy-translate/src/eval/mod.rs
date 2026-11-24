//! Independent Alloy AST evaluator and SAT instance/counterexample verifier.
//! Evaluates `alloy_core::sema::{Model, RExpr}` directly on [`TraceEnv`] without invoking the bounded-relational or SAT engine.

use alloy_core::error::AlloyError;
use alloy_core::sema::{
    FieldId, LocalId, Model, RExpr, SigKind, SIG_INT, SIG_NONE, SIG_SEQINT, SIG_STRING,
    SIG_UNIV,
};
use alloy_core::syntax::{BinOp, Const, Quant, UnOp};
use std::collections::{BTreeSet, HashMap, VecDeque};
use std::fmt;

use crate::{scope, Instance, Options};

pub(crate) mod expr;
pub(crate) mod temporal;
pub(crate) mod verify;

pub use expr::eval_expr;
pub use temporal::{expr_is_temporal, past_depth};
pub use verify::verify_instance;

/// Interned index of an atom inside [`Universe`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AtomIdx(pub u32);

/// Atom table of a command instance (`Int`, `String`, and model atoms).
#[derive(Debug, Clone)]
pub struct Universe {
    pub atoms: Vec<String>,
    pub by_name: HashMap<String, AtomIdx>,
    pub int_val: Vec<Option<i32>>,
    pub int_atom: HashMap<i32, AtomIdx>,
    pub str_atom: HashMap<String, AtomIdx>,
    pub min_int: i32,
    pub max_int: i32,
}

impl Universe {
    fn new(min_int: i32, max_int: i32) -> Self {
        Universe {
            atoms: Vec::new(),
            by_name: HashMap::new(),
            int_val: Vec::new(),
            int_atom: HashMap::new(),
            str_atom: HashMap::new(),
            min_int,
            max_int,
        }
    }

    pub fn intern(&mut self, name: &str) -> AtomIdx {
        if let Some(&idx) = self.by_name.get(name) {
            return idx;
        }
        let idx = AtomIdx(self.atoms.len() as u32);
        let parsed_int = name.parse::<i32>().ok().filter(|&v| v >= self.min_int && v <= self.max_int);
        self.atoms.push(name.to_string());
        self.by_name.insert(name.to_string(), idx);
        self.int_val.push(parsed_int);
        if let Some(v) = parsed_int {
            self.int_atom.entry(v).or_insert(idx);
        }
        if name.len() >= 2 && name.starts_with('"') && name.ends_with('"') {
            self.str_atom.entry(name[1..name.len() - 1].to_string()).or_insert(idx);
        }
        idx
    }

    pub fn atom_idx(&self, name: &str) -> Option<AtomIdx> {
        self.by_name.get(name).copied()
    }
}

/// Relation value with sorted, deduplicated tuples of uniform arity.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RelVal {
    pub arity: u32,
    pub tuples: Vec<Vec<AtomIdx>>,
}

impl RelVal {
    pub fn empty(arity: u32) -> Self {
        RelVal { arity, tuples: Vec::new() }
    }

    pub fn singleton(arity: u32, tuple: Vec<AtomIdx>) -> Self {
        debug_assert_eq!(tuple.len(), arity as usize);
        RelVal { arity, tuples: vec![tuple] }
    }

    pub fn from_tuples(arity: u32, mut tuples: Vec<Vec<AtomIdx>>) -> Self {
        for t in &tuples {
            debug_assert_eq!(t.len(), arity as usize);
        }
        tuples.sort();
        tuples.dedup();
        RelVal { arity, tuples }
    }

    pub fn is_empty(&self) -> bool {
        self.tuples.is_empty()
    }

    pub fn len(&self) -> usize {
        self.tuples.len()
    }

    pub fn contains(&self, t: &[AtomIdx]) -> bool {
        self.tuples.binary_search_by(|x| x.as_slice().cmp(t)).is_ok()
    }

    pub fn is_subset_of(&self, other: &Self) -> bool {
        if self.arity != other.arity {
            return false;
        }
        let (mut i, mut j) = (0, 0);
        while i < self.tuples.len() && j < other.tuples.len() {
            match self.tuples[i].cmp(&other.tuples[j]) {
                std::cmp::Ordering::Less => return false,
                std::cmp::Ordering::Equal => {
                    i += 1;
                    j += 1;
                }
                std::cmp::Ordering::Greater => j += 1,
            }
        }
        i == self.tuples.len()
    }

    pub fn is_disjoint(&self, other: &Self) -> bool {
        if self.arity != other.arity {
            return true;
        }
        let (mut i, mut j) = (0, 0);
        while i < self.tuples.len() && j < other.tuples.len() {
            match self.tuples[i].cmp(&other.tuples[j]) {
                std::cmp::Ordering::Less => i += 1,
                std::cmp::Ordering::Equal => return false,
                std::cmp::Ordering::Greater => j += 1,
            }
        }
        true
    }

    pub fn union(&self, other: &Self) -> Self {
        if self.tuples.is_empty() {
            return Self { arity: self.arity.max(other.arity), tuples: other.tuples.clone() };
        }
        if other.tuples.is_empty() {
            return self.clone();
        }
        let mut out = Vec::with_capacity(self.tuples.len() + other.tuples.len());
        let (mut i, mut j) = (0, 0);
        while i < self.tuples.len() && j < other.tuples.len() {
            match self.tuples[i].cmp(&other.tuples[j]) {
                std::cmp::Ordering::Less => {
                    out.push(self.tuples[i].clone());
                    i += 1;
                }
                std::cmp::Ordering::Equal => {
                    out.push(self.tuples[i].clone());
                    i += 1;
                    j += 1;
                }
                std::cmp::Ordering::Greater => {
                    out.push(other.tuples[j].clone());
                    j += 1;
                }
            }
        }
        out.extend_from_slice(&self.tuples[i..]);
        out.extend_from_slice(&other.tuples[j..]);
        RelVal { arity: self.arity, tuples: out }
    }

    pub fn intersect(&self, other: &Self) -> Self {
        let mut out = Vec::new();
        if self.arity != other.arity {
            return RelVal::empty(self.arity);
        }
        let (mut i, mut j) = (0, 0);
        while i < self.tuples.len() && j < other.tuples.len() {
            match self.tuples[i].cmp(&other.tuples[j]) {
                std::cmp::Ordering::Less => i += 1,
                std::cmp::Ordering::Equal => {
                    out.push(self.tuples[i].clone());
                    i += 1;
                    j += 1;
                }
                std::cmp::Ordering::Greater => j += 1,
            }
        }
        RelVal { arity: self.arity, tuples: out }
    }

    pub fn diff(&self, other: &Self) -> Self {
        if self.tuples.is_empty() || other.tuples.is_empty() || self.arity != other.arity {
            return self.clone();
        }
        let mut out = Vec::with_capacity(self.tuples.len());
        let (mut i, mut j) = (0, 0);
        while i < self.tuples.len() && j < other.tuples.len() {
            match self.tuples[i].cmp(&other.tuples[j]) {
                std::cmp::Ordering::Less => {
                    out.push(self.tuples[i].clone());
                    i += 1;
                }
                std::cmp::Ordering::Equal => {
                    i += 1;
                    j += 1;
                }
                std::cmp::Ordering::Greater => j += 1,
            }
        }
        out.extend_from_slice(&self.tuples[i..]);
        RelVal { arity: self.arity, tuples: out }
    }

    pub fn product(&self, other: &Self) -> Self {
        let ar = self.arity + other.arity;
        if self.tuples.is_empty() || other.tuples.is_empty() {
            return RelVal::empty(ar);
        }
        let mut out = Vec::with_capacity(self.tuples.len() * other.tuples.len());
        for a in &self.tuples {
            for b in &other.tuples {
                let mut t = Vec::with_capacity(ar as usize);
                t.extend_from_slice(a);
                t.extend_from_slice(b);
                out.push(t);
            }
        }
        RelVal { arity: ar, tuples: out }
    }

    pub fn join(&self, other: &Self) -> Result<Self, EvalError> {
        if self.arity + other.arity < 3 {
            return Err(EvalError::new(format!(
                "invalid join of arities {} and {}",
                self.arity, other.arity
            )));
        }
        let ar = self.arity + other.arity - 2;
        if self.tuples.is_empty() || other.tuples.is_empty() {
            return Ok(RelVal::empty(ar));
        }
        let mut by_first: HashMap<AtomIdx, Vec<&[AtomIdx]>> = HashMap::new();
        for b in &other.tuples {
            by_first.entry(b[0]).or_default().push(&b[1..]);
        }
        let mut out = Vec::new();
        for a in &self.tuples {
            let key = a[a.len() - 1];
            if let Some(matches) = by_first.get(&key) {
                let prefix = &a[..a.len() - 1];
                for suffix in matches {
                    let mut t = Vec::with_capacity(ar as usize);
                    t.extend_from_slice(prefix);
                    t.extend_from_slice(suffix);
                    out.push(t);
                }
            }
        }
        Ok(RelVal::from_tuples(ar, out))
    }

    pub fn domain_restrict(dom: &Self, rel: &Self) -> Self {
        if dom.arity != 1 || rel.arity < 1 || rel.tuples.is_empty() || dom.tuples.is_empty() {
            return RelVal::empty(rel.arity);
        }
        let mut out = Vec::new();
        for t in &rel.tuples {
            if dom.contains(&t[0..1]) {
                out.push(t.clone());
            }
        }
        RelVal { arity: rel.arity, tuples: out }
    }

    pub fn range_restrict(&self, rng: &Self) -> Self {
        if rng.arity != 1 || self.arity < 1 || self.tuples.is_empty() || rng.tuples.is_empty() {
            return RelVal::empty(self.arity);
        }
        let last = self.arity as usize - 1;
        let mut out = Vec::new();
        for t in &self.tuples {
            if rng.contains(&t[last..last + 1]) {
                out.push(t.clone());
            }
        }
        RelVal { arity: self.arity, tuples: out }
    }

    /// Relational override `a ++ b` (keeps all tuples of `b`, and tuples of `a` whose first atom `t[0]` is absent from `b`).
    pub fn override_(&self, other: &Self) -> Self {
        if other.tuples.is_empty() {
            return self.clone();
        }
        if self.tuples.is_empty() || self.arity < 1 {
            return other.clone();
        }
        let dom_b: BTreeSet<AtomIdx> = other.tuples.iter().map(|t| t[0]).collect();
        let mut out = other.tuples.clone();
        for t in &self.tuples {
            if !dom_b.contains(&t[0]) {
                out.push(t.clone());
            }
        }
        RelVal::from_tuples(self.arity, out)
    }

    pub fn transpose(&self) -> Result<Self, EvalError> {
        if self.arity != 2 {
            return Err(EvalError::new(format!("transpose of arity {}", self.arity)));
        }
        let out = self.tuples.iter().map(|t| vec![t[1], t[0]]).collect();
        Ok(RelVal::from_tuples(2, out))
    }

    pub fn closure(&self) -> Result<Self, EvalError> {
        if self.arity != 2 {
            return Err(EvalError::new(format!("closure of arity {}", self.arity)));
        }
        if self.tuples.is_empty() {
            return Ok(RelVal::empty(2));
        }
        let mut adj: HashMap<AtomIdx, Vec<AtomIdx>> = HashMap::new();
        let mut sources = BTreeSet::new();
        for t in &self.tuples {
            adj.entry(t[0]).or_default().push(t[1]);
            sources.insert(t[0]);
        }
        let mut out = Vec::new();
        let mut seen = BTreeSet::new();
        let mut q = VecDeque::new();
        for start in sources {
            seen.clear();
            q.clear();
            if let Some(nbrs) = adj.get(&start) {
                for &n in nbrs {
                    if seen.insert(n) {
                        q.push_back(n);
                    }
                }
            }
            while let Some(cur) = q.pop_front() {
                if let Some(nbrs) = adj.get(&cur) {
                    for &n in nbrs {
                        if seen.insert(n) {
                            q.push_back(n);
                        }
                    }
                }
            }
            for end in &seen {
                out.push(vec![start, *end]);
            }
        }
        Ok(RelVal::from_tuples(2, out))
    }

    pub fn refl_closure(&self, iden: &Self) -> Result<Self, EvalError> {
        Ok(self.closure()?.union(iden))
    }
}

/// Value returned by evaluating an Alloy `RExpr`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Value {
    Bool(bool),
    Rel(RelVal),
    Int(i32),
}

/// Relation valuation at a single trace state.
#[derive(Debug, Clone)]
pub struct StateValuation {
    pub sigs: Vec<RelVal>,
    pub fields: Vec<RelVal>,
    pub iden: RelVal,
    pub int_next: RelVal,
}

/// Complete trace environment constructed from an [`Instance`] and semantic [`Model`].
#[derive(Debug, Clone)]
pub struct TraceEnv {
    pub universe: Universe,
    pub states: Vec<StateValuation>,
    pub loop_state: Option<usize>,
    pub bitwidth: i32,
    pub maxseq: i32,
    pub no_overflow: bool,
    pub unrolls: i32,
    /// Raw `skolem:*` witness relations from state 0 (`skolem:$name` with or without leading `skolem:` kept in name).
    pub skolems: Vec<(String, Vec<Vec<AtomIdx>>)>,
    pub(crate) layout: scope::Layout,
}

#[derive(Debug, Clone)]
pub struct EvalError {
    pub message: String,
}

impl EvalError {
    pub fn new(message: impl Into<String>) -> Self {
        EvalError { message: message.into() }
    }
}

impl fmt::Display for EvalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for EvalError {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VerificationKind {
    ScopeViolation,
    SigHierarchyViolation,
    FieldDeclViolation,
    FactFailed,
    SigFactFailed,
    AssertionNotViolated,
    CommandFormulaFailed,
    EvalError,
}

#[derive(Debug, Clone)]
pub struct VerificationError {
    pub kind: VerificationKind,
    pub context: String,
    pub message: String,
}

impl VerificationError {
    pub fn new(kind: VerificationKind, context: impl Into<String>, message: impl Into<String>) -> Self {
        VerificationError {
            kind,
            context: context.into(),
            message: message.into(),
        }
    }
}

impl fmt::Display for VerificationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?} [{}]: {}", self.kind, self.context, self.message)
    }
}

impl std::error::Error for VerificationError {}

impl From<AlloyError> for EvalError {
    fn from(e: AlloyError) -> Self {
        EvalError::new(e.msg)
    }
}

impl From<EvalError> for VerificationError {
    fn from(e: EvalError) -> Self {
        VerificationError::new(VerificationKind::EvalError, "eval", e.message)
    }
}

/// Wraps a 64-bit signed value into signed `bitwidth` two's-complement range; also reports whether overflow occurred.
pub(crate) fn wrap_int(v: i64, bitwidth: i32) -> (i32, bool) {
    if bitwidth <= 0 {
        return (0, v != 0);
    }
    let min = -(1i64 << (bitwidth - 1));
    let max = (1i64 << (bitwidth - 1)) - 1;
    let of = v < min || v > max;
    let width = 1i64 << bitwidth;
    let u = v & (width - 1);
    let wrapped = if u >= (1i64 << (bitwidth - 1)) { u - width } else { u };
    (wrapped as i32, of)
}

/// Computes static relational arity of `f` directly from the semantic AST.
pub(crate) fn field_arity(model: &Model, f: FieldId) -> u32 {
    let mut visited = Vec::new();
    field_arity_rec(model, f, &mut visited)
}

fn field_arity_rec(model: &Model, f: FieldId, visited: &mut Vec<FieldId>) -> u32 {
    if visited.contains(&f) {
        return 2;
    }
    visited.push(f);
    let fd = &model.fields[f as usize];
    let mut locals = HashMap::new();
    locals.insert(fd.this_local, 1);
    let ar = 1 + expr_arity_rec(model, &fd.decl, &mut locals, visited, &mut Vec::new());
    visited.pop();
    ar
}

pub(crate) fn expr_arity(model: &Model, e: &RExpr) -> u32 {
    expr_arity_rec(model, e, &mut HashMap::new(), &mut Vec::new(), &mut Vec::new())
}

fn expr_arity_rec(
    model: &Model,
    e: &RExpr,
    locals: &mut HashMap<LocalId, u32>,
    visited_fields: &mut Vec<FieldId>,
    visited_funcs: &mut Vec<alloy_core::sema::FuncId>,
) -> u32 {
    match e {
        RExpr::Sig(_) | RExpr::Num(_) | RExpr::Str(_) => 1,
        RExpr::Field(f) => field_arity_rec(model, *f, visited_fields),
        RExpr::Local(l) => locals.get(l).copied().unwrap_or(1),
        RExpr::Const(Const::Iden | Const::IntNext) => 2,
        RExpr::Const(_) => 1,
        RExpr::Un(op, x) => match op {
            UnOp::Seq => 1 + expr_arity_rec(model, x, locals, visited_fields, visited_funcs),
            UnOp::IntCast | UnOp::SigInt | UnOp::Card | UnOp::Neg => 1,
            UnOp::Transpose | UnOp::Closure | UnOp::ReflClosure => 2,
            _ => expr_arity_rec(model, x, locals, visited_fields, visited_funcs),
        },
        RExpr::Bin(op, a, b) => match op {
            BinOp::Arrow(..) => {
                expr_arity_rec(model, a, locals, visited_fields, visited_funcs)
                    + expr_arity_rec(model, b, locals, visited_fields, visited_funcs)
            }
            BinOp::Join => {
                let aa = expr_arity_rec(model, a, locals, visited_fields, visited_funcs);
                let ba = expr_arity_rec(model, b, locals, visited_fields, visited_funcs);
                (aa + ba).saturating_sub(2).max(1)
            }
            BinOp::DomainRestrict => expr_arity_rec(model, b, locals, visited_fields, visited_funcs),
            BinOp::RangeRestrict => expr_arity_rec(model, a, locals, visited_fields, visited_funcs),
            _ => expr_arity_rec(model, a, locals, visited_fields, visited_funcs),
        },
        RExpr::Ite(_, a, _) => expr_arity_rec(model, a, locals, visited_fields, visited_funcs),
        RExpr::Let(bs, b) => {
            let mut old = Vec::with_capacity(bs.len());
            for (l, ex) in bs {
                let ar = expr_arity_rec(model, ex, locals, visited_fields, visited_funcs);
                old.push((*l, locals.insert(*l, ar)));
            }
            let r = expr_arity_rec(model, b, locals, visited_fields, visited_funcs);
            for (l, prev) in old.into_iter().rev() {
                match prev {
                    Some(v) => {
                        locals.insert(l, v);
                    }
                    None => {
                        locals.remove(&l);
                    }
                }
            }
            r
        }
        RExpr::Compr(ds, _) => {
            let mut sum = 0u32;
            for d in ds {
                let da = expr_arity_rec(model, &d.bound, locals, visited_fields, visited_funcs);
                for &v in &d.vars {
                    locals.insert(v, da);
                    sum += da;
                }
            }
            sum.max(1)
        }
        RExpr::Call(fid, _) => {
            if visited_funcs.contains(fid) {
                return 1;
            }
            visited_funcs.push(*fid);
            let func = &model.funcs[*fid as usize];
            let target = func.ret.as_ref().unwrap_or(&func.body);
            let mut callee_locals = HashMap::new();
            for (pl, pb) in &func.params {
                let pa = expr_arity_rec(model, pb, locals, visited_fields, visited_funcs);
                callee_locals.insert(*pl, pa);
            }
            let ar = expr_arity_rec(model, target, &mut callee_locals, visited_fields, visited_funcs);
            visited_funcs.pop();
            ar
        }
        RExpr::Block(items) if items.len() == 1 => {
            expr_arity_rec(model, &items[0], locals, visited_fields, visited_funcs)
        }
        RExpr::Choice(c) if !c.is_empty() => {
            expr_arity_rec(model, &c[0], locals, visited_fields, visited_funcs)
        }
        RExpr::Quant(Quant::Sum, _, _) => 1,
        _ => 1,
    }
}

impl TraceEnv {
    /// Builds a [`TraceEnv`] for command `cmd_idx` from an [`Instance`] and semantic [`Model`].
    pub fn from_instance(
        model: &Model,
        cmd_idx: usize,
        inst: &Instance,
        opt: &Options,
    ) -> Result<Self, VerificationError> {
        let cmd = model.commands.get(cmd_idx).ok_or_else(|| {
            VerificationError::new(
                VerificationKind::ScopeViolation,
                "command",
                format!("command index {cmd_idx} out of range ({})", model.commands.len()),
            )
        })?;
        let lay = scope::compute_scopes(model, cmd).map_err(|e| {
            VerificationError::new(VerificationKind::ScopeViolation, "scope", e.msg)
        })?;
        let bitwidth = cmd.bitwidth.unwrap_or(4);
        if !(0..=30).contains(&bitwidth) {
            return Err(VerificationError::new(
                VerificationKind::ScopeViolation,
                "bitwidth",
                format!("bitwidth {bitwidth} out of range 0..=30"),
            ));
        }
        let (min_int, max_int) = if bitwidth < 1 {
            (0, -1)
        } else {
            (-(1i32 << (bitwidth - 1)), (1i32 << (bitwidth - 1)) - 1)
        };
        let mut maxseq = match cmd.maxseq {
            Some(m) if m >= 0 => m,
            _ => cmd.overall.filter(|o| *o >= 0).unwrap_or(4).min(max_int),
        };
        if maxseq > max_int.max(0) {
            return Err(VerificationError::new(
                VerificationKind::ScopeViolation,
                "maxseq",
                format!("maxseq {maxseq} exceeds max int {max_int}"),
            ));
        }
        if maxseq < 0 {
            maxseq = 0;
        }
        if inst.states.is_empty() {
            return Err(VerificationError::new(
                VerificationKind::ScopeViolation,
                "states",
                "instance has zero states",
            ));
        }
        let loop_state = if model.temporal {
            if inst.loop_state < 0 || (inst.loop_state as usize) >= inst.states.len() {
                return Err(VerificationError::new(
                    VerificationKind::ScopeViolation,
                    "loop_state",
                    format!(
                        "invalid temporal loop_state {} for trace_length {}",
                        inst.loop_state,
                        inst.states.len()
                    ),
                ));
            }
            Some(inst.loop_state as usize)
        } else {
            if inst.loop_state != -1 || inst.states.len() != 1 {
                return Err(VerificationError::new(
                    VerificationKind::ScopeViolation,
                    "static_trace",
                    format!(
                        "static problem expected trace_length=1 loop_state=-1, got {} {}",
                        inst.states.len(),
                        inst.loop_state
                    ),
                ));
            }
            None
        };

        let mut universe = Universe::new(min_int, max_int);
        let mut int_atoms = Vec::new();
        let mut seq_atoms = Vec::new();
        if max_int >= min_int {
            for i in min_int..=max_int {
                let idx = universe.intern(&i.to_string());
                int_atoms.push(vec![idx]);
                if i >= 0 && i < maxseq {
                    seq_atoms.push(vec![idx]);
                }
            }
        }
        let mut base_str_atoms = Vec::new();
        for s in &lay.atoms[lay.string_range.0 as usize..lay.string_range.1 as usize] {
            let idx = universe.intern(s);
            base_str_atoms.push(vec![idx]);
        }
        let mut int_next_tuples = Vec::new();
        if max_int > min_int {
            for i in min_int..max_int {
                let a = universe.int_atom[&i];
                let b = universe.int_atom[&(i + 1)];
                int_next_tuples.push(vec![a, b]);
            }
        }
        let int_rel = RelVal::from_tuples(1, int_atoms);
        let seq_rel = RelVal::from_tuples(1, seq_atoms);
        let none_rel = RelVal::empty(1);
        let int_next_rel = RelVal::from_tuples(2, int_next_tuples);

        let f_arities: Vec<u32> = (0..model.fields.len() as FieldId)
            .map(|f| field_arity(model, f))
            .collect();

        // Intern all atoms mentioned in any state / skolem map first so string atoms are complete.
        for st in &inst.states {
            for tuples in st.values() {
                for t in tuples {
                    for name in t {
                        universe.intern(name);
                    }
                }
            }
        }

        let mut all_str_tuples = base_str_atoms;
        for (idx, a) in universe.atoms.iter().enumerate() {
            if a.len() >= 2 && a.starts_with('"') && a.ends_with('"') {
                all_str_tuples.push(vec![AtomIdx(idx as u32)]);
            }
        }
        let str_rel = RelVal::from_tuples(1, all_str_tuples);

        let mut states = Vec::with_capacity(inst.states.len());
        for (st_i, st_map) in inst.states.iter().enumerate() {
            let mut sigs = vec![RelVal::empty(1); model.sigs.len()];
            sigs[SIG_NONE as usize] = none_rel.clone();
            sigs[SIG_INT as usize] = int_rel.clone();
            sigs[SIG_SEQINT as usize] = seq_rel.clone();
            sigs[SIG_STRING as usize] = str_rel.clone();

            let mut univ_tuples = Vec::new();
            univ_tuples.extend(int_rel.tuples.iter().cloned());
            univ_tuples.extend(str_rel.tuples.iter().cloned());

            for (sid, sig) in model.sigs.iter().enumerate() {
                if sig.kind != SigKind::User {
                    continue;
                }
                let raw = st_map.get(&sig.label).ok_or_else(|| {
                    VerificationError::new(
                        VerificationKind::ScopeViolation,
                        &sig.label,
                        format!("missing sig '{}' in state {st_i}", sig.label),
                    )
                })?;
                let mut tuples = Vec::with_capacity(raw.len());
                for t in raw {
                    if t.len() != 1 {
                        return Err(VerificationError::new(
                            VerificationKind::ScopeViolation,
                            &sig.label,
                            format!("sig '{}' tuple {:?} has arity {} != 1", sig.label, t, t.len()),
                        ));
                    }
                    let idx = universe.atom_idx(&t[0]).ok_or_else(|| {
                        VerificationError::new(
                            VerificationKind::ScopeViolation,
                            &sig.label,
                            format!("unknown atom {}", t[0]),
                        )
                    })?;
                    tuples.push(vec![idx]);
                }
                let rv = RelVal::from_tuples(1, tuples);
                if sig.parent.is_none() && sig.subset_of.is_empty() {
                    univ_tuples.extend(rv.tuples.iter().cloned());
                }
                sigs[sid] = rv;
            }
            sigs[SIG_UNIV as usize] = RelVal::from_tuples(1, univ_tuples);
            let iden = RelVal::from_tuples(
                2,
                sigs[SIG_UNIV as usize]
                    .tuples
                    .iter()
                    .map(|t| vec![t[0], t[0]])
                    .collect(),
            );

            let mut fields = Vec::with_capacity(model.fields.len());
            for (fid, fld) in model.fields.iter().enumerate() {
                let arity = f_arities[fid];
                let raw = st_map.get(&fld.label).ok_or_else(|| {
                    VerificationError::new(
                        VerificationKind::ScopeViolation,
                        &fld.label,
                        format!("missing field '{}' in state {st_i}", fld.label),
                    )
                })?;
                let mut tuples = Vec::with_capacity(raw.len());
                for t in raw {
                    if t.len() != arity as usize {
                        return Err(VerificationError::new(
                            VerificationKind::FieldDeclViolation,
                            &fld.label,
                            format!(
                                "field '{}' tuple {:?} has arity {} != {arity}",
                                fld.label,
                                t,
                                t.len()
                            ),
                        ));
                    }
                    let row = t
                        .iter()
                        .map(|a| {
                            universe.atom_idx(a).ok_or_else(|| {
                                VerificationError::new(
                                    VerificationKind::FieldDeclViolation,
                                    &fld.label,
                                    format!("unknown atom {a}"),
                                )
                            })
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    tuples.push(row);
                }
                fields.push(RelVal::from_tuples(arity, tuples));
            }
            states.push(StateValuation {
                sigs,
                fields,
                iden,
                int_next: int_next_rel.clone(),
            });
        }

        let mut skolems = Vec::new();
        for (k, raw) in &inst.states[0] {
            if let Some(sk) = k.strip_prefix("skolem:") {
                let tuples = raw
                    .iter()
                    .map(|t| t.iter().filter_map(|a| universe.atom_idx(a)).collect())
                    .collect();
                skolems.push((sk.to_string(), tuples));
            }
        }

        Ok(TraceEnv {
            universe,
            states,
            loop_state,
            bitwidth,
            maxseq,
            no_overflow: opt.no_overflow,
            unrolls: opt.unrolls,
            skolems,
            layout: lay,
        })
    }
}
