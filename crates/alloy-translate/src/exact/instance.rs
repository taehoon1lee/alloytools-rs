//! Port of the instance side of `A4Solution`: solving with SAT4J (`A4Solution.solve`), the Kodkod instance,
//! `rename` (atom names `Sig$i`, ordered along `next`/`prev` fields, `unused<i>`, skolems `$name`) and `eval`
//! of sigs/fields/skolems as printed by the oracle (`AlloyOracle.instanceJson`).

use super::*;
use pardinus::instance::TupleSet as PTs;
use std::collections::{BTreeMap, HashSet};
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

/// Result of the exact pipeline for one command.
pub struct ExactOutcome {
    pub sat: bool,
    /// First instance, one map per state (static problems: one): `this/Sig`, `this/Sig.field`, `skolem:$x` ->
    /// tuples of atom names (sorted like Java).
    pub instance: Option<Vec<BTreeMap<String, Vec<Vec<String>>>>>,
    /// temporal: the loop state of the lasso (-1 for static problems)
    pub loop_state: i32,
    pub primary_vars: i32,
    pub vars: i32,
    pub clauses: i64,
}

/// Java `UniqueNameGenerator`.
struct Unique(HashSet<String>);
impl Unique {
    fn make(&mut self, name: &str) -> String {
        let mut n = name.to_string();
        while !self.0.insert(n.clone()) {
            n.push('\'');
        }
        n
    }
}

fn tail_this(s: &str) -> &str {
    s.strip_prefix("this/").unwrap_or(s)
}

/// Clause counter in front of SAT4J (A4Reporter.solve statistics).
struct Counting<'s> {
    s: &'s mut satsolver::sat4j::Sat4j,
    clauses: i64,
}
impl pardinus::cnf::CnfSink for Counting<'_> {
    fn num_vars(&self) -> i32 {
        self.s.num_vars() as i32
    }
    fn add_variables(&mut self, n: i32) {
        self.s.add_variables(n as u32)
    }
    fn add_clause(&mut self, lits: &[i32]) {
        self.clauses += 1;
        self.s.add_clause(lits);
    }
}

/// `TranslateAlloyToKodkod.execute_command` + `A4Solution.solve` + the oracle's instance printer, exactly as Java.
pub fn solve_first(
    world: &alloy_core::World,
    model: &Model,
    idx: usize,
    symmetry: i32,
    stop: Option<Arc<AtomicBool>>,
) -> Result<ExactOutcome, AlloyError> {
    let (mut cx, mut p) = prepare(world, model, idx, symmetry)?;
    if p.options.temporal {
        let ts = pardinus::temporal::solve(&mut p, stop, false).map_err(fatal)?;
        let mut out = ExactOutcome {
            sat: ts.sat,
            instance: None,
            loop_state: ts.loop_state as i32,
            primary_vars: ts.primary_vars,
            vars: ts.vars,
            clauses: ts.clauses,
        };
        if !ts.sat {
            return Ok(out);
        }
        let skolems: Vec<N> = ts.skolems.iter().filter(|(s, _)| cx.typed_vars.contains(&s.var)).map(|(s, _)| s.relation).collect();
        let mut insts = ts.states.clone();
        for m in &mut insts {
            for (s, v) in &ts.skolems {
                m.insert(s.relation, v.clone());
            }
        }
        let n = p.bounds.universe_size();
        let mut ev = Eval { ast: &mut p.ast, insts: &insts, n, ints: &p.bounds.ints, bitwidth: p.options.bitwidth };
        out.instance = Some(cx.render(&mut ev, &skolems, &p.bounds.atoms)?);
        return Ok(out);
    }
    let mut solver = satsolver::sat4j::Sat4j::new();
    if let Some(f) = stop {
        solver.set_stop_flag(f);
    }
    let mut sink = Counting { s: &mut solver, clauses: 0 };
    let tr = pardinus::translator::translate(&mut p, &mut sink).map_err(fatal)?;
    let clauses = sink.clauses;
    let sat = match tr.trivial {
        Some(v) => v,
        None => solver.solve().ok_or_else(|| AlloyError::new(ErrorKind::Other, None, "solver interrupted".to_string()))?,
    };
    let mut out = ExactOutcome { sat, instance: None, loop_state: -1, primary_vars: tr.num_primary, vars: solver.num_vars() as i32, clauses };
    if !sat {
        return Ok(out);
    }
    let trivial = tr.trivial.is_some();
    let value = |v: i32| !trivial && v > 0 && solver.value_of(v as u32);
    let inst: HashMap<N, PTs> = tr.interpret(&value).into_iter().collect();
    // A4Solution's skolemizing reporter: a skolem gets a type (and is shown) only if its variable has one
    let skolems: Vec<N> = tr.skolems.iter().filter(|s| cx.typed_vars.contains(&s.var)).map(|s| s.relation).collect();
    let insts = vec![inst];
    let mut ev = Eval { ast: &mut p.ast, insts: &insts, n: p.bounds.universe_size(), ints: &p.bounds.ints, bitwidth: p.options.bitwidth };
    out.instance = Some(cx.render(&mut ev, &skolems, &p.bounds.atoms)?);
    Ok(out)
}

/// `Evaluator` over the solution instance (one relation valuation per state).
struct Eval<'e> {
    ast: &'e mut Ast,
    insts: &'e [HashMap<N, PTs>],
    n: u32,
    ints: &'e BTreeMap<i32, PTs>,
    bitwidth: i32,
}
impl Eval<'_> {
    fn eval(&self, e: N) -> Result<Vec<Vec<u32>>, AlloyError> {
        self.eval_at(e, 0)
    }
    /// `Evaluator.evaluate(expr, state)`
    fn eval_at(&self, e: N, st: usize) -> Result<Vec<Vec<u32>>, AlloyError> {
        let mut rels: Vec<N> = Vec::new();
        collect_rels(self.ast, e, &mut rels);
        let mut m = HashMap::new();
        for r in rels {
            let t = self.insts[st].get(&r).cloned().unwrap_or_else(|| PTs::new(self.ast.arity(r), Vec::new()));
            m.insert(r, t);
        }
        let t = pardinus::translator::evaluate(self.ast, e, self.n, m, self.ints, self.bitwidth).map_err(fatal)?;
        let ar = t.arity;
        Ok(t
            .idx
            .iter()
            .map(|&i| {
                let mut v = vec![0u32; ar as usize];
                let mut x = i;
                for k in (0..ar as usize).rev() {
                    v[k] = x % self.n;
                    x /= self.n;
                }
                v
            })
            .collect())
    }
}

fn collect_rels(ast: &Ast, e: N, out: &mut Vec<N>) {
    if let Node::Rel(_) = ast.get(e) {
        if !out.contains(&e) {
            out.push(e);
        }
        return;
    }
    for c in pardinus::annotate::children(ast, e) {
        collect_rels(ast, c, out);
    }
}

/// `A4Solution.isOrder`: the elements of `u` along the chain `b`, if `b` is a total order of `u`.
fn is_order(b: &[Vec<u32>], u: &[Vec<u32>]) -> Option<Vec<u32>> {
    let n = u.len();
    let mut list = Vec::with_capacity(n);
    if b.is_empty() && n <= 1 {
        return Some(list);
    }
    if b.len() + 1 != n {
        return None;
    }
    let right: HashSet<u32> = b.iter().map(|t| t[1]).collect();
    let mut head = u.iter().map(|t| t[0]).find(|x| !right.contains(x))?;
    list.push(head);
    let us: HashSet<u32> = u.iter().map(|t| t[0]).collect();
    loop {
        let next = b.iter().find(|t| t[0] == head).map(|t| t[1]);
        let Some(hn) = next else {
            return if list.len() == n { Some(list) } else { None };
        };
        if list.len() == n || !us.contains(&hn) {
            return None;
        }
        head = hn;
        list.push(head);
    }
}

impl<'a> Cx<'a> {
    /// `A4Solution.rename` then the oracle's `instanceJson` (one state).
    fn render(&mut self, ev: &mut Eval, skolems: &[N], atoms: &[String]) -> Result<Vec<BTreeMap<String, Vec<Vec<String>>>>, AlloyError> {
        let mut un = Unique(HashSet::new());
        let sigs = self.alloc_order.clone();
        // orders along `next`/`prev` fields
        let mut nexts: Vec<(SigId, Vec<u32>)> = Vec::new();
        for pass in ["next", "prev"] {
            for &s in &sigs {
                for f in self.model.sigs[s as usize].fields.clone() {
                    if !self.model.fields[f as usize].name.eq_ignore_ascii_case(pass) {
                        continue;
                    }
                    let Some(fe) = self.a2k_field[f as usize] else { continue };
                    let ft = self.field_type(f)?;
                    let fold = self.hier().fold(&ft);
                    if fold.len() != 1 {
                        continue;
                    }
                    let t = &fold[0];
                    let has = |x: SigId, v: &Vec<(SigId, Vec<u32>)>| v.iter().any(|(y, _)| *y == x);
                    let (elem, rel) = if t.len() == 3 && self.is_user(t[0]) && self.is_one(t[0]) && t[1] == t[2] && !has(t[1], &nexts) {
                        let j = ev.ast.join(self.a2k(t[0]), fe);
                        (t[1], j)
                    } else if t.len() == 2 && t[0] == t[1] && !has(t[0], &nexts) {
                        (t[0], fe)
                    } else {
                        continue;
                    };
                    if !self.is_user(elem) {
                        continue;
                    }
                    let set = ev.eval(self.a2k(elem))?;
                    if set.len() <= 1 {
                        continue;
                    }
                    let rel = if pass == "prev" { ev.ast.transpose(rel) } else { rel };
                    let next = ev.eval(rel)?;
                    if let Some(o) = is_order(&next, &set) {
                        nexts.push((elem, o));
                    }
                }
            }
        }
        // atom -> name
        let mut claimed: HashSet<u32> = HashSet::new();
        let mut name: HashMap<u32, String> = HashMap::new();
        for a in self.sigint.iter().chain(self.seqidx.iter()).chain(self.strings.iter()) {
            claimed.insert(*a);
        }
        for &s in &sigs {
            if self.is_prim(s) && self.is_top(s) {
                self.rename_sig(ev, s, &nexts, &mut un, &mut claimed, &mut name)?;
            }
        }
        let mut unused = 0;
        for a in 0..ev.n {
            if !claimed.contains(&a) {
                name.insert(a, format!("unused{unused}"));
                unused += 1;
            }
        }
        let atom_name = |a: u32| name.get(&a).cloned().unwrap_or_else(|| atoms[a as usize].clone());
        let render = |ts: Vec<Vec<u32>>| -> Vec<Vec<String>> {
            let mut v: Vec<(String, Vec<String>)> = ts
                .into_iter()
                .map(|t| {
                    let names: Vec<String> = t.iter().map(|&a| atom_name(a)).collect();
                    (json_tuple(&names), names)
                })
                .collect();
            v.sort_by(|a, b| java_cmp(&a.0, &b.0));
            v.into_iter().map(|(_, t)| t).collect()
        };
        let mut sk_labels = Vec::new();
        for &r in skolems {
            let n = match ev.ast.get(r) {
                Node::Rel(ri) => ri.name.clone(),
                _ => continue,
            };
            let n = tail_this(&n).trim_start_matches('$').to_string();
            sk_labels.push((r, un.make(&format!("${n}"))));
        }
        let mut states = Vec::new();
        for st in 0..ev.insts.len() {
            let mut out = BTreeMap::new();
            for &s in &sigs {
                let label = self.label(s).to_string();
                let se = self.a2k(s);
                out.insert(label.clone(), render(ev.eval_at(se, st)?));
                for f in self.model.sigs[s as usize].fields.clone() {
                    let Some(fe) = self.a2k_field[f as usize] else { continue };
                    let key = format!("{label}.{}", self.model.fields[f as usize].name);
                    out.insert(key, render(ev.eval_at(fe, st)?));
                }
            }
            for (r, label) in &sk_labels {
                out.insert(format!("skolem:{label}"), render(ev.eval_at(*r, st)?));
            }
            states.push(out);
        }
        Ok(states)
    }

    fn rename_sig(
        &mut self,
        ev: &mut Eval,
        s: SigId,
        nexts: &[(SigId, Vec<u32>)],
        un: &mut Unique,
        claimed: &mut HashSet<u32>,
        name: &mut HashMap<u32, String>,
    ) -> Result<(), AlloyError> {
        for c in self.hier().children(s) {
            self.rename_sig(ev, c, nexts, un, claimed, name)?;
        }
        let signame = un.make(tail_this(self.label(s)));
        let mut list: Vec<u32> = Vec::new();
        for st in 0..ev.insts.len() {
            list.extend(ev.eval_at(self.a2k(s), st)?.into_iter().map(|t| t[0]));
        }
        if let Some((_, order)) = nexts.iter().find(|(x, _)| *x == s) {
            if order.len() == list.len() && list.iter().all(|a| order.contains(a)) {
                list = order.clone();
            }
        }
        let mut i = 0;
        for a in list {
            if claimed.contains(&a) {
                continue;
            }
            claimed.insert(a);
            name.insert(a, format!("{signame}${i}"));
            i += 1;
        }
        Ok(())
    }
}

/// `Json.quote` of a tuple, as the oracle sorts them.
fn json_tuple(t: &[String]) -> String {
    let mut s = String::from("[");
    for (i, a) in t.iter().enumerate() {
        if i > 0 {
            s.push(',');
        }
        s.push('"');
        for c in a.chars() {
            match c {
                '"' => s.push_str("\\\""),
                '\\' => s.push_str("\\\\"),
                '\n' => s.push_str("\\n"),
                '\r' => s.push_str("\\r"),
                '\t' => s.push_str("\\t"),
                c if (c as u32) < 0x20 => s.push_str(&format!("\\u{:04x}", c as u32)),
                c => s.push(c),
            }
        }
        s.push('"');
    }
    s.push(']');
    s
}

/// `String.compareTo` (UTF-16 code units).
fn java_cmp(a: &str, b: &str) -> std::cmp::Ordering {
    a.encode_utf16().cmp(b.encode_utf16())
}
