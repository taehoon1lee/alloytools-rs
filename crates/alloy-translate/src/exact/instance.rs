//! Port of the instance side of `A4Solution`: solving with `pardinus` + `BatSat`, the Kodkod instance,
//! `rename` (atom names `Sig$i`, ordered along `next`/`prev` fields, `unused<i>`, skolems `$name`) and `eval`
//! of sigs/fields/skolems as printed by the oracle (`AlloyOracle.instanceJson`).

use super::*;
use pardinus::instance::TupleSet as PTs;
use crate::xml::{XmlData, XmlField, XmlSig, XmlSkolem, XmlState};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::sync::atomic::AtomicBool;
use std::sync::Arc;
use std::time::Instant;

/// Result of solving a command via the unified `pardinus` + `BatSat` pipeline.
pub struct ExactOutcome {
    pub sat: bool,
    pub temporal: bool,
    pub min_trace: i32,
    pub max_trace: i32,
    pub translate_ms: f64,
    pub solve_ms: f64,
    /// First instance, one map per state (static problems: one): `this/Sig`, `this/Sig.field`, `skolem:$x` ->
    /// tuples of atom names (sorted like Java).
    pub instance: Option<Vec<BTreeMap<String, Vec<Vec<String>>>>>,
    /// temporal: the loop state of the lasso (-1 for static problems)
    pub loop_state: i32,
    pub primary_vars: i32,
    pub vars: i32,
    pub clauses: i64,
    pub xml_data: Option<XmlData>,
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

/// `TranslateAlloyToKodkod.execute_command` + `A4Solution.solve` + the oracle's instance printer.
pub fn solve_first(
    world: &alloy_core::World,
    model: &Model,
    idx: usize,
    opt: &crate::Options,
    stop: Option<Arc<AtomicBool>>,
) -> Result<ExactOutcome, AlloyError> {
    let t0 = Instant::now();
    let (mut cx, mut p) = prepare(world, model, idx, opt)?;
    let prep_ms = t0.elapsed().as_secs_f64() * 1000.0;
    p.options.stop = stop.clone();
    if p.options.temporal {
        let ts = pardinus::temporal::solve(&mut p, stop, false).map_err(fatal)?;
        let mut out = ExactOutcome {
            sat: ts.sat,
            temporal: true,
            min_trace: p.options.min_trace,
            max_trace: p.options.max_trace,
            translate_ms: prep_ms + ts.translate_ms,
            solve_ms: ts.solve_ms,
            instance: None,
            loop_state: if ts.sat { ts.loop_state as i32 } else { -1 },
            primary_vars: ts.primary_vars,
            vars: ts.vars,
            clauses: ts.clauses,
            xml_data: None,
        };
        if !ts.sat || (!opt.want_instance && !opt.want_xml) {
            return Ok(out);
        }
        let skolems: Vec<(N, N)> = ts.skolems.iter().filter(|(s, _)| cx.typed_vars.contains(&s.var)).map(|(s, _)| (s.var, s.relation)).collect();
        let mut insts = ts.states.clone();
        for m in &mut insts {
            for (s, v) in &ts.skolems {
                m.insert(s.relation, v.clone());
            }
        }
        let n = p.bounds.universe_size();
        let mut ev = Eval { ast: &mut p.ast, insts: &insts, n, ints: &p.bounds.ints, bitwidth: p.options.bitwidth };
        let (rendered, xml_data) = cx.render(&mut ev, &skolems, &p.bounds, opt.want_xml.then(|| XmlMeta {
            min_trace: out.min_trace,
            max_trace: out.max_trace,
            loop_state: out.loop_state,
            world,
            cmd_idx: idx,
        }))?;
        if opt.want_instance {
            out.instance = Some(rendered);
        }
        out.xml_data = xml_data;
        return Ok(out);
    }
    let solved = pardinus::translator::solve_portfolio(&mut p).map_err(fatal)?;
    let mut out = ExactOutcome {
        sat: solved.sat,
        temporal: false,
        min_trace: -1,
        max_trace: -1,
        translate_ms: prep_ms + solved.translate_ms,
        solve_ms: solved.solve_ms,
        instance: None,
        loop_state: -1,
        primary_vars: solved.translation.num_primary,
        vars: solved.vars,
        clauses: solved.clauses,
        xml_data: None,
    };
    if !solved.sat || (!opt.want_instance && !opt.want_xml) {
        return Ok(out);
    }
    let trivial = solved.translation.trivial.is_some();
    let value = |v: i32| !trivial && v > 0 && *solved.model.get(v as usize).unwrap_or(&false);
    let inst: HashMap<N, PTs> = solved.translation.interpret(&value).into_iter().collect();
    // A4Solution's skolemizing reporter: a skolem gets a type (and is shown) only if its variable has one
    let skolems: Vec<(N, N)> = solved.translation.skolems.iter().filter(|s| cx.typed_vars.contains(&s.var)).map(|s| (s.var, s.relation)).collect();
    let insts = vec![inst];
    let mut ev = Eval { ast: &mut p.ast, insts: &insts, n: p.bounds.universe_size(), ints: &p.bounds.ints, bitwidth: p.options.bitwidth };
    let (rendered, xml_data) = cx.render(&mut ev, &skolems, &p.bounds, opt.want_xml.then(|| XmlMeta {
        min_trace: -1,
        max_trace: -1,
        loop_state: 0,
        world,
        cmd_idx: idx,
    }))?;
    if opt.want_instance {
        out.instance = Some(rendered);
    }
    out.xml_data = xml_data;
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

struct XmlMeta<'w> {
    min_trace: i32,
    max_trace: i32,
    loop_state: i32,
    world: &'w alloy_core::World,
    cmd_idx: usize,
}

fn decode_tuple_idx(mut x: u32, arity: u32, n: u32) -> Vec<u32> {
    let mut v = vec![0u32; arity as usize];
    for k in (0..arity as usize).rev() {
        v[k] = x % n;
        x /= n;
    }
    v
}

impl<'a> Cx<'a> {
    /// `A4Solution.rename` then the oracle's `instanceJson` (one state) and optional XML data.
    fn render(
        &mut self,
        ev: &mut Eval,
        skolems: &[(N, N)],
        bounds: &Bounds,
        xml_meta: Option<XmlMeta<'_>>,
    ) -> Result<(Vec<BTreeMap<String, Vec<Vec<String>>>>, Option<XmlData>), AlloyError> {
        let atoms = &bounds.atoms;
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
        let mut sk_labels: Vec<(N, N, String)> = Vec::new();
        for &(sk_var, sk_rel) in skolems {
            let n = match ev.ast.get(sk_rel) {
                Node::Rel(ri) => ri.name.clone(),
                _ => continue,
            };
            let n = tail_this(&n).trim_start_matches('$').to_string();
            sk_labels.push((sk_var, sk_rel, un.make(&format!("${n}"))));
        }
        let mut states = Vec::with_capacity(ev.insts.len());
        let mut raw_sig_states: Vec<Vec<Vec<u32>>> = if xml_meta.is_some() { Vec::with_capacity(ev.insts.len()) } else { Vec::new() };
        let mut raw_field_states: Vec<Vec<Vec<Vec<u32>>>> = if xml_meta.is_some() { Vec::with_capacity(ev.insts.len()) } else { Vec::new() };
        let mut raw_sk_states: Vec<Vec<Vec<Vec<u32>>>> = if xml_meta.is_some() { Vec::with_capacity(ev.insts.len()) } else { Vec::new() };

        for st in 0..ev.insts.len() {
            let mut out = BTreeMap::new();
            let collect_raw = xml_meta.is_some();
            let mut st_sigs = if collect_raw { vec![Vec::new(); self.model.sigs.len()] } else { Vec::new() };
            let mut st_fields = if collect_raw { vec![Vec::new(); self.model.fields.len()] } else { Vec::new() };
            for &s in &sigs {
                let label = self.label(s).to_string();
                let se = self.a2k(s);
                let raw_s = ev.eval_at(se, st)?;
                if collect_raw {
                    st_sigs[s as usize] = raw_s.iter().map(|t| t[0]).collect();
                }
                out.insert(label.clone(), render(raw_s));
                for f in self.model.sigs[s as usize].fields.clone() {
                    let Some(fe) = self.a2k_field[f as usize] else { continue };
                    let key = format!("{label}.{}", self.model.fields[f as usize].name);
                    let raw_f = ev.eval_at(fe, st)?;
                    if collect_raw {
                        st_fields[f as usize] = raw_f.clone();
                    }
                    out.insert(key, render(raw_f));
                }
            }
            let mut st_sk = if collect_raw { Vec::with_capacity(sk_labels.len()) } else { Vec::new() };
            for &(sk_var, sk_rel, ref label) in &sk_labels {
                let _ = sk_var;
                let raw_k = ev.eval_at(sk_rel, st)?;
                if collect_raw {
                    st_sk.push(raw_k.clone());
                }
                out.insert(format!("skolem:{label}"), render(raw_k));
            }
            if collect_raw {
                raw_sig_states.push(st_sigs);
                raw_field_states.push(st_fields);
                raw_sk_states.push(st_sk);
            }
            states.push(out);
        }

        let xml_data = if let Some(meta) = xml_meta {
            Some(self.build_xml_data(
                ev,
                bounds,
                &atom_name,
                &render,
                &sk_labels,
                &raw_sig_states,
                &raw_field_states,
                &raw_sk_states,
                &states,
                meta,
            )?)
        } else {
            None
        };
        Ok((states, xml_data))
    }

    #[allow(clippy::too_many_arguments)]
    fn build_xml_data(
        &mut self,
        ev: &Eval,
        bounds: &Bounds,
        atom_name: &dyn Fn(u32) -> String,
        render: &dyn Fn(Vec<Vec<u32>>) -> Vec<Vec<String>>,
        sk_labels: &[(N, N, String)],
        raw_sig_states: &[Vec<Vec<u32>>],
        raw_field_states: &[Vec<Vec<Vec<u32>>>],
        raw_sk_states: &[Vec<Vec<Vec<u32>>>],
        rendered_states: &[BTreeMap<String, Vec<Vec<String>>>],
        meta: XmlMeta<'_>,
    ) -> Result<XmlData, AlloyError> {
        let n_sigs = self.model.sigs.len();
        let n_fields = self.model.fields.len();
        let n_states = ev.insts.len();

        let seqidx_set: HashSet<u32> = self.seqidx.iter().copied().collect();
        let sigint_set: HashSet<u32> = self.sigint.iter().copied().collect();
        let string_set: HashSet<u32> = self.strings.iter().copied().collect();

        let mut direct_prim_children: Vec<Vec<SigId>> = vec![Vec::new(); n_sigs];
        for (sid, s) in self.model.sigs.iter().enumerate() {
            if s.kind == SigKind::User && s.subset_of.is_empty() {
                if let Some(p) = s.parent {
                    direct_prim_children[p as usize].push(sid as SigId);
                }
            }
        }

        let mut global_atom_prim: HashMap<u32, SigId> = HashMap::new();
        for &a in &self.sigint {
            global_atom_prim.insert(a, SIG_INT);
        }
        for &a in &self.seqidx {
            global_atom_prim.insert(a, SIG_SEQINT);
        }
        for &a in &self.strings {
            global_atom_prim.insert(a, SIG_STRING);
        }

        let mut xml_states = Vec::with_capacity(n_states);
        let mut atom_prim_per_state: Vec<HashMap<u32, SigId>> = Vec::with_capacity(n_states);
        let string_atoms_rendered: Vec<String> = render(self.strings.iter().map(|&a| vec![a]).collect())
            .into_iter()
            .map(|mut t| t.pop().unwrap())
            .collect();

        for st in 0..n_states {
            let mut sig_direct_atoms = vec![Vec::new(); n_sigs];
            sig_direct_atoms[SIG_STRING as usize] = string_atoms_rendered.clone();
            let mut state_atom_prim = HashMap::new();

            for (sid, s) in self.model.sigs.iter().enumerate() {
                if s.kind != SigKind::User {
                    continue;
                }
                let raw = &raw_sig_states[st][sid];
                if s.subset_of.is_empty() {
                    let mut child_atoms = HashSet::new();
                    for &c in &direct_prim_children[sid] {
                        for &a in &raw_sig_states[st][c as usize] {
                            child_atoms.insert(a);
                        }
                    }
                    let mut direct_u32 = Vec::new();
                    for &a in raw {
                        if !child_atoms.contains(&a) {
                            direct_u32.push(vec![a]);
                            state_atom_prim.insert(a, sid as SigId);
                            global_atom_prim.entry(a).or_insert(sid as SigId);
                        }
                    }
                    sig_direct_atoms[sid] = render(direct_u32).into_iter().map(|mut t| t.pop().unwrap()).collect();
                } else {
                    sig_direct_atoms[sid] = render(raw.iter().map(|&a| vec![a]).collect())
                        .into_iter()
                        .map(|mut t| t.pop().unwrap())
                        .collect();
                }
            }
            atom_prim_per_state.push(state_atom_prim);

            let mut field_tuples = vec![Vec::new(); n_fields];
            for (fid, fld) in self.model.fields.iter().enumerate() {
                let key = format!("{}.{}", self.label(fld.owner), fld.name);
                if let Some(v) = rendered_states[st].get(&key) {
                    field_tuples[fid] = v.clone();
                }
            }

            let mut skolem_tuples = Vec::with_capacity(sk_labels.len());
            for (_, _, label) in sk_labels {
                let key = format!("skolem:{label}");
                skolem_tuples.push(rendered_states[st].get(&key).cloned().unwrap_or_default());
            }

            xml_states.push(XmlState {
                sig_direct_atoms,
                field_tuples,
                skolem_tuples,
            });
        }

        let atom_prim = |a: u32, st: Option<usize>| -> SigId {
            if seqidx_set.contains(&a) {
                return SIG_SEQINT;
            }
            if sigint_set.contains(&a) {
                return SIG_INT;
            }
            if string_set.contains(&a) {
                return SIG_STRING;
            }
            if let Some(st_i) = st {
                if let Some(&s) = atom_prim_per_state[st_i].get(&a) {
                    return s;
                }
            }
            global_atom_prim.get(&a).copied().unwrap_or(SIG_UNIV)
        };

        let mut fields = Vec::with_capacity(n_fields);
        for fid in 0..n_fields {
            let f = fid as FieldId;
            let mut jt = self.field_type(f)?;
            let h = self.hier();
            let mut seen_rows: HashSet<Vec<SigId>> = HashSet::new();
            for st in 0..n_states {
                for tup in &raw_field_states[st][fid] {
                    let sig_row: Vec<SigId> = tup.iter().map(|&a| atom_prim(a, Some(st))).collect();
                    if seen_rows.insert(sig_row.clone()) {
                        h.add(&mut jt.entries, sig_row);
                    }
                }
            }
            let types: Vec<Vec<SigId>> = h
                .fold(&jt)
                .into_iter()
                .filter(|r| !r.is_empty() && !r.contains(&SIG_NONE))
                .collect();
            let fld = &self.model.fields[fid];
            fields.push(XmlField {
                id: f,
                label: fld.name.clone(),
                owner: fld.owner,
                is_private: fld.is_private,
                is_var: fld.is_var,
                types,
            });
        }

        let mut xml_skolems = Vec::with_capacity(sk_labels.len());
        let h = self.hier();
        for (ki, &(sk_var, sk_rel, ref label)) in sk_labels.iter().enumerate() {
            let ar = ev.ast.arity(sk_rel);
            let mut jt = self
                .var_types
                .get(&sk_var)
                .filter(|t| t.entries.iter().any(|r| r.len() == ar as usize))
                .cloned()
                .unwrap_or_default();
            let mut seen_rows: HashSet<Vec<SigId>> = HashSet::new();
            if let Some(ub) = bounds.upper.get(&sk_rel) {
                for &idx_u in &ub.idx {
                    let tup = decode_tuple_idx(idx_u, ub.arity, ev.n);
                    let sig_row: Vec<SigId> = tup.iter().map(|&a| atom_prim(a, None)).collect();
                    if seen_rows.insert(sig_row.clone()) {
                        h.add(&mut jt.entries, sig_row);
                    }
                }
            }
            for st in 0..n_states {
                for tup in &raw_sk_states[st][ki] {
                    let sig_row: Vec<SigId> = tup.iter().map(|&a| atom_prim(a, Some(st))).collect();
                    if seen_rows.insert(sig_row.clone()) {
                        h.add(&mut jt.entries, sig_row);
                    }
                }
            }
            let mut types: Vec<Vec<SigId>> = h
                .fold(&jt)
                .into_iter()
                .filter(|r| !r.is_empty() && !r.contains(&SIG_NONE))
                .collect();
            if types.is_empty() && ar > 0 {
                types.push(vec![SIG_UNIV; ar as usize]);
            }
            xml_skolems.push(XmlSkolem {
                label: label.clone(),
                types,
            });
        }

        let _ = atom_name;
        let mut xml_sigs = Vec::with_capacity(n_sigs);
        for (sid, s) in self.model.sigs.iter().enumerate() {
            let id = sid as SigId;
            let builtin = s.kind == SigKind::Builtin;
            let label = if builtin { s.label.clone() } else { self.label(id).to_string() };
            let parent = match id {
                SIG_UNIV | SIG_NONE => None,
                SIG_INT | SIG_STRING => Some(SIG_UNIV),
                SIG_SEQINT => Some(SIG_INT),
                _ if !s.subset_of.is_empty() => None,
                _ => s.parent,
            };
            xml_sigs.push(XmlSig {
                id,
                label,
                parent,
                subset_of: s.subset_of.clone(),
                builtin,
                is_abstract: s.is_abstract,
                mult: s.mult,
                is_private: s.is_private,
                is_exact: s.is_exact,
                is_enum: s.is_enum,
                is_var: s.is_var,
                fields: s.fields.clone(),
            });
        }

        let command = meta
            .world
            .commands
            .get(meta.cmd_idx)
            .map_or_else(String::new, |c| c.scope_string.clone());
        let filename = meta
            .world
            .modules
            .first()
            .map_or_else(String::new, |m| m.path.clone());
        let mut sources = BTreeMap::new();
        for m in &meta.world.modules {
            sources.entry(m.path.clone()).or_insert_with(|| m.source.clone());
        }

        Ok(XmlData {
            bitwidth: self.bitwidth,
            maxseq: self.maxseq,
            min_trace: meta.min_trace,
            max_trace: meta.max_trace,
            trace_length: n_states as i32,
            loop_state: meta.loop_state,
            command,
            filename,
            sigs: xml_sigs,
            fields,
            skolems: xml_skolems,
            states: xml_states,
            sources,
        })
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
