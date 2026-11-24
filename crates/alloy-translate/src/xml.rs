//! Port of `edu.mit.csail.sdg.translator.A4SolutionWriter` and `Util.encodeXML`.
//! Emits Java Alloy 6.2.0 compatible `.xml` files for static and temporal SAT instances
//! as well as metamodel descriptors.

use crate::exact::{Hier, JType};
use alloy_core::sema::{
    FieldId, LocalId, Model, RExpr, SigId, SigKind, SIG_INT, SIG_NONE, SIG_SEQINT, SIG_STRING,
    SIG_UNIV,
};
use alloy_core::syntax::{BinOp, Const, Mult, UnOp};
use std::collections::{BTreeMap, HashMap};
use std::fmt::Write as _;

/// Complete Alloy solution metadata & state valuations needed for `A4SolutionWriter` XML output.
#[derive(Debug, Clone)]
pub struct XmlData {
    pub bitwidth: i32,
    pub maxseq: i32,
    pub min_trace: i32,
    pub max_trace: i32,
    pub trace_length: i32,
    /// `0` for static solutions (matching Java `looplength = 1 - 0 = 1`), `0..trace_length` for temporal.
    pub loop_state: i32,
    pub command: String,
    pub filename: String,
    /// Indexed by `SigId`.
    pub sigs: Vec<XmlSig>,
    /// Indexed by `FieldId`.
    pub fields: Vec<XmlField>,
    pub skolems: Vec<XmlSkolem>,
    pub states: Vec<XmlState>,
    /// Loaded module path -> source text for `<source>` elements.
    pub sources: BTreeMap<String, String>,
}

#[derive(Debug, Clone)]
pub struct XmlSig {
    pub id: SigId,
    pub label: String,
    pub parent: Option<SigId>,
    pub subset_of: Vec<SigId>,
    pub builtin: bool,
    pub is_abstract: bool,
    pub mult: Option<Mult>,
    pub is_private: bool,
    pub is_exact: bool,
    pub is_enum: bool,
    pub is_var: bool,
    pub fields: Vec<FieldId>,
}

#[derive(Debug, Clone)]
pub struct XmlField {
    pub id: FieldId,
    /// Short field name (`fld.name`), matching Java `Field.label`.
    pub label: String,
    pub owner: SigId,
    pub is_private: bool,
    pub is_var: bool,
    /// Folded `PrimSig` product types (`Type.fold()`). Empty skips emission.
    pub types: Vec<Vec<SigId>>,
}

#[derive(Debug, Clone)]
pub struct XmlSkolem {
    /// Skolem name starting with `$`.
    pub label: String,
    /// Folded `PrimSig` product types.
    pub types: Vec<Vec<SigId>>,
}

#[derive(Debug, Clone)]
pub struct XmlState {
    /// Direct atoms per `SigId` (`ts.minus(ts2)` for PrimSigs; empty for `UNIV`/`Int`/`seq/Int`).
    pub sig_direct_atoms: Vec<Vec<String>>,
    /// Tuple list per `FieldId`.
    pub field_tuples: Vec<Vec<Vec<String>>>,
    /// Tuple list per skolem index.
    pub skolem_tuples: Vec<Vec<Vec<String>>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum XmlObj {
    Sig(SigId),
    Field(FieldId),
    Skolem(usize),
}

struct XmlIds {
    next: usize,
    map: HashMap<XmlObj, usize>,
}

impl XmlIds {
    fn new() -> Self {
        XmlIds {
            next: 0,
            map: HashMap::new(),
        }
    }

    fn get(&mut self, obj: XmlObj) -> usize {
        if let Some(&id) = self.map.get(&obj) {
            return id;
        }
        let id = self.next;
        self.next += 1;
        self.map.insert(obj, id);
        id
    }
}

/// Port of `edu.mit.csail.sdg.alloy4.Util.encodeXML`.
pub fn encode_xml(out: &mut String, s: &str) {
    for unit in s.encode_utf16() {
        match unit {
            0x3c => out.push_str("&lt;"),
            0x3e => out.push_str("&gt;"),
            0x26 => out.push_str("&amp;"),
            0x27 => out.push_str("&apos;"),
            0x22 => out.push_str("&quot;"),
            32..=126 => out.push(char::from(unit as u8)),
            other => {
                let _ = write!(out, "&#x{other:04x};");
            }
        }
    }
}

/// Writes an [`XmlData`] solution into Java Alloy 6.2.0 `A4SolutionWriter`-compatible XML.
pub fn write_solution_xml(data: &XmlData) -> String {
    render_xml(data, false)
}

/// Writes a model metamodel (`sol == None`, `metamodel="yes"`) in Alloy XML format.
pub fn write_metamodel_xml(model: &Model, filename: &str) -> String {
    let data = build_metamodel_data(model, filename);
    render_xml(&data, true)
}

fn render_xml(data: &XmlData, metamodel: bool) -> String {
    let mut out = String::with_capacity(4096);
    out.push_str("<alloy builddate=\"");
    encode_xml(&mut out, "2026-11-24T00:00Z");
    out.push_str("\">\n\n");

    let looplength = data.trace_length - data.loop_state;
    let num_instances = if metamodel { 1 } else { data.states.len() };

    for st in 0..num_instances {
        let mut ids = XmlIds::new();
        let _ = write!(
            out,
            "<instance bitwidth=\"{}\" maxseq=\"{}\" mintrace=\"{}\" maxtrace=\"{}\" command=\"",
            data.bitwidth, data.maxseq, data.min_trace, data.max_trace
        );
        encode_xml(&mut out, &data.command);
        out.push_str("\" filename=\"");
        encode_xml(&mut out, &data.filename);
        let _ = write!(
            out,
            "\" tracelength=\"{}\" looplength=\"{}\"",
            data.trace_length, looplength
        );
        if metamodel {
            out.push_str(" metamodel=\"yes\"");
        }
        out.push_str(">\n");

        write_sig(data, SIG_UNIV, st, metamodel, &mut ids, &mut out);
        for s in &data.sigs {
            if !s.subset_of.is_empty() {
                write_sig(data, s.id, st, metamodel, &mut ids, &mut out);
            }
        }
        if !metamodel {
            for (ki, sk) in data.skolems.iter().enumerate() {
                write_skolem(data, ki, sk, st, &mut ids, &mut out);
            }
        }
        out.push_str("\n</instance>\n");
    }

    if !metamodel {
        for (fname, content) in &data.sources {
            out.push_str("\n<source filename=\"");
            encode_xml(&mut out, fname);
            out.push_str("\" content=\"");
            encode_xml(&mut out, content);
            out.push_str("\"/>\n");
        }
    }

    out.push_str("\n</alloy>\n");
    out
}

fn prim_children(data: &XmlData, sig_id: SigId) -> Vec<SigId> {
    if sig_id == SIG_NONE {
        return Vec::new();
    }
    if sig_id == SIG_UNIV {
        let mut kids = vec![SIG_INT, SIG_STRING];
        for s in &data.sigs {
            if !s.builtin && s.subset_of.is_empty() && s.parent.is_none() {
                kids.push(s.id);
            }
        }
        return kids;
    }
    if sig_id == SIG_INT {
        return vec![SIG_SEQINT];
    }
    data.sigs
        .iter()
        .filter(|s| !s.builtin && s.subset_of.is_empty() && s.parent == Some(sig_id))
        .map(|s| s.id)
        .collect()
}

fn write_sig(
    data: &XmlData,
    sig_id: SigId,
    st: usize,
    metamodel: bool,
    ids: &mut XmlIds,
    out: &mut String,
) {
    if sig_id == SIG_NONE {
        return;
    }
    let s = &data.sigs[sig_id as usize];
    if s.subset_of.is_empty() {
        for sub in prim_children(data, sig_id) {
            write_sig(data, sub, st, metamodel, ids, out);
        }
    }

    let my_id = ids.get(XmlObj::Sig(sig_id));
    out.push_str("\n<sig label=\"");
    encode_xml(out, &s.label);
    let _ = write!(out, "\" ID=\"{my_id}\"");

    if s.subset_of.is_empty() && sig_id != SIG_UNIV {
        let parent_sig = match sig_id {
            SIG_INT | SIG_STRING => SIG_UNIV,
            SIG_SEQINT => SIG_INT,
            _ => s.parent.unwrap_or(SIG_UNIV),
        };
        let pid = ids.get(XmlObj::Sig(parent_sig));
        let _ = write!(out, " parentID=\"{pid}\"");
    }
    if s.builtin {
        out.push_str(" builtin=\"yes\"");
    }
    if s.is_abstract {
        out.push_str(" abstract=\"yes\"");
    }
    match s.mult {
        Some(Mult::One) => out.push_str(" one=\"yes\""),
        Some(Mult::Lone) => out.push_str(" lone=\"yes\""),
        Some(Mult::Some) => out.push_str(" some=\"yes\""),
        Some(Mult::Set) | None => {}
    }
    if s.is_private {
        out.push_str(" private=\"yes\"");
    }
    if !s.subset_of.is_empty() && s.is_exact {
        out.push_str(" exact=\"yes\"");
    }
    if s.is_enum {
        out.push_str(" enum=\"yes\"");
    }
    if s.is_var {
        out.push_str(" var=\"yes\"");
    }
    out.push_str(">\n");

    if !metamodel && sig_id != SIG_UNIV && sig_id != SIG_INT && sig_id != SIG_SEQINT {
        for atom in &data.states[st].sig_direct_atoms[sig_id as usize] {
            out.push_str("   <atom label=\"");
            encode_xml(out, atom);
            out.push_str("\"/>\n");
        }
    }

    if !s.subset_of.is_empty() {
        for &p in &s.subset_of {
            let pid = ids.get(XmlObj::Sig(p));
            let _ = write!(out, "   <type ID=\"{pid}\"/>\n");
        }
    }
    out.push_str("</sig>\n");

    for &fid in &s.fields {
        write_field(data, fid, st, metamodel, ids, out);
    }
}

fn write_field(
    data: &XmlData,
    fid: FieldId,
    st: usize,
    metamodel: bool,
    ids: &mut XmlIds,
    out: &mut String,
) {
    let fld = &data.fields[fid as usize];
    if fld.types.is_empty() {
        return;
    }
    let my_id = ids.get(XmlObj::Field(fid));
    let pid = ids.get(XmlObj::Sig(fld.owner));
    out.push_str("\n<field label=\"");
    encode_xml(out, &fld.label);
    let _ = write!(out, "\" ID=\"{my_id}\" parentID=\"{pid}\"");
    if fld.is_private {
        out.push_str(" private=\"yes\"");
    }
    if fld.is_var {
        out.push_str(" var=\"yes\"");
    }
    out.push_str(">\n");

    if !metamodel {
        write_tuples(&data.states[st].field_tuples[fid as usize], out);
    }
    write_types(&fld.types, ids, out);
    out.push_str("</field>\n");
}

fn write_skolem(
    data: &XmlData,
    ki: usize,
    sk: &XmlSkolem,
    st: usize,
    ids: &mut XmlIds,
    out: &mut String,
) {
    if sk.types.is_empty() {
        return;
    }
    let my_id = ids.get(XmlObj::Skolem(ki));
    out.push_str("\n<skolem label=\"");
    encode_xml(out, &sk.label);
    let _ = write!(out, "\" ID=\"{my_id}\">\n");
    write_tuples(&data.states[st].skolem_tuples[ki], out);
    write_types(&sk.types, ids, out);
    out.push_str("</skolem>\n");
}

fn write_tuples(tuples: &[Vec<String>], out: &mut String) {
    for tup in tuples {
        out.push_str("   <tuple>");
        for atom in tup {
            out.push_str(" <atom label=\"");
            encode_xml(out, atom);
            out.push_str("\"/>");
        }
        out.push_str(" </tuple>\n");
    }
}

fn write_types(types: &[Vec<SigId>], ids: &mut XmlIds, out: &mut String) {
    for row in types {
        out.push_str("   <types>");
        for &sig_id in row {
            let tid = ids.get(XmlObj::Sig(sig_id));
            let _ = write!(out, " <type ID=\"{tid}\"/>");
        }
        out.push_str(" </types>\n");
    }
}

fn build_metamodel_data(model: &Model, filename: &str) -> XmlData {
    let mut sigs = Vec::with_capacity(model.sigs.len());
    for (sid, s) in model.sigs.iter().enumerate() {
        let id = sid as SigId;
        let builtin = s.kind == SigKind::Builtin;
        let parent = match id {
            SIG_UNIV | SIG_NONE => None,
            SIG_INT | SIG_STRING => Some(SIG_UNIV),
            SIG_SEQINT => Some(SIG_INT),
            _ if !s.subset_of.is_empty() => None,
            _ => s.parent,
        };
        sigs.push(XmlSig {
            id,
            label: s.label.clone(),
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

    let mut fcache: HashMap<FieldId, JType> = HashMap::new();
    let mut fields = Vec::with_capacity(model.fields.len());
    for (fid, f) in model.fields.iter().enumerate() {
        let jt = model_field_jtype(model, fid as FieldId, &mut fcache);
        let types: Vec<Vec<SigId>> = Hier { model }
            .fold(&jt)
            .into_iter()
            .filter(|r| !r.is_empty() && !r.contains(&SIG_NONE))
            .collect();
        fields.push(XmlField {
            id: fid as FieldId,
            label: f.name.clone(),
            owner: f.owner,
            is_private: f.is_private,
            is_var: f.is_var,
            types,
        });
    }

    XmlData {
        bitwidth: 4,
        maxseq: 4,
        min_trace: 1,
        max_trace: 1,
        trace_length: 1,
        loop_state: 0,
        command: "show metamodel".to_string(),
        filename: filename.to_string(),
        sigs,
        fields,
        skolems: Vec::new(),
        states: Vec::new(),
        sources: BTreeMap::new(),
    }
}

fn model_sig_jtype(model: &Model, s: SigId) -> JType {
    let h = Hier { model };
    let sig = &model.sigs[s as usize];
    if sig.subset_of.is_empty() {
        return h.make(s);
    }
    let mut t: Option<JType> = None;
    for &p in &sig.subset_of {
        let pt = model_sig_jtype(model, p);
        t = Some(match t {
            None => pt,
            Some(x) => {
                let mut ee = x.entries;
                for e in pt.entries {
                    h.add(&mut ee, e);
                }
                JType { entries: ee }
            }
        });
    }
    t.unwrap_or_default()
}

fn model_field_jtype(model: &Model, f: FieldId, cache: &mut HashMap<FieldId, JType>) -> JType {
    if let Some(t) = cache.get(&f) {
        return t.clone();
    }
    let fd = &model.fields[f as usize];
    let ot = model_sig_jtype(model, fd.owner);
    let mut tenv = vec![(fd.this_local, ot.clone())];
    let dt = model_expr_jtype(model, &fd.decl, &mut tenv, cache);
    let t = Hier { model }.product(&ot, &dt);
    cache.insert(f, t.clone());
    t
}

fn model_expr_jtype(
    model: &Model,
    e: &RExpr,
    tenv: &mut Vec<(LocalId, JType)>,
    cache: &mut HashMap<FieldId, JType>,
) -> JType {
    let h = Hier { model };
    match e {
        RExpr::Sig(s) => model_sig_jtype(model, *s),
        RExpr::Field(f) => model_field_jtype(model, *f, cache),
        RExpr::Local(l) => tenv
            .iter()
            .rev()
            .find(|(x, _)| x == l)
            .map(|(_, t)| t.clone())
            .unwrap_or_else(|| h.make(SIG_UNIV)),
        RExpr::Const(Const::Univ) => h.make(SIG_UNIV),
        RExpr::Const(Const::None) => h.make(SIG_NONE),
        RExpr::Const(Const::SigInt) | RExpr::Num(_) => h.make(SIG_INT),
        RExpr::Const(Const::SigString) | RExpr::Str(_) => h.make(SIG_STRING),
        RExpr::Const(Const::Iden) => h.product(&h.make(SIG_UNIV), &h.make(SIG_UNIV)),
        RExpr::Un(UnOp::Set | UnOp::One | UnOp::Lone | UnOp::Some | UnOp::ExactlyOf, x) => {
            model_expr_jtype(model, x, tenv, cache)
        }
        RExpr::Un(UnOp::Seq, x) => {
            let t = model_expr_jtype(model, x, tenv, cache);
            h.product(&h.make(SIG_SEQINT), &t)
        }
        RExpr::Un(UnOp::Transpose, x) => h.transpose(&model_expr_jtype(model, x, tenv, cache)),
        RExpr::Un(UnOp::Closure, x) => h.closure(&model_expr_jtype(model, x, tenv, cache)),
        RExpr::Un(UnOp::IntCast | UnOp::SigInt | UnOp::Card, _) => h.make(SIG_INT),
        RExpr::Bin(BinOp::Arrow(..), a, b) => {
            let x = model_expr_jtype(model, a, tenv, cache);
            let y = model_expr_jtype(model, b, tenv, cache);
            h.product(&x, &y)
        }
        RExpr::Bin(BinOp::Plus | BinOp::Override, a, b) => {
            let x = model_expr_jtype(model, a, tenv, cache);
            let y = model_expr_jtype(model, b, tenv, cache);
            h.union(&x, &y)
        }
        RExpr::Bin(BinOp::Intersect, a, b) => {
            let x = model_expr_jtype(model, a, tenv, cache);
            let y = model_expr_jtype(model, b, tenv, cache);
            h.intersect(&x, &y)
        }
        RExpr::Bin(BinOp::Minus, a, _) => model_expr_jtype(model, a, tenv, cache),
        RExpr::Bin(BinOp::Join, a, b) => {
            let x = model_expr_jtype(model, a, tenv, cache);
            let y = model_expr_jtype(model, b, tenv, cache);
            h.join(&x, &y)
        }
        RExpr::Block(items) if items.len() == 1 => model_expr_jtype(model, &items[0], tenv, cache),
        RExpr::Compr(ds, _) => {
            let old = tenv.len();
            let mut t: Option<JType> = None;
            for d in ds {
                let inner = match &d.bound {
                    RExpr::Un(
                        UnOp::Set | UnOp::One | UnOp::Lone | UnOp::Some | UnOp::ExactlyOf,
                        x,
                    ) => x,
                    other => other,
                };
                let dt = model_expr_jtype(model, inner, tenv, cache);
                for &v in &d.vars {
                    tenv.push((v, dt.clone()));
                    t = Some(match t {
                        None => dt.clone(),
                        Some(x) => h.product(&x, &dt),
                    });
                }
            }
            tenv.truncate(old);
            t.unwrap_or_default()
        }
        _ => h.make(SIG_UNIV),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{execute_command, Options};
    use alloy_core::{parse_everything_from_file, sema};

    fn solve_xml(src: &str, idx: usize) -> (String, alloy_core::World, sema::Model) {
        static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
        let n = N.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        let dir = std::env::temp_dir().join(format!("alloy_rs_xml_{}_{}", std::process::id(), n));
        std::fs::create_dir_all(&dir).unwrap();
        let file = dir.join("m.als");
        std::fs::write(&file, src).unwrap();
        let world = parse_everything_from_file(&file).unwrap();
        let model = sema::build(&world.modules).unwrap();
        let mut opt = Options::default();
        opt.want_xml = true;
        let sol = execute_command(&world, idx, &opt).unwrap();
        assert!(sol.sat);
        (sol.to_xml().expect("expected xml output"), world, model)
    }

    #[test]
    fn encode_xml_matches_java_util_rules() {
        let mut s = String::new();
        encode_xml(&mut s, "<tag attr='\"a&b\"'>\n\t©");
        assert_eq!(
            s,
            "&lt;tag attr=&apos;&quot;a&amp;b&quot;&apos;&gt;&#x000a;&#x0009;&#x00a9;"
        );
    }

    #[test]
    fn static_xml_schema_builtins_enum_subset_and_strings() {
        let src = r#"
enum Color { Red, Blue }
abstract sig Node { nxt: lone Node, tag: one String }
sig Leaf extends Node {}
sig Marked in Node {}
sig AllNodes = Leaf + Node {}
run { some Leaf and some Marked and tag.String = Leaf and some "hello" } for 3
"#;
        let (xml, _, _) = solve_xml(src, 0);
        assert!(xml.contains("mintrace=\"-1\" maxtrace=\"-1\""));
        assert!(xml.contains("tracelength=\"1\" looplength=\"1\""));
        assert!(xml.contains("<sig label=\"seq/Int\" ID=\"0\" parentID=\"1\" builtin=\"yes\">"));
        assert!(xml.contains("<sig label=\"Int\" ID=\"1\" parentID=\"2\" builtin=\"yes\">"));
        assert!(xml.contains("label=\"String\""));
        assert!(xml.contains("builtin=\"yes\""));
        assert!(xml.contains("<atom label=\"&quot;hello&quot;\"/>"));
        assert!(xml.contains("label=\"this/Color\"") && xml.contains("enum=\"yes\"") && xml.contains("abstract=\"yes\""));
        assert!(xml.contains("label=\"this/Red\"") && xml.contains("one=\"yes\""));
        assert!(xml.contains("label=\"this/Marked\"") && !xml.contains("label=\"this/Marked\" ID=\"0\""));
        assert!(xml.contains("label=\"this/AllNodes\"") && xml.contains("exact=\"yes\""));
        assert!(xml.contains("<source filename="));
        assert!(xml.contains("content=\""));
    }

    #[test]
    fn temporal_xml_emits_all_states_looplength_and_consistent_skolem_ids() {
        let src = r#"
sig Node { var inbox: set Node }
var sig Active in Node {}
run { some Active and after (no Active and always (no Active and some n: Node | n in Node)) } for 2 but 2..2 steps
"#;
        let (xml, _, _) = solve_xml(src, 0);
        assert!(xml.contains("mintrace=\"2\" maxtrace=\"2\""));
        assert!(xml.contains("tracelength=\"2\" looplength=\"1\""));
        assert_eq!(xml.matches("<instance ").count(), 2);
        assert!(xml.contains("label=\"this/Active\"") && xml.contains("var=\"yes\""));
        assert!(xml.contains("<field label=\"inbox\"") && xml.contains("var=\"yes\""));
    }

    #[test]
    fn metamodel_xml_omits_atoms_tuples_and_sets_metamodel_yes() {
        let (_, _, model) = solve_xml("sig A { r: set A }\nrun {} for 2\n", 0);
        let mm = write_metamodel_xml(&model, "m.als");
        assert!(mm.contains("metamodel=\"yes\""));
        assert!(!mm.contains("<atom "));
        assert!(!mm.contains("<tuple>"));
        assert!(!mm.contains("<skolem "));
        assert!(mm.contains("<field label=\"r\""));
        assert!(mm.contains("<types>"));
    }
}
