//! Writes a `Problem` in the `.kk` format of `tools/exact/java/.../KKDump.java`, emitting nodes in the same order,
//! so a Rust-built problem can be diffed textually against Java's dump (dev/verification only).

use crate::ast::*;
use crate::instance::Problem;
use std::collections::HashMap;
use std::fmt::Write;

fn q(s: &str) -> String {
    let mut o = String::from("\"");
    for c in s.chars() {
        match c {
            '"' | '\\' => {
                o.push('\\');
                o.push(c);
            }
            c if (c as u32) < 0x20 => {
                let _ = write!(o, "\\u{:04x}", c as u32);
            }
            c => o.push(c),
        }
    }
    o.push('"');
    o
}

fn eop(o: EOp) -> &'static str {
    match o {
        EOp::Union => "UNION",
        EOp::Intersection => "INTERSECTION",
        EOp::Override => "OVERRIDE",
        EOp::Product => "PRODUCT",
        EOp::Difference => "DIFFERENCE",
        EOp::Join => "JOIN",
        EOp::Transpose => "TRANSPOSE",
        EOp::Closure => "CLOSURE",
        EOp::ReflexiveClosure => "REFLEXIVE_CLOSURE",
    }
}
fn iop(o: IOp) -> &'static str {
    match o {
        IOp::Plus => "PLUS",
        IOp::Minus => "MINUS",
        IOp::Multiply => "MULTIPLY",
        IOp::Divide => "DIVIDE",
        IOp::Modulo => "MODULO",
        IOp::And => "AND",
        IOp::Or => "OR",
        IOp::Xor => "XOR",
        IOp::Shl => "SHL",
        IOp::Shr => "SHR",
        IOp::Sha => "SHA",
        IOp::Neg => "NEG",
        IOp::Not => "NOT",
        IOp::Abs => "ABS",
        IOp::Sgn => "SGN",
    }
}
fn mult(m: Mult) -> &'static str {
    match m {
        Mult::No => "NO",
        Mult::Lone => "LONE",
        Mult::One => "ONE",
        Mult::Some => "SOME",
        Mult::Set => "SET",
    }
}
fn cast(c: CastOp) -> &'static str {
    match c {
        CastOp::IntCast => "INTCAST",
        CastOp::BitsetCast => "BITSETCAST",
        CastOp::Cardinality => "CARDINALITY",
        CastOp::Sum => "SUM",
    }
}
fn top(t: TOp) -> &'static str {
    match t {
        TOp::Always => "ALWAYS",
        TOp::Eventually => "EVENTUALLY",
        TOp::After => "AFTER",
        TOp::Historically => "HISTORICALLY",
        TOp::Once => "ONCE",
        TOp::Before => "BEFORE",
        TOp::Until => "UNTIL",
        TOp::Releases => "RELEASES",
        TOp::Since => "SINCE",
        TOp::Triggered => "TRIGGERED",
        TOp::Prime => "PRIME",
    }
}

struct W<'a> {
    ast: &'a Ast,
    ids: HashMap<N, u32>,
    next: u32,
    out: String,
}

impl W<'_> {
    fn id(&mut self, n: N) -> u32 {
        if let Some(&i) = self.ids.get(&n) {
            return i;
        }
        let line = self.emit(n);
        let k = self.next;
        self.next += 1;
        self.ids.insert(n, k);
        let _ = writeln!(self.out, "n {k} {line}");
        k
    }
    fn ids(&mut self, v: &[N]) -> String {
        let mut s = String::new();
        for &x in v {
            let i = self.id(x);
            let _ = write!(s, " {i}");
        }
        s
    }
    fn emit(&mut self, n: N) -> String {
        match self.ast.get(n).clone() {
            Node::Rel(r) => format!("REL {} {} {} {}", r.arity, r.var as u8, r.atom as u8, q(&r.name)),
            Node::Var { name, arity } => format!("VAR {arity} {}", q(&name)),
            Node::ConstE(c) => format!(
                "CONSTE {}",
                match c {
                    ConstE::Univ => "UNIV",
                    ConstE::Iden => "IDEN",
                    ConstE::None => "NONE",
                    ConstE::Ints => "INTS",
                }
            ),
            Node::ConstF(b) => format!("CONSTF {}", if b { "TRUE" } else { "FALSE" }),
            Node::BinE(o, l, r) => {
                let (a, b) = (self.id(l), self.id(r));
                format!("BINE {} {a} {b}", eop(o))
            }
            Node::UnE(o, e) => format!("UNE {} {}", eop(o), self.id(e)),
            Node::NaryE(o, cs) => format!("NARYE {}{}", eop(o), self.ids(&cs)),
            Node::Compr(d, f) => {
                let (a, b) = (self.id(d), self.id(f));
                format!("COMPR {a} {b}")
            }
            Node::IfE(c, t, e) => {
                let (a, b, x) = (self.id(c), self.id(t), self.id(e));
                format!("IFE {a} {b} {x}")
            }
            Node::Proj(e, cols) => {
                let a = self.id(e);
                format!("PROJ {a}{}", self.ids(&cols))
            }
            Node::I2E(o, i) => format!("I2E {} {}", cast(o), self.id(i)),
            Node::E2I(o, e) => format!("E2I {} {}", cast(o), self.id(e)),
            Node::IConst(v) => format!("ICONST {v}"),
            Node::BinI(o, l, r) => {
                let (a, b) = (self.id(l), self.id(r));
                format!("BINI {} {a} {b}", iop(o))
            }
            Node::NaryI(o, cs) => format!("NARYI {}{}", iop(o), self.ids(&cs)),
            Node::UnI(o, e) => format!("UNI {} {}", iop(o), self.id(e)),
            Node::Sum(d, e) => {
                let (a, b) = (self.id(d), self.id(e));
                format!("SUM {a} {b}")
            }
            Node::IfI(c, t, e) => {
                let (a, b, x) = (self.id(c), self.id(t), self.id(e));
                format!("IFI {a} {b} {x}")
            }
            Node::ICmp(o, l, r) => {
                let (a, b) = (self.id(l), self.id(r));
                let s = match o {
                    ICmpOp::Eq => "EQ",
                    ICmpOp::Neq => "NEQ",
                    ICmpOp::Lt => "LT",
                    ICmpOp::Lte => "LTE",
                    ICmpOp::Gt => "GT",
                    ICmpOp::Gte => "GTE",
                };
                format!("ICMP {s} {a} {b}")
            }
            Node::Cmp(o, l, r) => {
                let (a, b) = (self.id(l), self.id(r));
                format!("CMP {} {a} {b}", if o == CmpOp::Subset { "SUBSET" } else { "EQUALS" })
            }
            Node::Mult(m, e) => format!("MULT {} {}", mult(m), self.id(e)),
            Node::Quant(qq, d, f) => {
                let (a, b) = (self.id(d), self.id(f));
                format!("QUANT {} {a} {b}", if qq == Quant::All { "ALL" } else { "SOME" })
            }
            Node::BinF(o, l, r) => {
                let (a, b) = (self.id(l), self.id(r));
                let s = match o {
                    FOp::And => "AND",
                    FOp::Or => "OR",
                    FOp::Iff => "IFF",
                    FOp::Implies => "IMPLIES",
                };
                format!("BINF {s} {a} {b}")
            }
            Node::NaryF(o, cs) => format!("NARYF {}{}", if o == FOp::And { "AND" } else { "OR" }, self.ids(&cs)),
            Node::Not(f) => format!("NOT {}", self.id(f)),
            Node::PAcyclic(r) => format!("PACYCLIC {}", self.id(r)),
            Node::PFunction(r, d, m, rg) => {
                let (a, b, c) = (self.id(r), self.id(d), self.id(rg));
                format!("PFUNCTION {a} {b} {} {c}", mult(m))
            }
            Node::PTotal(r, o, f, l) => {
                let (a, b, c, d) = (self.id(r), self.id(o), self.id(f), self.id(l));
                format!("PTOTAL {a} {b} {c} {d}")
            }
            Node::Decl(v, m, e) => {
                let (a, b) = (self.id(v), self.id(e));
                format!("DECL {a} {} {b}", mult(m))
            }
            Node::Decls(ds) => format!("DECLS{}", self.ids(&ds)),
            Node::UTempF(o, f) => format!("UTEMPF {} {}", top(o), self.id(f)),
            Node::BTempF(o, l, r) => {
                let (a, b) = (self.id(l), self.id(r));
                format!("BTEMPF {} {a} {b}", top(o))
            }
            Node::TempE(o, e) => format!("TEMPE {} {}", top(o), self.id(e)),
        }
    }
}

/// Serializes the problem like KKDump (`O` line reduced to the options the reader knows).
pub fn write_kk(p: &Problem) -> String {
    let mut w = W { ast: &p.ast, ids: HashMap::new(), next: 0, out: String::new() };
    let b = &p.bounds;
    let mut head = String::new();
    let _ = writeln!(head, "U {}", b.atoms.len());
    for a in &b.atoms {
        let _ = writeln!(head, "A {}", q(a));
    }
    let o = &p.options;
    let _ = writeln!(
        head,
        "O bitwidth={} symmetry={} skolemDepth={} sharing={} noOverflow={} intEncoding=TWOSCOMPLEMENT temporal={} minTrace={} maxTrace={} coreGranularity=0 logTranslation=0 decomposed=false",
        o.bitwidth, o.symmetry, o.skolem_depth, o.sharing, o.no_overflow, o.temporal, o.min_trace, o.max_trace
    );
    let g = w.id(p.goal);
    let mut tail = String::new();
    let rels = b.relations();
    for &r in &rels {
        let i = w.id(r);
        let _ = writeln!(tail, "R {i}");
    }
    for &r in &rels {
        let i = w.id(r);
        if let Some(lo) = b.lower.get(&r) {
            let _ = write!(tail, "L {i}");
            for x in &lo.idx {
                let _ = write!(tail, " {x}");
            }
            tail.push('\n');
        }
        if let Some(hi) = b.upper.get(&r) {
            let _ = write!(tail, "H {i}");
            for x in &hi.idx {
                let _ = write!(tail, " {x}");
            }
            tail.push('\n');
        }
    }
    for &(r, lo, hi) in &b.symb {
        let (ri, li, hj) = (w.id(r), w.id(lo), w.id(hi));
        let _ = writeln!(tail, "SB {ri} {li} {hj}");
    }
    for (i, ts) in &b.ints {
        let _ = write!(tail, "IB {i}");
        for x in &ts.idx {
            let _ = write!(tail, " {x}");
        }
        tail.push('\n');
    }
    let _ = writeln!(tail, "G {g}");
    head + &w.out + &tail
}
