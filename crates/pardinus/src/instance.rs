//! Port of `kodkod.instance` (`Universe`, `TupleSet` as a sorted index set, `Bounds`/`PardinusBounds` with
//! insertion-ordered concrete and symbolic bounds) and the `.kk` problem reader used by the verification tools.

use crate::ast::*;
use std::collections::{BTreeMap, HashMap};

/// A tuple set: arity + ascending tuple indices (Kodkod `TupleSet.indexView()`).
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct TupleSet {
    pub arity: u32,
    pub idx: Vec<u32>,
}

impl TupleSet {
    pub fn new(arity: u32, mut idx: Vec<u32>) -> TupleSet {
        idx.sort_unstable();
        idx.dedup();
        TupleSet { arity, idx }
    }
    pub fn empty(arity: u32) -> TupleSet {
        TupleSet { arity, idx: Vec::new() }
    }
    pub fn len(&self) -> usize {
        self.idx.len()
    }
    pub fn is_empty(&self) -> bool {
        self.idx.is_empty()
    }
    pub fn contains(&self, i: u32) -> bool {
        self.idx.binary_search(&i).is_ok()
    }
    pub fn contains_all(&self, o: &TupleSet) -> bool {
        o.idx.iter().all(|&i| self.contains(i))
    }
}

/// `Bounds` / `PardinusBounds`.
#[derive(Clone, Debug, Default)]
pub struct Bounds {
    pub atoms: Vec<String>,
    /// concrete bounds in `LinkedHashMap` insertion order
    pub conc: Vec<N>,
    pub lower: HashMap<N, TupleSet>,
    pub upper: HashMap<N, TupleSet>,
    /// symbolic bounds (`lowers_symb`/`uppers_symb`), insertion order: (relation, lower expr, upper expr)
    pub symb: Vec<(N, N, N)>,
    /// int bounds (`SparseSequence`, ascending int)
    pub ints: BTreeMap<i32, TupleSet>,
    /// `TemporalTranslator.STATE` when these are expanded temporal bounds (symmetry breaking per time step)
    pub state: Option<N>,
}

impl Bounds {
    pub fn universe_size(&self) -> u32 {
        self.atoms.len() as u32
    }
    /// `relations()`: concrete keys, then symbolic keys
    pub fn relations(&self) -> Vec<N> {
        let mut v = self.conc.clone();
        v.extend(self.symb.iter().map(|x| x.0));
        v
    }
    pub fn has_concrete(&self, r: N) -> bool {
        self.upper.contains_key(&r)
    }
    /// `Bounds.bound(r, lower, upper)` (LinkedHashMap.put keeps an existing key's position)
    pub fn bound(&mut self, r: N, lower: TupleSet, upper: TupleSet) {
        if !self.upper.contains_key(&r) {
            self.conc.push(r);
        }
        self.lower.insert(r, lower);
        self.upper.insert(r, upper);
    }
    pub fn bound_exactly(&mut self, r: N, ts: TupleSet) {
        self.bound(r, ts.clone(), ts);
    }
    /// `bound(r, upper)`: empty lower bound
    pub fn bound_upper(&mut self, r: N, upper: TupleSet) {
        let a = upper.arity;
        self.bound(r, TupleSet::empty(a), upper);
    }
    pub fn lower_of(&self, r: N) -> Option<&TupleSet> {
        self.lower.get(&r)
    }
    pub fn upper_of(&self, r: N) -> Option<&TupleSet> {
        self.upper.get(&r)
    }
    pub fn remove_concrete(&mut self, r: N) {
        if self.upper.remove(&r).is_some() {
            self.lower.remove(&r);
            self.conc.retain(|x| *x != r);
        }
    }
    /// `TupleFactory.tuple(atoms...).index()`
    pub fn tuple_index(&self, atoms: &[u32]) -> u32 {
        let n = self.universe_size();
        atoms.iter().fold(0u32, |acc, &a| acc * n + a)
    }
    /// atoms of a tuple index
    pub fn tuple_atoms(&self, mut idx: u32, arity: u32) -> Vec<u32> {
        let n = self.universe_size();
        let mut v = vec![0u32; arity as usize];
        for k in (0..arity as usize).rev() {
            v[k] = idx % n;
            idx /= n;
        }
        v
    }
}

/// Kodkod options that influence the translation (`ExtendedOptions`).
#[derive(Clone, Debug)]
pub struct Options {
    pub bitwidth: i32,
    pub symmetry: i32,
    pub skolem_depth: i32,
    pub sharing: i32,
    pub no_overflow: bool,
    pub temporal: bool,
    pub min_trace: i32,
    pub max_trace: i32,
}

impl Default for Options {
    fn default() -> Self {
        Options { bitwidth: 4, symmetry: 20, skolem_depth: 0, sharing: 3, no_overflow: false, temporal: false, min_trace: -1, max_trace: -1 }
    }
}

/// A Kodkod problem: formula + bounds + options.
pub struct Problem {
    pub ast: Ast,
    pub bounds: Bounds,
    pub options: Options,
    pub goal: N,
}

fn unquote(s: &str) -> Result<String, String> {
    let s = s.trim();
    if !s.starts_with('"') || !s.ends_with('"') || s.len() < 2 {
        return Err(format!("expected a quoted string: {s}"));
    }
    let inner = &s[1..s.len() - 1];
    let mut out = String::new();
    let mut it = inner.chars();
    while let Some(c) = it.next() {
        if c == '\\' {
            match it.next() {
                Some('u') => {
                    let h: String = it.by_ref().take(4).collect();
                    let v = u32::from_str_radix(&h, 16).map_err(|e| e.to_string())?;
                    out.push(char::from_u32(v).unwrap_or('?'));
                }
                Some(x) => out.push(x),
                None => {}
            }
        } else {
            out.push(c);
        }
    }
    Ok(out)
}

fn eop(s: &str) -> Result<EOp, String> {
    Ok(match s {
        "UNION" => EOp::Union,
        "INTERSECTION" => EOp::Intersection,
        "OVERRIDE" => EOp::Override,
        "PRODUCT" => EOp::Product,
        "DIFFERENCE" => EOp::Difference,
        "JOIN" => EOp::Join,
        "TRANSPOSE" => EOp::Transpose,
        "CLOSURE" => EOp::Closure,
        "REFLEXIVE_CLOSURE" => EOp::ReflexiveClosure,
        _ => return Err(format!("expr op {s}")),
    })
}
fn iop(s: &str) -> Result<IOp, String> {
    Ok(match s {
        "PLUS" => IOp::Plus,
        "MINUS" => IOp::Minus,
        "MULTIPLY" => IOp::Multiply,
        "DIVIDE" => IOp::Divide,
        "MODULO" => IOp::Modulo,
        "AND" => IOp::And,
        "OR" => IOp::Or,
        "XOR" => IOp::Xor,
        "SHL" => IOp::Shl,
        "SHR" => IOp::Shr,
        "SHA" => IOp::Sha,
        "NEG" => IOp::Neg,
        "NOT" => IOp::Not,
        "ABS" => IOp::Abs,
        "SGN" => IOp::Sgn,
        _ => return Err(format!("int op {s}")),
    })
}
fn mult(s: &str) -> Result<Mult, String> {
    Ok(match s {
        "NO" => Mult::No,
        "LONE" => Mult::Lone,
        "ONE" => Mult::One,
        "SOME" => Mult::Some,
        "SET" => Mult::Set,
        _ => return Err(format!("multiplicity {s}")),
    })
}
fn top(s: &str) -> Result<TOp, String> {
    Ok(match s {
        "ALWAYS" => TOp::Always,
        "EVENTUALLY" => TOp::Eventually,
        "AFTER" => TOp::After,
        "HISTORICALLY" => TOp::Historically,
        "ONCE" => TOp::Once,
        "BEFORE" => TOp::Before,
        "UNTIL" => TOp::Until,
        "RELEASES" => TOp::Releases,
        "SINCE" => TOp::Since,
        "TRIGGERED" => TOp::Triggered,
        "PRIME" => TOp::Prime,
        _ => return Err(format!("temporal op {s}")),
    })
}
fn cast(s: &str) -> Result<CastOp, String> {
    Ok(match s {
        "INTCAST" => CastOp::IntCast,
        "BITSETCAST" => CastOp::BitsetCast,
        "CARDINALITY" => CastOp::Cardinality,
        "SUM" => CastOp::Sum,
        _ => return Err(format!("cast op {s}")),
    })
}

/// Reads a `.kk` dump written by `tools/exact/java/.../KKDump.java`.
pub fn read_kk(text: &str) -> Result<Problem, String> {
    let mut ast = Ast::new();
    let mut ids: HashMap<u32, N> = HashMap::new();
    let mut bounds = Bounds::default();
    let mut options = Options::default();
    let mut goal = None;
    let mut rel_order: Vec<N> = Vec::new();
    for (lineno, line) in text.lines().enumerate() {
        let err = |m: String| format!("line {}: {m}: {line}", lineno + 1);
        let (head, rest) = line.split_once(' ').unwrap_or((line, ""));
        let id = |s: &str, ids: &HashMap<u32, N>| -> Result<N, String> {
            let k: u32 = s.parse().map_err(|_| format!("bad id {s}"))?;
            ids.get(&k).copied().ok_or_else(|| format!("unknown id {k}"))
        };
        match head {
            "U" | "" | "NONE" => {}
            "A" => bounds.atoms.push(unquote(rest).map_err(err)?),
            "O" => {
                for kv in rest.split_whitespace() {
                    let (k, v) = kv.split_once('=').unwrap_or((kv, ""));
                    match k {
                        "bitwidth" => options.bitwidth = v.parse().map_err(|_| err("bitwidth".into()))?,
                        "symmetry" => options.symmetry = v.parse().map_err(|_| err("symmetry".into()))?,
                        "skolemDepth" => options.skolem_depth = v.parse().map_err(|_| err("skolemDepth".into()))?,
                        "sharing" => options.sharing = v.parse().map_err(|_| err("sharing".into()))?,
                        "noOverflow" => options.no_overflow = v == "true",
                        "temporal" => options.temporal = v == "true",
                        "minTrace" => options.min_trace = v.parse().unwrap_or(-1),
                        "maxTrace" => options.max_trace = v.parse().unwrap_or(-1),
                        _ => {}
                    }
                }
            }
            "n" => {
                let (k, body) = rest.split_once(' ').ok_or_else(|| err("node".into()))?;
                let k: u32 = k.parse().map_err(|_| err("node id".into()))?;
                let (kind, args) = body.split_once(' ').unwrap_or((body, ""));
                let toks: Vec<&str> = args.split_whitespace().collect();
                let ni = |i: usize| -> Result<N, String> { id(toks.get(i).ok_or("missing arg")?, &ids) };
                let nall = |from: usize| -> Result<Vec<N>, String> { (from..toks.len()).map(|i| id(toks[i], &ids)).collect() };
                let node = match kind {
                    "REL" => {
                        // REL arity var atom "name"
                        let mut p = args.splitn(4, ' ');
                        let arity: u32 = p.next().unwrap_or("").parse().map_err(|_| err("arity".into()))?;
                        let var = p.next() == Some("1");
                        let atom = p.next() == Some("1");
                        let name = unquote(p.next().unwrap_or("")).map_err(err)?;
                        Node::Rel(RelInfo { name, arity, var, atom, skolem: false })
                    }
                    "VAR" => {
                        let (a, nm) = args.split_once(' ').ok_or_else(|| err("var".into()))?;
                        Node::Var { name: unquote(nm).map_err(err)?, arity: a.parse().map_err(|_| err("arity".into()))? }
                    }
                    "CONSTE" => Node::ConstE(match toks[0] {
                        "UNIV" => ConstE::Univ,
                        "IDEN" => ConstE::Iden,
                        "NONE" => ConstE::None,
                        "INTS" => ConstE::Ints,
                        _ => return Err(err("const".into())),
                    }),
                    "CONSTF" => Node::ConstF(toks[0] == "TRUE"),
                    "BINE" => Node::BinE(eop(toks[0])?, ni(1)?, ni(2)?),
                    "UNE" => Node::UnE(eop(toks[0])?, ni(1)?),
                    "NARYE" => Node::NaryE(eop(toks[0])?, nall(1)?),
                    "COMPR" => Node::Compr(ni(0)?, ni(1)?),
                    "IFE" => Node::IfE(ni(0)?, ni(1)?, ni(2)?),
                    "PROJ" => Node::Proj(ni(0)?, nall(1)?),
                    "I2E" => Node::I2E(cast(toks[0])?, ni(1)?),
                    "E2I" => Node::E2I(cast(toks[0])?, ni(1)?),
                    "ICONST" => Node::IConst(toks[0].parse().map_err(|_| err("int".into()))?),
                    "BINI" => Node::BinI(iop(toks[0])?, ni(1)?, ni(2)?),
                    "NARYI" => Node::NaryI(iop(toks[0])?, nall(1)?),
                    "UNI" => Node::UnI(iop(toks[0])?, ni(1)?),
                    "SUM" => Node::Sum(ni(0)?, ni(1)?),
                    "IFI" => Node::IfI(ni(0)?, ni(1)?, ni(2)?),
                    "ICMP" => Node::ICmp(
                        match toks[0] {
                            "EQ" => ICmpOp::Eq,
                            "NEQ" => ICmpOp::Neq,
                            "LT" => ICmpOp::Lt,
                            "LTE" => ICmpOp::Lte,
                            "GT" => ICmpOp::Gt,
                            "GTE" => ICmpOp::Gte,
                            _ => return Err(err("icmp".into())),
                        },
                        ni(1)?,
                        ni(2)?,
                    ),
                    "CMP" => Node::Cmp(if toks[0] == "SUBSET" { CmpOp::Subset } else { CmpOp::Equals }, ni(1)?, ni(2)?),
                    "MULT" => Node::Mult(mult(toks[0])?, ni(1)?),
                    "QUANT" => Node::Quant(if toks[0] == "ALL" { Quant::All } else { Quant::Some }, ni(1)?, ni(2)?),
                    "BINF" => Node::BinF(
                        match toks[0] {
                            "AND" => FOp::And,
                            "OR" => FOp::Or,
                            "IFF" => FOp::Iff,
                            "IMPLIES" => FOp::Implies,
                            _ => return Err(err("fop".into())),
                        },
                        ni(1)?,
                        ni(2)?,
                    ),
                    "NARYF" => Node::NaryF(if toks[0] == "AND" { FOp::And } else { FOp::Or }, nall(1)?),
                    "NOT" => Node::Not(ni(0)?),
                    "PACYCLIC" => Node::PAcyclic(ni(0)?),
                    "PFUNCTION" => Node::PFunction(ni(0)?, ni(1)?, mult(toks[2])?, ni(3)?),
                    "PTOTAL" => Node::PTotal(ni(0)?, ni(1)?, ni(2)?, ni(3)?),
                    "DECL" => Node::Decl(ni(0)?, mult(toks[1])?, ni(2)?),
                    "DECLS" => Node::Decls(nall(0)?),
                    "UTEMPF" => Node::UTempF(top(toks[0])?, ni(1)?),
                    "BTEMPF" => Node::BTempF(top(toks[0])?, ni(1)?, ni(2)?),
                    "TEMPE" => Node::TempE(top(toks[0])?, ni(1)?),
                    _ => return Err(err(format!("unknown node kind {kind}"))),
                };
                let n = ast.add(node);
                ids.insert(k, n);
            }
            "R" => rel_order.push(id(rest, &ids).map_err(err)?),
            "L" | "H" => {
                let toks: Vec<&str> = rest.split_whitespace().collect();
                let r = id(toks[0], &ids).map_err(err)?;
                let arity = ast.rel_info(r).arity;
                let idx: Vec<u32> = toks[1..].iter().map(|t| t.parse().unwrap()).collect();
                let ts = TupleSet::new(arity, idx);
                if head == "L" {
                    bounds.lower.insert(r, ts);
                } else {
                    bounds.upper.insert(r, ts);
                }
            }
            "SB" => {
                let toks: Vec<&str> = rest.split_whitespace().collect();
                let r = id(toks[0], &ids).map_err(err)?;
                let lo = id(toks[1], &ids).map_err(err)?;
                let hi = id(toks[2], &ids).map_err(err)?;
                bounds.symb.push((r, lo, hi));
            }
            "IB" => {
                let toks: Vec<&str> = rest.split_whitespace().collect();
                let i: i32 = toks[0].parse().map_err(|_| err("int".into()))?;
                let idx: Vec<u32> = toks[1..].iter().map(|t| t.parse().unwrap()).collect();
                bounds.ints.insert(i, TupleSet::new(1, idx));
            }
            "G" => goal = Some(id(rest, &ids).map_err(err)?),
            _ => return Err(err("unknown line".into())),
        }
    }
    // concrete order = relations() order minus the symbolic-only ones
    for r in rel_order {
        if bounds.upper.contains_key(&r) {
            bounds.conc.push(r);
        }
    }
    Ok(Problem { ast, bounds, options, goal: goal.ok_or("no goal")? })
}
