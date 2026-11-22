//! Resolved semantic model. Port of the sig/field/function/fact/assert/command part of
//! `CORE/parser/CompModule.java` (`addSig`, `addField`, `addFunc`, `addFact`, `addAssertion`,
//! `resolveSigs`, `resolveFieldDecl`, `resolveFuncDecls`, `resolveFacts`, `resolveAssertions`,
//! `resolveCommand`) and of `CORE/ast/{Sig,Field,Func,Decl,ExprVar}.java`.
//!
//! Every loaded module *instance* (root and each `open`) gets its own sigs, fields, functions,
//! macros and assertions, exactly like Java's per-open re-parse. Module parameters are bound to the
//! open's arguments (`open util/ordering[State]` makes the parameter name denote `State`).
//!
//! Names are resolved to ids here, so later phases never look names up again:
//! - sigs: [`SigId`] (`0` = univ, `1` = none, `2` = Int, `3` = String, `4` = seq/Int are the built-ins),
//! - fields: [`FieldId`] (declared once per owning sig), functions: [`FuncId`], locals: [`LocalId`].
//!
//! Not yet supported (returns `Unsupported`, which the harness counts as a failure, never a guess):
//! temporal operators and `var` sigs/fields, module-level overloading (ambiguous names),
//! integer arithmetic operators, and macros with arguments that are not expressions.

use std::collections::HashMap;

use crate::error::{AlloyError, ErrorKind, Pos};
use crate::loader::LoadedModule;
use crate::syntax::{
    BinOp, CommandTarget, Const, Decl, Expr, ExprKind, Mult, Paragraph, Quant, SigExtends, UnOp,
};

pub type SigId = u32;
pub type FieldId = u32;
pub type FuncId = u32;
pub type LocalId = u32;

pub const SIG_UNIV: SigId = 0;
pub const SIG_NONE: SigId = 1;
pub const SIG_INT: SigId = 2;
pub const SIG_STRING: SigId = 3;
pub const SIG_SEQINT: SigId = 4;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SigKind {
    Builtin,
    User,
}

#[derive(Debug, Clone)]
pub struct Sig {
    /// Java label: `this/A` for user sigs, `univ`, `Int`, `String`, `none`, `seq/Int` for built-ins.
    pub label: String,
    /// Short name (`A`).
    pub name: String,
    pub kind: SigKind,
    /// `extends B`.
    pub parent: Option<SigId>,
    /// `in B + C` (subset) or `= B + C` (exact union) targets.
    pub subset_of: Vec<SigId>,
    pub is_exact: bool,
    pub is_abstract: bool,
    /// `one` / `lone` / `some` multiplicity of the sig.
    pub mult: Option<Mult>,
    pub is_private: bool,
    pub fields: Vec<FieldId>,
    /// Loaded module instance that declares the sig.
    pub module: usize,
    /// Declared by an `enum` (Java `Sig.isEnum`): its scope is 0 and its values are the atoms.
    pub is_enum: bool,
    /// `var sig` (membership changes over time).
    pub is_var: bool,
}

#[derive(Debug, Clone)]
pub struct Field {
    /// Java label: `this/A.f`.
    pub label: String,
    pub name: String,
    pub owner: SigId,
    /// The declared bound (multiplicity keyword removed).
    pub decl: RExpr,
    /// The local standing for `this` inside `decl`.
    pub this_local: LocalId,
    /// `var` field (its value changes over time).
    pub is_var: bool,
    /// Multiplicity keyword of the declared bound (None = none written: `one` when the bound is unary).
    pub mult: Option<Mult>,
    /// Defined field `f = e` (Java `EXACTLYOF`).
    pub defined: bool,
    pub is_private: bool,
    pub module: usize,
}

#[derive(Debug, Clone)]
pub struct Func {
    pub label: String,
    pub name: String,
    /// Number of parameters (receiver included), known at declaration time (before bodies are resolved).
    pub nparams: usize,
    /// Receiver sig for `fun A.f`; the receiver is the first parameter (`this`).
    pub owner: Option<SigId>,
    pub is_pred: bool,
    /// Parameters as locals with their declared bounds (receiver first).
    pub params: Vec<(LocalId, RExpr)>,
    /// The declarations the parameters come from (Java `Func.decls`): (number of names, `disj`), in order.
    pub param_decls: Vec<(usize, bool)>,
    pub ret: Option<RExpr>,
    pub body: RExpr,
    pub is_private: bool,
    pub module: usize,
}

#[derive(Debug, Clone)]
pub struct Assertion {
    pub name: String,
    pub body: RExpr,
    pub module: usize,
}

#[derive(Debug, Clone)]
pub struct Fact {
    pub name: Option<String>,
    pub body: RExpr,
    pub module: usize,
}

/// `disj a, b: E` in the resolved IR (Java `ExprQt` decl list entry).
#[derive(Debug, Clone, PartialEq)]
pub struct RDecl {
    pub vars: Vec<LocalId>,
    pub disjoint: bool,
    pub bound: RExpr,
}

/// Resolved expression. Formulas and expressions share one tree; their kind is decided by typing (M3.4).
#[derive(Debug, Clone, PartialEq)]
pub enum RExpr {
    Sig(SigId),
    Field(FieldId),
    Local(LocalId),
    Const(Const),
    Num(i32),
    /// String literal (an atom of the `String` sig named with its quotes).
    Str(String),
    Un(UnOp, Box<RExpr>),
    Bin(BinOp, Box<RExpr>, Box<RExpr>),
    Quant(Quant, Vec<RDecl>, Box<RExpr>),
    Compr(Vec<RDecl>, Box<RExpr>),
    Ite(Box<RExpr>, Box<RExpr>, Box<RExpr>),
    Let(Vec<(LocalId, RExpr)>, Box<RExpr>),
    /// Call of a predicate/function; arguments in parameter order (receiver first).
    Call(FuncId, Vec<RExpr>),
    /// Conjunction of expressions (`{ e1 e2 }`); `Block([])` is TRUE.
    Block(Vec<RExpr>),
    /// `disj[a, b, ...]` builtin (Java `ExprList.Op.DISJOINT`).
    Disj(Vec<RExpr>),
    /// `pred/totalOrder[elem, first, next]` builtin (Java `ExprList.Op.TOTALORDER`).
    TotalOrder(Vec<RExpr>),
    /// Overloaded name: candidates resolved by type in M3.4 (Java `ExprChoice`).
    Choice(Vec<RExpr>),
}

/// One resolved `for` entry of a command: `[exactly] start[..end][:increment] sig` (Java `CommandScope`).
#[derive(Debug, Clone, PartialEq)]
pub struct RScope {
    pub sig: SigId,
    pub start: i32,
    pub end: i32,
    pub increment: i32,
    pub exact: bool,
}

/// One resolved command (its `CommandInfo` is the same index in `World::commands`).
#[derive(Debug, Clone)]
pub struct RCommand {
    pub check: bool,
    /// For `run f` / `check A`: the formula to solve/refute. `run` with parameters is an existential.
    pub formula: RExpr,
    /// Command label (Java `Command.label`).
    pub name: String,
    /// `for N` (overall), `N int` (bitwidth), `N seq` (maximum sequence length), as written (`None` = unset).
    pub overall: Option<i32>,
    pub bitwidth: Option<i32>,
    pub maxseq: Option<i32>,
    /// Per-sig scopes from the `for ... but` list (`int`/`seq`/`steps` are not among them).
    pub scopes: Vec<RScope>,
    /// `N steps` / `min..max steps`: (min, max), max == i32::MAX for `N..` (unbounded).
    pub steps: Option<(Option<i32>, i32)>,
}

#[derive(Debug, Clone, Default)]
pub struct Model {
    pub sigs: Vec<Sig>,
    pub fields: Vec<Field>,
    pub funcs: Vec<Func>,
    pub asserts: Vec<Assertion>,
    pub facts: Vec<Fact>,
    /// Local variable names (debugging / instance output).
    pub locals: Vec<String>,
    pub commands: Vec<RCommand>,
    /// Sig facts (`sig A { ... }` appended blocks) per sig, as resolved expressions over `this`.
    pub sig_facts: Vec<(SigId, RExpr)>,
    /// Sigs forced to have an exact scope by `module m[exactly A]` parameters (Java `exactSigs`).
    pub exact_sigs: Vec<SigId>,
    /// Every string literal of the model (without quotes), in order of first use.
    pub strings: Vec<String>,
    /// The model uses `var` sigs/fields or temporal operators (Alloy 6 traces).
    pub temporal: bool,
    /// Uses of a bare name that denotes a parameterless function of this module and also functions of the same
    /// name in opened modules (Java sees all of them; identical declared types make the use ambiguous).
    pub shadowed_uses: Vec<Vec<FuncId>>,
    /// `disj f, g: e` field declarations: the fields of each group are pairwise disjoint.
    pub field_disjoint: Vec<Vec<FieldId>>,
    /// Locals standing for macro parameters (Java substitutes the argument expression at every use).
    pub macro_locals: Vec<LocalId>,
}

#[derive(Debug, Clone)]
enum Sym {
    Sig(SigId),
    Field(FieldId),
    Func(FuncId),
    Assert(usize),
    Macro(usize),
}

#[derive(Debug, Clone)]
struct MacroDef {
    params: Vec<String>,
    body: Expr,
    module: usize,
}

/// Per module instance name tables.
#[derive(Debug, Default)]
struct Scope {
    names: HashMap<String, Vec<Sym>>,
    private: HashMap<String, bool>,
    params: HashMap<String, Sym>,
    /// (alias, target instance) in source order.
    opens: Vec<(String, usize)>,
}

struct Builder<'a> {
    mods: &'a [LoadedModule],
    model: Model,
    scopes: Vec<Scope>,
    macros: Vec<MacroDef>,
    /// Locals in scope while resolving a body: name -> id.
    locals: Vec<(String, LocalId)>,
    /// Bodies of sig-local functions get `this` in scope.
    /// Macro expansion depth (guards against recursive macros).
    depth: usize,
    /// Sigs whose body is being resolved (field declarations, appended facts, sig-local functions).
    /// Inside them a field name of the sig (or an ancestor) means `this.field` (Java implicit `this`).
    this_sigs: Vec<SigId>,
    /// Resolving a field declaration: only fields of the sig itself and its ancestors are visible, no functions.
    in_field_decl: bool,
}

/// Builds the resolved model for the loaded modules (index 0 = root).
pub fn build(mods: &[LoadedModule]) -> Result<Model, AlloyError> {
    let mut b = Builder {
        mods,
        model: Model::default(),
        scopes: Vec::new(),
        macros: Vec::new(),
        locals: Vec::new(),
        depth: 0,
        this_sigs: Vec::new(),
        in_field_decl: false,
    };
    b.builtins();
    for _ in mods {
        b.scopes.push(Scope::default());
    }
    for i in 0..mods.len() {
        b.declare(i)?;
    }
    b.bind_params()?;
    // Sig hierarchy first: a sig fact may use fields of ancestors declared later in the file.
    for i in 0..mods.len() {
        b.link_sigs(i)?;
    }
    for i in 0..mods.len() {
        b.resolve(i)?;
    }
    b.check_identical_overloads()?;
    // Commands last: their formulas inline predicates, whose bodies are resolved above.
    // Only the root module's commands are run (Java `World::commands`).
    if let Some(root) = mods.first() {
        for p in &root.module.paragraphs {
            if let Paragraph::Command(c) = p {
                let cmd = b.resolve_command(0, c)?;
                b.model.commands.push(cmd);
            }
        }
    }
    // Java `CompModule.addDefaultCommand`: a root module without commands runs `Run Default` (formula TRUE).
    if b.model.commands.is_empty() && !mods.is_empty() {
        let has_command = mods[0]
            .module
            .paragraphs
            .iter()
            .any(|p| matches!(p, Paragraph::Command(_)));
        if !has_command {
            b.model.commands.push(RCommand {
                check: false,
                formula: RExpr::Block(Vec::new()),
                name: "Default".to_string(),
                overall: None,
                bitwidth: None,
                maxseq: None,
                scopes: Vec::new(),
                steps: None,
            });
        }
    }
    Ok(b.model)
}

fn err<T>(
    module: usize,
    mods: &[LoadedModule],
    line: i32,
    col: i32,
    msg: impl Into<String>,
) -> Result<T, AlloyError> {
    Err(AlloyError::new(
        ErrorKind::Type,
        Some(Pos {
            file: mods[module].path.clone(),
            line,
            col,
        }),
        msg,
    ))
}

impl<'a> Builder<'a> {
    fn builtins(&mut self) {
        let mk = |label: &str| Sig {
            label: label.to_string(),
            name: label.to_string(),
            kind: SigKind::Builtin,
            parent: None,
            subset_of: Vec::new(),
            is_exact: false,
            is_abstract: false,
            mult: None,
            is_private: false,
            fields: Vec::new(),
            module: 0,
            is_enum: false,
            is_var: false,
        };
        self.model.sigs = vec![
            mk("univ"),
            mk("none"),
            mk("Int"),
            mk("String"),
            mk("seq/Int"),
        ];
    }

    /// Phase 1: create the sigs, fields, functions, assertions and macros of instance `i`.
    fn declare(&mut self, i: usize) -> Result<(), AlloyError> {
        let module = &self.mods[i].module;
        if i == 0 {
            // A root module with parameters: each parameter is a free sig (no opener binds it).
            let params = module
                .header
                .as_ref()
                .map(|h| h.params.clone())
                .unwrap_or_default();
            for p in params {
                let id = self.push_sig(i, &p, None, false, None, false);
                self.add_name(i, &p, Sym::Sig(id), false);
            }
        }
        for p in &module.paragraphs {
            match p {
                Paragraph::Enum(e) => {
                    let id = self.push_sig(i, &e.name, None, true, None, e.is_private);
                    self.model.sigs[id as usize].is_enum = true;
                    self.add_name(i, &e.name, Sym::Sig(id), e.is_private);
                    for v in &e.values {
                        let vid = self.push_sig(i, v, Some(id), false, Some(Mult::One), false);
                        self.add_name(i, v, Sym::Sig(vid), false);
                    }
                }
                Paragraph::Sig(s) => {
                    for name in &s.names {
                        let id = self.model.sigs.len() as SigId;
                        let mult = s
                            .quals
                            .one
                            .then_some(Mult::One)
                            .or(s.quals.lone.then_some(Mult::Lone))
                            .or(s.quals.some.then_some(Mult::Some));
                        self.push_sig(i, name, None, s.quals.is_abstract, mult, s.quals.is_private);
                        if s.quals.var {
                            self.model.sigs[id as usize].is_var = true;
                            self.model.temporal = true;
                        }
                        self.add_name(i, name, Sym::Sig(id), s.quals.is_private);
                        for d in &s.fields {
                            for f in &d.names {
                                let fid = self.model.fields.len() as FieldId;
                                self.model.fields.push(Field {
                                    label: format!("this/{name}.{f}"),
                                    name: f.clone(),
                                    owner: id,
                                    decl: RExpr::Num(0),
                                    this_local: 0,
                                    is_var: d.var,
                                    mult: None,
                                    defined: false,
                                    is_private: d.is_private,
                                    module: i,
                                });
                                self.model.sigs[id as usize].fields.push(fid);
                                self.add_name(i, f, Sym::Field(fid), d.is_private);
                            }
                        }
                    }
                }
                Paragraph::Fun(f) | Paragraph::Pred(f) => {
                    let (owner, name) = split_owner(&f.name);
                    let fid = self.model.funcs.len() as FuncId;
                    let nparams = f.params.iter().map(|d| d.names.len()).sum::<usize>()
                        + owner.is_some() as usize;
                    self.model.funcs.push(Func {
                        label: f.name.clone(),
                        name: name.to_string(),
                        nparams,
                        owner: None,
                        is_pred: matches!(p, Paragraph::Pred(_)),
                        params: Vec::new(),
                        param_decls: Vec::new(),
                        ret: None,
                        body: RExpr::Block(Vec::new()),
                        is_private: f.is_private,
                        module: i,
                    });
                    let _ = owner;
                    self.add_name(i, name, Sym::Func(fid), f.is_private);
                }
                Paragraph::Assert(a) => {
                    let name = a.name.clone().unwrap_or_default();
                    let idx = self.model.asserts.len();
                    self.model.asserts.push(Assertion {
                        name: name.clone(),
                        body: RExpr::Block(Vec::new()),
                        module: i,
                    });
                    if !name.is_empty() {
                        self.add_name(i, &name, Sym::Assert(idx), false);
                    }
                }
                Paragraph::Macro(m) => {
                    let idx = self.macros.len();
                    self.macros.push(MacroDef {
                        params: m.params.clone(),
                        body: m.body.clone(),
                        module: i,
                    });
                    self.add_name(i, &m.name, Sym::Macro(idx), m.is_private);
                }
                Paragraph::Open(_) | Paragraph::Fact(_) | Paragraph::Command(_) => {}
            }
        }
        Ok(())
    }

    /// Appends a user sig (Java `CompModule.addSig`) and returns its id.
    fn push_sig(
        &mut self,
        i: usize,
        name: &str,
        parent: Option<SigId>,
        is_abstract: bool,
        mult: Option<Mult>,
        is_private: bool,
    ) -> SigId {
        let id = self.model.sigs.len() as SigId;
        self.model.sigs.push(Sig {
            label: format!("this/{name}"),
            name: name.to_string(),
            kind: SigKind::User,
            parent,
            subset_of: Vec::new(),
            is_exact: false,
            is_abstract,
            mult,
            is_private,
            fields: Vec::new(),
            module: i,
            is_enum: false,
            is_var: false,
        });
        id
    }

    fn add_name(&mut self, i: usize, name: &str, sym: Sym, private: bool) {
        self.scopes[i]
            .names
            .entry(name.to_string())
            .or_default()
            .push(sym);
        self.scopes[i].private.insert(name.to_string(), private);
    }

    /// Phase 1b: bind module parameters of every instance from its opener's arguments.
    fn bind_params(&mut self) -> Result<(), AlloyError> {
        // Parents come before children in the loaded list, so a child's parameters are bound
        // (by its opener) before the child binds its own opens.
        for i in 0..self.mods.len() {
            let resolved = self.mods[i].opens.clone();
            for r in &resolved {
                self.scopes[i].opens.push((r.alias.clone(), r.target));
                let Some(k) = r.paragraph else { continue };
                let Some((oloc, oargs)) = crate::loader::open_args(&self.mods[i].module, k) else {
                    continue;
                };
                let target = r.target;
                let params = self.mods[target]
                    .module
                    .header
                    .as_ref()
                    .map(|h| h.params.clone())
                    .unwrap_or_default();
                if params.len() != oargs.len() {
                    return err(
                        i,
                        self.mods,
                        oloc.line,
                        oloc.col,
                        format!(
                            "You supplied {} arguments to the open statement, but the imported module requires {} arguments.",
                            oargs.len(),
                            params.len()
                        ),
                    );
                }
                let args = oargs.clone();
                let exact_params = self.mods[target]
                    .module
                    .header
                    .as_ref()
                    .map(|h| h.exact_params.clone())
                    .unwrap_or_default();
                for (p, a) in params.iter().zip(args.iter()) {
                    let sym = self.resolve_sig_arg(i, a)?;
                    if let Sym::Sig(sid) = &sym {
                        if exact_params.contains(p) && !self.model.exact_sigs.contains(sid) {
                            self.model.exact_sigs.push(*sid);
                        }
                    }
                    self.scopes[target].params.insert(p.clone(), sym);
                }
            }
        }
        Ok(())
    }

    /// Module argument of an `open` (a sig name, as Java requires for sig parameters).
    fn resolve_sig_arg(&self, i: usize, a: &Expr) -> Result<Sym, AlloyError> {
        let ExprKind::Name(n) = &a.kind else {
            return err(
                i,
                self.mods,
                a.loc.line,
                a.loc.col,
                "Module arguments must be sig names.",
            );
        };
        match self.lookup(i, n) {
            Some(syms) if syms.len() == 1 && matches!(syms[0], Sym::Sig(_)) => Ok(syms[0].clone()),
            _ => err(
                i,
                self.mods,
                a.loc.line,
                a.loc.col,
                format!("The name \"{n}\" cannot be found."),
            ),
        }
    }

    /// Java type-checks every body of the root module: a bare name that denotes several parameterless functions
    /// with the same declared type can never be resolved (`This name is ambiguous due to multiple matches`).
    fn check_identical_overloads(&self) -> Result<(), AlloyError> {
        fn walk(e: &RExpr, found: &mut Option<Vec<FuncId>>, funcs: &[Func]) {
            if found.is_some() {
                return;
            }
            match e {
                RExpr::Choice(c) if c.len() > 1 => {
                    let calls: Vec<FuncId> = c
                        .iter()
                        .filter_map(|x| match x {
                            RExpr::Call(f, a) if a.is_empty() => Some(*f),
                            _ => None,
                        })
                        .collect();
                    if calls.len() == c.len() {
                        let first = &funcs[calls[0] as usize];
                        if first.ret.is_some()
                            && calls.iter().all(|f| {
                                funcs[*f as usize].ret == first.ret
                                    && funcs[*f as usize].is_pred == first.is_pred
                            })
                        {
                            *found = Some(calls);
                            return;
                        }
                    }
                    for x in c {
                        walk(x, found, funcs);
                    }
                }
                RExpr::Un(_, a) => walk(a, found, funcs),
                RExpr::Bin(_, a, b) => {
                    walk(a, found, funcs);
                    walk(b, found, funcs);
                }
                RExpr::Quant(_, ds, b) | RExpr::Compr(ds, b) => {
                    for d in ds {
                        walk(&d.bound, found, funcs);
                    }
                    walk(b, found, funcs);
                }
                RExpr::Ite(a, b, c) => {
                    walk(a, found, funcs);
                    walk(b, found, funcs);
                    walk(c, found, funcs);
                }
                RExpr::Let(bs, b) => {
                    for (_, x) in bs {
                        walk(x, found, funcs);
                    }
                    walk(b, found, funcs);
                }
                RExpr::Call(_, args)
                | RExpr::Block(args)
                | RExpr::Disj(args)
                | RExpr::TotalOrder(args) => {
                    for x in args {
                        walk(x, found, funcs);
                    }
                }
                _ => {}
            }
        }
        let mut found: Option<Vec<FuncId>> = None;
        for group in &self.model.shadowed_uses {
            let first = &self.model.funcs[group[0] as usize];
            if std::env::var("KDBG_SEMA").is_ok() {
                eprintln!("group {:?} ret0={:?}", group, first.ret);
            }
            if first.ret.is_some()
                && group.iter().all(|f| {
                    let g = &self.model.funcs[*f as usize];
                    g.ret == first.ret && g.is_pred == first.is_pred
                })
            {
                found = Some(group.clone());
                break;
            }
        }
        for f in self.model.funcs.iter() {
            walk(&f.body, &mut found, &self.model.funcs);
        }
        for f in self.model.facts.iter() {
            walk(&f.body, &mut found, &self.model.funcs);
        }
        if let Some(calls) = found {
            let names: Vec<String> = calls
                .iter()
                .map(|f| {
                    format!(
                        "{} {}",
                        if self.model.funcs[*f as usize].is_pred {
                            "pred"
                        } else {
                            "fun"
                        },
                        self.model.funcs[*f as usize].label
                    )
                })
                .collect();
            return Err(AlloyError::new(
                ErrorKind::Type,
                None,
                format!(
                    "This name is ambiguous due to multiple matches:
{}",
                    names.join(
                        "
"
                    )
                ),
            ));
        }
        Ok(())
    }

    /// Resolves `extends` / `in` / `=` of every sig of instance `i` (the sig hierarchy).
    fn link_sigs(&mut self, i: usize) -> Result<(), AlloyError> {
        let mut sig_next = self
            .model
            .sigs
            .iter()
            .position(|x| x.module == i && x.kind == SigKind::User)
            .unwrap_or(0);
        if i == 0 {
            sig_next += self.mods[0]
                .module
                .header
                .as_ref()
                .map_or(0, |h| h.params.len());
        }
        let paragraphs = self.mods[i].module.paragraphs.clone();
        for p in &paragraphs {
            match p {
                Paragraph::Sig(s) => {
                    for k in 0..s.names.len() {
                        let sid = (sig_next + k) as SigId;
                        match &s.extends {
                            Some(SigExtends::Extends(e)) => {
                                let p = self.sig_ref(i, e)?;
                                self.model.sigs[sid as usize].parent = Some(p);
                            }
                            Some(SigExtends::In(v)) | Some(SigExtends::Equal(v)) => {
                                let mut out = Vec::new();
                                for e in v {
                                    out.push(self.sig_ref(i, e)?);
                                }
                                self.model.sigs[sid as usize].subset_of = out;
                                if matches!(s.extends, Some(SigExtends::Equal(_))) {
                                    self.model.sigs[sid as usize].is_exact = true;
                                }
                            }
                            None => {}
                        }
                    }
                    sig_next += s.names.len();
                }
                Paragraph::Enum(e) => sig_next += 1 + e.values.len(),
                _ => {}
            }
        }
        Ok(())
    }

    /// Phase 2: resolve everything that refers to names of instance `i`.
    fn resolve(&mut self, i: usize) -> Result<(), AlloyError> {
        // Entities of one instance are declared contiguously and in source order, so counters suffice.
        let mut sig_next = self
            .model
            .sigs
            .iter()
            .position(|x| x.module == i && x.kind == SigKind::User)
            .unwrap_or(0);
        if i == 0 {
            // Root parameters were declared as sigs before the root's own sigs.
            sig_next += self.mods[0]
                .module
                .header
                .as_ref()
                .map_or(0, |h| h.params.len());
        }
        let mut func_next = self
            .model
            .funcs
            .iter()
            .position(|x| x.module == i)
            .unwrap_or(0);
        let mut assert_next = self
            .model
            .asserts
            .iter()
            .position(|x| x.module == i)
            .unwrap_or(0);
        let paragraphs = self.mods[i].module.paragraphs.clone();
        for p in &paragraphs {
            match p {
                Paragraph::Sig(s) => {
                    let ids: Vec<SigId> = (0..s.names.len())
                        .map(|k| (sig_next + k) as SigId)
                        .collect();
                    sig_next += s.names.len();
                    self.resolve_sig(i, s, &ids)?;
                }
                Paragraph::Enum(e) => sig_next += 1 + e.values.len(),
                Paragraph::Fact(f) => {
                    let body = self.conj(i, &f.body)?;
                    self.model.facts.push(Fact {
                        name: f.name.clone(),
                        body,
                        module: i,
                    });
                }
                Paragraph::Fun(f) | Paragraph::Pred(f) => {
                    self.resolve_func(i, f, func_next as FuncId)?;
                    func_next += 1;
                }
                Paragraph::Assert(a) => {
                    let body = self.conj(i, &a.body)?;
                    self.model.asserts[assert_next].body = body;
                    assert_next += 1;
                }
                Paragraph::Command(_) => {}
                Paragraph::Open(_) | Paragraph::Macro(_) => {}
            }
        }
        Ok(())
    }

    fn resolve_sig(
        &mut self,
        i: usize,
        s: &crate::syntax::SigDecl,
        ids: &[SigId],
    ) -> Result<(), AlloyError> {
        for &sid in ids {
            match &s.extends {
                Some(SigExtends::Extends(e)) => {
                    let p = self.sig_ref(i, e)?;
                    self.model.sigs[sid as usize].parent = Some(p);
                }
                Some(SigExtends::In(v)) => {
                    let mut out = Vec::new();
                    for e in v {
                        out.push(self.sig_ref(i, e)?);
                    }
                    self.model.sigs[sid as usize].subset_of = out;
                }
                Some(SigExtends::Equal(v)) => {
                    let mut out = Vec::new();
                    for e in v {
                        out.push(self.sig_ref(i, e)?);
                    }
                    self.model.sigs[sid as usize].subset_of = out;
                    self.model.sigs[sid as usize].is_exact = true;
                }
                None => {}
            }
            // Field declarations of this sig (each name of a multi-name sig has its own fields).
            let fields = self.model.sigs[sid as usize].fields.clone();
            let mut k = 0;
            for d in &s.fields {
                if d.disjoint && d.names.len() > 1 {
                    self.model
                        .field_disjoint
                        .push(fields[k..k + d.names.len()].to_vec());
                }
                for _ in &d.names {
                    let fid = fields[k];
                    k += 1;
                    let (mult, inner) = strip_mult(&d.expr);
                    let defined = matches!(inner.kind, ExprKind::Unary(UnOp::ExactlyOf, _));
                    let inner = match &inner.kind {
                        ExprKind::Unary(UnOp::ExactlyOf, e) => (**e).clone(),
                        _ => inner.clone(),
                    };
                    let mark = self.locals.len();
                    let lid = self.new_local("this");
                    self.locals.push(("this".into(), lid));
                    self.this_sigs.push(sid);
                    self.in_field_decl = true;
                    let decl = self.expr(i, &inner);
                    self.in_field_decl = false;
                    self.this_sigs.pop();
                    self.locals.truncate(mark);
                    let decl = decl?;
                    let f = &mut self.model.fields[fid as usize];
                    f.decl = decl;
                    f.this_local = lid;
                    f.mult = mult;
                    f.defined = defined;
                }
            }
            if let Some(app) = &s.appended_fact {
                let body = self.conj_with_this(i, sid, app)?;
                self.model.sig_facts.push((sid, body));
            }
        }
        Ok(())
    }

    fn resolve_func(
        &mut self,
        i: usize,
        f: &crate::syntax::Func,
        fid: FuncId,
    ) -> Result<(), AlloyError> {
        let (owner_name, _) = split_owner(&f.name);
        let mark = self.locals.len();
        let mut params = Vec::new();
        let mut param_decls: Vec<(usize, bool)> = Vec::new();
        let mut pushed_this = false;
        if let Some(on) = owner_name {
            let builtin = match on {
                "String" => Some(SIG_STRING),
                "Int" => Some(SIG_INT),
                "univ" => Some(SIG_UNIV),
                _ => None,
            };
            let owner_sig = match builtin {
                Some(b) => Some(b),
                None => match self.lookup(i, on).and_then(|v| v.into_iter().next()) {
                    Some(Sym::Sig(sid)) => Some(sid),
                    _ => None,
                },
            };
            if let Some(sid) = owner_sig {
                let lid = self.new_local("this");
                self.locals.push(("this".into(), lid));
                params.push((lid, RExpr::Sig(sid)));
                param_decls.push((1, false));
                self.model.funcs[fid as usize].owner = Some(sid);
                // Java `populate`: only sig facts and field declarations have a root sig (implicit `this.f`);
                // a sig-local function sees the raw fields.
                pushed_this = true;
            }
        }
        for d in &f.params {
            params.extend(self.decl_locals(i, d)?);
            param_decls.push((d.names.len(), d.disjoint));
        }
        let ret = match &f.ret {
            Some(r) => Some(self.expr(i, r)?),
            None => None,
        };
        let body = self.expr(i, &f.body);
        let _ = pushed_this;
        self.locals.truncate(mark);
        let body = body?;
        let func = &mut self.model.funcs[fid as usize];
        func.params = params;
        func.param_decls = param_decls;
        func.ret = ret;
        func.body = body;
        Ok(())
    }

    fn resolve_command(
        &mut self,
        i: usize,
        c: &crate::syntax::Command,
    ) -> Result<RCommand, AlloyError> {
        let name = match &c.target {
            CommandTarget::Name(n) => n.clone(),
            CommandTarget::Block(_) => String::new(),
        };
        let formula = match &c.target {
            CommandTarget::Block(items) => self.conj(i, items)?,
            CommandTarget::Name(n) => match self.lookup(i, n).and_then(|v| v.into_iter().next()) {
                Some(Sym::Assert(idx)) if c.check => self.model.asserts[idx].body.clone(),
                Some(Sym::Func(fid)) if !c.check => {
                    let params = self.model.funcs[fid as usize].params.clone();
                    let args: Vec<RExpr> = params.iter().map(|(l, _)| RExpr::Local(*l)).collect();
                    let mut call = RExpr::Call(fid, args);
                    // `run f` on a function means `some f[..]` (the function value is non-empty)
                    if !self.model.funcs[fid as usize].is_pred {
                        call = RExpr::Un(UnOp::Some, Box::new(call));
                    }
                    if params.is_empty() {
                        call
                    } else {
                        // Java: `some f.decls | body` (one declaration per group of names, `disj` kept)
                        let mut groups = self.model.funcs[fid as usize].param_decls.clone();
                        if groups.iter().map(|g| g.0).sum::<usize>() != params.len() {
                            groups = vec![(1, false); params.len()];
                        }
                        let mut decls = Vec::new();
                        let mut k = 0;
                        for (cnt, disjoint) in groups {
                            decls.push(RDecl {
                                vars: params[k..k + cnt].iter().map(|(l, _)| *l).collect(),
                                disjoint,
                                bound: params[k].1.clone(),
                            });
                            k += cnt;
                        }
                        RExpr::Quant(Quant::Some, decls, Box::new(call))
                    }
                }
                _ => {
                    return err(
                        i,
                        self.mods,
                        c.loc.line,
                        c.loc.col,
                        format!("The predicate/assertion name \"{n}\" cannot be found."),
                    )
                }
            },
        };
        let label = c.label.clone().unwrap_or_else(|| name.clone());
        let mut scopes = Vec::new();
        for t in &c.scopes.typescopes {
            let sig = match t.sig.as_str() {
                "String" => SIG_STRING,
                n => match self.lookup(i, n).and_then(|v| v.into_iter().next()) {
                    Some(Sym::Sig(id)) => id,
                    _ => {
                        return err(
                            i,
                            self.mods,
                            t.loc.line,
                            t.loc.col,
                            format!("The name \"{n}\" cannot be found."),
                        )
                    }
                },
            };
            scopes.push(RScope {
                sig,
                start: t.start,
                end: t.end,
                increment: t.increment,
                exact: t.exactly,
            });
        }
        Ok(RCommand {
            check: c.check,
            formula,
            name: label,
            overall: c.scopes.overall,
            bitwidth: c.scopes.bitwidth,
            maxseq: c.scopes.maxseq,
            scopes,
            steps: c.scopes.steps.map(|s| (s.min, s.max)),
        })
    }

    /// Sig reference in `extends` / `in`: must denote a sig.
    fn sig_ref(&self, i: usize, e: &Expr) -> Result<SigId, AlloyError> {
        if let ExprKind::Name(n) = &e.kind {
            if let Some(v) = self.lookup(i, n) {
                if let Some(Sym::Sig(id)) = v.first() {
                    return Ok(*id);
                }
            }
            return match n.as_str() {
                "univ" => Ok(SIG_UNIV),
                "Int" => Ok(SIG_INT),
                "String" => Ok(SIG_STRING),
                "none" => Ok(SIG_NONE),
                "seq/Int" => Ok(SIG_SEQINT),
                _ => err(
                    i,
                    self.mods,
                    e.loc.line,
                    e.loc.col,
                    format!("The name \"{n}\" cannot be found."),
                ),
            };
        }
        err(i, self.mods, e.loc.line, e.loc.col, "Expected a sig name.")
    }

    fn decl_locals(&mut self, i: usize, d: &Decl) -> Result<Vec<(LocalId, RExpr)>, AlloyError> {
        let bound = self.expr(i, &d.expr)?;
        let mut out = Vec::new();
        for n in &d.names {
            let lid = self.new_local(n);
            self.locals.push((n.clone(), lid));
            out.push((lid, bound.clone()));
        }
        Ok(out)
    }

    fn new_local(&mut self, name: &str) -> LocalId {
        self.model.locals.push(name.to_string());
        (self.model.locals.len() - 1) as LocalId
    }

    fn conj(&mut self, i: usize, items: &[Expr]) -> Result<RExpr, AlloyError> {
        let mut out = Vec::new();
        for e in items {
            out.push(self.expr(i, e)?);
        }
        Ok(RExpr::Block(out))
    }

    /// Appended sig fact: `this` is the sig itself.
    fn conj_with_this(
        &mut self,
        i: usize,
        sid: SigId,
        items: &[Expr],
    ) -> Result<RExpr, AlloyError> {
        let mark = self.locals.len();
        let lid = self.new_local("this");
        self.locals.push(("this".into(), lid));
        self.this_sigs.push(sid);
        let body = self.conj(i, items);
        self.this_sigs.pop();
        self.locals.truncate(mark);
        Ok(RExpr::Quant(
            Quant::All,
            vec![RDecl {
                vars: vec![lid],
                disjoint: false,
                bound: RExpr::Sig(sid),
            }],
            Box::new(body?),
        ))
    }

    /// Looks a name up as seen from instance `i`: own names, parameters, then `alias/rest`, then the
    /// public names of the opens. Returns `None` if not found.
    fn lookup(&self, i: usize, name: &str) -> Option<Vec<Sym>> {
        let name = name.strip_prefix("this/").unwrap_or(name);
        if let Some(v) = self.scopes[i].names.get(name) {
            return Some(v.clone());
        }
        if let Some(s) = self.scopes[i].params.get(name) {
            return Some(vec![s.clone()]);
        }
        if let Some((alias, rest)) = name.split_once('/') {
            if let Some((_, target)) = self.scopes[i].opens.iter().find(|(a, _)| a == alias) {
                return self.lookup_public(*target, rest);
            }
        }
        for (_, target) in &self.scopes[i].opens {
            if let Some(v) = self.lookup_public(*target, name) {
                return Some(v);
            }
        }
        None
    }

    /// Unqualified name (Java `getRawQS` then `getRawNQS`): the module's own names first; otherwise the
    /// public names of every module reachable through `open` (transitively). Several candidates form a choice.
    fn lookup_unqualified(&self, i: usize, name: &str) -> Option<Vec<Sym>> {
        if let Some(v) = self.scopes[i].names.get(name) {
            // Java (CompModule.getRawNQS / populate) also sees the functions of the opened modules next to a
            // field or sig of this module; the type checker picks one (e.g. `x.next` with util/ordering).
            if v.iter().all(|s| matches!(s, Sym::Field(_) | Sym::Sig(_))) {
                let mut extra: Vec<Sym> = Vec::new();
                let mut visited = vec![i];
                for (_, t) in &self.scopes[i].opens {
                    self.collect_public(*t, name, &mut visited, &mut extra);
                }
                let mut out = v.clone();
                for x in extra {
                    if matches!(x, Sym::Func(_)) && !out.iter().any(|o| same_sym(o, &x)) {
                        out.push(x);
                    }
                }
                return Some(out);
            }
            return Some(v.clone());
        }
        if let Some(s) = self.scopes[i].params.get(name) {
            return Some(vec![s.clone()]);
        }
        let mut out: Vec<Sym> = Vec::new();
        let mut visited = vec![i];
        for (_, t) in &self.scopes[i].opens {
            self.collect_public(*t, name, &mut visited, &mut out);
        }
        if out.is_empty() {
            None
        } else {
            Some(out)
        }
    }

    fn collect_public(&self, t: usize, name: &str, visited: &mut Vec<usize>, out: &mut Vec<Sym>) {
        if visited.contains(&t) {
            return;
        }
        visited.push(t);
        let sc = &self.scopes[t];
        if !sc.private.get(name).copied().unwrap_or(false) {
            let mut found: Vec<Sym> = sc.names.get(name).cloned().unwrap_or_default();
            if let Some(s) = sc.params.get(name) {
                found.push(s.clone());
            }
            for f in found {
                if !out
                    .iter()
                    .any(|o| same_sym(o, &f) || self.same_instance_func(o, &f))
                {
                    out.push(f);
                }
            }
        }
        for (_, t2) in &sc.opens {
            self.collect_public(*t2, name, visited, out);
        }
    }

    /// The same function of the same module file instantiated with the same arguments (Java loads such a
    /// module once, so e.g. an explicit `open util/integer` does not duplicate the implicit one).
    fn same_instance_func(&self, a: &Sym, b: &Sym) -> bool {
        let (Sym::Func(x), Sym::Func(y)) = (a, b) else {
            return false;
        };
        let (fx, fy) = (
            &self.model.funcs[*x as usize],
            &self.model.funcs[*y as usize],
        );
        if fx.name != fy.name
            || fx.nparams != fy.nparams
            || fx.is_pred != fy.is_pred
            || fx.module == fy.module
        {
            return fx.module == fy.module && x == y;
        }
        let (mx, my) = (&self.mods[fx.module], &self.mods[fy.module]);
        if mx.path != my.path {
            return false;
        }
        let (px, py) = (
            &self.scopes[fx.module].params,
            &self.scopes[fy.module].params,
        );
        px.len() == py.len()
            && px
                .iter()
                .all(|(k, v)| py.get(k).map_or(false, |w| same_sym(v, w)))
    }

    fn lookup_public(&self, target: usize, name: &str) -> Option<Vec<Sym>> {
        let sc = &self.scopes[target];
        if let Some(v) = sc.names.get(name) {
            if sc.private.get(name).copied().unwrap_or(false) {
                return None;
            }
            return Some(v.clone());
        }
        if let Some(s) = sc.params.get(name) {
            return Some(vec![s.clone()]);
        }
        if let Some((alias, rest)) = name.split_once('/') {
            if let Some((_, t)) = sc.opens.iter().find(|(a, _)| a == alias) {
                return self.lookup_public(*t, rest);
            }
        }
        None
    }

    /// Expression resolution (names, operators, quantifiers, calls, macros).
    fn expr(&mut self, i: usize, e: &Expr) -> Result<RExpr, AlloyError> {
        Ok(match &e.kind {
            ExprKind::Name(n) => self.name(i, e, n, &[])?,
            ExprKind::Const(Const::This) => self.name(i, e, "this", &[])?,
            ExprKind::Const(c) => match c {
                Const::Univ => RExpr::Sig(SIG_UNIV),
                Const::None => RExpr::Sig(SIG_NONE),
                Const::SigInt => RExpr::Sig(SIG_INT),
                Const::SigString => RExpr::Sig(SIG_STRING),
                other => RExpr::Const(*other),
            },
            ExprKind::Num(n) => RExpr::Num(*n),
            ExprKind::Str(text) => {
                if !self.model.strings.contains(text) {
                    self.model.strings.push(text.clone());
                }
                RExpr::Str(text.clone())
            }
            ExprKind::Unary(op, x) => {
                if matches!(
                    op,
                    UnOp::Always
                        | UnOp::Eventually
                        | UnOp::Historically
                        | UnOp::Once
                        | UnOp::Before
                        | UnOp::After
                        | UnOp::Prime
                ) {
                    self.model.temporal = true;
                }
                RExpr::Un(*op, Box::new(self.expr(i, x)?))
            }
            ExprKind::Binary(BinOp::Join, l, r) => {
                let cands = self.func_cands(i, r, 1);
                if !cands.is_empty() {
                    let recv = self.expr(i, l)?;
                    return Ok(Self::calls(cands, vec![recv]));
                }
                // Java `CompModule.process`: a name that is both a one-argument function and a field/sig gives a
                // choice between the joins and the calls; the type checker picks one.
                let mixed = self.mixed_func_cands(i, r);
                if !mixed.is_empty() {
                    let recv = self.expr(i, l)?;
                    let alts = match self.expr(i, r)? {
                        RExpr::Choice(v) if v.len() > 1 => v,
                        other => vec![other],
                    };
                    let mut out = Vec::new();
                    for a in alts {
                        out.push(match a {
                            RExpr::Choice(mut v) if v.len() == 1 => {
                                RExpr::Choice(vec![RExpr::Bin(
                                    BinOp::Join,
                                    Box::new(recv.clone()),
                                    Box::new(v.remove(0)),
                                )])
                            }
                            other => {
                                RExpr::Bin(BinOp::Join, Box::new(recv.clone()), Box::new(other))
                            }
                        });
                    }
                    for f in mixed {
                        out.push(RExpr::Call(f, vec![recv.clone()]));
                    }
                    return Ok(RExpr::Choice(out));
                }
                // Java `populate`: a field of the enclosing sig is `this.f` in every position (`x.@f` avoids it).
                let rr = self.expr(i, r)?;
                let ll = self.expr(i, l)?;
                Self::join_over(ll, rr)
            }
            ExprKind::Binary(op, l, r) => {
                if matches!(
                    op,
                    BinOp::Until | BinOp::Releases | BinOp::Since | BinOp::Triggered
                ) {
                    self.model.temporal = true;
                }
                RExpr::Bin(*op, Box::new(self.expr(i, l)?), Box::new(self.expr(i, r)?))
            }
            ExprKind::BoxJoin(f, args) => {
                if let ExprKind::Name(n) = &f.kind {
                    if n == "disj" {
                        return Ok(RExpr::Disj(self.exprs(i, args)?));
                    }
                    if n == "pred/totalOrder" {
                        return Ok(RExpr::TotalOrder(self.exprs(i, args)?));
                    }
                }
                // `Int[e]` casts an integer to its `Int` atom (Java CAST2SIGINT).
                if matches!(&f.kind, ExprKind::Const(Const::SigInt)) && args.len() == 1 {
                    return Ok(RExpr::Un(UnOp::SigInt, Box::new(self.expr(i, &args[0])?)));
                }
                // `x.f[a]` where `f` takes parameters: call with the receiver first.
                if let ExprKind::Binary(BinOp::Join, l, r) = &f.kind {
                    // Same for a macro: the receiver is its first parameter.
                    if let ExprKind::Name(mn) = &r.kind {
                        if let Some(Sym::Macro(m)) =
                            self.lookup(i, mn).and_then(|v| v.into_iter().next())
                        {
                            if self.macros[m].params.len() == args.len() + 1 {
                                let mut all = vec![(**l).clone()];
                                all.extend(args.iter().cloned());
                                return self.macro_call(i, e, m, &all);
                            }
                        }
                    }
                    let cands = self.func_cands(i, r, args.len() + 1);
                    if !cands.is_empty() {
                        let mut a = vec![self.expr(i, l)?];
                        a.extend(self.exprs(i, args)?);
                        return Ok(Self::calls(cands, a));
                    }
                }
                // `f[a, b]`: a call when `f` names a function, else a join `b.a` (Java BoxJoin).
                if let ExprKind::Name(n) = &f.kind {
                    let cands = self.func_cands(i, f, args.len());
                    if !cands.is_empty() {
                        let a = self.exprs(i, args)?;
                        return Ok(Self::calls(cands, a));
                    }
                    if let Some(v) = self.lookup(i, n) {
                        // `f[a, b]` is a call only when `f` takes exactly that many parameters; otherwise it is a join.
                        if let Some(Sym::Func(fid)) = v.first() {
                            if self.model.funcs[*fid as usize].nparams == args.len() {
                                let mut a = Vec::new();
                                for x in args {
                                    a.push(self.expr(i, x)?);
                                }
                                return Ok(RExpr::Call(*fid, a));
                            }
                        }
                        // `m[a, b]` is a call only when `m` takes that many parameters; a parameterless
                        // macro (a relation) boxed with arguments is a join, as in Java.
                        if let Some(Sym::Macro(m)) = v.first() {
                            let m = *m;
                            if !args.is_empty() && self.macros[m].params.len() == args.len() {
                                return self.macro_call(i, e, m, args);
                            }
                        }
                    }
                }
                let mut acc = self.expr(i, f)?;
                for a in args {
                    let arg = self.expr(i, a)?;
                    acc = Self::join_over(arg, acc);
                }
                acc
            }
            ExprKind::Quant(q, decls, body) => {
                let mark = self.locals.len();
                let mut ds = Vec::new();
                for d in decls {
                    let bound = self.expr(i, &d.expr)?;
                    let mut vars = Vec::new();
                    for n in &d.names {
                        let lid = self.new_local(n);
                        self.locals.push((n.clone(), lid));
                        vars.push(lid);
                    }
                    ds.push(RDecl {
                        vars,
                        disjoint: d.disjoint,
                        bound,
                    });
                }
                let b = self.expr(i, body);
                self.locals.truncate(mark);
                RExpr::Quant(*q, ds, Box::new(b?))
            }
            ExprKind::Compr(decls, body) => {
                let mark = self.locals.len();
                let mut ds = Vec::new();
                for d in decls {
                    let bound = self.expr(i, &d.expr)?;
                    let mut vars = Vec::new();
                    for n in &d.names {
                        let lid = self.new_local(n);
                        self.locals.push((n.clone(), lid));
                        vars.push(lid);
                    }
                    ds.push(RDecl {
                        vars,
                        disjoint: d.disjoint,
                        bound,
                    });
                }
                let b = self.expr(i, body);
                self.locals.truncate(mark);
                RExpr::Compr(ds, Box::new(b?))
            }
            ExprKind::Let(binds, body) => {
                let mark = self.locals.len();
                let mut bs = Vec::new();
                for b in binds {
                    let v = self.expr(i, &b.expr)?;
                    let lid = self.new_local(&b.name);
                    self.locals.push((b.name.clone(), lid));
                    bs.push((lid, v));
                }
                let body = self.expr(i, body);
                self.locals.truncate(mark);
                RExpr::Let(bs, Box::new(body?))
            }
            ExprKind::IfElse(c, t, f) => RExpr::Ite(
                Box::new(self.expr(i, c)?),
                Box::new(self.expr(i, t)?),
                Box::new(self.expr(i, f)?),
            ),
            ExprKind::Block(items) => self.conj(i, items)?,
            ExprKind::Paren(x) => self.expr(i, x)?,
        })
    }

    fn exprs(&mut self, i: usize, items: &[Expr]) -> Result<Vec<RExpr>, AlloyError> {
        items.iter().map(|x| self.expr(i, x)).collect()
    }

    /// Functions a plain name may denote that take exactly `nargs` parameters (every symbol of that name
    /// must be such a function; locals shadow). Several candidates form a type-resolved overload.
    fn func_cands(&self, i: usize, e: &Expr, nargs: usize) -> Vec<FuncId> {
        let ExprKind::Name(n) = &e.kind else {
            return Vec::new();
        };
        let n = n.strip_prefix('@').unwrap_or(n);
        if self.locals.iter().any(|(name, _)| name == n) {
            return Vec::new();
        }
        let Some(v) = self.lookup_any(i, n) else {
            return Vec::new();
        };
        let mut out = Vec::new();
        let mut others = false;
        for sym in &v {
            match sym {
                Sym::Func(fid) if self.model.funcs[*fid as usize].nparams == nargs && nargs > 0 => {
                    out.push(*fid)
                }
                Sym::Func(_) => {}
                // a field of the same name: with two or more box arguments only the function can fit
                Sym::Field(_) if nargs >= 2 => {}
                _ => others = true,
            }
        }
        if others {
            return Vec::new();
        }
        out
    }

    /// One-argument functions named by `e` when the name also denotes a field or sig (else empty).
    fn mixed_func_cands(&self, i: usize, e: &Expr) -> Vec<FuncId> {
        let ExprKind::Name(n) = &e.kind else {
            return Vec::new();
        };
        let n = n.strip_prefix('@').unwrap_or(n);
        if self.locals.iter().any(|(name, _)| name == n) {
            return Vec::new();
        }
        let Some(v) = self.lookup_any(i, n) else {
            return Vec::new();
        };
        let mut out = Vec::new();
        let mut others = false;
        for sym in &v {
            match sym {
                Sym::Func(fid) if self.model.funcs[*fid as usize].nparams == 1 => out.push(*fid),
                Sym::Func(_) => {}
                Sym::Field(_) | Sym::Sig(_) => others = true,
                _ => return Vec::new(),
            }
        }
        if !others {
            return Vec::new();
        }
        out
    }

    /// `l.r`; an overloaded `r` gives the choice of the joins (Java `CompModule.process`).
    fn join_over(l: RExpr, r: RExpr) -> RExpr {
        match r {
            RExpr::Choice(v) if v.len() > 1 => RExpr::Choice(
                v.into_iter()
                    .map(|c| match c {
                        RExpr::Choice(mut w) if w.len() == 1 => {
                            RExpr::Choice(vec![RExpr::Bin(BinOp::Join, Box::new(l.clone()), Box::new(w.remove(0)))])
                        }
                        other => RExpr::Bin(BinOp::Join, Box::new(l.clone()), Box::new(other)),
                    })
                    .collect(),
            ),
            other => RExpr::Bin(BinOp::Join, Box::new(l), Box::new(other)),
        }
    }

    fn calls(cands: Vec<FuncId>, args: Vec<RExpr>) -> RExpr {
        if cands.len() == 1 {
            RExpr::Call(cands[0], args)
        } else {
            RExpr::Choice(
                cands
                    .into_iter()
                    .map(|f| RExpr::Call(f, args.clone()))
                    .collect(),
            )
        }
    }

    /// A bare name: local, then module symbol, then built-in constant. `@x` skips the locals.
    fn name(&mut self, i: usize, e: &Expr, n: &str, args: &[Expr]) -> Result<RExpr, AlloyError> {
        let _ = args;
        let (n, skip_locals) = match n.strip_prefix('@') {
            Some(rest) => (rest, true),
            None => (n, false),
        };
        if !skip_locals {
            if let Some((_, lid)) = self.locals.iter().rev().find(|(name, _)| name == n) {
                return Ok(RExpr::Local(*lid));
            }
        }
        match n {
            "univ" => return Ok(RExpr::Sig(SIG_UNIV)),
            "none" => return Ok(RExpr::Sig(SIG_NONE)),
            "iden" => return Ok(RExpr::Const(Const::Iden)),
            "Int" => return Ok(RExpr::Sig(SIG_INT)),
            "String" => return Ok(RExpr::Sig(SIG_STRING)),
            "seq/Int" => return Ok(RExpr::Sig(SIG_SEQINT)),
            _ => {}
        }
        let found = self.lookup_any(i, n);
        match found {
            Some(v) if v.len() == 1 => match &v[0] {
                Sym::Sig(id) => Ok(RExpr::Sig(*id)),
                Sym::Field(id) => Ok(if skip_locals {
                    RExpr::Field(*id)
                } else {
                    self.field_ref(*id)
                }),
                Sym::Func(fid) => {
                    if self.model.funcs[*fid as usize].nparams == 0 {
                        if self.scopes[i].names.contains_key(n) && !n.contains('/') {
                            let mut visited = vec![i];
                            let mut extra: Vec<Sym> = Vec::new();
                            for (_, t) in &self.scopes[i].opens {
                                self.collect_public(*t, n, &mut visited, &mut extra);
                            }
                            let mut group = vec![*fid];
                            for x in extra {
                                if let Sym::Func(g) = x {
                                    if self.model.funcs[g as usize].nparams == 0
                                        && !group.iter().any(|o| {
                                            *o == g
                                                || self.same_instance_func(
                                                    &Sym::Func(*o),
                                                    &Sym::Func(g),
                                                )
                                        })
                                    {
                                        group.push(g);
                                    }
                                }
                            }
                            if group.len() > 1 {
                                self.model.shadowed_uses.push(group);
                            }
                        }
                        Ok(RExpr::Call(*fid, Vec::new()))
                    } else {
                        err(
                            i,
                            self.mods,
                            e.loc.line,
                            e.loc.col,
                            format!("Function \"{n}\" needs arguments."),
                        )
                    }
                }
                Sym::Macro(m) => {
                    let m = *m;
                    self.macro_call(i, e, m, &[])
                }
                Sym::Assert(_) => err(
                    i,
                    self.mods,
                    e.loc.line,
                    e.loc.col,
                    format!("\"{n}\" is an assertion, not an expression."),
                ),
            },
            Some(v) => {
                let mut cands = Vec::new();
                for sym in &v {
                    cands.push(match sym {
                        Sym::Sig(id) => RExpr::Sig(*id),
                        Sym::Field(id) => {
                            let r = if skip_locals {
                                RExpr::Field(*id)
                            } else {
                                self.field_ref(*id)
                            };
                            // Java `populate`: inside a sig fact a field of an unrelated sig has penalty 1
                            // (a one-element `Choice` marks a penalized candidate).
                            if matches!(r, RExpr::Field(_))
                                && !self.this_sigs.is_empty()
                                && !self.in_field_decl
                            {
                                RExpr::Choice(vec![r])
                            } else {
                                r
                            }
                        }
                        Sym::Func(fid) if self.model.funcs[*fid as usize].nparams == 0 => {
                            RExpr::Call(*fid, Vec::new())
                        }
                        // a function that needs arguments cannot be this bare name (Java ExprBadCall)
                        Sym::Func(_) => continue,
                        _ => {
                            return Err(unsupported(format!(
                                "overloaded name \"{n}\" with arguments (M3.3)"
                            )))
                        }
                    });
                }
                if cands.is_empty() {
                    return Err(unsupported(format!(
                        "overloaded name \"{n}\" with arguments (M3.3)"
                    )));
                }
                if cands.len() == 1 {
                    return Ok(cands.remove(0));
                }
                Ok(RExpr::Choice(cands))
            }
            None => err(
                i,
                self.mods,
                e.loc.line,
                e.loc.col,
                format!("The name \"{n}\" cannot be found."),
            ),
        }
    }

    /// Name lookup as Java `populate`: qualified or unqualified; inside a field declaration only the sig's own
    /// (and ancestors') fields and no functions are visible.
    fn lookup_any(&self, i: usize, n: &str) -> Option<Vec<Sym>> {
        let found = if n.contains('/') {
            self.lookup(i, n)
        } else {
            self.lookup_unqualified(i, n)
        };
        if !self.in_field_decl {
            return found;
        }
        let this_sig = *self.this_sigs.last()?;
        let kept: Vec<Sym> = found?
            .into_iter()
            .filter(|sym| match sym {
                Sym::Func(_) => false,
                Sym::Field(f) => {
                    let owner = self.model.fields[*f as usize].owner;
                    let mut p = Some(this_sig);
                    while let Some(x) = p {
                        if x == owner {
                            return true;
                        }
                        p = self.model.sigs[x as usize].parent;
                    }
                    false
                }
                _ => true,
            })
            .collect();
        if kept.is_empty() {
            None
        } else {
            Some(kept)
        }
    }

    /// A field named inside a sig body (own or inherited field) means `this.field`.
    fn field_ref(&self, id: FieldId) -> RExpr {
        if let (Some(&ts), Some((_, this_l))) = (
            self.this_sigs.last(),
            self.locals.iter().rev().find(|(name, _)| name == "this"),
        ) {
            let owner = self.model.fields[id as usize].owner;
            let mut p = Some(ts);
            while let Some(x) = p {
                if x == owner {
                    return RExpr::Bin(
                        BinOp::Join,
                        Box::new(RExpr::Local(*this_l)),
                        Box::new(RExpr::Field(id)),
                    );
                }
                p = self.model.sigs[x as usize].parent;
            }
        }
        RExpr::Field(id)
    }

    /// Macro call: the body is resolved with the parameters bound to the argument expressions
    /// (`let` semantics, like Java's macro expansion).
    fn macro_call(
        &mut self,
        i: usize,
        e: &Expr,
        m: usize,
        args: &[Expr],
    ) -> Result<RExpr, AlloyError> {
        let def = self.macros[m].clone();
        if def.params.len() != args.len() {
            return err(
                i,
                self.mods,
                e.loc.line,
                e.loc.col,
                "Wrong number of arguments for macro.",
            );
        }
        let mut binds = Vec::new();
        for (p, a) in def.params.iter().zip(args.iter()) {
            let v = self.expr(i, a)?;
            binds.push((p.clone(), v));
        }
        if self.depth > 64 {
            return Err(unsupported(
                "macro expansion is too deep (recursive macro?)",
            ));
        }
        // The body sees only its own parameters, never the caller's locals.
        let saved = std::mem::take(&mut self.locals);
        let mut lets = Vec::new();
        for (p, v) in binds {
            let lid = self.new_local(&p);
            self.locals.push((p, lid));
            self.model.macro_locals.push(lid);
            lets.push((lid, v));
        }
        self.depth += 1;
        let body = self.expr(def.module, &def.body);
        self.depth -= 1;
        self.locals = saved;
        let body = body?;
        if lets.is_empty() {
            Ok(body)
        } else {
            Ok(RExpr::Let(lets, Box::new(body)))
        }
    }
}

fn same_sym(a: &Sym, b: &Sym) -> bool {
    match (a, b) {
        (Sym::Sig(x), Sym::Sig(y)) => x == y,
        (Sym::Field(x), Sym::Field(y)) => x == y,
        (Sym::Func(x), Sym::Func(y)) => x == y,
        (Sym::Assert(x), Sym::Assert(y)) => x == y,
        (Sym::Macro(x), Sym::Macro(y)) => x == y,
        _ => false,
    }
}

/// Splits `Sig.name` (sig-local function names are kept as written).
fn split_owner(name: &str) -> (Option<&str>, &str) {
    match name.split_once('.') {
        Some((o, n)) => (Some(o), n),
        None => (None, name),
    }
}

/// Top-level `set/one/lone/some` of a declaration bound.
fn strip_mult(e: &Expr) -> (Option<Mult>, &Expr) {
    match &e.kind {
        ExprKind::Unary(UnOp::One, x) => (Some(Mult::One), x),
        ExprKind::Unary(UnOp::Lone, x) => (Some(Mult::Lone), x),
        ExprKind::Unary(UnOp::Some, x) => (Some(Mult::Some), x),
        ExprKind::Unary(UnOp::Set, x) => (Some(Mult::Set), x),
        _ => (None, e),
    }
}

fn unsupported(msg: impl Into<String>) -> AlloyError {
    AlloyError::unsupported(msg)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::{Path, PathBuf};

    fn collect(dir: &Path, out: &mut Vec<PathBuf>) {
        let Ok(rd) = std::fs::read_dir(dir) else {
            return;
        };
        for ent in rd.flatten() {
            let p = ent.path();
            if p.is_dir() {
                collect(&p, out);
            } else if p.extension().is_some_and(|x| x == "als") {
                out.push(p);
            }
        }
    }

    /// Corpus survey: how many models get a resolved model, and why the others do not.
    /// Prints a tally with `--nocapture`; asserts only that nothing panics.
    #[test]
    fn corpus_resolution_survey() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../reference/models");
        let mut files = Vec::new();
        collect(&root, &mut files);
        files.sort();
        let (mut ok, mut unsup, mut other) = (0, 0, 0);
        for f in &files {
            match crate::loader::load_root(f).and_then(|m| build(&m)) {
                Ok(_) => ok += 1,
                Err(e) if e.kind == ErrorKind::Unsupported => {
                    unsup += 1;
                    println!("UNSUP {}: {}", f.display(), e.msg);
                }
                Err(e) => {
                    other += 1;
                    println!(
                        "ERR {}: {}",
                        f.display(),
                        e.msg.lines().next().unwrap_or("")
                    );
                }
            }
        }
        println!(
            "SURVEY ok={ok} unsupported={unsup} other={other} total={}",
            files.len()
        );
    }
}
