//! Port of `kodkod.util.nodes.AnnotatedNode` (sharing detection, relations, `usesInts`, predicate collection,
//! free-variable / quantified-formula detectors) and of `FOL2BoolCache`'s `CacheCollector`
//! (`FreeVariableCollector` + `AbstractCollector`). Traversal orders follow the Java visitors exactly, because the
//! set of cached nodes depends on the first visit.

use crate::ast::*;
use std::collections::{HashMap, HashSet};

/// Children of a node in `AbstractVoidVisitor` order (leaves have none).
pub fn children(ast: &Ast, n: N) -> Vec<N> {
    match ast.get(n) {
        Node::Rel(_) | Node::Var { .. } | Node::ConstE(_) | Node::ConstF(_) | Node::IConst(_) => vec![],
        Node::BinE(_, a, b) | Node::BinI(_, a, b) | Node::ICmp(_, a, b) | Node::Cmp(_, a, b) | Node::BinF(_, a, b) => {
            vec![*a, *b]
        }
        Node::BTempF(_, a, b) => vec![*a, *b],
        Node::UnE(_, a) | Node::I2E(_, a) | Node::E2I(_, a) | Node::UnI(_, a) | Node::Mult(_, a) | Node::Not(a) => vec![*a],
        Node::UTempF(_, a) | Node::TempE(_, a) => vec![*a],
        Node::NaryE(_, cs) | Node::NaryI(_, cs) | Node::NaryF(_, cs) | Node::Decls(cs) => cs.clone(),
        Node::Compr(d, f) | Node::Sum(d, f) | Node::Quant(_, d, f) => vec![*d, *f],
        Node::IfE(c, t, e) | Node::IfI(c, t, e) => vec![*c, *t, *e],
        Node::Proj(e, cols) => {
            let mut v = vec![*e];
            v.extend(cols.iter().copied());
            v
        }
        Node::PAcyclic(r) => vec![*r],
        Node::PFunction(r, d, _, rg) => vec![*r, *d, *rg],
        Node::PTotal(r, o, f, l) => vec![*r, *o, *f, *l],
        Node::Decl(v, _, e) => vec![*v, *e],
    }
}

pub fn is_leaf(ast: &Ast, n: N) -> bool {
    matches!(ast.get(n), Node::Rel(_) | Node::Var { .. } | Node::ConstE(_) | Node::ConstF(_) | Node::IConst(_))
}

/// `AnnotatedNode` (sharing information only; sources are irrelevant without logging).
pub struct Annotated {
    pub node: N,
    pub shared: HashSet<N>,
}

/// `AnnotatedNode.annotate(node)`: SharingDetector.
pub fn annotate(ast: &Ast, root: N) -> Annotated {
    let mut status: HashMap<N, bool> = HashMap::new();
    let mut stack = vec![root];
    // iterative pre-order DFS with the same child order as the recursive visitor
    while let Some(n) = stack.pop() {
        if is_leaf(ast, n) {
            continue;
        }
        match status.get(&n).copied() {
            None => {
                status.insert(n, false);
                let cs = children(ast, n);
                for c in cs.into_iter().rev() {
                    stack.push(c);
                }
            }
            Some(false) => {
                status.insert(n, true);
            }
            Some(true) => {}
        }
    }
    let shared = status.into_iter().filter(|(_, s)| *s).map(|(n, _)| n).collect();
    Annotated { node: root, shared }
}

impl Annotated {
    /// `relations()`
    pub fn relations(&self, ast: &Ast) -> HashSet<N> {
        let mut out = HashSet::new();
        let mut visited = HashSet::new();
        let mut stack = vec![self.node];
        while let Some(n) = stack.pop() {
            if let Node::Rel(_) = ast.get(n) {
                out.insert(n);
                continue;
            }
            if is_leaf(ast, n) {
                continue;
            }
            if self.shared.contains(&n) && !visited.insert(n) {
                continue;
            }
            for c in children(ast, n).into_iter().rev() {
                stack.push(c);
            }
        }
        out
    }

    /// `usesInts()`
    pub fn uses_ints(&self, ast: &Ast) -> bool {
        let mut seen = HashSet::new();
        let mut stack = vec![self.node];
        while let Some(n) = stack.pop() {
            match ast.get(n) {
                Node::I2E(..) | Node::E2I(..) | Node::ConstE(ConstE::Ints) => return true,
                _ => {}
            }
            if is_leaf(ast, n) || !seen.insert(n) {
                continue;
            }
            for c in children(ast, n).into_iter().rev() {
                stack.push(c);
            }
        }
        false
    }

    /// `predicates()` (PredicateCollector): (totals, acyclics, functions) collected through positive conjunctions.
    pub fn predicates(&self, ast: &Ast) -> (Vec<N>, Vec<N>) {
        struct C<'a> {
            ast: &'a Ast,
            shared: &'a HashSet<N>,
            visited: HashMap<N, Option<bool>>,
            negated: bool,
            totals: Vec<N>,
            acyclics: Vec<N>,
        }
        impl C<'_> {
            fn visited(&mut self, n: N) -> bool {
                if self.shared.contains(&n) {
                    match self.visited.get(&n).copied() {
                        None => {
                            self.visited.insert(n, Some(self.negated));
                            false
                        }
                        Some(None) => true,
                        Some(Some(v)) if v == self.negated => true,
                        Some(Some(_)) => {
                            self.visited.insert(n, None);
                            false
                        }
                    }
                } else {
                    false
                }
            }
            fn visit(&mut self, n: N) {
                match self.ast.get(n).clone() {
                    Node::BinF(op, l, r) => {
                        if self.visited(n) {
                            return;
                        }
                        if (!self.negated && op == FOp::And) || (self.negated && op == FOp::Or) {
                            self.visit(l);
                            self.visit(r);
                        } else if self.negated && op == FOp::Implies {
                            self.negated = !self.negated;
                            self.visit(l);
                            self.negated = !self.negated;
                            self.visit(r);
                        }
                    }
                    Node::NaryF(op, cs) => {
                        if self.visited(n) {
                            return;
                        }
                        if (!self.negated && op == FOp::And) || (self.negated && op == FOp::Or) {
                            for c in cs {
                                self.visit(c);
                            }
                        }
                    }
                    Node::Not(f) => {
                        if self.visited(n) {
                            return;
                        }
                        self.negated = !self.negated;
                        self.visit(f);
                        self.negated = !self.negated;
                    }
                    Node::UTempF(op, f) => {
                        if self.visited(n) {
                            return;
                        }
                        if (!self.negated && op == TOp::Always) || (self.negated && op == TOp::Eventually) {
                            self.visit(f);
                        }
                    }
                    Node::PAcyclic(_) | Node::PTotal(..) | Node::PFunction(..) => {
                        if self.visited(n) {
                            return;
                        }
                        if !self.negated {
                            match self.ast.get(n) {
                                Node::PAcyclic(_) => {
                                    if !self.acyclics.contains(&n) {
                                        self.acyclics.push(n)
                                    }
                                }
                                Node::PTotal(..) => {
                                    if !self.totals.contains(&n) {
                                        self.totals.push(n)
                                    }
                                }
                                _ => {}
                            }
                        }
                    }
                    // Comprehension, IfExpression, IfIntExpression, IntComparison, Quantified, BinaryTemp,
                    // Comparison, Multiplicity: only marked visited
                    Node::Compr(..) | Node::IfE(..) | Node::IfI(..) | Node::ICmp(..) | Node::Quant(..) | Node::BTempF(..)
                    | Node::Cmp(..) | Node::Mult(..) => {
                        self.visited(n);
                    }
                    _ => {}
                }
            }
        }
        let mut c = C { ast, shared: &self.shared, visited: HashMap::new(), negated: false, totals: vec![], acyclics: vec![] };
        c.visit(self.node);
        (c.totals, c.acyclics)
    }

    /// `freeVariableDetector()` applied to `n`: does `n` have free variables?
    pub fn has_free_vars(&self, ast: &Ast, n: N, memo: &mut HashMap<N, bool>) -> bool {
        let mut scope: Vec<N> = Vec::new();
        self.fv_detect(ast, n, &mut scope, memo)
    }
    fn fv_detect(&self, ast: &Ast, n: N, scope: &mut Vec<N>, memo: &mut HashMap<N, bool>) -> bool {
        if let Some(&b) = memo.get(&n) {
            return b;
        }
        let r = match ast.get(n) {
            Node::Var { .. } => !scope.contains(&n),
            Node::Rel(_) | Node::ConstE(_) | Node::ConstF(_) | Node::IConst(_) => false,
            Node::Quant(_, d, b) | Node::Compr(d, b) | Node::Sum(d, b) => {
                let decls = ast.decls_list(*d);
                let mut ret = false;
                for dl in &decls {
                    if let Node::Decl(v, _, e) = ast.get(*dl) {
                        ret = self.fv_detect(ast, *e, scope, memo) || ret;
                        scope.push(*v);
                    }
                }
                ret = self.fv_detect(ast, *b, scope, memo) || ret;
                for _ in 0..decls.len() {
                    scope.pop();
                }
                ret
            }
            Node::Decl(_, _, e) => self.fv_detect(ast, *e, scope, memo),
            _ => {
                let mut ret = false;
                for c in children(ast, n) {
                    if self.fv_detect(ast, c, scope, memo) {
                        ret = true;
                        break;
                    }
                }
                ret
            }
        };
        if self.shared.contains(&n) {
            memo.insert(n, r);
        }
        r
    }

    /// `quantifiedFormulaDetector()` applied to `n`.
    pub fn has_quantifier(&self, ast: &Ast, n: N) -> bool {
        let mut seen = HashSet::new();
        let mut stack = vec![n];
        while let Some(x) = stack.pop() {
            if let Node::Quant(..) = ast.get(x) {
                return true;
            }
            if is_leaf(ast, x) || !seen.insert(x) {
                continue;
            }
            stack.extend(children(ast, x));
        }
        false
    }
}

/// `FOL2BoolCache` record kinds: `None` = NoVarRecord, `Some(vars)` = MultiVarRecord.
pub type CacheRecords = HashMap<N, Vec<N>>;

/// `FOL2BoolCache.CacheCollector`: which nodes get a translation-cache record (shared nodes, and nodes that do
/// not depend on the innermost quantified variable), with their free variables.
pub fn cache_records(ast: &Ast, ann: &Annotated) -> CacheRecords {
    struct C<'a> {
        ast: &'a Ast,
        shared: &'a HashSet<N>,
        cache: HashMap<N, Vec<N>>,
        scope: Vec<N>,
    }
    fn union_into(dst: &mut Vec<N>, src: &[N]) {
        for &v in src {
            if !dst.contains(&v) {
                dst.push(v);
            }
        }
    }
    impl C<'_> {
        // FreeVariableCollector/CacheCollector.cache
        fn cache(&mut self, n: N, fv: Vec<N>) -> Vec<N> {
            if self.shared.contains(&n) || (!self.scope.is_empty() && !fv.contains(self.scope.last().unwrap())) {
                self.cache.insert(n, fv.clone());
            }
            fv
        }
        fn visit(&mut self, n: N) -> Vec<N> {
            match self.ast.get(n).clone() {
                Node::Rel(_) | Node::ConstE(_) | Node::IConst(_) | Node::ConstF(_) => Vec::new(),
                Node::Var { .. } => self.cache(n, vec![n]),
                Node::Quant(_, d, b) | Node::Compr(d, b) | Node::Sum(d, b) => {
                    if let Some(v) = self.cache.get(&n) {
                        return v.clone();
                    }
                    let mut ret = Vec::new();
                    let mut bound: Vec<N> = Vec::new();
                    let decls = self.ast.decls_list(d);
                    for dl in &decls {
                        let dv = self.visit_decl(*dl);
                        for v in dv {
                            if !bound.contains(&v) && !ret.contains(&v) {
                                ret.push(v);
                            }
                        }
                        if let Node::Decl(var, _, _) = self.ast.get(*dl) {
                            self.scope.push(*var);
                            bound.push(*var);
                        }
                    }
                    for v in self.visit(b) {
                        if !bound.contains(&v) && !ret.contains(&v) {
                            ret.push(v);
                        }
                    }
                    for _ in 0..decls.len() {
                        self.scope.pop();
                    }
                    self.cache(n, ret)
                }
                Node::Decl(..) => self.visit_decl(n),
                _ => {
                    if let Some(v) = self.cache.get(&n) {
                        return v.clone();
                    }
                    let mut ret = Vec::new();
                    for c in children(self.ast, n) {
                        let cv = match self.ast.get(c) {
                            Node::Decl(..) => self.visit_decl(c),
                            _ => self.visit(c),
                        };
                        union_into(&mut ret, &cv);
                    }
                    self.cache(n, ret)
                }
            }
        }
        // FreeVariableCollector.visit(Decl): only the expression's variables
        fn visit_decl(&mut self, d: N) -> Vec<N> {
            if let Some(v) = self.cache.get(&d) {
                return v.clone();
            }
            let e = match self.ast.get(d) {
                Node::Decl(_, _, e) => *e,
                _ => unreachable!(),
            };
            let fv = self.visit(e);
            self.cache(d, fv)
        }
    }
    let mut c = C { ast, shared: &ann.shared, cache: HashMap::new(), scope: Vec::new() };
    c.visit(ann.node);
    c.cache
}
