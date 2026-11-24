//! Port of `kodkod.engine.fol2sat.Bool2CNFTranslator` (+ `PolarityDetector`): Plaisted-Greenbaum CNF with gate
//! labels as CNF variables.

use crate::bool::*;

/// Receiver of the clause stream (`SATSolver.addVariables` / `addClause`).
pub trait CnfSink {
    fn num_vars(&self) -> i32;
    fn add_variables(&mut self, n: i32);
    fn add_clause(&mut self, lits: &[i32]);
}

/// Streams CNF clauses directly into any [`satsolver::SatSolver`].
pub struct SolverSink<'s, S: satsolver::SatSolver> {
    pub solver: &'s mut S,
    pub clauses: i64,
}

impl<'s, S: satsolver::SatSolver> SolverSink<'s, S> {
    pub fn new(solver: &'s mut S) -> Self {
        SolverSink { solver, clauses: 0 }
    }
}

impl<S: satsolver::SatSolver> CnfSink for SolverSink<'_, S> {
    fn num_vars(&self) -> i32 {
        self.solver.num_vars() as i32
    }
    fn add_variables(&mut self, n: i32) {
        self.solver.add_variables(n as u32);
    }
    fn add_clause(&mut self, lits: &[i32]) {
        self.clauses += 1;
        self.solver.add_clause(lits);
    }
}

/// Flat, `0`-terminated DIMACS clause buffer for recording, parallel replay, and pre-BVE verification.
#[derive(Clone, Debug, Default)]
pub struct ClauseBuffer {
    pub num_vars: i32,
    pub num_clauses: i64,
    pub clauses: Vec<i32>,
    pub has_empty: bool,
}

impl ClauseBuffer {
    pub fn new() -> Self {
        Self::default()
    }

    /// Feeds buffered variables and clauses into `solver`. Returns `false` if trivially UNSAT.
    pub fn feed_to<S: satsolver::SatSolver>(&self, solver: &mut S) -> bool {
        if self.num_vars > 0 {
            solver.add_variables(self.num_vars as u32);
        }
        if self.has_empty {
            return false;
        }
        let mut i = 0;
        let len = self.clauses.len();
        while i < len {
            let mut j = i;
            while j < len && self.clauses[j] != 0 {
                j += 1;
            }
            if !solver.add_clause(&self.clauses[i..j]) {
                return false;
            }
            i = j + 1;
        }
        true
    }
}

impl CnfSink for ClauseBuffer {
    fn num_vars(&self) -> i32 {
        self.num_vars
    }
    fn add_variables(&mut self, n: i32) {
        self.num_vars += n;
    }
    fn add_clause(&mut self, lits: &[i32]) {
        self.num_clauses += 1;
        if lits.is_empty() {
            self.has_empty = true;
        }
        self.clauses.extend_from_slice(lits);
        self.clauses.push(0);
    }
}

/// Verifies that `value_of` (1-based variable -> bool) satisfies every clause in a `0`-terminated flat CNF buffer.
pub fn verify_cnf_model(clauses: &[i32], value_of: &dyn Fn(u32) -> bool) -> Result<(), String> {
    let mut i = 0;
    let mut ci = 0usize;
    let len = clauses.len();
    while i < len {
        let mut j = i;
        while j < len && clauses[j] != 0 {
            j += 1;
        }
        let clause = &clauses[i..j];
        if clause.is_empty() {
            return Err(format!("clause #{ci} is empty"));
        }
        if !clause.iter().any(|&l| value_of(l.unsigned_abs()) == (l > 0)) {
            return Err(format!("clause #{ci} violated: {clause:?}"));
        }
        ci += 1;
        i = j + 1;
    }
    Ok(())
}

/// `Bool2CNFTranslator.translate(BooleanConstant)`
pub fn translate_constant(value: BV, sink: &mut dyn CnfSink) {
    if value == FALSE {
        sink.add_clause(&[]);
    }
}

struct Pol {
    offset: i32,
    pol: Vec<u8>,
}

impl Pol {
    #[inline]
    fn visited(&mut self, label: i32, p: u8) -> bool {
        let i = (label - self.offset) as usize;
        let v = self.pol[i];
        self.pol[i] = v | p;
        (v | p) == v
    }
    fn visit(&mut self, f: &Factory, v: BV, arg: u8) {
        let mut stack = vec![(v, arg)];
        while let Some((mut cur, mut a)) = stack.pop() {
            if cur < 0 {
                // NotGate: ints[3-arg] with ints = {3, 1, 2}
                a = match a {
                    1 => 2,
                    2 => 1,
                    _ => 3,
                };
                cur = -cur;
            }
            match f.op(cur) {
                Op::Var | Op::Const => {}
                Op::And | Op::Or => {
                    if !self.visited(cur, a) {
                        for &i in f.inputs(cur).iter().rev() {
                            stack.push((i, a));
                        }
                    }
                }
                Op::Ite => {
                    if !self.visited(cur, a) {
                        let ins = f.inputs(cur);
                        stack.push((ins[2], a));
                        stack.push((ins[1], a));
                        stack.push((ins[0], 3));
                    }
                }
                Op::Not => unreachable!(),
            }
        }
    }
    #[inline]
    fn positive(&self, label: i32) -> bool {
        self.pol[(label - self.offset) as usize] & 1 > 0
    }
    #[inline]
    fn negative(&self, label: i32) -> bool {
        self.pol[(label - self.offset) as usize] & 2 > 0
    }
}

struct Tr<'a> {
    f: &'a Factory,
    pol: Pol,
    offset: i32,
    visited: Vec<bool>,
    sink: &'a mut dyn CnfSink,
    buf: Vec<i32>,
}

impl Tr<'_> {
    #[inline]
    fn push_gate(&mut self, x: BV, stack: &mut Vec<(BV, usize)>) {
        let pos = x.abs();
        if pos >= self.offset && matches!(self.f.op(pos), Op::And | Op::Or | Op::Ite) {
            let idx = (pos - self.offset) as usize;
            if !self.visited[idx] {
                self.visited[idx] = true;
                stack.push((pos, 0));
            }
        }
    }

    fn visit(&mut self, root: BV) -> i32 {
        let mut stack: Vec<(BV, usize)> = Vec::new();
        self.push_gate(root, &mut stack);
        while let Some(&(v, idx)) = stack.last() {
            let op = self.f.op(v);
            let ins = self.f.inputs(v);
            match op {
                Op::And | Op::Or => {
                    let sgn = if op == Op::And { 1 } else { -1 };
                    let (p, n) = if op == Op::And {
                        (self.pol.positive(v), self.pol.negative(v))
                    } else {
                        (self.pol.negative(v), self.pol.positive(v))
                    };
                    if idx > 0 && p {
                        let il = ins[idx - 1];
                        self.sink.add_clause(&[il * sgn, v * -sgn]);
                    }
                    if idx < ins.len() {
                        stack.last_mut().unwrap().1 = idx + 1;
                        let next_in = ins[idx];
                        self.push_gate(next_in, &mut stack);
                    } else {
                        if n {
                            self.buf.clear();
                            for &il in ins {
                                self.buf.push(il * -sgn);
                            }
                            self.buf.push(v * sgn);
                            self.sink.add_clause(&self.buf);
                        }
                        stack.pop();
                    }
                }
                Op::Ite => {
                    if idx < 3 {
                        stack.last_mut().unwrap().1 = idx + 1;
                        let next_in = ins[idx];
                        self.push_gate(next_in, &mut stack);
                    } else {
                        let (i, t, e) = (ins[0], ins[1], ins[2]);
                        let (p, n) = (self.pol.positive(v), self.pol.negative(v));
                        if p {
                            self.sink.add_clause(&[-i, t, -v]);
                            self.sink.add_clause(&[i, e, -v]);
                            self.sink.add_clause(&[t, e, -v]);
                        }
                        if n {
                            self.sink.add_clause(&[-i, -t, v]);
                            self.sink.add_clause(&[i, -e, v]);
                            self.sink.add_clause(&[-t, -e, v]);
                        }
                        stack.pop();
                    }
                }
                Op::Var | Op::Const | Op::Not => unreachable!(),
            }
        }
        root
    }
}

/// `Bool2CNFTranslator.translate(circuit, maxPrimaryVar, factory)` for a non-constant circuit.
pub fn translate(f: &Factory, circuit: BV, max_primary_var: i32, sink: &mut dyn CnfSink) {
    let max_literal = circuit.abs();
    let offset = max_primary_var + 1;
    let n_gates = (max_literal - max_primary_var).max(0) as usize;
    let mut pol = Pol { offset, pol: vec![0u8; n_gates] };
    pol.visit(f, circuit, 1);
    let new_vars = max_literal.max(max_primary_var) - sink.num_vars();
    if new_vars > 0 {
        sink.add_variables(new_vars);
    }
    let mut tr = Tr { f, pol, offset, visited: vec![false; n_gates], sink, buf: Vec::new() };
    if circuit > 0 && f.op(circuit) == Op::And {
        for &i in f.inputs(circuit) {
            tr.visit(i);
        }
        for &i in f.inputs(circuit) {
            tr.sink.add_clause(&[i]);
        }
    } else {
        let l = tr.visit(circuit);
        tr.sink.add_clause(&[l]);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn verify_cnf_model_accepts_valid_and_rejects_violated_or_empty() {
        let mut buf = ClauseBuffer::new();
        buf.add_variables(2);
        buf.add_clause(&[1, 2]);
        buf.add_clause(&[-1, 2]);
        assert!(verify_cnf_model(&buf.clauses, &|v| v == 2).is_ok());
        assert!(verify_cnf_model(&buf.clauses, &|_| false).is_err());

        let mut empty_buf = ClauseBuffer::new();
        empty_buf.add_clause(&[]);
        assert!(verify_cnf_model(&empty_buf.clauses, &|_| true).is_err());
    }
}
