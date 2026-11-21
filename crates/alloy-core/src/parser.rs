//! Port of the expression productions of `org.alloytools.alloy.core/parser/Alloy.cup`
//! (`Expr` .. `BaseExpr`) plus the token merges of `CORE/parser/CompFilter.java` that apply inside
//! expressions (`!in`, `!=`, `one ->`, `fun/add`, `pred/totalOrder`, `-1`, `all x:` quantifiers).
//!
//! Precedence is encoded by the call chain, one method per grammar level, lowest first. Java's
//! `A`/`B` grammar variants only decide whether a quantifier or `let` may be a right operand; here
//! `bind` is a primary, so it is accepted in any operand position and its body absorbs the rest,
//! exactly like Java's `ExprNoSeq` body.
//!
//! Surface conventions (see `syntax.rs`):
//! - `{}` and a comprehension without `|` use `Block(vec![])` as the constant TRUE.
//! - `a[b, c]` stays `BoxJoin(a, [b, c])` (Java `c.(b.a)`); `disj[..]` / `pred/totalOrder[..]`
//!   become `BoxJoin(Name("disj" | "pred/totalOrder"), args)`.
//! - `int[e]`, `sum[e]`, `e.int`, `e.sum` and prefix `sum e` / `int e` become `Unary(IntCast, e)`.
//! - `a !in b`, `a != b`, `a !< b` ... become `Unary(Not, Binary(op, a, b))`.
//! - The multiplicity of a `Binary` `Arrow` is kept on the operator (`Arrow(Mult, Mult)`).
//! - Multiplicity keywords on `in`/`=` right operands are not rewritten (`lone B` stays `Unary(Lone, B)`).

use crate::error::{AlloyError, Pos};
use crate::lexer::{lex, Tok, Token};
use crate::syntax::*;

type PResult<T> = Result<T, AlloyError>;

/// Parses one standalone expression; the whole input must be consumed.
pub fn parse_expression(file: &str, src: &str) -> PResult<Expr> {
    let mut p = Parser::new(file, lex(file, src)?);
    let e = p.expr()?;
    if *p.peek() != Tok::Eof {
        return p.err("unexpected token after expression");
    }
    Ok(e)
}

/// Recursive-descent parser over the token vector of one file.
pub struct Parser {
    file: String,
    toks: Vec<Token>,
    pos: usize,
}

impl Parser {
    pub fn new(file: &str, mut toks: Vec<Token>) -> Self {
        let (line, col) = toks.last().map_or((1, 1), |t| (t.line, t.col + 1));
        toks.push(Token {
            tok: Tok::Eof,
            line,
            col,
        });
        Parser {
            file: file.to_string(),
            toks,
            pos: 0,
        }
    }

    // ---- token access -------------------------------------------------------------------

    /// Token at offset `k` from the cursor (clamped to the final `Eof`).
    fn tok(&self, k: usize) -> &Tok {
        &self.toks[(self.pos + k).min(self.toks.len() - 1)].tok
    }

    fn peek(&self) -> &Tok {
        self.tok(0)
    }

    fn loc(&self) -> Loc {
        let t = &self.toks[self.pos.min(self.toks.len() - 1)];
        Loc {
            line: t.line,
            col: t.col,
        }
    }

    fn bump(&mut self) {
        self.bump_n(1);
    }

    fn bump_n(&mut self, n: usize) {
        self.pos = (self.pos + n).min(self.toks.len() - 1);
    }

    fn eat(&mut self, t: &Tok) -> bool {
        if self.peek() == t {
            self.bump();
            true
        } else {
            false
        }
    }

    fn expect(&mut self, t: &Tok) -> PResult<()> {
        if self.eat(t) {
            Ok(())
        } else {
            self.err(&format!("expected {t:?}"))
        }
    }

    fn err<T>(&self, msg: &str) -> PResult<T> {
        let l = self.loc();
        let pos = Pos {
            file: self.file.clone(),
            line: l.line,
            col: l.col,
        };
        Err(AlloyError::syntax(
            pos,
            format!("Syntax error: {msg}, found {:?}", self.peek()),
        ))
    }

    /// `fun/add`-style builtin: the keyword `fun` / `pred` followed by `/` and an identifier.
    fn fun_name(&self) -> Option<&str> {
        if *self.tok(0) == Tok::Fun && *self.tok(1) == Tok::Slash {
            if let Tok::Id(s) = self.tok(2) {
                return Some(s.as_str());
            }
        }
        None
    }

    /// Index offset just past a `Name` (`a`, `a/b`, `this/A`, `seq/Int`) starting at offset `k`.
    fn name_end(&self, mut k: usize) -> Option<usize> {
        match self.tok(k) {
            Tok::Id(_) => k += 1,
            Tok::This | Tok::Seq => {
                let ok = *self.tok(k + 1) == Tok::Slash
                    && matches!(self.tok(k + 2), Tok::Id(_) | Tok::SigInt);
                if !ok {
                    return None;
                }
                k += 3;
            }
            _ => return None,
        }
        while *self.tok(k) == Tok::Slash && matches!(self.tok(k + 1), Tok::Id(_)) {
            k += 2;
        }
        Some(k)
    }

    /// CompFilter lookahead for a declaration `[var] [private] [disj] names :` at offset `k`.
    fn decl_ahead(&self, mut k: usize) -> bool {
        if *self.tok(k) == Tok::Var {
            k += 1;
        }
        if *self.tok(k) == Tok::Private {
            k += 1;
        }
        if *self.tok(k) == Tok::Disj {
            k += 1;
        }
        loop {
            let Some(next) = self.name_end(k) else {
                return false;
            };
            match self.tok(next) {
                Tok::Comma => k = next + 1,
                Tok::Colon => return true,
                _ => return false,
            }
        }
    }

    /// CompFilter: `no/some/lone/one/sum` start a quantifier only when the previous token is not
    /// `:` or `disj` and a declaration follows. Otherwise they are multiplicity keywords.
    fn quant_ahead(&self) -> bool {
        if self.pos > 0 && matches!(self.toks[self.pos - 1].tok, Tok::Colon | Tok::Disj) {
            return false;
        }
        self.decl_ahead(1)
    }

    /// `sum e` / `int e` prefix (not `sum[..]`, not a quantifier).
    fn is_int_prefix(&self) -> bool {
        matches!(self.peek(), Tok::Sum | Tok::Int)
            && *self.tok(1) != Tok::LBracket
            && !(*self.peek() == Tok::Sum && self.quant_ahead())
    }

    // ---- entry points -------------------------------------------------------------------

    /// `Expr ::= ExprNoSeq | ExprNoSeq ; Expr` (trace sequencing, lowest precedence).
    pub fn expr(&mut self) -> PResult<Expr> {
        let left = self.or_level()?;
        if self.eat(&Tok::TrcSeq) {
            let right = self.expr()?;
            let after = un(left.loc, UnOp::After, right);
            return Ok(bin(BinOp::And, left, after));
        }
        Ok(left)
    }

    /// `SuperOrBar`: `| ExprNoSeq [; Expr]` or a `{ }` block.
    fn body(&mut self) -> PResult<Expr> {
        if self.eat(&Tok::Bar) {
            let e = self.or_level()?;
            if self.eat(&Tok::TrcSeq) {
                let right = self.expr()?;
                let after = un(e.loc, UnOp::After, right);
                return Ok(bin(BinOp::And, e, after));
            }
            return Ok(e);
        }
        if *self.peek() == Tok::LBrace {
            return self.block();
        }
        self.err("expected '|' or '{'")
    }

    // ---- binary levels, lowest precedence first -----------------------------------------

    fn or_level(&mut self) -> PResult<Expr> {
        let mut l = self.iff_level()?;
        while self.eat(&Tok::Or) {
            let r = self.iff_level()?;
            l = bin(BinOp::Or, l, r);
        }
        Ok(l)
    }

    fn iff_level(&mut self) -> PResult<Expr> {
        let mut l = self.implies_level()?;
        while self.eat(&Tok::Iff) {
            let r = self.implies_level()?;
            l = bin(BinOp::Iff, l, r);
        }
        Ok(l)
    }

    /// `c => a else b` (ITE) or `a => b`; right-associative.
    fn implies_level(&mut self) -> PResult<Expr> {
        let c = self.and_level()?;
        if !self.eat(&Tok::Implies) {
            return Ok(c);
        }
        let t = self.implies_level()?;
        if self.eat(&Tok::Else) {
            let e = self.implies_level()?;
            return Ok(Expr::new(
                c.loc,
                ExprKind::IfElse(Box::new(c), Box::new(t), Box::new(e)),
            ));
        }
        Ok(bin(BinOp::Implies, c, t))
    }

    fn and_level(&mut self) -> PResult<Expr> {
        let mut l = self.temporal_level()?;
        while self.eat(&Tok::And) {
            let r = self.temporal_level()?;
            l = bin(BinOp::And, l, r);
        }
        Ok(l)
    }

    fn temporal_level(&mut self) -> PResult<Expr> {
        let mut l = self.unary_level()?;
        loop {
            let op = match self.peek() {
                Tok::Until => BinOp::Until,
                Tok::Since => BinOp::Since,
                Tok::Releases => BinOp::Releases,
                Tok::Triggered => BinOp::Triggered,
                _ => return Ok(l),
            };
            self.bump();
            let r = self.unary_level()?;
            l = bin(op, l, r);
        }
    }

    /// Prefix `!`/`not` and the temporal prefix operators; operand is the next unary level.
    fn unary_level(&mut self) -> PResult<Expr> {
        let op = match self.peek() {
            Tok::Not => UnOp::Not,
            Tok::Always => UnOp::Always,
            Tok::Eventually => UnOp::Eventually,
            Tok::After => UnOp::After,
            Tok::Historically => UnOp::Historically,
            Tok::Once => UnOp::Once,
            Tok::Before => UnOp::Before,
            _ => return self.compare_level(),
        };
        let loc = self.loc();
        self.bump();
        let e = self.unary_level()?;
        Ok(un(loc, op, e))
    }

    /// Comparisons (`in`, `=`, `<`, ..., negated with `!`), and the prefix multiplicities
    /// `no/some/lone/one/set/seq`. Comparisons are left-associative in the grammar.
    fn compare_level(&mut self) -> PResult<Expr> {
        if self.prefix_mult_ahead() {
            let loc = self.loc();
            let op = match self.peek() {
                Tok::No => UnOp::No,
                Tok::SomeKw => UnOp::Some,
                Tok::Lone => UnOp::Lone,
                Tok::One => UnOp::One,
                Tok::Set => UnOp::Set,
                _ => UnOp::Seq,
            };
            self.bump();
            let e = self.shift_level()?;
            return Ok(un(loc, op, e));
        }
        let mut l = self.shift_level()?;
        loop {
            let (op, negated, n) = match (self.tok(0), self.tok(1)) {
                (Tok::Equals, _) => (BinOp::Equals, false, 1),
                (Tok::In, _) => (BinOp::In, false, 1),
                (Tok::Lt, _) => (BinOp::Lt, false, 1),
                (Tok::Lte, _) => (BinOp::Le, false, 1),
                (Tok::Gt, _) => (BinOp::Gt, false, 1),
                (Tok::Gte, _) => (BinOp::Ge, false, 1),
                (Tok::Not, Tok::Equals) => (BinOp::Equals, true, 2),
                (Tok::Not, Tok::In) => (BinOp::In, true, 2),
                (Tok::Not, Tok::Lt) => (BinOp::Lt, true, 2),
                (Tok::Not, Tok::Lte) => (BinOp::Le, true, 2),
                (Tok::Not, Tok::Gt) => (BinOp::Gt, true, 2),
                (Tok::Not, Tok::Gte) => (BinOp::Ge, true, 2),
                _ => return Ok(l),
            };
            self.bump_n(n);
            let r = self.shift_level()?;
            let b = bin(op, l, r);
            l = if negated { un(b.loc, UnOp::Not, b) } else { b };
        }
    }

    fn prefix_mult_ahead(&self) -> bool {
        match self.peek() {
            Tok::No | Tok::SomeKw | Tok::Lone | Tok::One => !self.quant_ahead(),
            Tok::Set => true,
            Tok::Seq => *self.tok(1) != Tok::Slash,
            _ => false,
        }
    }

    fn shift_level(&mut self) -> PResult<Expr> {
        let mut l = self.union_level()?;
        loop {
            let op = match self.peek() {
                Tok::Shl => BinOp::Shl,
                Tok::Shr => BinOp::Shr,
                Tok::Sha => BinOp::Sha,
                _ => return Ok(l),
            };
            self.bump();
            let r = self.union_level()?;
            l = bin(op, l, r);
        }
    }

    /// Set union/difference (`+`, `-`) and integer `fun/add`, `fun/sub`.
    fn union_level(&mut self) -> PResult<Expr> {
        let mut l = self.mul_level()?;
        loop {
            let (op, n) = match (self.peek(), self.fun_name()) {
                (Tok::Plus, _) => (BinOp::Plus, 1),
                (Tok::Minus, _) => (BinOp::Minus, 1),
                (_, Some("add")) => (BinOp::IntPlus, 3),
                (_, Some("sub")) => (BinOp::IntMinus, 3),
                _ => return Ok(l),
            };
            self.bump_n(n);
            let r = self.mul_level()?;
            l = bin(op, l, r);
        }
    }

    /// Integer `fun/mul`, `fun/div`, `fun/rem`.
    fn mul_level(&mut self) -> PResult<Expr> {
        let mut l = self.num_unop()?;
        loop {
            let op = match self.fun_name() {
                Some("mul") => BinOp::Mul,
                Some("div") => BinOp::Div,
                Some("rem") => BinOp::Rem,
                _ => return Ok(l),
            };
            self.bump_n(3);
            let r = self.num_unop()?;
            l = bin(op, l, r);
        }
    }

    /// Prefix `#` (cardinality) and `sum`/`int` (integer cast), operand is the next num level.
    fn num_unop(&mut self) -> PResult<Expr> {
        let loc = self.loc();
        match self.peek() {
            Tok::Hash => {
                self.bump();
                let e = self.num_unop()?;
                Ok(un(loc, UnOp::Card, e))
            }
            _ if self.is_int_prefix() => {
                self.bump();
                let e = self.num_unop()?;
                Ok(un(loc, UnOp::IntCast, e))
            }
            _ => self.override_level(),
        }
    }

    fn override_level(&mut self) -> PResult<Expr> {
        let mut l = self.intersect_level()?;
        while self.eat(&Tok::PlusPlus) {
            let r = self.intersect_level()?;
            l = bin(BinOp::Override, l, r);
        }
        Ok(l)
    }

    fn intersect_level(&mut self) -> PResult<Expr> {
        let mut l = self.arrow_level()?;
        while self.eat(&Tok::Ampersand) {
            let r = self.arrow_level()?;
            l = bin(BinOp::Intersect, l, r);
        }
        Ok(l)
    }

    /// `A m1 -> m2 B`: optional multiplicity keywords on each side of `->`; right-associative.
    fn arrow_level(&mut self) -> PResult<Expr> {
        let left = self.domain_level()?;
        let lm = if *self.peek() == Tok::Arrow {
            Mult::Set
        } else if let (Some(m), true) = (mult_kw(self.peek()), *self.tok(1) == Tok::Arrow) {
            self.bump();
            m
        } else {
            return Ok(left);
        };
        self.bump(); // `->`
        let rm = match mult_kw(self.peek()) {
            Some(m) => {
                self.bump();
                m
            }
            None => Mult::Set,
        };
        let right = self.arrow_level()?;
        Ok(bin(BinOp::Arrow(lm, rm), left, right))
    }

    /// Domain restriction `<:`, left-associative.
    fn domain_level(&mut self) -> PResult<Expr> {
        let mut l = self.range_level()?;
        while self.eat(&Tok::Domain) {
            let r = self.range_level()?;
            l = bin(BinOp::DomainRestrict, l, r);
        }
        Ok(l)
    }

    /// Range restriction `:>`, left-associative.
    fn range_level(&mut self) -> PResult<Expr> {
        let mut l = self.dot_level()?;
        while self.eat(&Tok::Range) {
            let r = self.dot_level()?;
            l = bin(BinOp::RangeRestrict, l, r);
        }
        Ok(l)
    }

    /// Join `.` and box join `[..]`, both left-associative at the same level.
    fn dot_level(&mut self) -> PResult<Expr> {
        let mut l = self.unop_level()?;
        loop {
            if self.eat(&Tok::Dot) {
                l = match self.peek() {
                    Tok::Disj => {
                        self.bump();
                        boxed(Expr::new(l.loc, ExprKind::Name("disj".into())), vec![l])
                    }
                    Tok::Int | Tok::Sum => {
                        self.bump();
                        un(l.loc, UnOp::IntCast, l)
                    }
                    _ if self.is_total_order() => {
                        self.bump_n(3);
                        boxed(
                            Expr::new(l.loc, ExprKind::Name("pred/totalOrder".into())),
                            vec![l],
                        )
                    }
                    _ => {
                        let r = self.unop_level()?;
                        bin(BinOp::Join, l, r)
                    }
                };
            } else if self.eat(&Tok::LBracket) {
                let args = self.expr_list(&Tok::RBracket)?;
                if !args.is_empty() {
                    l = boxed(l, args);
                }
            } else {
                return Ok(l);
            }
        }
    }

    /// Prefix `~` (transpose), `*` (reflexive closure), `^` (closure); postfix `'` (prime).
    fn unop_level(&mut self) -> PResult<Expr> {
        let loc = self.loc();
        let op = match self.peek() {
            Tok::Tilde => UnOp::Transpose,
            Tok::Star => UnOp::ReflClosure,
            Tok::Caret => UnOp::Closure,
            _ => {
                let mut e = self.primary()?;
                while self.eat(&Tok::Prime) {
                    e = un(e.loc, UnOp::Prime, e);
                }
                return Ok(e);
            }
        };
        self.bump();
        let e = self.unop_level()?;
        Ok(un(loc, op, e))
    }

    // ---- primaries ----------------------------------------------------------------------

    fn primary(&mut self) -> PResult<Expr> {
        let loc = self.loc();
        let kind = match self.peek().clone() {
            Tok::Num(n) => {
                self.bump();
                ExprKind::Num(n)
            }
            Tok::Minus => match *self.tok(1) {
                Tok::Num(n) => {
                    self.bump_n(2);
                    ExprKind::Num(-n)
                }
                _ => return self.err("expected expression"),
            },
            Tok::Str(s) => {
                self.bump();
                ExprKind::Str(s)
            }
            Tok::Iden => self.konst(Const::Iden),
            Tok::Univ => self.konst(Const::Univ),
            Tok::NoneKw => self.konst(Const::None),
            Tok::SigInt => self.konst(Const::SigInt),
            Tok::StringKw => self.konst(Const::SigString),
            Tok::This if *self.tok(1) != Tok::Slash => self.konst(Const::This),
            Tok::Time => {
                self.bump();
                ExprKind::Name("steps".into())
            }
            Tok::Id(_) | Tok::This | Tok::Seq => ExprKind::Name(self.name()?),
            Tok::At => {
                self.bump();
                ExprKind::Name(format!("@{}", self.name()?))
            }
            Tok::LParen => {
                self.bump();
                let e = self.expr()?;
                self.expect(&Tok::RParen)?;
                ExprKind::Paren(Box::new(e))
            }
            Tok::LBrace => return self.brace(),
            Tok::All | Tok::Let => return self.bind(),
            Tok::No | Tok::SomeKw | Tok::Lone | Tok::One | Tok::Sum if self.quant_ahead() => {
                return self.bind()
            }
            Tok::Int | Tok::Sum if *self.tok(1) == Tok::LBracket => return self.int_box(),
            Tok::Disj if *self.tok(1) == Tok::LBracket => {
                self.bump();
                let args = self.bracket_args()?;
                return Ok(keyword_box("disj", args, loc));
            }
            _ if self.is_total_order() => {
                self.bump_n(2);
                let args = self.bracket_args()?;
                return Ok(keyword_box("pred/totalOrder", args, loc));
            }
            Tok::Fun if matches!(self.fun_name(), Some("min" | "max" | "next")) => {
                let c = match self.fun_name() {
                    Some("min") => Const::IntMin,
                    Some("max") => Const::IntMax,
                    _ => Const::IntNext,
                };
                self.bump_n(3);
                ExprKind::Const(c)
            }
            _ => return self.err("expected expression"),
        };
        Ok(Expr::new(loc, kind))
    }

    /// `pred/totalOrder [`
    fn is_total_order(&self) -> bool {
        *self.peek() == Tok::Pred
            && *self.tok(1) == Tok::Slash
            && matches!(self.tok(2), Tok::Id(s) if s == "totalOrder")
            && *self.tok(3) == Tok::LBracket
    }

    fn konst(&mut self, c: Const) -> ExprKind {
        self.bump();
        ExprKind::Const(c)
    }

    /// `[ args ]` after a keyword (the opening bracket is consumed here).
    fn bracket_args(&mut self) -> PResult<Vec<Expr>> {
        self.expect(&Tok::LBracket)?;
        self.expr_list(&Tok::RBracket)
    }

    /// `Exprs` up to and including the closing token.
    fn expr_list(&mut self, close: &Tok) -> PResult<Vec<Expr>> {
        let mut out = Vec::new();
        if self.eat(close) {
            return Ok(out);
        }
        loop {
            out.push(self.expr()?);
            if self.eat(&Tok::Comma) {
                continue;
            }
            self.expect(close)?;
            return Ok(out);
        }
    }

    /// `int[e]` / `sum[e]`: only the one-argument form (Java's multi-argument form is not ported).
    fn int_box(&mut self) -> PResult<Expr> {
        let loc = self.loc();
        self.bump();
        let args = self.bracket_args()?;
        match <[Expr; 1]>::try_from(args) {
            Ok([e]) => Ok(un(loc, UnOp::IntCast, e)),
            Err(_) => self.err("int[..] / sum[..] takes exactly one argument"),
        }
    }

    /// `Name ::= ID (/ ID)* | this/ID | seq/ID | seq/Int`.
    fn name(&mut self) -> PResult<String> {
        let mut s = match self.peek() {
            Tok::Id(x) => {
                let x = x.clone();
                self.bump();
                x
            }
            Tok::This | Tok::Seq => {
                let kw = if *self.peek() == Tok::This {
                    "this"
                } else {
                    "seq"
                };
                self.bump();
                self.expect(&Tok::Slash)?;
                match self.peek() {
                    Tok::Id(x) => {
                        let x = format!("{kw}/{x}");
                        self.bump();
                        x
                    }
                    Tok::SigInt if kw == "seq" => {
                        self.bump();
                        "seq/Int".to_string()
                    }
                    _ => return self.err("expected a name after '/'"),
                }
            }
            _ => return self.err("expected a name"),
        };
        while *self.peek() == Tok::Slash {
            let Tok::Id(x) = self.tok(1) else { break };
            s.push('/');
            s.push_str(x);
            self.bump_n(2);
        }
        Ok(s)
    }

    /// `{ decls | body }` comprehension, or a `{ e1 e2 .. }` block.
    fn brace(&mut self) -> PResult<Expr> {
        if !self.decl_ahead(1) {
            return self.block();
        }
        let loc = self.loc();
        self.bump();
        let decls = self.decls()?;
        let body = if matches!(self.peek(), Tok::Bar | Tok::LBrace) {
            self.body()?
        } else {
            Expr::new(loc, ExprKind::Block(Vec::new()))
        };
        self.expect(&Tok::RBrace)?;
        Ok(Expr::new(loc, ExprKind::Compr(decls, Box::new(body))))
    }

    fn block(&mut self) -> PResult<Expr> {
        let loc = self.loc();
        self.expect(&Tok::LBrace)?;
        let mut items = Vec::new();
        while *self.peek() != Tok::RBrace {
            if *self.peek() == Tok::Eof {
                return self.err("unclosed '{'");
            }
            items.push(self.expr()?);
        }
        self.bump();
        Ok(Expr::new(loc, ExprKind::Block(items)))
    }

    /// Quantifier (`all`, `no`, `some`, `lone`, `one`, `sum`) or `let`.
    fn bind(&mut self) -> PResult<Expr> {
        let loc = self.loc();
        let q = match self.peek() {
            Tok::Let => {
                self.bump();
                return self.let_expr(loc);
            }
            Tok::All => Quant::All,
            Tok::No => Quant::No,
            Tok::SomeKw => Quant::Some,
            Tok::Lone => Quant::Lone,
            Tok::One => Quant::One,
            Tok::Sum => Quant::Sum,
            _ => return self.err("expected a quantifier"),
        };
        self.bump();
        let decls = self.decls()?;
        let body = self.body()?;
        Ok(Expr::new(loc, ExprKind::Quant(q, decls, Box::new(body))))
    }

    /// `let a = e1, b = e2 | body` (the `let` keyword is already consumed).
    fn let_expr(&mut self, loc: Loc) -> PResult<Expr> {
        let mut binds = Vec::new();
        loop {
            let bl = self.loc();
            let name = self.name()?;
            if name.contains('/') {
                return self.err("let variable name cannot contain '/'");
            }
            self.expect(&Tok::Equals)?;
            let expr = self.expr()?;
            binds.push(LetBind {
                loc: bl,
                name,
                expr,
            });
            if !self.eat(&Tok::Comma) {
                break;
            }
        }
        let body = self.body()?;
        Ok(Expr::new(loc, ExprKind::Let(binds, Box::new(body))))
    }

    // ---- declarations (used by quantifiers and comprehensions; fields reuse them later) -

    /// `decl (, decl)*`
    pub fn decls(&mut self) -> PResult<Vec<Decl>> {
        let mut out = vec![self.decl()?];
        while self.eat(&Tok::Comma) {
            out.push(self.decl()?);
        }
        Ok(out)
    }

    /// `[var] [private] [disj] name (, name)* : [disj] expr` (Java `Decla`).
    pub fn decl(&mut self) -> PResult<Decl> {
        let loc = self.loc();
        let var = self.eat(&Tok::Var);
        let is_private = self.eat(&Tok::Private);
        let mut disjoint = self.eat(&Tok::Disj);
        let mut names = vec![self.name()?];
        while self.eat(&Tok::Comma) {
            names.push(self.name()?);
        }
        self.expect(&Tok::Colon)?;
        disjoint |= self.eat(&Tok::Disj);
        let expr = self.expr()?;
        Ok(Decl {
            loc,
            is_private,
            disjoint,
            var,
            names,
            expr,
        })
    }
}

// ---- constructors and helpers ---------------------------------------------------------------

fn bin(op: BinOp, l: Expr, r: Expr) -> Expr {
    Expr::new(l.loc, ExprKind::Binary(op, Box::new(l), Box::new(r)))
}

fn un(loc: Loc, op: UnOp, e: Expr) -> Expr {
    Expr::new(loc, ExprKind::Unary(op, Box::new(e)))
}

fn boxed(e: Expr, args: Vec<Expr>) -> Expr {
    Expr::new(e.loc, ExprKind::BoxJoin(Box::new(e), args))
}

fn keyword_box(kw: &str, args: Vec<Expr>, loc: Loc) -> Expr {
    let base = Expr::new(loc, ExprKind::Name(kw.to_string()));
    if args.is_empty() {
        base
    } else {
        boxed(base, args)
    }
}

fn mult_kw(t: &Tok) -> Option<Mult> {
    match t {
        Tok::One => Some(Mult::One),
        Tok::Lone => Some(Mult::Lone),
        Tok::SomeKw => Some(Mult::Some),
        Tok::Set => Some(Mult::Set),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// S-expression rendering so tests state tree shape without source locations.
    fn show(e: &Expr) -> String {
        let decls = |ds: &[Decl]| {
            ds.iter()
                .map(|d| format!("{}:{}", d.names.join(","), show(&d.expr)))
                .collect::<Vec<_>>()
                .join(", ")
        };
        match &e.kind {
            ExprKind::Name(s) => s.clone(),
            ExprKind::Const(c) => format!("{c:?}"),
            ExprKind::Num(n) => n.to_string(),
            ExprKind::Str(s) => format!("{s:?}"),
            ExprKind::Unary(op, x) => format!("({op:?} {})", show(x)),
            ExprKind::Binary(op, l, r) => format!("({op:?} {} {})", show(l), show(r)),
            ExprKind::BoxJoin(x, args) => {
                let a: Vec<String> = args.iter().map(show).collect();
                format!("(Box {} {})", show(x), a.join(" "))
            }
            ExprKind::Quant(q, ds, b) => format!("({q:?} [{}] {})", decls(ds), show(b)),
            ExprKind::Compr(ds, b) => format!("(Compr [{}] {})", decls(ds), show(b)),
            ExprKind::Let(bs, b) => {
                let s: Vec<String> = bs
                    .iter()
                    .map(|x| format!("{}={}", x.name, show(&x.expr)))
                    .collect();
                format!("(Let {} {})", s.join(" "), show(b))
            }
            ExprKind::IfElse(c, t, f) => format!("(ITE {} {} {})", show(c), show(t), show(f)),
            ExprKind::Block(items) => {
                let s: Vec<String> = items.iter().map(show).collect();
                format!("{{{}}}", s.join("; "))
            }
            ExprKind::Paren(x) => show(x),
        }
    }

    fn p(src: &str) -> String {
        match parse_expression("t.als", src) {
            Ok(e) => show(&e),
            Err(e) => panic!("{src:?} should parse: {}", e.msg),
        }
    }

    #[test]
    fn box_join_applies_to_whole_dot_chain() {
        assert_eq!(p("a.b[c]"), "(Box (Join a b) c)");
        assert_eq!(p("a[b].c"), "(Join (Box a b) c)");
        assert_eq!(p("a.b.c"), "(Join (Join a b) c)");
    }

    #[test]
    fn quantifier_body_takes_ite() {
        assert_eq!(p("all x: A | p => q else r"), "(All [x:A] (ITE p q r))");
        assert_eq!(p("some x, y: A | x in y"), "(Some [x,y:A] (In x y))");
    }

    #[test]
    fn prime_and_cardinality() {
        assert_eq!(p("x' = y"), "(Equals (Prime x) y)");
        assert_eq!(p("#a + 1"), "(Plus (Card a) 1)");
        assert_eq!(p("#a.b"), "(Card (Join a b))");
        assert_eq!(p("~a.b"), "(Join (Transpose a) b)");
        assert_eq!(p("^r"), "(Closure r)");
    }

    #[test]
    fn precedence_levels() {
        assert_eq!(p("a & b -> c"), "(Intersect a (Arrow(Set, Set) b c))");
        assert_eq!(p("a in b and c"), "(And (In a b) c)");
        assert_eq!(p("a or b => c"), "(Or a (Implies b c))");
        assert_eq!(p("not a = b"), "(Not (Equals a b))");
        assert_eq!(p("a => b else c"), "(ITE a b c)");
        assert_eq!(p("a + b.c"), "(Plus a (Join b c))");
        assert_eq!(p("a -> b.c"), "(Arrow(Set, Set) a (Join b c))");
    }

    #[test]
    fn negated_comparisons() {
        assert_eq!(p("a !in b"), "(Not (In a b))");
        assert_eq!(p("a != b"), "(Not (Equals a b))");
        assert_eq!(p("a !< b"), "(Not (Lt a b))");
        assert_eq!(p("!a"), "(Not a)");
    }

    #[test]
    fn multiplicities_and_arrows() {
        assert_eq!(p("one A"), "(One A)");
        assert_eq!(p("A one -> B"), "(Arrow(One, Set) A B)");
        assert_eq!(
            p("A -> lone B -> C"),
            "(Arrow(Set, Lone) A (Arrow(Set, Set) B C))"
        );
        assert_eq!(p("A set -> some B"), "(Arrow(Set, Some) A B)");
    }

    #[test]
    fn negative_literal_and_int_ops() {
        assert_eq!(p("x = -1"), "(Equals x -1)");
        assert_eq!(p("-1 + 2"), "(Plus -1 2)");
        assert_eq!(p("a fun/add b"), "(IntPlus a b)");
        assert_eq!(p("a fun/mul b fun/sub c"), "(IntMinus (Mul a b) c)");
    }

    #[test]
    fn comprehension_block_and_let() {
        assert_eq!(p("{ x: A | x in B }"), "(Compr [x:A] (In x B))");
        assert_eq!(p("{ a b }"), "{a; b}");
        assert_eq!(p("{}"), "{}");
        assert_eq!(p("let a = x | a.f"), "(Let a=x (Join a f))");
        assert_eq!(p("sum x: A | x.n"), "(Sum [x:A] (Join x n))");
    }

    #[test]
    fn names_keywords_and_restrictions() {
        assert_eq!(
            p("all disj x, y: A | x != y"),
            "(All [x,y:A] (Not (Equals x y)))"
        );
        assert_eq!(p("a.(b.c)"), "(Join a (Join b c))");
        assert_eq!(p("r.~s"), "(Join r (Transpose s))");
        assert_eq!(p("a.b'"), "(Join a (Prime b))");
        assert_eq!(p("@x"), "@x");
        assert_eq!(p("this/A"), "this/A");
        assert_eq!(p("seq/Int"), "seq/Int");
        assert_eq!(p("a[b, c]"), "(Box a b c)");
        assert_eq!(p("disj[a, b]"), "(Box disj a b)");
        assert_eq!(p("int[x]"), "(IntCast x)");
        assert_eq!(p("sum x"), "(IntCast x)");
        assert_eq!(p("some A"), "(Some A)");
        assert_eq!(p("no x: A | p"), "(No [x:A] p)");
        assert_eq!(p("seq A"), "(Seq A)");
        assert_eq!(p("x = none"), "(Equals x None)");
        assert_eq!(
            p("a -> b -> c"),
            "(Arrow(Set, Set) a (Arrow(Set, Set) b c))"
        );
        assert_eq!(p("a <: b :> c"), "(DomainRestrict a (RangeRestrict b c))");
        assert_eq!(p("a + b & c"), "(Plus a (Intersect b c))");
        assert_eq!(p("a ++ b & c"), "(Override a (Intersect b c))");
        assert_eq!(p("not a and b"), "(And (Not a) b)");
        assert_eq!(p("a; b"), "(And a (After b))");
    }

    #[test]
    fn rejects_malformed_input() {
        assert!(parse_expression("t.als", "a +").is_err());
        assert!(parse_expression("t.als", "(a").is_err());
        assert!(parse_expression("t.als", "a b )").is_err());
    }
}
