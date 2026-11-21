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
                self.bump_n(3);
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
        if self.eat(&Tok::Equals) {
            // Java `Declb ::= Names EQUALS Expr`: a defined field `f = e` (no `var`, no `disj`).
            if disjoint || *self.peek() == Tok::Disj {
                return self.err_at(loc, "Defined fields cannot be disjoint.");
            }
            if var {
                return self.err_at(loc, "Syntax error: defined fields cannot be 'var'.");
            }
            let e = self.expr()?;
            let expr = un(loc, UnOp::ExactlyOf, e);
            return Ok(Decl {
                loc,
                is_private,
                disjoint: false,
                var: false,
                names,
                expr,
            });
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

/// Parses one `.als` file into a [`Module`]: optional `module` header, then paragraphs in source order.
/// Java: `Spec` productions of `Alloy.cup` (+ the `CompModule.add*` actions they call).
/// `run`/`check`/`let` paragraphs are not parsed yet (M1.4b) and return `Unsupported`.
pub fn parse_module(file: &str, src: &str) -> PResult<Module> {
    let mut p = Parser::new(file, lex(file, src)?);
    let header = if *p.peek() == Tok::Module {
        Some(p.module_header()?)
    } else {
        None
    };
    let mut paragraphs = Vec::new();
    while *p.peek() != Tok::Eof {
        paragraphs.push(p.paragraph()?);
    }
    Ok(Module { header, paragraphs })
}

/// Result of a Java `TypeNumber` production (`CommandScope` start/end/increment/isExact).
struct TypeNum {
    exactly: bool,
    start: i32,
    end: i32,
    increment: i32,
}

// ---- paragraphs (Alloy.cup `Spec`, `Sig`, `Function`, `Predicate`, `Super`) -----------------
impl Parser {
    /// `module Name [ [exactly] A, B ]` (Java `Spec MODULE Name [Namex]`).
    fn module_header(&mut self) -> PResult<ModuleHeader> {
        let loc = self.loc();
        self.expect(&Tok::Module)?;
        let name = self.name()?;
        let mut params = Vec::new();
        if self.eat(&Tok::LBracket) {
            loop {
                self.eat(&Tok::Exactly);
                params.push(self.name()?);
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
            self.expect(&Tok::RBracket)?;
        }
        Ok(ModuleHeader { loc, name, params })
    }

    /// One paragraph. `[private]` is consumed here for the productions that accept `Vis`;
    /// sigs re-read their own qualifiers.
    fn paragraph(&mut self) -> PResult<Paragraph> {
        let start = self.pos;
        let is_private = self.eat(&Tok::Private);
        // `label: run ...` / `label: check ...` (Alloy 6): CompFilter rewrites it to `run label ...`.
        let labelled = matches!(self.peek(), Tok::Id(_))
            && *self.tok(1) == Tok::Colon
            && matches!(self.tok(2), Tok::Run | Tok::Check);
        let p = if labelled {
            let Tok::Id(label) = self.peek().clone() else {
                unreachable!("checked above")
            };
            self.bump_n(2);
            Paragraph::Command(self.command(Some(label))?)
        } else {
            match self.peek() {
                Tok::Open => Paragraph::Open(self.open(is_private)?),
                Tok::Enum => Paragraph::Enum(self.enum_decl(is_private)?),
                Tok::Fact => Paragraph::Fact(self.fact()?),
                Tok::Assert => Paragraph::Assert(self.assert()?),
                Tok::Pred => Paragraph::Pred(self.func(is_private, false)?),
                Tok::Fun => Paragraph::Fun(self.func(is_private, true)?),
                Tok::Let => Paragraph::Macro(self.macro_decl(is_private)?),
                Tok::Run | Tok::Check => Paragraph::Command(self.command(None)?),
                _ => {
                    self.pos = start;
                    Paragraph::Sig(self.sig()?)
                }
            }
        };
        Ok(p)
    }

    /// `[private] let Name [ (names) | [names] ] (= Expr | Super)` (Java `Macro`, `MacroBody`).
    fn macro_decl(&mut self, is_private: bool) -> PResult<Macro> {
        let loc = self.loc();
        self.expect(&Tok::Let)?;
        let name = self.name()?;
        let params = if self.eat(&Tok::LParen) {
            let v = self.name_list(&Tok::RParen)?;
            self.expect(&Tok::RParen)?;
            v
        } else if self.eat(&Tok::LBracket) {
            let v = self.name_list(&Tok::RBracket)?;
            self.expect(&Tok::RBracket)?;
            v
        } else {
            Vec::new()
        };
        let body = if self.eat(&Tok::Equals) {
            self.expr()?
        } else {
            let bl = self.loc();
            Expr::new(bl, ExprKind::Block(self.super_block()?))
        };
        Ok(Macro {
            loc,
            is_private,
            name,
            params,
            body,
        })
    }

    /// Possibly empty `name (, name)*` ending before `close` (not consumed).
    fn name_list(&mut self, close: &Tok) -> PResult<Vec<String>> {
        let mut out = Vec::new();
        while self.peek() != close {
            out.push(self.name()?);
            if !self.eat(&Tok::Comma) {
                break;
            }
        }
        Ok(out)
    }

    /// `run|check [Name] [Name|{Super}] [Scope] [Expects]` (Java `Command`, `c(...)` action).
    /// The label is passed in by `paragraph` for `L: run ...`; `run L foo` / `run L { }` set it here.
    fn command(&mut self, label: Option<String>) -> PResult<Command> {
        let loc = self.loc();
        let check = *self.peek() == Tok::Check;
        self.bump();
        let mut label = label;
        let target = if *self.peek() == Tok::LBrace {
            CommandTarget::Block(self.super_block()?)
        } else {
            let first = self.name()?;
            let has_label = label.is_some();
            if *self.peek() == Tok::LBrace || self.name_follows() {
                if has_label {
                    return self.err("a command can have only one label");
                }
                label = Some(first);
                if *self.peek() == Tok::LBrace {
                    CommandTarget::Block(self.super_block()?)
                } else {
                    CommandTarget::Name(self.name()?)
                }
            } else {
                CommandTarget::Name(first)
            }
        };
        let scopes = self.scope()?;
        let expect = if self.eat(&Tok::Expect) {
            Some(self.number()?)
        } else {
            None
        };
        if *self.peek() == Tok::Implies {
            return Err(AlloyError::unsupported(
                "follow-up commands (`cmd => cmd`) are not parsed yet",
            ));
        }
        Ok(Command {
            loc,
            label,
            check,
            target,
            scopes,
            expect,
        })
    }

    /// True if the next token starts another name of the same command (`run L foo`).
    /// `Id :` is the next labelled paragraph, not a name.
    fn name_follows(&self) -> bool {
        matches!(self.peek(), Tok::Id(_)) && *self.tok(1) != Tok::Colon
    }

    fn number(&mut self) -> PResult<i32> {
        match *self.peek() {
            Tok::Num(n) => {
                self.bump();
                Ok(n)
            }
            _ => self.err("expected a number"),
        }
    }

    /// `[for [N] [but] TypeScope, ...]` (Java `Scope`, `Typescopes`) followed by the parse-time
    /// extraction of `univ`/`int`/`seq`/`steps` done by `Alloy.cup` `c(...)`.
    fn scope(&mut self) -> PResult<Scopes> {
        let mut overall = None;
        let mut raw = Vec::new();
        if self.eat(&Tok::For) {
            let overall_only = match *self.tok(0) {
                Tok::Num(_) => {
                    let after = self.tok(1);
                    !(matches!(after, Tok::Dot | Tok::Colon) || self.type_name_start(1))
                }
                _ => false,
            };
            if overall_only {
                overall = Some(self.number()?);
                if self.eat(&Tok::But) {
                    raw = self.typescopes()?;
                }
            } else {
                raw = self.typescopes()?;
            }
        }
        let mut sc = Scopes {
            overall,
            ..Scopes::default()
        };
        // Java processes the list from the end; `univ` and `int`/`seq`/`steps` are removed from it.
        let mut kept = Vec::new();
        for ts in raw {
            match ts.sig.as_str() {
                "int" => {
                    if sc.bitwidth.is_some() {
                        return self.err_at(ts.loc, "The bitwidth cannot be specified more than once.");
                    }
                    sc.bitwidth = Some(ts.start);
                }
                "seq" => {
                    if sc.maxseq.is_some() {
                        return self.err_at(
                            ts.loc,
                            "The maximum sequence length cannot be specified more than once.",
                        );
                    }
                    sc.maxseq = Some(ts.start);
                }
                "steps" => {
                    if ts.end == i32::MAX && ts.start != 1 {
                        return self.err_at(ts.loc, "Unbounded time scope must start at 1.");
                    }
                    if ts.increment != 1 {
                        return self.err_at(ts.loc, "Step scopes must be incremented by 1.");
                    }
                    if ts.start < 1 {
                        return self.err_at(ts.loc, "Trace solutions must contain at least one step.");
                    }
                    if sc.steps.is_some() {
                        return self.err_at(ts.loc, "Steps scope cannot be specified more than once.");
                    }
                    sc.steps = Some(if ts.exactly {
                        Steps {
                            min: Some(ts.start),
                            max: ts.start,
                        }
                    } else if ts.end != ts.start {
                        Steps {
                            min: Some(ts.start),
                            max: ts.end,
                        }
                    } else {
                        Steps {
                            min: None,
                            max: ts.start,
                        }
                    });
                }
                _ => kept.push(ts),
            }
        }
        sc.typescopes = kept;
        Ok(sc)
    }

    /// Does a sig-name scope keyword (`Name`, `Int`, `int`, `seq`, `String`, `steps`) start at offset `k`?
    fn type_name_start(&self, k: usize) -> bool {
        matches!(
            self.tok(k),
            Tok::Id(_) | Tok::SigInt | Tok::Int | Tok::Seq | Tok::StringKw | Tok::Time | Tok::Univ | Tok::NoneKw
        )
    }

    /// `TypeScope (, TypeScope)*`.
    fn typescopes(&mut self) -> PResult<Vec<TypeScope>> {
        let mut out = vec![self.typescope()?];
        while self.eat(&Tok::Comma) {
            out.push(self.typescope()?);
        }
        Ok(out)
    }

    /// `TypeNumber sig` with the `Typescope` checks of `Alloy.cup` (growing/exact rules for int/seq).
    fn typescope(&mut self) -> PResult<TypeScope> {
        let loc = self.loc();
        let tn = self.type_number()?;
        let (sig, start, end, exactly, increment) = match self.peek() {
            Tok::Univ => return self.err_at(loc, "You cannot set a scope on univ."),
            Tok::NoneKw => return self.err_at(loc, "You cannot set a scope on none."),
            Tok::SigInt | Tok::Int => {
                self.bump();
                self.builtin_scope(loc, "int", tn, "Cannot specify a growing scope for \"Int\"", "The exactly keyword is redundant here since the integer bitwidth must be exact.")?
            }
            Tok::Seq if *self.tok(1) != Tok::Slash => {
                self.bump();
                self.builtin_scope(loc, "seq", tn, "Cannot specify a growing scope for \"seq\"", "The exactly keyword is redundant here since the number of sequence index has to be exact.")?
            }
            Tok::StringKw => {
                self.bump();
                ("String".to_string(), tn.start, tn.end, tn.exactly, tn.increment)
            }
            Tok::Time => {
                self.bump();
                ("steps".to_string(), tn.start, tn.end, tn.exactly, tn.increment)
            }
            _ => (self.name()?, tn.start, tn.end, tn.exactly, tn.increment),
        };
        Ok(TypeScope {
            loc,
            sig,
            exactly,
            start,
            end,
            increment,
        })
    }

    /// `int` / `Int` / `seq` scopes: a single exact value (no range, no `exactly`).
    #[allow(clippy::type_complexity)]
    fn builtin_scope(
        &self,
        loc: Loc,
        sig: &str,
        tn: TypeNum,
        growing: &str,
        redundant: &str,
    ) -> PResult<(String, i32, i32, bool, i32)> {
        if tn.end > tn.start {
            return self.err_at(loc, growing);
        }
        if tn.exactly {
            return self.err_at(loc, redundant);
        }
        Ok((sig.to_string(), tn.start, tn.start, false, 1))
    }

    /// Java `TypeNumber`: `[exactly] N [.. [M]] [: I]`. `N..M` is exact when N == M.
    fn type_number(&mut self) -> PResult<TypeNum> {
        let exactly = self.eat(&Tok::Exactly);
        let start = self.number()?;
        let mut end = start;
        let mut increment = 1;
        let mut range = false;
        if self.eat(&Tok::Dot) {
            self.expect(&Tok::Dot)?;
            range = true;
            end = if let Tok::Num(m) = *self.peek() {
                self.bump();
                m
            } else {
                i32::MAX
            };
        } else if *self.peek() == Tok::Colon {
            end = i32::MAX;
        }
        if self.eat(&Tok::Colon) {
            increment = self.number()?;
        }
        Ok(TypeNum {
            exactly: exactly || (range && start == end),
            start,
            end,
            increment,
        })
    }

    /// `[private] open
    fn open(&mut self, is_private: bool) -> PResult<Open> {
        let loc = self.loc();
        self.expect(&Tok::Open)?;
        let name = self.name()?;
        let mut args = Vec::new();
        if self.eat(&Tok::LBracket) {
            if !self.eat(&Tok::RBracket) {
                loop {
                    args.push(self.sig_ref()?);
                    if !self.eat(&Tok::Comma) {
                        break;
                    }
                }
                self.expect(&Tok::RBracket)?;
            }
        }
        let alias = if self.eat(&Tok::As) {
            Some(self.name()?)
        } else {
            None
        };
        Ok(Open {
            loc,
            is_private,
            name,
            args,
            alias,
        })
    }

    /// `[private] enum Name { A, B }` (the empty body `{}` is accepted, as in Java).
    fn enum_decl(&mut self, is_private: bool) -> PResult<EnumDecl> {
        let loc = self.loc();
        self.expect(&Tok::Enum)?;
        let name = self.name()?;
        self.expect(&Tok::LBrace)?;
        let mut values = Vec::new();
        if !self.eat(&Tok::RBrace) {
            loop {
                values.push(self.name()?);
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
            self.expect(&Tok::RBrace)?;
        }
        Ok(EnumDecl {
            loc,
            is_private,
            name,
            values,
        })
    }

    /// `fact [Name | "string"] Super`.
    fn fact(&mut self) -> PResult<Fact> {
        let loc = self.loc();
        self.expect(&Tok::Fact)?;
        let name = self.para_name()?;
        let body = self.super_block()?;
        Ok(Fact { loc, name, body })
    }

    /// `assert [Name | "string"] Super`.
    fn assert(&mut self) -> PResult<Assert> {
        let loc = self.loc();
        self.expect(&Tok::Assert)?;
        let name = self.para_name()?;
        let body = self.super_block()?;
        Ok(Assert { loc, name, body })
    }

    /// Optional name of a fact/assert: an identifier path or a string literal.
    fn para_name(&mut self) -> PResult<Option<String>> {
        match self.peek().clone() {
            Tok::LBrace => Ok(None),
            Tok::Str(s) => {
                self.bump();
                Ok(Some(s))
            }
            _ => Ok(Some(self.name()?)),
        }
    }

    /// `[private] pred [Sig.]name [ (decls) | [decls] ] Super` and
    /// `[private] fun [Sig.]name [ (decls) | [decls] ] : Expr Super`.
    /// The body is stored as one `Block` of conjuncts (Java wraps `Super` in `NOOP`).
    fn func(&mut self, is_private: bool, is_fun: bool) -> PResult<Func> {
        let loc = self.loc();
        self.bump(); // `pred` or `fun`
        let name = self.func_name()?;
        let params = if self.eat(&Tok::LParen) {
            let d = self.decl_list(&Tok::RParen)?;
            self.expect(&Tok::RParen)?;
            d
        } else if self.eat(&Tok::LBracket) {
            let d = self.decl_list(&Tok::RBracket)?;
            self.expect(&Tok::RBracket)?;
            d
        } else {
            Vec::new()
        };
        let ret = if is_fun {
            self.expect(&Tok::Colon)?;
            Some(self.expr()?)
        } else {
            None
        };
        let body_loc = self.loc();
        let body = Expr::new(body_loc, ExprKind::Block(self.super_block()?));
        Ok(Func {
            loc,
            is_private,
            name,
            params,
            ret,
            body,
        })
    }

    /// `Name` or `SigRef . Name` (sig-local `pred`/`fun`, rendered as `Sig.name`).
    fn func_name(&mut self) -> PResult<String> {
        let save = self.pos;
        if let Ok(sig) = self.sig_ref_name() {
            if self.eat(&Tok::Dot) {
                let n = self.name()?;
                return Ok(format!("{sig}.{n}"));
            }
        }
        self.pos = save;
        self.name()
    }

    /// `[private] [var] [abstract] [lone|one|some] sig Names [extends|in|= ...] { decls } [Super]`.
    /// Java `Sig` + `SigQuals` (a repeated qualifier is a syntax error at the second occurrence).
    fn sig(&mut self) -> PResult<SigDecl> {
        let loc = self.loc();
        let mut quals = SigQuals::default();
        loop {
            let at = self.loc();
            let slot: &mut bool = match self.peek() {
                Tok::Abstract => &mut quals.is_abstract,
                Tok::Lone => &mut quals.lone,
                Tok::One => &mut quals.one,
                Tok::SomeKw => &mut quals.some,
                Tok::Private => &mut quals.is_private,
                Tok::Var => &mut quals.var,
                Tok::Sig => break,
                _ => return self.err("expected 'sig'"),
            };
            if *slot {
                return self.err_at(
                    at,
                    "The same qualifier cannot be specified more than once for the same sig.",
                );
            }
            *slot = true;
            self.bump();
        }
        self.expect(&Tok::Sig)?;
        let mut names = vec![self.name()?];
        while self.eat(&Tok::Comma) {
            names.push(self.name()?);
        }
        let extends = match self.peek() {
            Tok::Extends => {
                self.bump();
                Some(SigExtends::Extends(self.sig_ref()?))
            }
            Tok::In => {
                self.bump();
                Some(SigExtends::In(self.sig_ref_plus()?))
            }
            Tok::Equals => {
                self.bump();
                Some(SigExtends::Equal(self.sig_ref_plus()?))
            }
            _ => None,
        };
        self.expect(&Tok::LBrace)?;
        let fields = self.decl_list(&Tok::RBrace)?;
        self.expect(&Tok::RBrace)?;
        let appended_fact = if *self.peek() == Tok::LBrace {
            Some(self.super_block()?)
        } else {
            None
        };
        Ok(SigDecl {
            loc,
            quals,
            names,
            extends,
            fields,
            appended_fact,
        })
    }

    /// Possibly empty `decl (, decl)*` ending before `close` (Java `Decls`); `close` is not consumed.
    fn decl_list(&mut self, close: &Tok) -> PResult<Vec<Decl>> {
        let mut out = Vec::new();
        while self.peek() != close {
            out.push(self.decl()?);
            if !self.eat(&Tok::Comma) {
                break;
            }
        }
        Ok(out)
    }

    /// `SigRef (+ SigRef)*` (Java `SigRefu`).
    fn sig_ref_plus(&mut self) -> PResult<Vec<Expr>> {
        let mut out = vec![self.sig_ref()?];
        while self.eat(&Tok::Plus) {
            out.push(self.sig_ref()?);
        }
        Ok(out)
    }

    /// A sig reference as an expression (Java `SigRef`): a name or a built-in sig keyword.
    fn sig_ref(&mut self) -> PResult<Expr> {
        let loc = self.loc();
        let s = self.sig_ref_name()?;
        Ok(Expr::new(loc, ExprKind::Name(s)))
    }

    /// Text of a `SigRef`: `univ`, `String`, `steps` (Java `TIME`), `Int`, `none`, `seq/Int`, or a `Name`.
    fn sig_ref_name(&mut self) -> PResult<String> {
        let s = match self.peek() {
            Tok::Univ => "univ",
            Tok::StringKw => "String",
            Tok::Time => "steps",
            Tok::SigInt => "Int",
            Tok::NoneKw => "none",
            _ => return self.name(),
        };
        self.bump();
        Ok(s.to_string())
    }

    /// `{ conjunct* }` (Java `Super`). Returns the top-level conjuncts; `{}` gives an empty list (TRUE).
    fn super_block(&mut self) -> PResult<Vec<Expr>> {
        self.expect(&Tok::LBrace)?;
        let out = self.super_p(&Tok::RBrace)?;
        self.expect(&Tok::RBrace)?;
        Ok(out)
    }

    /// Java `SuperP`: `ExprNoSeq*`, where `a ; rest` makes `rest` the operand of `after`
    /// (`a ; b c` = `a and after(b and c)`), so the sequence rule is applied here, not by `expr()`.
    fn super_p(&mut self, close: &Tok) -> PResult<Vec<Expr>> {
        let mut out = Vec::new();
        while self.peek() != close {
            let loc = self.loc();
            out.push(self.or_level()?);
            if self.eat(&Tok::TrcSeq) {
                let rest = self.super_p(close)?;
                let block = Expr::new(loc, ExprKind::Block(rest));
                out.push(Expr::new(
                    loc,
                    ExprKind::Unary(UnOp::After, Box::new(block)),
                ));
                break;
            }
        }
        Ok(out)
    }

    /// Syntax error at an explicit location (like `err`, but not at the cursor).
    fn err_at<T>(&self, at: Loc, msg: &str) -> PResult<T> {
        Err(AlloyError::syntax(
            Pos {
                file: self.file.clone(),
                line: at.line,
                col: at.col,
            },
            msg,
        ))
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
        assert_eq!(p("pred/totalOrder[a, b, c]"), "(Box pred/totalOrder a b c)");
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

    use crate::error::ErrorKind;

    fn module(src: &str) -> Module {
        parse_module("t.als", src).unwrap_or_else(|e| panic!("{src}: {e:?}"))
    }

    #[test]
    fn header_open_and_enum() {
        let m = module(
            "module util/foo[exactly T, U]\nprivate open util/ordering[S] as ord\nopen a/b\nprivate enum Color { Red, Green }\nenum E {}",
        );
        let h = m.header.unwrap();
        assert_eq!(h.name, "util/foo");
        assert_eq!(h.params, vec!["T", "U"]);
        let Paragraph::Open(o) = &m.paragraphs[0] else {
            panic!()
        };
        assert!(o.is_private);
        assert_eq!(o.name, "util/ordering");
        assert_eq!(o.alias.as_deref(), Some("ord"));
        assert_eq!(o.args.len(), 1);
        let Paragraph::Open(o2) = &m.paragraphs[1] else {
            panic!()
        };
        assert!(!o2.is_private && o2.args.is_empty() && o2.alias.is_none());
        let Paragraph::Enum(e) = &m.paragraphs[2] else {
            panic!()
        };
        assert_eq!(e.values, vec!["Red", "Green"]);
        let Paragraph::Enum(e2) = &m.paragraphs[3] else {
            panic!()
        };
        assert!(e2.values.is_empty());
    }

    #[test]
    fn sigs_with_qualifiers_fields_and_appended_fact() {
        let m = module(
            "abstract lone sig A, B extends C {f, g: set A, h: one B -> lone A} { some f } \
             var private sig D in A + B {} sig E = A + B {}",
        );
        let Paragraph::Sig(s) = &m.paragraphs[0] else {
            panic!()
        };
        assert!(s.quals.is_abstract && s.quals.lone && !s.quals.one);
        assert_eq!(s.names, vec!["A", "B"]);
        assert!(matches!(&s.extends, Some(SigExtends::Extends(e)) if show(e) == "C"));
        assert_eq!(s.fields.len(), 2);
        assert_eq!(s.fields[0].names, vec!["f", "g"]);
        assert_eq!(s.appended_fact.as_ref().map(Vec::len), Some(1));
        let Paragraph::Sig(d) = &m.paragraphs[1] else {
            panic!()
        };
        assert!(d.quals.var && d.quals.is_private);
        assert!(matches!(d.extends, Some(SigExtends::In(ref v)) if v.len() == 2));
        assert!(d.appended_fact.is_none());
        let Paragraph::Sig(e) = &m.paragraphs[2] else {
            panic!()
        };
        assert!(matches!(e.extends, Some(SigExtends::Equal(ref v)) if v.len() == 2));
    }

    #[test]
    fn facts_asserts_preds_and_funs() {
        let m = module(
            "fact \"name\" { all x: A | x in B  some C }\nassert NoX { no x }\nfact { }\n\
             pred p[a: A, b: B] { a = b }\nfun A.f(x: A): lone B { x.r }\nfun g: A { none }\n\
             pred Sig/h { }",
        );
        let Paragraph::Fact(f) = &m.paragraphs[0] else {
            panic!()
        };
        assert_eq!(f.name.as_deref(), Some("name"));
        assert_eq!(f.body.len(), 2);
        let Paragraph::Assert(a) = &m.paragraphs[1] else {
            panic!()
        };
        assert_eq!(a.name.as_deref(), Some("NoX"));
        let Paragraph::Fact(f2) = &m.paragraphs[2] else {
            panic!()
        };
        assert!(f2.name.is_none() && f2.body.is_empty());
        let Paragraph::Pred(p) = &m.paragraphs[3] else {
            panic!()
        };
        assert_eq!(p.name, "p");
        assert_eq!(p.params.len(), 2);
        assert!(p.ret.is_none());
        let Paragraph::Fun(f3) = &m.paragraphs[4] else {
            panic!()
        };
        assert_eq!(f3.name, "A.f");
        assert!(f3.ret.is_some());
        let Paragraph::Fun(g) = &m.paragraphs[5] else {
            panic!()
        };
        assert_eq!(g.name, "g");
        let Paragraph::Pred(h) = &m.paragraphs[6] else {
            panic!()
        };
        assert_eq!(h.name, "Sig/h");
    }

    #[test]
    fn temporal_sequence_inside_block_wraps_rest_in_after() {
        let m = module("fact { a; b c }");
        let Paragraph::Fact(f) = &m.paragraphs[0] else {
            panic!()
        };
        assert_eq!(f.body.len(), 2);
        assert_eq!(show(&f.body[0]), "a");
        assert_eq!(show(&f.body[1]), "(After {b; c})");
    }

    #[test]
    fn repeated_qualifier_and_missing_braces_are_syntax_errors() {
        let e = parse_module("t.als", "lone lone sig A {}").unwrap_err();
        assert_eq!(e.kind, ErrorKind::Syntax);
        assert_eq!(e.pos.as_ref().map(|p| p.col), Some(6));
        assert!(parse_module("t.als", "sig A").is_err());
        assert!(parse_module("t.als", "fact { a").is_err());
        assert!(parse_module("t.als", "pred p").is_err());
    }

    fn collect_als(dir: &std::path::Path, out: &mut Vec<std::path::PathBuf>) {
        let Ok(rd) = std::fs::read_dir(dir) else {
            return;
        };
        for ent in rd.flatten() {
            let p = ent.path();
            if p.is_dir() {
                collect_als(&p, out);
            } else if p.extension().is_some_and(|x| x == "als") {
                out.push(p);
            }
        }
    }

    /// Every corpus file must parse; the only allowed exception is the not-yet-ported follow-up
    /// command form (`cmd => cmd`). Lists every failure so the next step is obvious.
    #[test]
    fn corpus_parses_apart_from_unsupported_paragraphs() {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../reference");
        let mut files = Vec::new();
        collect_als(&root, &mut files);
        assert!(!files.is_empty());
        let mut failures = Vec::new();
        for f in &files {
            let src = std::fs::read_to_string(f).unwrap_or_default();
            match parse_module(&f.display().to_string(), &src) {
                Ok(_) => {}
                Err(e) if e.kind == ErrorKind::Unsupported && e.msg.contains("follow-up") => {}
                Err(e) => failures.push(format!("{}: {e}", f.display())),
            }
        }
        assert!(
            failures.is_empty(),
            "{} files failed to parse:\n{}",
            failures.len(),
            failures.join("\n")
        );
    }

    fn command_of(src: &str) -> Command {
        let m = module(src);
        match m.paragraphs.into_iter().next() {
            Some(Paragraph::Command(c)) => c,
            other => panic!("{src}: not a command: {other:?}"),
        }
    }

    #[test]
    fn command_forms_and_labels() {
        let c = command_of("run {} for 3");
        assert!(!c.check && c.label.is_none());
        assert!(matches!(c.target, CommandTarget::Block(ref b) if b.is_empty()));
        assert_eq!(c.scopes.overall, Some(3));

        let c = command_of("check A_ok for 4 but 2 B, exactly 1 C expect 0");
        assert!(c.check);
        assert_eq!(c.expect, Some(0));
        assert!(matches!(c.target, CommandTarget::Name(ref n) if n == "A_ok"));
        assert_eq!(c.scopes.overall, Some(4));
        assert_eq!(c.scopes.typescopes.len(), 2);
        assert_eq!(c.scopes.typescopes[1].sig, "C");
        assert!(c.scopes.typescopes[1].exactly);

        let c = command_of("WriteRead: check { some A } for 3");
        assert_eq!(c.label.as_deref(), Some("WriteRead"));
        assert!(matches!(c.target, CommandTarget::Block(_)));

        let c = command_of("run L foo for 2");
        assert_eq!(c.label.as_deref(), Some("L"));
        assert!(matches!(c.target, CommandTarget::Name(ref n) if n == "foo"));

        let c = command_of("example: run {}");
        assert_eq!(c.label.as_deref(), Some("example"));
    }

    #[test]
    fn scope_extraction_like_java_c_action() {
        let c = command_of("run f for 6 but 5 int, 3 seq, 2..4 steps, 7 Node, 2 String");
        assert_eq!(c.scopes.overall, Some(6));
        assert_eq!(c.scopes.bitwidth, Some(5));
        assert_eq!(c.scopes.maxseq, Some(3));
        let st = c.scopes.steps.unwrap();
        assert_eq!((st.min, st.max), (Some(2), 4));
        let names: Vec<&str> = c.scopes.typescopes.iter().map(|t| t.sig.as_str()).collect();
        assert_eq!(names, vec!["Node", "String"]);

        let c = command_of("run f for exactly 3 Node, 1..1 steps");
        let t = &c.scopes.typescopes[0];
        assert!(t.exactly && t.start == 3 && t.end == 3 && t.increment == 1);
        let st = c.scopes.steps.unwrap();
        assert_eq!((st.min, st.max), (Some(1), 1));

        let c = command_of("run f for 3:2 Node");
        assert_eq!(c.scopes.typescopes[0].end, i32::MAX);
        assert_eq!(c.scopes.typescopes[0].increment, 2);
    }

    #[test]
    fn scope_errors_are_syntax_errors() {
        for src in [
            "run f for 3 int, 4 int",
            "run f for 2..5 int",
            "run f for exactly 3 int",
            "run f for univ",
            "run f for 3 none",
            "run f for 3 steps, 2 steps",
            "run f for 0 steps",
        ] {
            let e = parse_module("t.als", &format!("{src} expect 1 ")).unwrap_err();
            assert_eq!(e.kind, ErrorKind::Syntax, "{src}");
        }
    }

    #[test]
    fn follow_up_commands_are_unsupported_for_now() {
        let e = parse_module("t.als", "run {} => check {}").unwrap_err();
        assert_eq!(e.kind, ErrorKind::Unsupported);
    }

    #[test]
    fn let_macros_and_defined_fields() {
        let m = module("let twice(a, b) = a.b\nprivate let m[] { some A }\nlet k = 3\nsig S { f = A -> B }");
        let Paragraph::Macro(t) = &m.paragraphs[0] else { panic!() };
        assert_eq!(t.params, vec!["a", "b"]);
        assert!(matches!(t.body.kind, ExprKind::Binary(_, _, _)));
        let Paragraph::Macro(mm) = &m.paragraphs[1] else { panic!() };
        assert!(mm.is_private && mm.params.is_empty());
        let Paragraph::Macro(k) = &m.paragraphs[2] else { panic!() };
        assert!(matches!(k.body.kind, ExprKind::Num(3)));
        let Paragraph::Sig(s) = &m.paragraphs[3] else { panic!() };
        let f = &s.fields[0];
        assert_eq!(f.names, vec!["f"]);
        assert!(matches!(f.expr.kind, ExprKind::Unary(UnOp::ExactlyOf, _)));
        assert!(parse_module("t.als", "sig S { disj f = A }").is_err());
    }

    #[test]
    fn rejects_malformed_input() {
        assert!(parse_expression("t.als", "a +").is_err());
        assert!(parse_expression("t.als", "(a").is_err());
        assert!(parse_expression("t.als", "a b )").is_err());
    }
}
