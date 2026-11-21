# PROGRESS — append-only iteration log (max 6 lines per entry)

## 2026-11-21 M0 — environment built (Opus)
parse 0/199, commands 0/199, verdict 0/465, perf 0/465 (Rust returns `unsupported` everywhere)
next: M1.1 lexer

## 2026-11-21 M1.1 — lexer (`crates/alloy-core/src/lexer.rs`, longest-match like JFlex)
parse 0/199, commands 0/199, verdict 0/465, perf 0/465 (no parser yet; lexer unit tests + all 199+ corpus .als lex OK)
next: M1.2 surface AST (`syntax.rs`)

## 2026-11-21 M1.2 — surface AST (`crates/alloy-core/src/syntax.rs`, types only, no parsing yet)
parse 0/199, commands 0/199, verdict 0/465, perf 0/465 (unchanged; Rust still `unsupported`; 9 unit tests pass; gate exit 0)
next: M1.3 expression parser (precedence from Alloy.cup) producing `syntax::Expr`

## 2026-11-21 M1.3 — expression parser (`crates/alloy-core/src/parser.rs`, one fn per Alloy.cup level)
parse 0/199, commands 0/199, verdict 0/465, perf 0/465 (no paragraph parser yet; 19 alloy-core unit tests pass; gate exit 0)
Surface AST: added `Mult`, `BinOp::Arrow(Mult,Mult)`, `IntPlus/IntMinus`, `UnOp::IntCast`, `Const::IntMin/IntMax/IntNext`.
next: M1.4 declarations/paragraphs (sigs, fields via `Parser::decl`, facts, pred/fun, assert, run/check, open, enum, let)
