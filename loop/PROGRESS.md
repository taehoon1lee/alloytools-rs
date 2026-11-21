# PROGRESS — append-only iteration log (max 6 lines per entry)

## 2026-11-21 M0 — environment built (Opus)
parse 0/199, commands 0/199, verdict 0/465, perf 0/465 (Rust returns `unsupported` everywhere)
next: M1.1 lexer

## 2026-11-21 M1.1 — lexer (`crates/alloy-core/src/lexer.rs`, longest-match like JFlex)
parse 0/199, commands 0/199, verdict 0/465, perf 0/465 (no parser yet; lexer unit tests + all 199+ corpus .als lex OK)
next: M1.2 surface AST (`syntax.rs`)
