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

## 2026-11-21 M1.4a — paragraph parser (`parse_module` in `parser.rs`: header, open, enum, sig, fact, assert, pred, fun)
parse 0/199, commands 0/199, verdict 0/465, perf 0/465 (`parse_everything_from_file` not wired yet; 26 alloy-core tests pass; gate exit 0)
Fixed M1.3 bug: `pred/totalOrder[..]` in primary position bumped 2 tokens instead of 3.
Corpus test: every file parses except run/check/let/labelled commands (Unsupported). Errors after the first command are not checked yet.
next: M1.4b run/check/labelled commands + `let` macros + `x = e` field form, then wire `parse_everything_from_file` (`World::commands`)

## 2026-11-21 M1.4b/M1.5 — commands, macros, `f = e` fields; parse 194/199 (acceptance met)
parse 194/199, commands 0/199, verdict 0/465, perf 0/465 (`parse_everything_from_file` = root module only; `scope_string` empty)
Parse misses are Java module/type errors (natural dup alias = M2.1; integer/seqrel/sequniv/sequence type errors = M3). 30 alloy-core tests; strict corpus parse test; gate exit 0.
next: M2.1 module loading (`open`, params, aliases) then M2.2/M2.3 commands (labels, Command.toString)

## 2026-11-21 M2.2/M2.3/M2.4 — command headers: Command.toString, default `Run Default`, labels; commands 194/199 (acceptance met)
parse 194/199, commands 194/199, verdict 0/465, perf 0/465 (`command_to_string`/`scope_entry_to_string` in lib.rs mirror Command.java toString + CommandScope.toString; no-command module gets Java's `Default`)
next: M2.1 module loading (natural.als dup alias; `open` resolution), then M3 semantics

## 2026-11-21 M2.1 — module loader (`loader.rs`): opens resolved relative to the file, else embedded library; parse 194/199
parse 194/199, commands 194/199, verdict 0/465, perf 0/465 (opened modules are loaded into `World::modules`; no semantics yet)
Embedded `examples/algorithms/messaging` (ringlead needs it). natural.als alias error still open (see NOTES).
next: M3.1 resolved sig hierarchy / fields (semantic model)
