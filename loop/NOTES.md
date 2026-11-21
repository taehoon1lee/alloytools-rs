# NOTES — durable knowledge (keep bullets short; newest at the bottom of each section)

## Environment
- Windows 11, Rust stable via rustup, host `x86_64-pc-windows-gnu`, **no C compiler** → pure-Rust crates only.
- `cargo` lives in `%USERPROFILE%\.cargo\bin`; add to PATH if a shell does not see it.
- Java 25 (only for the oracle). Alloy reference jar: `reference/bin/org.alloytools.alloy.dist.jar` (6.2.0).
- On Windows the Java launcher expands `*` arguments as file globs — irrelevant for us (oracle has no wildcard args).

## Harness facts
- Goldens were produced with `TranslateAlloyToKodkod.execute_command` (NOT `execute_commandFromBook`), SAT4J,
  symmetry 20, skolemDepth 0, per-command timeout 60s, sequential (-j1) on this machine.
- Java timings include JVM/JIT cold start per file (first command of a file is the slowest).
- `temporal` in goldens = `A4Solution.getMinTrace() != -1`.
- Instances are informational only: different SAT solvers legitimately find different instances.
- Corpus golden status: 194 ok, 4 type_error, 1 syntax_error (natural.als: duplicate alias).
  Commands: 238 UNSAT, 215 SAT, 12 ERROR (higher-order quantification not skolemizable), 1 Java TIMEOUT (unscored). 19 temporal commands.
- Java SAT/UNSAT total time over the corpus ~286 s; dominated by hotel4 NoBadEntry (47 s), p306-hotel NoIntruder (24 s), temporal buffer (21-24 s).

## Java quirks (add as you discover them)
- Anonymous command labels: `run$N` / `check$N` with N = 1 + number of commands already added (CompModule ~l.1951).
- `Command.toString()` is at `CORE/ast/Command.java` ~l.137; scopes print like `3 Prisoner, exactly 2 X`.

- Lexer (Alloy.lex): longest match, ties -> earlier rule. `1_000` is a "Name cannot start with a number" error
  (name rule ties with decimal and wins). Hex `0x` digits come in pairs (`0xa_b` is an error, `0xab_cd` ok).
- Lexer emits raw `!` `=` for `!=`, `!` `in` for `!in`; the parser must merge them (Java Filter class).
- `Version.experimental = true`, so string literals are accepted. Java keeps the quote chars inside the string
  value; our `Tok::Str` stores the content without quotes (keep this in mind when comparing string constants).

- Expression precedence (CUP call chain, loosest first): `;` (trace seq, right) < `||` < `<=>` < `=>`/`else` (right)
  < `&&` < `until/since/releases/triggered` < prefix `!` `always`.. < `=` `in` `<` `>` `<=` `>=` (+ `!` forms)
  < `<<` `>>` `>>>` < `+` `-` (+ `fun/add`,`fun/sub`) < `fun/mul`,`fun/div`,`fun/rem` < prefix `#`/`sum`/`int`
  < `++` < `&` < `->` (right) < `<:` < `:>` < `.` and `[]` (same level, left) < prefix `~` `*` `^` < postfix `'`.
  So `a + b & c` = `a + (b & c)` and `a.b[c]` = `c.(a.b)`.
- Quantifier keywords (`all no some lone one sum`) are quantifiers only when a `[private] [disj] names :` follows
  and the previous token is not `:` / `disj` (CompFilter). Otherwise they are multiplicity prefixes (`x: one A`).
- `A set -> some B`: multiplicity keywords between/after `->` are merged into the arrow (CompFilter). `A -> set B` == `A -> B`.
- `-1` merges into a number literal only in primary position (CompFilter rule: not after `) ] } ID NUMBER ...`).

## Design decisions
- Surface AST (`syntax.rs`): `c => a else b` is `ExprKind::IfElse`; `a !in b` / `a != b` have no own BinOp —
  build `Unary(Not, Binary(In|Equals))` like Java's `ExprUnary.Op.NOT` wrapping. `a[b]` stays `BoxJoin` until M3.
- SAT backend: `satsolver::BatSat` (pure-Rust MiniSat-like). Java baseline uses SAT4J (Java MiniSat-like).

- Expression parser (`parser.rs`): one method per CUP level, no precedence table. Surface conventions are listed in
  the module doc (e.g. `{}` = TRUE, `disj[..]`/`pred/totalOrder[..]` = `BoxJoin(Name(..))`, `int[e]`/`e.int` = `IntCast`).
- Paragraph parser (`parse_module`): `Super` blocks are `Vec<Expr>` conjuncts; `a; b c` is parsed by `super_p` as
  `a` and `after({b; c})` (Java `SuperP`), NOT by `expr()` (which would make `after(b)` and leave `c` at time 0).
  `pred`/`fun` bodies are `Block(conjuncts)`; `{}` = `Block([])` = TRUE. Sig-local names are kept as `Sig.name`.
  `sig A = B` is `SigExtends::Equal` (Java marker `"="`), `in` is `SigExtends::In`, `extends` is `SigExtends::Extends`.
- Labelled commands (`L: run {..}`) exist in the corpus (Alloy 6 syntax); now parsed (M1.4b).
- Labelled commands: CompFilter rewrites `L: run` to `run L ...`; the label is the ID before the colon. `run L foo` / `run L {`
  means label L; `run foo` alone is a target. A following `Id :` is the next labelled paragraph, not a name.
- Scopes: `for N` is overall only when followed by nothing or `but`; `for 5 int`/`for 3 seq`/`for 2..4 steps` are typescopes.
  `int` and `Int` both set bitwidth. `N..M` is exact when N==M. `3:2 Node` = increment 2, end MAX (increment comes before the sig).
  The Java `c(...)` extraction (univ/int/seq/steps out of the list, dup errors) is done in the parser (`Parser::scope`).
- Labels for CommandInfo: explicit label, else the target name, else `run$N`/`check$N` (N = 1 + commands before it).
- Known gaps (not ported yet): `int[a, b]` multi-argument form (error for now); the `x = e` declaration form
  (`Declb EQUALS`, used for fields); multiplicity on `in`/`=` right operands is not rewritten to `*Of` forms (M3 must
  apply `CompModule.mult`).

- Module loading (`loader.rs`): `open` target not next to the file -> embedded library (`stdlib.rs`). `examples/algorithms/messaging`
  is embedded too (Java gets it from the distribution `models/`). Default alias = last segment if plain identifier and no args, else `open$N` renamed to that segment when free.
- OPEN QUESTION (natural.als): Java rejects `open util/integer as integer` ("same alias") even alone in a neutral module, but accepts `as foo`
  and no alias; `open util/ordering as integer` after `open util/integer as bar` is also rejected. The clash source is not in addOpen's
  visible state; investigate the `opens` map seeding in CompModule (~l.1370 `opens.clear()` pass) before porting.

## HARNESS ISSUES (write evidence here instead of editing harness/)
