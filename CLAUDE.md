# alloy-rs — Rust rewrite of the Alloy Analyzer (Alloy 6.2.0)

Goal: a Rust CLI `alloy-rs` that gives **the same answers as Java Alloy 6.2.0** on the sample
models and is **not slower** than Java. You work in a loop; each iteration does ONE small task.
The per-iteration procedure is in `loop/PROMPT.md`. The task list is `loop/TASKS.md`.

## Directory map
| path | what | may you edit? |
|---|---|---|
| `crates/alloy-core` | lexer, parser, AST, modules, type checker (port of `edu.mit.csail.sdg.{alloy4,ast,parser}`) | YES |
| `crates/kodkod` | relational engine (port of Kodkod/Pardinus `kodkod.*`) | YES |
| `crates/satsolver` | SAT solver trait + pure-Rust backend (batsat) | YES |
| `crates/alloy-translate` | Alloy→Kodkod translation, bounds, solutions (port of `edu.mit.csail.sdg.translator`) | YES |
| `crates/alloy-cli` | `alloy-rs` binary; harness JSON protocol | only to add features; keep the protocol (`harness/SCHEMA.md`) |
| `loop/TASKS.md`, `loop/PROGRESS.md`, `loop/NOTES.md` | your plan / log / knowledge base | YES (keep them short) |
| `docs/JAVA_MAP.md` | Java→Rust file map | YES (add what you learn) |
| `harness/**` (scripts, goldens, oracle) | the judge | **NO — never** |
| `reference/**` | Java source + sample models (read-only reference) | **NO** |
| `loop/PROMPT.md`, `loop/run-loop.*` | loop driver | **NO** |

Java reference source root: `reference/alloy-java/` (see `docs/JAVA_MAP.md`). Key entry points:
- Grammar: `reference/alloy-java/org.alloytools.alloy.core/parser/Alloy.cup` (+ `Alloy.lex`)
- `.../edu/mit/csail/sdg/parser/CompModule.java`, `CompUtil.java`
- `.../edu/mit/csail/sdg/translator/TranslateAlloyToKodkod.java`, `ScopeComputer.java`, `BoundsComputer.java`
- `reference/alloy-java/org.alloytools.pardinus.core/src/main/java/kodkod/...`

## Commands (run from repo root `D:\sw\alloytoolRS`)
```
cargo build --release                      # binary: target/release/alloy-rs.exe
cargo test -q                              # unit tests (add tests for every ported piece)
python harness/check.py --quick            # smoke set, fast
python harness/check.py --filter <substr>  # subset
python harness/check.py --id <id> --verbose   # side-by-side Java vs Rust for one model
python harness/check.py --gate             # FULL run; exit 1 on regression vs harness/results/best.json
python harness/check.py --update-best      # FULL run; record new baseline (refused if regression)
python harness/check.py --perf --filter X  # sequential timing (trustworthy perf numbers)
python harness/check.py --count            # solution-count parity (symmetry=0), later milestone
target/release/alloy-rs exec --json --file reference/models/puzzles/money.als   # run one model
```
Java oracle for ad-hoc experiments (do not write to harness/golden):
```
java -cp "reference/bin/org.alloytools.alloy.dist.jar;harness/java-oracle/classes" AlloyOracle --file <model.als> [--count N --symmetry 0] [--no-instance]
```
If `cargo` is not found: `export PATH="$HOME/.cargo/bin:$PATH"` (bash) / `$env:PATH="$env:USERPROFILE\.cargo\bin;$env:PATH"` (PowerShell).

## Hard rules
1. **Port, don't invent.** When Rust differs from Java (answer, command header, error, speed), read the
   corresponding Java code and mirror its logic. Semantics must equal Java's, including scope defaults,
   command labels (`run$1`), `Command.toString()` text, atom names (`House$0`), and bitwidth rules.
2. **No cheating.** Never read harness/golden* from Rust code, never special-case model file names or
   labels, never hard-code answers, never weaken/skip harness checks. A pass must come from real logic.
3. **Never regress.** Before committing, `python harness/check.py --gate` must exit 0. If it fails, fix or
   revert your change.
4. **Pure-Rust dependencies only** (toolchain is `x86_64-pc-windows-gnu`, no C/C++ compiler). Prefer std.
   Allowed so far: serde, serde_json, batsat. Ask in `loop/NOTES.md` before adding more.
5. Small steps: one task per iteration, commit when it builds, tests pass and the gate passes.
6. Keep output small: pipe long outputs through `head`/`tail`; read big Java files by line ranges
   (`grep -n` first, then read ~150 lines around the hit). Never cat a whole 1000+ line file.
7. Library code must not panic on user input: return `AlloyError`. Avoid deep recursion blowups
   (the CLI runs work on a 1 GiB stack thread, but prefer iteration for long chains).

## Architecture contract (CLI ⇄ libraries)
- `alloy_core::parse_everything_from_file(&Path) -> Result<World, AlloyError>`
  (≈ `CompUtil.parseEverything_fromFile`). `World::commands()` lists **only the root module's** commands
  in source order, as `CommandInfo` (fields = Java `Command` fields; `scope_string` = `Command.toString()`).
- `alloy_translate::execute_command(&World, idx, &Options) -> Result<Solution, AlloyError>`
  (≈ `TranslateAlloyToKodkod.execute_command`). `Solution{sat, temporal, translate_ms, solve_ms, stats, ..}`,
  `Solution::instance()`, `Solution::next()` (≈ `A4Solution.next()`).
- `AlloyError.kind`: `Syntax`/`Type`/`Other` mirror Java `ErrorSyntax`/`ErrorType`/other `Err`;
  `Unsupported` = not ported yet (always a failure, but honest).
- A Java `ERROR` command (e.g. "higher-order quantification that could not be skolemized") must be an
  `Err(AlloyError)` in Rust too.

## Style
- Rust 2021, `cargo fmt` style, no `unsafe` unless measured necessary.
- Put a `//! Port of <java path>` header in every module, and `// Java: Class.method` comments on
  non-obvious ported functions, so the next iteration can find the counterpart quickly.
- Prefer arena/index-based ASTs (`Vec<Node>` + `NodeId(u32)`) over `Rc<RefCell<>>` graphs — faster and
  easier for the borrow checker; hash-cons where Kodkod relies on node identity/sharing.
