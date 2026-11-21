# alloy-rs — Alloy Analyzer (Java) → Rust rewrite, built as a loop-engineering environment

Opus built the environment; the actual porting is done by **separate Haiku sessions running in an iteration loop**.
There is a single judge: the score of `python harness/check.py` — the **same answers** as Java Alloy 6.2.0, and **not slower**.

## Layout
```
reference/                    (not in git, read-only)
  alloy-java/                 github.com/AlloyTools/org.alloytools.alloy  (Java source being ported)
  models/                     github.com/AlloyTools/models                (sample models)
  bin/org.alloytools.alloy.dist.jar   official Alloy 6.2.0 release (reference executor)
harness/                      the judge — must not be edited inside the loop
  java-oracle/src/AlloyOracle.java   runs every command through the Alloy API and prints normalized JSON
  corpus.json                 the 199 .als files compared (models repo + Alloy's bundled examples)
  golden/                     Java results (status, SAT/UNSAT, timings, variable/clause counts, first instance)
  golden_count/               solution counts with symmetry breaking off (symmetry=0, capped at 100) — for M7
  check.py                    runs Rust → compares with golden → scoreboard / regression check
  quick.txt                   16-model smoke set
  SCHEMA.md                   JSON protocol shared by Java and Rust
crates/                       Rust workspace (filled in by Haiku)
  alloy-core  kodkod  satsolver  alloy-translate  alloy-cli (→ target/release/alloy-rs.exe)
loop/
  PROMPT.md                   procedure for one Haiku iteration (do not edit)
  TASKS.md                    milestone task list M1~M9 (ticked off by Haiku)
  PROGRESS.md / NOTES.md      iteration log / knowledge base (memory across sessions)
  run-loop.ps1                loop driver
CLAUDE.md                     rules every session reads automatically
docs/JAVA_MAP.md              Java file ↔ Rust module map
```

## Score levels (check.py)
| Level | Criterion |
|---|---|
| parse | file status (ok / syntax_error / type_error) equals Java's |
| commands | the command list (label, run/check, expect, the `Command.toString()` scope string, ...) equals Java's |
| verdict | per-command SAT / UNSAT / ERROR equals Java's (465 commands; the one Java timeout is excluded) |
| perf | verdict matches **and** `rust_ms ≤ 1.1 × java_ms + 20ms` |
| --count | (M7) the number of solutions with symmetry=0 equals Java's |

## Current status (2026-11-22)
| Item | Result |
|---|---|
| parse / commands | 199/199, 199/199 |
| verdict | 465/465 (SAT/UNSAT/ERROR identical to Java) |
| perf (sequential `--perf`) | 465/465; total time Rust 28.5 s vs Java 285.7 s (about 0.10×; was 44.3 s before the SAT/BVE/temporal work) |
| `--count` (symmetry=0) | 432/432 (the 34 commands Java timed out on are not scored) |
| temporal logic (`var`, LTL, steps) | implemented; every temporal command in the corpus matches |

- `--gate` runs 8 commands in parallel, so the perf score of borderline commands fluctuates with machine load
  (409–465/465 observed). Check speed with the sequential `python harness/check.py --perf`.
- In `--count` mode `check.py` prints "REGRESSIONS vs best.json". That is not a real regression: the verdict-mode
  `best.json` contains commands that Java timed out on, which count mode does not score.
- Debug environment variables: `KTIME`, `KPROF`, `KSAT_CONFIGS`, `KSAT_STATS`, `KCOUNT`, `KSAT_WHO`, `KSAT_DUMP`,
  `KSAT_NOBIN`, `KSAT_NOSIMP`, `KTRACE_ALL` (see loop/NOTES.md).

## Implementation notes: temporal logic (Alloy 6)
(`crates/alloy-translate/src/translate.rs`, `lib.rs`)
- Traces of length k are solved for k = min..max steps (default 1..10), stopping at the first SAT. An unbounded
  `N..` steps range gives the same ERROR as Java ("Bounded engines do not support complete model checking.").
- Each time atom `$time$i` lives in its own exact relation; a free relation `$loop` (exactly one tuple) points at the
  state the loop returns to. `var` sigs/fields get a trailing time column.
- Every expression is translated at a time point `Tp{level, state}`. Level 1 is the first pass; level 2 is the loop
  part (reachable only if the loop start is at or before that state). `always`, `eventually`, `after`, `before`,
  `historically`, `once`, `until`, `since`, `releases` and `triggered` expand into And/Or over the reachable time
  points, and `e'` becomes an ITE over the loop targets at the last state. Facts and the command formula are
  evaluated at `Tp{1,0}`; declaration constraints of var sigs/fields and sig facts are imposed in every state.
- 240 random temporal formulas (including the until/since/releases/triggered equivalences) were differentially tested
  against Java with 0 mismatches.

## Implementation notes: `--count` (solution enumeration)
(`alloy_translate::count_solutions`, `kodkod::translate::{count_all, count_projected, first_instance}`)
- Non-temporal models: solutions are counted one by one without symmetry breaking, adding a clause that blocks the
  primary and skolem variables of each solution found (limit N, reported as `count_capped`).
- Temporal models follow Pardinus `next()` semantics. The first solution fixes the static relations; afterwards only
  distinct lasso traces are counted, over increasing trace lengths. Each trace is counted once, at its minimal
  prefix and minimal loop period (`canonical_lasso`).
- Java's count depends on its first solution (MiniSat's false-first phase), so the static-relation variables are
  chosen lexicographically smallest (`first_instance` + `SatSolver::solve_assuming`). This matches Java on the whole
  corpus but is an approximation, not a copy of Java's solver.

## Running the Haiku loop

### Option A — headless driver (recommended)
Every iteration starts a Haiku session with a **fresh context** and performs one task.
```powershell
cd D:\sw\alloytoolRS
pwsh -File loop/run-loop.ps1                          # defaults: --model haiku, up to 100 iterations, 45 min each
pwsh -File loop/run-loop.ps1 -MaxIterations 10 -IterationTimeoutMin 30 -MaxBudgetUsdPerIter 2
New-Item loop/STOP                                    # stop after the current iteration
```
After every iteration the driver:
1. reverts any change to protected files (harness/, PROMPT.md, CLAUDE.md, the driver, settings)
2. commits leftover uncommitted changes
3. **re-runs the full gate** (`check.py --gate --update-best`)
   - pass → updates and commits the baseline (best.json)
   - build failure / regression → keeps that iteration's work on a `rejected/iter-NNN` branch, resets HEAD to the
     state before the iteration and records the reason in `loop/LAST_REJECTED.md`, which the next iteration reads
4. stops after 4 consecutive iterations without changes under `crates/` (stuck detection)

Logs: `loop/logs/driver.log` (summary), `loop/logs/iter-NNN-*.jsonl` (full stream-json of each session).
To test the driver itself without calling Claude, substitute a fake agent with `-Agent <fake-agent.ps1>`.

### Option B — interactive Haiku session
```powershell
cd D:\sw\alloytoolRS
claude --model haiku --settings loop/haiku-settings.json
> /loop read loop/PROMPT.md and perform one iteration following that procedure
```
Context keeps accumulating in one session (with automatic summarization), so Option A is better for long runs.
In Option B nothing reverts regressions for you, so run `python harness/check.py --gate` yourself now and then.

## Watching progress
```powershell
python harness/check.py --no-build          # current scoreboard (skip the build)
Get-Content harness/results/history.csv     # score history per run
Get-Content loop/PROGRESS.md -Tail 30       # Haiku work log
git log --oneline | Select-Object -First 20
```

## Rebuilding / checks
```powershell
python harness/setup.py                    # check reference, jar, oracle, cargo (installs/builds what is missing)
python harness/gen_golden.py --force       # regenerate golden (about 8 min, sequential = accurate timings)
python harness/gen_golden.py --count-mode --force -j 4
```

## Design notes
- **Java oracle**: the official CLI's receipt.json has no parse-error positions, translation statistics or per-command
  timing split, and the Windows Java launcher expands `-c *` as a file glob. So the oracle calls the Alloy API directly
  (`CompUtil.parseEverything_fromFile`, `TranslateAlloyToKodkod.execute_command`). Per-command timeout 60 s.
- **Rust execution**: the harness runs every command in a separate process (isolating crashes and infinite loops);
  timeout = `min(60s, max(3s, 5×Java+2s))`.
- **SAT solver**: the pure-Rust `batsat` (MiniSat family, vendored in `crates/batsat` with binary-clause watches) sits
  behind the `satsolver` trait, standing in for Java's default SAT4J; `satsolver::simp` adds MiniSat-style variable
  elimination. The toolchain is `x86_64-pc-windows-gnu` (no C compiler), so only pure-Rust dependencies are allowed.
- **Anti-cheating**: Rust code must not read golden files or special-case file names (CLAUDE.md). Protected files are
  guarded twice: the deny rules in `loop/haiku-settings.json` (the driver applies them to Haiku only, via `--settings`)
  and the driver's automatic revert. The deny rules do not apply to interactive sessions (Option B), so start those
  with `claude --model haiku --settings loop/haiku-settings.json`.
- Instances themselves can legitimately differ between SAT solvers, so they are not compared; semantic equality is
  checked through solution counts (symmetry=0) instead (M7).
