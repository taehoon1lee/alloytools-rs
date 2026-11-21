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

## Design decisions
- SAT backend: `satsolver::BatSat` (pure-Rust MiniSat-like). Java baseline uses SAT4J (Java MiniSat-like).

## HARNESS ISSUES (write evidence here instead of editing harness/)
