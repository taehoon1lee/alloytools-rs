# Third-Party Licenses & Provenance

`alloy-rs` is a pure-Rust port of Alloy Analyzer 6.2.0 and its underlying relational/SAT engines, with one vendored Rust SAT backend (`batsat`). Upstream sources are pinned under `reference/alloy-java/` and documented in `docs/JAVA_MAP.md` and `docs/EXACT_PORT.md`.

## Upstream & Vendored Components

| Component | Upstream / Reference Source | Rust Location | License |
|---|---|---|---|
| **Alloy Analyzer 6.2.0** | `reference/alloy-java/org.alloytools.alloy.core` ([Alloy.txt](reference/alloy-java/org.alloytools.alloy.dist/LICENSES/Alloy.txt)) | `crates/alloy-core`, `crates/alloy-translate` | **MIT** (incl. MIT no-endorsement clause) |
| **Kodkod / Pardinus** | `reference/alloy-java/org.alloytools.pardinus.core` ([Kodkod.txt](reference/alloy-java/org.alloytools.alloy.dist/LICENSES/Kodkod.txt)) | `crates/kodkod`, `crates/pardinus` | **MIT** |
| **batsat 0.6.0** (vendored, modified in-tree) | `github.com/c-cube/batsat` (`crates/batsat/Cargo.toml`) | `crates/batsat`, `crates/satsolver` | **MIT** |
| **SAT4J 2.3.1** (`SolverFactory.newDefault()`) | `org.sat4j.core` 2.3.1 embedded in Alloy 6.2.0 ([SAT4J.txt](reference/alloy-java/org.alloytools.alloy.dist/LICENSES/SAT4J.txt)) | `crates/satsolver/src/sat4j.rs` | **GNU LGPL-2.1** (upstream SAT4J 2.3.1 is dual-licensed EPL-1.0 / LGPL-2.1) |

## Licensing Status & Distribution Notice

1. **Direct translation under LGPL-2.1**:
   GNU LGPL-2.1 Section 0 explicitly defines a work *"translated straightforwardly into another language"* as a derivative work (*"work based on the Library"*). `crates/satsolver/src/sat4j.rs` is a bit-exact port of SAT4J 2.3.1 (`org.sat4j.core`), and therefore remains subject to **LGPL-2.1** (or upstream **EPL-1.0**).
2. **Current workspace build (`alloy-rs`) is NOT pure MIT**:
   Because `crates/satsolver/src/sat4j.rs` is currently compiled unconditionally inside `crates/satsolver` (used by `crates/pardinus` and `crates/alloy-translate`'s exact pipeline) and statically linked into the `alloy-rs` binary, any binary or combined library built from the current workspace carries **LGPL-2.1** (or EPL-1.0) obligations — including LGPL-2.1 Section 6 requirements for static linking (providing relinkable object files/source or equivalent compliance notices).
3. **Planned follow-up for pure-MIT builds**:
   Before any binary distribution intended as pure MIT, isolate `crates/satsolver/src/sat4j.rs` (and the exact-instance SAT4J path) into a separate crate behind an opt-in Cargo feature (e.g., `sat4j-exact`), keeping the default `batsat`-backed build pure MIT.
4. **MIT no-endorsement notice**:
   Per `reference/alloy-java/org.alloytools.alloy.dist/LICENSES/Alloy.txt`, the name of the Massachusetts Institute of Technology must not be used in advertising or otherwise to promote this software without prior written authorization.
