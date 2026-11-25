# alloytools-rs

A pure-Rust port of the [Alloy Analyzer](https://alloytools.org) 6.2.0 (parser, type checker,
Kodkod/Pardinus translation and a built-in SAT solver). It aims to give the same answers as
the Java Alloy 6.2.0 on its sample models. No JVM and no C/C++ toolchain required.

```
cargo install alloytools-rs        # installs the `alloy-rs` binary
alloy-rs exec --json --file model.als
```

Prebuilt binaries for Windows, Linux and macOS are attached to each
[GitHub release](https://github.com/taehoon1lee/alloytools-rs/releases).

The output is a JSON document with one entry per `run`/`check` command (status, bounds,
statistics and the first instance or counterexample).

## License

MIT. See `LICENSE` (includes the upstream Alloy, Kodkod and BatSat/MiniSat notices).
