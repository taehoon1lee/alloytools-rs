//! alloy-rs — Rust port of the Alloy Analyzer (CLI only).
//!
//! Harness protocol (see harness/SCHEMA.md). The harness calls:
//!   alloy-rs exec --json --file F --display-name ID --no-solve          (parse + command headers)
//!   alloy-rs exec --json --file F --display-name ID --command I [--timeout-ms MS] [--count N --symmetry 0 --no-instance]
//! and prints exactly ONE JSON document on stdout. Exit code 3 = a command timed out.
//!
//! This file is infrastructure: keep the protocol stable. Put semantics in the library crates.

use alloy_core::{AlloyError, CommandInfo, World};
use alloy_translate::{execute_command, Instance, Options};
use serde_json::{json, Map, Value};
use std::path::PathBuf;
use std::sync::{mpsc, Arc};
use std::time::{Duration, Instant};

const SOLVER_STACK: usize = 1024 * 1024 * 1024; // deep recursion in translators

struct Args {
    file: PathBuf,
    display: String,
    no_solve: bool,
    command: Option<usize>,
    timeout_ms: u64,
    count: u32,
    opt: Options,
}

fn usage() -> ! {
    eprintln!(
        "usage: alloy-rs exec --json --file F [--display-name N] [--no-solve] [--command I]\n\
         \x20                [--timeout-ms MS] [--symmetry S] [--count N] [--no-instance]"
    );
    std::process::exit(2)
}

fn parse_args() -> Args {
    let mut it = std::env::args().skip(1);
    if it.next().as_deref() != Some("exec") {
        usage();
    }
    let mut a = Args {
        file: PathBuf::new(),
        display: String::new(),
        no_solve: false,
        command: None,
        timeout_ms: 60_000,
        count: 0,
        opt: Options::default(),
    };
    while let Some(s) = it.next() {
        let mut val = || it.next().unwrap_or_else(|| usage());
        match s.as_str() {
            "--json" => {}
            "--file" => a.file = PathBuf::from(val()),
            "--display-name" => a.display = val(),
            "--no-solve" => a.no_solve = true,
            "--command" => a.command = Some(val().parse().unwrap_or_else(|_| usage())),
            "--timeout-ms" => a.timeout_ms = val().parse().unwrap_or_else(|_| usage()),
            "--symmetry" => a.opt.symmetry = val().parse().unwrap_or_else(|_| usage()),
            "--count" => a.count = val().parse().unwrap_or_else(|_| usage()),
            "--no-instance" => a.opt.want_instance = false,
            _ => usage(),
        }
    }
    if a.file.as_os_str().is_empty() {
        usage();
    }
    if a.display.is_empty() {
        a.display = a.file.display().to_string();
    }
    a
}

fn err_json(e: &AlloyError) -> Value {
    let (line, col, in_file) = match &e.pos {
        Some(p) => (
            p.line,
            p.col,
            std::path::Path::new(&p.file).file_name().map(|s| s.to_string_lossy().to_string()).unwrap_or_default(),
        ),
        None => (-1, -1, String::new()),
    };
    json!({"kind": e.status_str(), "line": line, "col": col, "in_file": in_file, "msg": e.msg})
}

fn header(c: &CommandInfo, idx: usize) -> Map<String, Value> {
    let v = json!({
        "index": idx, "label": c.label, "kind": if c.check {"check"} else {"run"},
        "expects": c.expects, "scope": c.scope_string, "overall": c.overall, "bitwidth": c.bitwidth,
        "maxseq": c.maxseq, "minprefix": c.minprefix, "maxprefix": c.maxprefix,
    });
    match v {
        Value::Object(m) => m,
        _ => unreachable!(),
    }
}

fn instance_json(i: &Instance) -> Value {
    let states: Vec<Value> = i
        .states
        .iter()
        .map(|st| {
            let mut m = Map::new();
            for (k, tuples) in st {
                // the oracle sorts the JSON text of each tuple (`String.compareTo`)
                let mut t = tuples.clone();
                t.sort_by_cached_key(|x| serde_json::to_string(x).unwrap_or_default().encode_utf16().collect::<Vec<u16>>());
                m.insert(k.clone(), json!(t));
            }
            Value::Object(m)
        })
        .collect();
    json!({"trace_length": i.trace_length, "loop": i.loop_state, "states": states})
}

fn ms(t: Instant) -> f64 {
    (t.elapsed().as_secs_f64() * 1e6).round() / 1e3
}

/// Runs one command; never panics outward (panics are converted to CRASH by the caller).
fn run_command(world: &World, idx: usize, opt: &Options, count: u32) -> Map<String, Value> {
    let mut j = header(&world.commands()[idx], idx);
    let t0 = Instant::now();
    match execute_command(world, idx, opt) {
        Ok(sol) => {
            j.insert("status".into(), json!(if sol.sat { "SAT" } else { "UNSAT" }));
            j.insert("error".into(), Value::Null);
            j.insert("temporal".into(), json!(sol.temporal));
            j.insert("min_trace".into(), json!(sol.min_trace));
            j.insert("max_trace".into(), json!(sol.max_trace));
            j.insert("translate_ms".into(), json!(sol.translate_ms));
            j.insert("solve_ms".into(), json!(sol.solve_ms));
            j.insert("total_ms".into(), json!(ms(t0)));
            j.insert(
                "stats".into(),
                json!({"primary_vars": sol.stats.primary_vars, "vars": sol.stats.vars, "clauses": sol.stats.clauses}),
            );
            if sol.sat && opt.want_instance {
                if let Some(i) = sol.instance() {
                    j.insert("instance".into(), instance_json(&i));
                }
            }
            if count > 0 {
                let c0 = Instant::now();
                match alloy_translate::count_solutions(world, idx, opt, count) {
                    Ok((n, capped)) => {
                        j.insert("count".into(), json!(n));
                        j.insert("count_capped".into(), json!(capped));
                        j.insert("count_ms".into(), json!(ms(c0)));
                    }
                    Err(e) => {
                        j.insert("count_error".into(), err_json(&e));
                    }
                }
            }
        }
        Err(e) => {
            let st = if e.kind == alloy_core::ErrorKind::Unsupported { "UNSUPPORTED" } else { "ERROR" };
            j.insert("status".into(), json!(st));
            j.insert("error".into(), err_json(&e));
            j.insert("total_ms".into(), json!(ms(t0)));
        }
    }
    j
}

fn main() {
    let a = parse_args();
    let mut doc = Map::new();
    doc.insert("schema".into(), json!(1));
    doc.insert("tool".into(), json!(concat!("alloy-rs-", env!("CARGO_PKG_VERSION"))));
    doc.insert("file".into(), json!(a.display));

    let p0 = Instant::now();
    let parsed = {
        let f = a.file.clone();
        std::thread::Builder::new()
            .stack_size(SOLVER_STACK)
            .spawn(move || alloy_core::parse_everything_from_file(&f))
            .expect("spawn")
            .join()
    };
    let world = match parsed {
        Ok(Ok(w)) => Arc::new(w),
        Ok(Err(e)) => {
            doc.insert("status".into(), json!(e.status_str()));
            doc.insert("error".into(), err_json(&e));
            doc.insert("parse_ms".into(), json!(ms(p0)));
            doc.insert("commands".into(), json!([]));
            println!("{}", Value::Object(doc));
            return;
        }
        Err(panic) => {
            doc.insert("status".into(), json!("crash"));
            doc.insert("error".into(), json!({"kind": "crash", "msg": panic_msg(&panic)}));
            doc.insert("commands".into(), json!([]));
            println!("{}", Value::Object(doc));
            std::process::exit(101);
        }
    };
    // Java reports type errors of the root module at load time, before any command runs.
    if a.no_solve {
        let w = world.clone();
        let r = std::thread::Builder::new()
            .stack_size(SOLVER_STACK)
            .spawn(move || alloy_translate::check_types(&w))
            .expect("spawn")
            .join();
        if let Ok(Err(e)) = r {
            doc.insert("status".into(), json!(e.status_str()));
            doc.insert("error".into(), err_json(&e));
            doc.insert("parse_ms".into(), json!(ms(p0)));
            doc.insert("commands".into(), json!([]));
            println!("{}", Value::Object(doc));
            return;
        }
    }
    doc.insert("status".into(), json!("ok"));
    doc.insert("error".into(), Value::Null);
    doc.insert("parse_ms".into(), json!(ms(p0)));
    doc.insert("command_count".into(), json!(world.commands().len()));

    let mut out_cmds: Vec<Value> = Vec::new();
    let mut exit = 0;
    let indices: Vec<usize> = match a.command {
        Some(i) if i < world.commands().len() => vec![i],
        Some(_) => vec![],
        None => (0..world.commands().len()).collect(),
    };
    if a.no_solve {
        for (i, c) in world.commands().iter().enumerate() {
            let mut h = header(c, i);
            h.insert("status".into(), json!("NOT_RUN"));
            out_cmds.push(Value::Object(h));
        }
    } else {
        for idx in indices {
            let (tx, rx) = mpsc::channel();
            let w = world.clone();
            let opt = a.opt.clone();
            let count = a.count;
            std::thread::Builder::new()
                .stack_size(SOLVER_STACK)
                .spawn(move || {
                    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| run_command(&w, idx, &opt, count)));
                    let _ = tx.send(r);
                })
                .expect("spawn");
            match rx.recv_timeout(Duration::from_millis(a.timeout_ms)) {
                Ok(Ok(m)) => out_cmds.push(Value::Object(m)),
                Ok(Err(panic)) => {
                    let mut h = header(&world.commands()[idx], idx);
                    h.insert("status".into(), json!("CRASH"));
                    h.insert("error".into(), json!({"kind": "crash", "msg": panic_msg(&panic)}));
                    out_cmds.push(Value::Object(h));
                }
                Err(_) => {
                    let mut h = header(&world.commands()[idx], idx);
                    h.insert("status".into(), json!("TIMEOUT"));
                    h.insert("timeout_ms".into(), json!(a.timeout_ms));
                    out_cmds.push(Value::Object(h));
                    exit = 3;
                    break;
                }
            }
        }
    }
    doc.insert("commands".into(), Value::Array(out_cmds));
    println!("{}", Value::Object(doc));
    use std::io::Write;
    let _ = std::io::stdout().flush();
    std::process::exit(exit);
}

fn panic_msg(p: &Box<dyn std::any::Any + Send>) -> String {
    if let Some(s) = p.downcast_ref::<&str>() {
        s.to_string()
    } else if let Some(s) = p.downcast_ref::<String>() {
        s.clone()
    } else {
        "panic".into()
    }
}
