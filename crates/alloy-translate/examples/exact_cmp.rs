//! Dev tool: builds the exact Kodkod problem of commands and compares it with Java's dumps.
//! stdin lines: `<model.als>\t<command index>\t<dump prefix>` (prefix.kk / prefix.cnf from tools/exact/trace_all.py)
//! cargo run --release -p alloy-translate --example exact_cmp < list.txt

use pardinus::cnf::CnfSink;
use std::io::{BufRead, BufReader};

#[derive(Default)]
struct Rec {
    calls: Vec<String>,
    vars: i32,
}
impl CnfSink for Rec {
    fn num_vars(&self) -> i32 {
        self.vars
    }
    fn add_variables(&mut self, n: i32) {
        self.vars += n;
        self.calls.push(format!("v {n}"));
    }
    fn add_clause(&mut self, lits: &[i32]) {
        let mut s = String::from("c");
        for l in lits {
            s.push(' ');
            s.push_str(&l.to_string());
        }
        self.calls.push(s);
    }
}

fn java_calls(path: &str) -> Vec<String> {
    let mut out = Vec::new();
    if let Ok(f) = std::fs::File::open(path) {
        for line in BufReader::new(f).lines() {
            let line = line.unwrap();
            if line == "begin" {
                continue;
            }
            if line == "end" || line.starts_with("s ") {
                break;
            }
            out.push(line);
        }
    }
    out
}

fn java_blocks(path: &str) -> Vec<Vec<String>> {
    let mut out = Vec::new();
    let mut cur: Option<Vec<String>> = None;
    if let Ok(f) = std::fs::File::open(path) {
        for line in BufReader::new(f).lines() {
            let line = line.unwrap();
            if line == "begin" {
                cur = Some(Vec::new());
            } else if line.starts_with("s ") || line == "end" {
                if let Some(c) = cur.take() {
                    out.push(c);
                }
            } else if let Some(c) = &mut cur {
                c.push(line);
            }
        }
    }
    out
}

fn run(model: &str, idx: usize, prefix: &str) -> Result<(bool, bool, String), String> {
    let world = alloy_core::parse_everything_from_file(std::path::Path::new(model))
        .map_err(|e| e.to_string())?;
    let m = alloy_core::sema::build(&world.modules).map_err(|e| e.to_string())?;
    let (mut p, _info) =
        alloy_translate::exact::build(&world, &m, idx).map_err(|e| format!("{}", e))?;
    let text = pardinus::kkwrite::write_kk(&p);
    let want = std::fs::read_to_string(format!("{prefix}.kk")).map_err(|e| e.to_string())?;
    let kk_same = text == want;
    let mut detail = String::new();
    if !kk_same {
        let (a, b): (Vec<&str>, Vec<&str>) = (text.lines().collect(), want.lines().collect());
        let i = a
            .iter()
            .zip(b.iter())
            .position(|(x, y)| x != y)
            .unwrap_or(a.len().min(b.len()));
        detail = format!(
            "kk line {}: rust={:?} java={:?}",
            i + 1,
            a.get(i).map(|s| &s[..s.len().min(160)]),
            b.get(i).map(|s| &s[..s.len().min(160)])
        );
        let _ = std::fs::write(format!("{prefix}.rust.kk"), &text);
    }
    if p.options.temporal {
        // one CNF block per trace length tried
        let logs = alloy_translate::exact::temporal_cnf_log(&world, &m, idx).map_err(|e| e.to_string())?;
        if std::env::var("DUMP_TCNF").is_ok() {
            let mut t = String::new();
            for b in &logs {
                t.push_str("begin\n");
                for l in b {
                    t.push_str(l);
                    t.push('\n');
                }
                t.push_str("end\n");
            }
            let _ = std::fs::write(format!("{prefix}.rust.cnf"), t);
        }
        let want = java_blocks(&format!("{prefix}.cnf"));
        let same = logs == want;
        let mut d = detail;
        if !same {
            let k = logs.iter().zip(want.iter()).position(|(a, b)| a != b).unwrap_or(logs.len().min(want.len()));
            let line = match (logs.get(k), want.get(k)) {
                (Some(a), Some(b)) => {
                    let i = a.iter().zip(b.iter()).position(|(x, y)| x != y).unwrap_or(a.len().min(b.len()));
                    format!("block {k} line {i}: rust={:?} java={:?} (lens {} {})", a.get(i), b.get(i), a.len(), b.len())
                }
                _ => format!("blocks rust={} java={}", logs.len(), want.len()),
            };
            d = format!("{d} [{line}]");
        }
        return Ok((kk_same, same, d));
    }
    let mut rec = Rec::default();
    if let Err(e) = pardinus::translator::translate(&mut p, &mut rec) {
        return Ok((kk_same, false, format!("{detail} [translate: {e}]")));
    }
    let cnf_same = rec.calls == java_calls(&format!("{prefix}.cnf"));
    Ok((kk_same, cnf_same, detail))
}

fn main() {
    let stdin = std::io::stdin();
    let (mut kk, mut cnf, mut n, mut err) = (0, 0, 0, 0);
    for line in stdin.lock().lines() {
        let line = line.unwrap();
        let p: Vec<&str> = line.split('\t').collect();
        if p.len() != 3 {
            continue;
        }
        let (model, idx, prefix) = (
            p[0].to_string(),
            p[1].parse::<usize>().unwrap(),
            p[2].to_string(),
        );
        n += 1;
        let tag = prefix
            .rsplit(['/', '\\'])
            .next()
            .unwrap_or(&prefix)
            .to_string();
        let res = std::thread::Builder::new()
            .stack_size(1 << 30)
            .spawn(move || run(&model, idx, &prefix))
            .unwrap()
            .join();
        match res {
            Ok(Ok((a, b, d))) => {
                kk += a as i32;
                cnf += b as i32;
                if !a || !b {
                    println!(
                        "{} {} {tag} {d}",
                        if a { "KK " } else { "kk!" },
                        if b { "CNF" } else { "cnf!" }
                    );
                }
            }
            Ok(Err(e)) => {
                err += 1;
                println!("ERR {tag}: {}", &e[..e.len().min(2000)]);
            }
            Err(_) => {
                err += 1;
                println!("PANIC {tag}");
            }
        }
    }
    println!("commands={n} kk_identical={kk} cnf_identical={cnf} errors={err}");
}
