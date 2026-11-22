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
    let mut rec = Rec::default();
    pardinus::translator::translate(&mut p, &mut rec)?;
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
                if !b {
                    println!(
                        "{} {} {tag} {d}",
                        if a { "KK " } else { "kk!" },
                        if b { "CNF" } else { "cnf!" }
                    );
                }
            }
            Ok(Err(e)) => {
                err += 1;
                println!("ERR {tag}: {}", &e[..e.len().min(200)]);
            }
            Err(_) => {
                err += 1;
                println!("PANIC {tag}");
            }
        }
    }
    println!("commands={n} kk_identical={kk} cnf_identical={cnf} errors={err}");
}
