//! Standalone instance verifier driver for the independent AST evaluator.
//! Reads stdin lines: `<model.als>\t<command_index>\t<tag>\t<instance_json>`
//! Outputs one JSON line per input:
//! `{"tag":...,"ok":bool,"verify_ms":f64,"kind":...,"error":...}`

use std::collections::{BTreeMap, HashMap};
use std::io::{BufRead, BufWriter, Write};
use std::path::Path;
use std::time::Instant;

use alloy_core::sema::{self, Model};
use alloy_core::World;
use alloy_translate::{verify_instance, Instance, Options};

fn parse_instance_json(raw: &str) -> Result<Instance, String> {
    let v: serde_json::Value =
        serde_json::from_str(raw).map_err(|e| format!("invalid instance json: {e}"))?;
    let obj = v
        .as_object()
        .ok_or_else(|| "instance json must be an object".to_string())?;
    let trace_length = obj
        .get("trace_length")
        .and_then(|x| x.as_i64())
        .map(|x| x as i32)
        .ok_or_else(|| "missing integer trace_length".to_string())?;
    let loop_state = obj
        .get("loop")
        .and_then(|x| x.as_i64())
        .map(|x| x as i32)
        .unwrap_or(-1);
    let states_arr = obj
        .get("states")
        .and_then(|x| x.as_array())
        .ok_or_else(|| "missing array states".to_string())?;

    let mut states = Vec::with_capacity(states_arr.len());
    for (si, st) in states_arr.iter().enumerate() {
        let st_obj = st
            .as_object()
            .ok_or_else(|| format!("state {si} must be an object"))?;
        let mut map = BTreeMap::new();
        for (label, tuples_val) in st_obj {
            let tuples_arr = tuples_val
                .as_array()
                .ok_or_else(|| format!("state {si} label {label} must be an array"))?;
            let mut tuples = Vec::with_capacity(tuples_arr.len());
            for tup_val in tuples_arr {
                let tup_arr = tup_val
                    .as_array()
                    .ok_or_else(|| format!("state {si} label {label} tuple must be an array"))?;
                let mut atoms = Vec::with_capacity(tup_arr.len());
                for a in tup_arr {
                    let s = a
                        .as_str()
                        .ok_or_else(|| format!("state {si} label {label} atom must be a string"))?;
                    atoms.push(s.to_string());
                }
                tuples.push(atoms);
            }
            map.insert(label.clone(), tuples);
        }
        states.push(map);
    }

    Ok(Instance {
        trace_length,
        loop_state,
        states,
    })
}

fn json_str(s: &str) -> String {
    serde_json::to_string(s).unwrap_or_else(|_| "\"\"".to_string())
}

fn main_loop() {
    let stdin = std::io::stdin();
    let stdout = std::io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut cache: HashMap<String, Result<(World, Model), String>> = HashMap::new();
    let opt = Options::default();

    for line in stdin.lock().lines() {
        let line = match line {
            Ok(l) => l,
            Err(e) => {
                eprintln!("stdin read error: {e}");
                break;
            }
        };
        let trimmed = line.trim_end_matches(&['\r', '\n'][..]);
        if trimmed.is_empty() {
            continue;
        }
        let mut parts = trimmed.splitn(4, '\t');
        let Some(als_path) = parts.next() else { continue };
        let Some(cmd_str) = parts.next() else { continue };
        let Some(tag) = parts.next() else { continue };
        let Some(inst_json) = parts.next() else {
            let _ = writeln!(
                out,
                "{{\"tag\":{},\"ok\":false,\"verify_ms\":0.0,\"kind\":\"InputError\",\"error\":\"missing 4th tab field\"}}",
                json_str(tag)
            );
            continue;
        };

        let cmd_idx: usize = match cmd_str.trim().parse() {
            Ok(i) => i,
            Err(e) => {
                let _ = writeln!(
                    out,
                    "{{\"tag\":{},\"ok\":false,\"verify_ms\":0.0,\"kind\":\"InputError\",\"error\":{}}}",
                    json_str(tag),
                    json_str(&format!("bad command index: {e}"))
                );
                continue;
            }
        };

        let inst = match parse_instance_json(inst_json) {
            Ok(i) => i,
            Err(e) => {
                let _ = writeln!(
                    out,
                    "{{\"tag\":{},\"ok\":false,\"verify_ms\":0.0,\"kind\":\"InputError\",\"error\":{}}}",
                    json_str(tag),
                    json_str(&e)
                );
                continue;
            }
        };

        let cached = cache.entry(als_path.to_string()).or_insert_with(|| {
            let world = alloy_core::parse_everything_from_file(Path::new(als_path))
                .map_err(|e| format!("parse error: {e}"))?;
            let model = sema::build(&world.modules).map_err(|e| format!("sema error: {e}"))?;
            Ok((world, model))
        });

        let (_world, model) = match cached {
            Ok(pair) => pair,
            Err(e) => {
                let _ = writeln!(
                    out,
                    "{{\"tag\":{},\"ok\":false,\"verify_ms\":0.0,\"kind\":\"ModelError\",\"error\":{}}}",
                    json_str(tag),
                    json_str(e)
                );
                continue;
            }
        };

        let t0 = Instant::now();
        let res = verify_instance(model, cmd_idx, &inst, &opt);
        let verify_ms = t0.elapsed().as_secs_f64() * 1000.0;

        match res {
            Ok(()) => {
                let _ = writeln!(
                    out,
                    "{{\"tag\":{},\"ok\":true,\"verify_ms\":{verify_ms:.3}}}",
                    json_str(tag)
                );
            }
            Err(e) => {
                let _ = writeln!(
                    out,
                    "{{\"tag\":{},\"ok\":false,\"verify_ms\":{verify_ms:.3},\"kind\":{},\"error\":{}}}",
                    json_str(tag),
                    json_str(&format!("{:?}", e.kind)),
                    json_str(&e.to_string())
                );
            }
        }
        let _ = out.flush();
    }
}

fn main() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(main_loop)
        .expect("spawn eval_verify worker thread")
        .join()
        .expect("eval_verify worker thread panicked");
}
