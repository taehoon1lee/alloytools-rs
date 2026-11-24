import argparse
import json
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(r"D:\sw\alloytoolRS")
sys.path.insert(0, str(ROOT / "harness"))
import common  # noqa: E402

TOOLS_XML = ROOT / "tools" / "xml_check"
CLASSES = TOOLS_XML / "classes"
OUT_DIR = TOOLS_XML / "out"
RUST_OUT = OUT_DIR / "rust"
JAVA_OUT = OUT_DIR / "java"
JAVA_SRC = TOOLS_XML / "XmlCheck.java"

REPRESENTATIVE_GUI = [
    ("models/models/systems/hotel4", 0),
    ("models/software-abstractions-book/chapter2/addressBook3d", None),
    ("models/models/logic/philosophers", 1),
    ("extra/examples/temporal/buffer", None),
    ("extra/examples/temporal/leader_events", 1),
]


def resolve_path(p: str) -> Path:
    pp = Path(p)
    return pp if pp.is_absolute() else (ROOT / pp)


def collect_sat_commands():
    corpus = common.load_corpus()
    items = []
    for entry in corpus:
        gpath = common.GOLDEN_DIR / common.golden_name(entry["id"])
        g = common.load_json(gpath)
        if not g or g.get("status") != "ok":
            continue
        als_path = resolve_path(entry["path"])
        for jc in g.get("commands", []):
            if jc.get("status") == "SAT" and jc.get("instance") is not None:
                items.append((entry, als_path, jc))
    return items


def compile_java():
    CLASSES.mkdir(parents=True, exist_ok=True)
    cp = f"{common.JAR}{common.CP_SEP}{CLASSES}"
    r = subprocess.run(
        ["javac", "-cp", cp, "-d", str(CLASSES), str(JAVA_SRC)],
        cwd=str(ROOT),
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    if r.returncode != 0:
        print("JAVAC FAILED:\n", r.stderr)
        sys.exit(1)


def find_gui_targets(items):
    # Match requested representative models (preferring canonical IDs, falling back safely)
    targets = []
    want_keys = [
        ("hotel", lambda cid: cid.endswith("/hotel3") or cid.endswith("/hotel1")),
        ("addressBook", lambda cid: "addressBook" in cid),
        ("philosophers", lambda cid: cid.endswith("/philosophers")),
        ("buffer", lambda cid: cid.endswith("/buffer")),
        ("leader_events", lambda cid: cid.endswith("/leader_events")),
    ]
    for name, pred in want_keys:
        matches = [(e, p, jc) for (e, p, jc) in items if pred(e["id"])]
        if matches:
            e, p, jc = matches[0]
            targets.append((name, e["id"], jc["index"]))
    return targets


def run_xml_batch(rows, viz_tags: set[str], label: str):
    cp = f"{common.JAR}{common.CP_SEP}{CLASSES}"
    payload = "\n".join(
        f"{als}\t{idx}\t{tag}\t{xml_path}\t{1 if tag in viz_tags else 0}"
        for als, idx, tag, xml_path in rows
    ) + "\n"
    t0 = time.perf_counter()
    p = subprocess.run(
        ["java", "-Djava.awt.headless=true", "-cp", cp, "XmlCheck", "--batch"],
        cwd=str(ROOT),
        input=payload,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    wall = time.perf_counter() - t0
    if p.returncode != 0:
        print(f"[{label}] XmlCheck failed rc={p.returncode}\nSTDERR:\n{p.stderr[-1500:]}")
        return False, []
    results = []
    for line in p.stdout.splitlines():
        line = line.strip()
        if line.startswith("{"):
            results.append(json.loads(line))
    ok_cnt = sum(1 for r in results if r.get("ok"))
    read_ok = sum(1 for r in results if r.get("read_ok"))
    viz_ok = sum(1 for r in results if r.get("viz_ok"))
    ho_cnt = sum(1 for r in results if r.get("mode") == "higher_order_sat")
    print(
        f"[{label}] {ok_cnt}/{len(rows)} ok (read_ok={read_ok}, viz_ok={viz_ok}, ho_fallback={ho_cnt}) in {wall:.2f}s"
    )
    failures = [r for r in results if not r.get("ok")]
    for f in failures[:20]:
        print(f"  FAIL {f['tag']}: read={f.get('read_ok')} viz={f.get('viz_ok')} facts={f.get('facts_ok')} cmd={f.get('cmd_ok')} err={f.get('error')}")
    if len(failures) > 20:
        print(f"  ... ({len(failures) - 20} more)")
    return ok_cnt == len(rows) and len(results) == len(rows), results


def dump_java_xmls(items, out_dir: Path):
    out_dir.mkdir(parents=True, exist_ok=True)
    cp = f"{common.JAR}{common.CP_SEP}{CLASSES}"
    rows = []
    out_rows = []
    for entry, als_path, jc in items:
        i = jc["index"]
        tag = f"{entry['id']}#{i}"
        xml_path = out_dir / f"{common.golden_name(entry['id']).replace('.json', '')}__{i}.xml"
        rows.append(f"{als_path}\t{i}\t{tag}\t{xml_path}")
        out_rows.append((als_path, i, tag, xml_path))
    p = subprocess.run(
        ["java", "-Djava.awt.headless=true", "-cp", cp, "XmlCheck", "--dump-java-xml"],
        cwd=str(ROOT),
        input="\n".join(rows) + "\n",
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    if p.returncode != 0:
        print("Java XML dump failed:\n", p.stderr[-1500:])
        sys.exit(1)
    return out_rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--oracle-self-test", action="store_true", help="Also generate Java A4SolutionWriter XMLs and verify them")
    ap.add_argument("--filter", default="", help="Substring filter on model id")
    args = ap.parse_args()

    compile_java()
    items = collect_sat_commands()
    if args.filter:
        items = [(e, p, jc) for (e, p, jc) in items if args.filter in e["id"]]
    else:
        assert len(items) == 215, f"expected 215 SAT commands, got {len(items)}"
    static_cnt = sum(1 for _, _, jc in items if not jc.get("temporal"))
    temp_cnt = sum(1 for _, _, jc in items if jc.get("temporal"))
    print(f"Collected {len(items)} SAT commands (static={static_cnt}, temporal={temp_cnt}).")

    RUST_OUT.mkdir(parents=True, exist_ok=True)
    rust_rows = []
    gen_errors = []
    t0 = time.perf_counter()
    for entry, als_path, jc in items:
        i = jc["index"]
        tag = f"{entry['id']}#{i}"
        xml_path = RUST_OUT / f"{common.golden_name(entry['id']).replace('.json', '')}__{i}.xml"
        jt = float(jc.get("total_ms") or 0) + float(jc.get("count_ms") or 0)
        tmo = int(min(60000, max(5000, 5 * jt + 2000)))
        cmd = [
            str(common.RUST_BIN),
            "exec",
            "--file",
            str(als_path),
            "--display-name",
            entry["id"],
            "--command",
            str(i),
            "--timeout-ms",
            str(tmo),
            "--xml",
            str(xml_path),
        ]
        rc, out, err, _ = common.run_proc(cmd, timeout_s=tmo / 1000.0 + 15.0)
        if rc != 0 or not xml_path.exists() or xml_path.stat().st_size == 0:
            gen_errors.append((tag, rc, (err or out)[-300:]))
        else:
            rust_rows.append((als_path, i, tag, xml_path))

    print(f"[Rust XML gen] {len(rust_rows)}/{len(items)} generated in {time.perf_counter() - t0:.2f}s (errors={len(gen_errors)})")
    for g in gen_errors[:10]:
        print("  GEN ERR:", g)

    gui_targets = find_gui_targets(items)
    viz_tags = {f"{cid}#{idx}" for _, cid, idx in gui_targets}
    print("Representative GUI targets:", [(n, f"{cid}#{idx}") for n, cid, idx in gui_targets])

    ok_rust, res_rust = run_xml_batch(rust_rows, viz_tags, "Rust XML -> Java A4SolutionReader + eval")

    # Verify VizState explicitly succeeded for every representative GUI target
    by_tag = {r["tag"]: r for r in res_rust}
    for name, cid, idx in gui_targets:
        tag = f"{cid}#{idx}"
        r = by_tag.get(tag)
        if not r or not r.get("viz_state_ok"):
            print(f"  GUI VIZ FAILED for {name} ({tag}): {r}")
            ok_rust = False
        else:
            print(f"  GUI VIZ OK ({name}): {tag}")

    ok_java = True
    if args.oracle_self_test:
        java_rows = dump_java_xmls(items, JAVA_OUT)
        ok_java, _ = run_xml_batch(java_rows, viz_tags, "Java XML self-test -> A4SolutionReader + eval")

    if gen_errors or not ok_rust or not ok_java:
        sys.exit(1)
    print(f"SUCCESS: {len(rust_rows)}/{len(items)} Rust XML checks passed!")


if __name__ == "__main__":
    main()
