"""Compare the first instance of the Rust exact pipeline with Java's (harness goldens) for every SAT command.
With --all, every scored command is run and UNSAT/ERROR verdicts must agree as well (so the CLI never needs its
fallback instance).
usage: python tools/exact/cmp_inst.py [--filter S] [--show N] [--all] [-j N]"""
import argparse, concurrent.futures, json, os, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, "harness"))
from common import load_corpus  # noqa

ap = argparse.ArgumentParser()
ap.add_argument("--filter")
ap.add_argument("--show", type=int, default=3)
ap.add_argument("--all", action="store_true")
ap.add_argument("-j", type=int, default=1)
a = ap.parse_args()
corpus = {e["id"]: e["path"] for e in load_corpus()}
want = {}
lines = []
for cid, path in sorted(corpus.items()):
    if a.filter and a.filter not in cid:
        continue
    gp = os.path.join(ROOT, "harness", "golden", cid.replace("/", "__") + ".json")
    if not os.path.exists(gp):
        continue
    g = json.load(open(gp, encoding="utf-8"))
    for c in g.get("commands", []):
        tag = f"{cid}#{c['index']}"
        if c.get("status") == "SAT" and c.get("instance"):
            want[tag] = c["instance"]
        elif a.all and c.get("status") in ("UNSAT", "ERROR"):
            want[tag] = c["status"]
        else:
            continue
        lines.append(f"{path}\t{c['index']}\t{tag}")
exe = os.path.join(ROOT, "target", "release", "examples", "exact_inst" + (".exe" if os.name == "nt" else ""))


def run(chunk):
    return subprocess.run([exe], input="\n".join(chunk) + "\n", capture_output=True, text=True, encoding="utf-8",
                          errors="replace", cwd=ROOT)


chunks = [lines[i::a.j] for i in range(max(1, a.j))]
with concurrent.futures.ThreadPoolExecutor(len(chunks)) as ex:
    procs = list(ex.map(run, chunks))
stdout = "".join(p.stdout for p in procs)
stderr = "".join(p.stderr for p in procs)
same = diff = err = 0
shown = 0
seen = set()
for line in stdout.splitlines():
    r = json.loads(line)
    tag = r["tag"]
    seen.add(tag)
    w = want[tag]
    if isinstance(w, str):
        ok = (w == "UNSAT" and r.get("sat") is False) or (w == "ERROR" and "error" in r)
        if ok:
            same += 1
        else:
            diff += 1
            print(f"VERDICT {tag}: java={w} rust={r.get('sat', str(r.get('error', ''))[:160])}")
        continue
    if "error" in r:
        err += 1
        print(f"ERR  {tag}: {r['error'][:160]}")
        continue
    got = r.get("instance")
    if got == w:
        same += 1
    else:
        diff += 1
        print(f"DIFF {tag} sat={r['sat']} ms={r['ms']}")
        if shown < a.show and got:
            shown += 1
            ws, gs = w["states"][0], got["states"][0]
            for k in sorted(set(ws) | set(gs)):
                if ws.get(k) != gs.get(k):
                    print(f"     {k}: java={json.dumps(ws.get(k))[:150]} rust={json.dumps(gs.get(k))[:150]}")
missing = [t for t in want if t not in seen]
for t in missing:
    print(f"MISSING {t}")
print(f"commands={len(want)} identical={same} different={diff} errors={err} missing={len(missing)}")
if stderr.strip():
    print(stderr[-1500:])
