"""Compare the first instance of the Rust exact pipeline with Java's (harness goldens) for every SAT command.
usage: python tools/exact/cmp_inst.py [--filter S] [--show N]"""
import argparse, json, os, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, "harness"))
from common import load_corpus  # noqa

ap = argparse.ArgumentParser()
ap.add_argument("--filter")
ap.add_argument("--show", type=int, default=3)
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
        if c.get("status") == "SAT" and c.get("instance"):
            tag = f"{cid}#{c['index']}"
            want[tag] = c["instance"]
            lines.append(f"{path}\t{c['index']}\t{tag}")
exe = os.path.join(ROOT, "target", "release", "examples", "exact_inst" + (".exe" if os.name == "nt" else ""))
p = subprocess.run([exe], input="\n".join(lines) + "\n", capture_output=True, text=True, encoding="utf-8", errors="replace", cwd=ROOT)
same = diff = err = 0
shown = 0
for line in p.stdout.splitlines():
    r = json.loads(line)
    tag = r["tag"]
    if "error" in r:
        err += 1
        print(f"ERR  {tag}: {r['error'][:160]}")
        continue
    got = r.get("instance")
    if got == want[tag]:
        same += 1
    else:
        diff += 1
        print(f"DIFF {tag} sat={r['sat']} ms={r['ms']}")
        if shown < a.show and got:
            shown += 1
            ws, gs = want[tag]["states"][0], got["states"][0]
            for k in sorted(set(ws) | set(gs)):
                if ws.get(k) != gs.get(k):
                    print(f"     {k}: java={json.dumps(ws.get(k))[:150]} rust={json.dumps(gs.get(k))[:150]}")
print(f"instances={len(want)} identical={same} different={diff} errors={err}")
if p.stderr.strip():
    print(p.stderr[-1500:])
