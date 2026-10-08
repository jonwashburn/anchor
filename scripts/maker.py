#!/usr/bin/env python3
"""The residue pass: obligations the search left open, for a model agent to try once each.

    maker.py tasks  <census.jsonl> <out.jsonl> [--only NAMES_FILE] [--max N] [--sample N]
                    [--refute]
    maker.py check  <tasks.jsonl> <answers dir> <imports> <out dir> --lean-path PATH
                    [--tsv FILE] [--jobs N]
    maker.py supply <out dir>/accepted.txt <answers dir> <supplied.jsonl>

`tasks` reads census reports and writes one task per open obligation: vacuity for a statement
with neither a model nor a proof of vacuity, and hypothesis k for a hypothesis with neither a
counterexample model nor a proof of removability. A task shows the statement and the two
goals the obligation can be settled by, with the theorem name each must be stated under. It
carries no label: the agent decides which side holds. With `--refute`, for corpora whose
statements are proved by `sorry`, a hypothesis task also offers `X.anchorFalse`: when the
statement is false, neither of the two obligations holds and the negation is the answer.

`check` compiles each answer (`<answers dir>/<task id>.lean`, the theorem only) in a file that
imports `Anchor` and the statement's module, adds the extraction with `anchor_spec`, and
prints the answer's axioms. An answer is accepted when Lean exits 0, the theorem has the name
the task asked for, its type is the obligation (an `example` restates it at the task's type),
and its axioms are among propext, Classical.choice and Quot.sound. One
answer per task is read; there is no second attempt. With `--tsv` (name, module, as the census
reads it) each answer also imports its own statement's module, so tasks from different files of
one corpus are checked in one call; `--jobs` checks that many answers at once.

`supply` writes the accepted answers, one JSON line per statement holding its `anchor_spec`
line and its answers, for `census.py --supplied`: a shard carries the blocks of its own
statements ahead of `anchor_census`, so the analysis reads them as supplied proofs.
"""

import hashlib
import json
import os
import re
import subprocess
import sys

STD = {"propext", "Classical.choice", "Quot.sound"}


def readable(s):
    return re.sub(r"\._@\.[A-Za-z0-9_.'@]*_hyg\.\d+", "", s).replace("✝", "")


def statement_text(r):
    model = " ".join(r.get("model", [])) or "(none)"
    hyps = "\n".join(f"  [{i}] {h['text']}" for i, h in enumerate(r.get("hypotheses", [])))
    return readable(f"model: {model}\nhypotheses:\n{hyps}\nconclusion: {r.get('conclusion', '')}")


def tasks(argv):
    src, out = argv[0], argv[1]
    only = None
    if "--only" in argv:
        only = {ln.strip() for ln in open(argv[argv.index("--only") + 1]) if ln.strip()}
    cap = int(argv[argv.index("--max") + 1]) if "--max" in argv else 0
    refute = "--refute" in argv
    rows = []
    for ln in open(src):
        r = json.loads(ln)
        if "error" in r or not r.get("supported", False):
            continue
        d = r["decl"]
        if only is not None and d not in only:
            continue
        if not r.get("hypotheses"):
            continue
        st = statement_text(r)
        nv, vac = r["nonvacuous"], r["vacuous"]
        if nv["status"] != "proved" and vac["status"] != "proved":
            rows.append({"id": f"{d}::vacuity", "decl": d, "statement": st, "choices": [
                {"theorem": f"{d}.anchorNonvacuous",
                 "type": f"Anchor.Spec.Nonvacuous {d}.anchorSpec",
                 "goal": nv.get("goal", ""), "means": "some model satisfies every hypothesis"},
                {"theorem": f"{d}.anchorVacuous",
                 "type": f"Anchor.Spec.Vacuous {d}.anchorSpec",
                 "goal": vac.get("goal", ""), "means": "no model satisfies the hypotheses"}]})
            continue
        if vac["status"] == "proved" or r["trivial_conclusion"]["status"] == "proved":
            continue
        for k, h in enumerate(r["hypotheses"]):
            if h["load_bearing"]["status"] == "proved" or h["drop"]["status"] == "proved":
                continue
            rows.append({"id": f"{d}::hyp{k}", "decl": d, "statement": st, "choices": [
                {"theorem": f"{d}.anchorLoadBearing_{k}",
                 "type": f"Anchor.Spec.LoadBearing {d}.anchorSpec {k}",
                 "goal": h["load_bearing"].get("goal", ""),
                 "means": f"a model satisfies the other hypotheses and not the conclusion"},
                {"theorem": f"{d}.anchorDrop_{k}",
                 "type": f"Anchor.Spec.Drop {d}.anchorSpec {k}",
                 "goal": h["drop"].get("goal", ""),
                 "means": f"the other hypotheses already give the conclusion"}]})
            if refute:
                rows[-1]["choices"].append(
                    {"theorem": f"{d}.anchorFalse", "type": f"¬ Anchor.Spec.Holds {d}.anchorSpec",
                     "goal": "", "means": "the statement is false: some model satisfies every "
                                          "hypothesis and not the conclusion"})
    for t in rows:
        for ch in t["choices"]:
            ch["goal"] = readable(ch["goal"])
    if "--sample" in argv:
        k = int(argv[argv.index("--sample") + 1])
        rows = sorted(rows, key=lambda t: hashlib.sha256(t["id"].encode()).hexdigest())[:k]
    rows.sort(key=lambda t: t["id"])
    if cap:
        rows = rows[:cap]
    with open(out, "w") as f:
        for t in rows:
            f.write(json.dumps(t, sort_keys=True) + "\n")
    print(f"{len(rows)} tasks written to {out}")


def safe(tid):
    return re.sub(r"[^A-Za-z0-9_.:-]", "_", tid).replace("::", "__")


def check_one(t, answers, imports, outdir, lean, lean_path):
    sid = safe(t["id"])
    ans = os.path.join(answers, sid + ".lean")
    if not os.path.exists(ans):
        return {"id": t["id"], "result": "no answer"}, None
    body = open(ans).read()
    names = [c["theorem"] for c in t["choices"]]
    m = re.search(r"theorem\s+(\S+)", body)
    stated = m.group(1) if m else None
    if stated not in names:
        return {"id": t["id"], "result": f"theorem name {stated} is not one of {names}"}, None
    if re.search(r"\b(sorry|admit)\b|^\s*axiom\b", body, re.M):
        return {"id": t["id"], "result": "answer contains sorry, admit or axiom"}, None
    ty = next(c["type"] for c in t["choices"] if c["theorem"] == stated)
    src = "\n".join(["import Anchor"] + [f"import {i}" for i in imports] +
                    ["", f"anchor_spec {t['decl']}", "", body, "",
                     f"example : {ty} := {stated}", "",
                     f"#print axioms {stated}", ""])
    fn = os.path.join(outdir, sid + ".lean")
    with open(fn, "w") as f:
        f.write(src)
    try:
        p = subprocess.run([lean, fn], capture_output=True, text=True,
                           env=dict(os.environ, LEAN_PATH=lean_path), timeout=900)
        code, log = p.returncode, p.stdout + p.stderr
    except subprocess.TimeoutExpired:
        code, log = None, "wall-clock timeout after 900 s\n"
    with open(fn + ".log", "w") as f:
        f.write(log)
    ax = set()
    mm = re.search(r"depends on axioms: \[([^\]]*)\]", log, re.S)
    if mm:
        ax = {a.strip() for a in mm.group(1).replace("\n", " ").split(",") if a.strip()}
    ok = code == 0 and not re.search(r":\d+:\d+: error", log) and mm is not None and ax <= STD
    why = "accepted" if ok else f"rejected: exit {code}, axioms {sorted(ax)}"
    return ({"id": t["id"], "theorem": stated, "result": why, "axioms": sorted(ax),
             "type": ty},
            f"{t['id']}\t{stated}\t{sid}" if ok else None)


def check(argv):
    tasks_path, answers, imports, outdir = argv[0], argv[1], argv[2].split(), argv[3]
    lean_path = argv[argv.index("--lean-path") + 1]
    jobs = int(argv[argv.index("--jobs") + 1]) if "--jobs" in argv else 1
    module_of = {}
    if "--tsv" in argv:
        for ln in open(argv[argv.index("--tsv") + 1]):
            p = ln.rstrip("\n").split("\t")
            if len(p) >= 2:
                module_of.setdefault(p[0], p[1])
    lean = os.path.expanduser("~/.elan/toolchains/leanprover--lean4---v4.27.0-rc1/bin/lean")
    os.makedirs(outdir, exist_ok=False)
    ts = [json.loads(ln) for ln in open(tasks_path) if ln.strip()]
    from concurrent.futures import ThreadPoolExecutor
    with ThreadPoolExecutor(max_workers=jobs) as ex:
        outs = list(ex.map(lambda t: check_one(
            t, answers, imports + ([module_of[t["decl"]]] if t["decl"] in module_of else []),
            outdir, lean, lean_path), ts))
    results = [r for r, _ in outs]
    accepted = [a for _, a in outs if a]
    with open(os.path.join(outdir, "results.jsonl"), "w") as f:
        for r in results:
            f.write(json.dumps(r, sort_keys=True) + "\n")
    with open(os.path.join(outdir, "accepted.txt"), "w") as f:
        f.write("\n".join(accepted) + ("\n" if accepted else ""))
    print(f"{len(accepted)} of {len(results)} answers accepted")


def supply(argv):
    acc, answers, out = argv[0], argv[1], argv[2]
    blocks = {}
    for ln in open(acc):
        if not ln.strip():
            continue
        tid, thm, sid = ln.rstrip("\n").split("\t")
        d = tid.split("::")[0]
        blocks.setdefault(d, [f"anchor_spec {d}"])
        blocks[d].append(open(os.path.join(answers, sid + ".lean")).read().strip())
    with open(out, "w") as f:
        for d in sorted(blocks):
            f.write(json.dumps({"decl": d, "lean": "\n\n".join(blocks[d])}, sort_keys=True) + "\n")
    n = sum(len(b) - 1 for b in blocks.values())
    print(f"{n} supplied proofs for {len(blocks)} statements")


if __name__ == "__main__":
    cmd = sys.argv[1]
    {"tasks": tasks, "check": check, "supply": supply}[cmd](sys.argv[2:])
