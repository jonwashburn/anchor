#!/usr/bin/env python3
"""Turn census runs into the census report: counts, findings with their proofs, and checks.

    census_report.py --run NAME=PATH/NAME.jsonl [--run ...] [--repeat NAME=PATH/NAME.jsonl]
                     [--labels AnchorTest/planted_labels.json] --html OUT.html --json OUT.json

Each `--run` is the `NAME.jsonl` a census run wrote; its `NAME.summary.json` beside it supplies
timeouts and wall time. `NAME=first.jsonl+second.jsonl` reads a corpus finished by a second run
after `census_collect.py` collected a stopped first run; no statement may appear in both. A `--repeat` is a second run of the same corpus into a fresh directory;
the report states whether the two are byte-identical, and otherwise whether every differing line
is an error line that differs only in the elapsed seconds its message states. With `--labels`, planted statements found
inside the runs are judged exactly as `p1_check.py` judges them, and kept out of the corpus counts.

A finding is reported only when the report names the declaration that proves it and lists that
declaration's axioms, all among propext, Classical.choice and Quot.sound. The kernel checked
each such declaration when the census added it. A finding whose proof is not listed is counted
under "unchecked" and makes the report exit 1. A finding whose proof rests on another axiom
(`Lean.ofReduceBool`, from a `native_decide` in the library) is listed under "nonstandard",
and the statement's class is computed as if that obligation were open.

Removable hypotheses are split by a stated text rule. A hypothesis that reads as a side
condition (`≠ 0`, `0 <`, `≤`, `Nonempty`, `Summable`, ...) on a conclusion that uses an
operation with a conventional value outside its domain (`/`, `⁻¹`, `log`, `√`, `deriv`, `∫`,
`tsum`, `sSup`, `Nat.card`, `finrank`, truncated `-`, ...) is classed as a junk-value
convention: Mathlib often keeps such hypotheses on purpose, so the statement reads as the
mathematics does. Every other removable hypothesis is listed as removable. Neither class is
called a bug; the rule is a reading aid, and the proofs are what the report vouches for.
"""

import argparse
import collections
import hashlib
import html
import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from p1_check import judge  # noqa: E402

STD_ORDER = ["propext", "Classical.choice", "Quot.sound"]
STD = set(STD_ORDER)

JUNK_OPS = ["/", "⁻¹", "log", "√", "sqrt", "deriv", "∫", "∑'", "tsum", "sSup", "sInf", "⨆",
            "⨅", "iSup", "iInf", "choose", "toNat", "pred", "rpow", "arcsin", "arccos", "%",
            " - ", "Nat.card", "finrank", "rank", "limUnder", "Nat.find", "orderOf",
            "natDegree", "degree", "leadingCoeff"]
SIDE_CONDITIONS = ["≠ 0", "0 <", "0 ≤", " < ", " ≤ ", "≠", "Nonempty", "Finite",
                   "FiniteDimensional", "IsUnit", "Summable", "Integrable", "Differentiable",
                   "HasDeriv", "Continuous", "Bounded", "Measurable", "NeZero", "Invertible"]


def proof_axioms(r, name):
    for a in r.get("axioms", []):
        if a["decl"] == name:
            return set(a["axioms"])
    return None


def settled(r, outcome, name):
    """An obligation counts as settled only when its proof is listed with standard axioms."""
    if (outcome or {}).get("status") != "proved":
        return False
    ax = proof_axioms(r, name)
    return ax is not None and ax <= STD


def classify(r):
    """The statement's class, recomputed from the obligations whose proofs are standard.

    A proof resting on `Lean.ofReduceBool` (a `native_decide` somewhere in its closure) leaves
    its obligation open here, whatever verdict the run printed."""
    if "error" in r:
        return "error"
    v = r.get("verdict", "")
    for key, prefix in [("unsupported", "UNSUPPORTED"), ("no_hypotheses", "NO HYPOTHESIS TO TEST")]:
        if v.startswith(prefix):
            return key
    if not v:
        return "other"
    d = r["decl"].split(" (again)")[0]
    hyps = r.get("hypotheses", [])
    if settled(r, r.get("vacuous"), f"{d}.anchorVacuous"):
        return "contradiction" if r.get("conclusion", "").strip() == "False" else "vacuous"
    drops = [k for k, h in enumerate(hyps) if settled(r, h.get("drop"), f"{d}.anchorDrop_{k}")]
    if not settled(r, r.get("nonvacuous"), f"{d}.anchorNonvacuous"):
        return "uncertified_removable" if drops else "uncertified_no_model"
    if settled(r, r.get("trivial_conclusion"), f"{d}.anchorTrivial"):
        return "trivial"
    lbs = [k for k, h in enumerate(hyps)
           if settled(r, h.get("load_bearing"), f"{d}.anchorLoadBearing_{k}")]
    if hyps and len(lbs) == len(hyps):
        return "certified" if v.startswith("CERTIFIED") else "statement_only"
    return "decorative" if drops else "uncertified_open"


def findings(r):
    """(kind, detail, method, proof name, axioms or None) for each finding in one report."""
    d = r["decl"].split(" (again)")[0]
    out = []
    v = r.get("verdict", "")
    if v.startswith("VACUOUS"):
        n = f"{d}.anchorVacuous"
        out.append(("vacuous", "no model satisfies all the hypotheses",
                    r.get("vacuous", {}).get("method", ""), n, proof_axioms(r, n)))
    if v.startswith("TRIVIAL CONCLUSION"):
        n = f"{d}.anchorTrivial"
        out.append(("trivial", "the conclusion holds without any hypothesis",
                    r.get("trivial_conclusion", {}).get("method", ""), n, proof_axioms(r, n)))
    for k, h in enumerate(r.get("hypotheses", [])):
        if h.get("drop", {}).get("status") == "proved":
            n = f"{d}.anchorDrop_{k}"
            out.append(("removable", f"[{k}] {h['text']}", h["drop"].get("method", ""), n,
                        proof_axioms(r, n)))
    return out


def junk(r, hyp_text):
    concl = r.get("conclusion", "")
    return any(t in concl for t in JUNK_OPS) and any(t in hyp_text for t in SIDE_CONDITIONS)


def sha(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        h.update(f.read())
    return h.hexdigest()


def load(path, seen=None):
    """Report lines of one file. A name reported twice in one run (a corpus that reuses a name
    in two modules) is keyed `NAME (again)` from its second report on, as census.py keys it;
    pass one `seen` set for all the parts of a run."""
    rows, seen = [], set() if seen is None else seen
    with open(path, encoding="utf-8") as f:
        for ln in f:
            ln = ln.strip()
            if ln:
                r = json.loads(ln)
                if "decl" in r:
                    while r["decl"] in seen:
                        r["decl"] += " (again)"
                    seen.add(r["decl"])
                rows.append(r)
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--run", action="append", default=[])
    ap.add_argument("--repeat", action="append", default=[])
    ap.add_argument("--residue", action="append", default=[],
                    help="NAME=PATH: second-pass reports (with supplied proofs) that replace "
                         "the first-pass reports of the same statements")
    ap.add_argument("--maker", action="append", default=[],
                    help="NAME=results.jsonl[+...]: maker.py check results for the corpus")
    ap.add_argument("--maker-model", action="append", default=[],
                    help="NAME=TEXT: the model the corpus's maker agents ran on")
    ap.add_argument("--refuted", action="append", default=[],
                    help="NAME=results.jsonl[+...]: maker.py check results whose accepted "
                         "theorems have type ¬ Anchor.Spec.Holds X.anchorSpec")
    ap.add_argument("--subset", action="append", default=[],
                    help="NAME=RUN:NAMES_FILE: the statements of run RUN named in the file, "
                         "reported again as their own corpus (counted inside RUN too)")
    ap.add_argument("--expect", action="append", default=[],
                    help="NAME=FILE[+...]: the run's input tables (name in the first tab "
                         "column, one row per statement); every name must have as many reports "
                         "as rows")
    ap.add_argument("--labels")
    ap.add_argument("--commit", default="", help="commit of the Anchor code that ran")
    ap.add_argument("--lead", help="HTML fragment placed under the title")
    ap.add_argument("--html", required=True)
    ap.add_argument("--json", required=True)
    a = ap.parse_args()
    if not a.run:
        print("no runs given")
        return 2
    labels = json.load(open(a.labels, encoding="utf-8")) if a.labels else []
    by_label = {l["name"]: l for l in labels}
    repeats = dict(x.split("=", 1) for x in a.repeat)
    residues = dict(x.split("=", 1) for x in a.residue)
    makers = dict(x.split("=", 1) for x in a.maker)
    refuted = dict(x.split("=", 1) for x in a.refuted)
    maker_model = dict(x.split("=", 1) for x in a.maker_model)
    expects = dict(x.split("=", 1) for x in a.expect)
    result = {"corpora": {}, "planted": None, "commit": a.commit,
              "lead": open(a.lead, encoding="utf-8").read() if a.lead else ""}
    planted_seen, loaded, unfinished, reused = {}, {}, {}, {}

    def entry(name, rows, summ, path, paths, replaced, subset_of=None, subset_names=None):
        corpus = [r for r in rows if r["decl"] not in by_label]
        counts = collections.Counter(classify(r) for r in corpus)
        own_nonstandard = 0
        for r in corpus:
            if classify(r) == "certified":
                ax = proof_axioms(r, r["decl"].split(" (again)")[0] + ".anchorCertificate")
                own_nonstandard += ax is not None and not ax <= STD
        found, nonstandard, unchecked = [], [], []
        for r in corpus:
            for kind, detail, method, pname, ax in findings(r):
                item = {"decl": r["decl"], "kind": kind, "detail": detail, "method": method,
                        "proof": pname, "axioms": sorted(ax) if ax is not None else None,
                        "conclusion": r.get("conclusion", "")}
                if kind == "removable":
                    item["junk_value"] = junk(r, detail)
                if kind == "vacuous":
                    item["intended"] = r.get("conclusion", "").strip() == "False"
                if ax is None:
                    unchecked.append(item)
                elif not ax <= STD:
                    nonstandard.append(item)
                else:
                    found.append(item)
        premises = sum(1 for r in corpus if r.get("premises"))
        rep = None
        if name in repeats and subset_of is None:
            first, second = open(paths[0]).read().splitlines(), \
                open(repeats[name]).read().splitlines()
            diff = [(x, y) for x, y in zip(first, second) if x != y]
            clock = [p for p in diff if all(
                "error" in json.loads(z) and "decl" in json.loads(z) for z in p) and
                re.sub(r"\d+ s\b", "N s", p[0]) == re.sub(r"\d+ s\b", "N s", p[1])]
            rep = {"path": repeats[name], "identical": sha(paths[0]) == sha(repeats[name]),
                   "sha256": sha(paths[0]), "sha256_repeat": sha(repeats[name]),
                   "lines": [len(first), len(second)], "differing": len(diff),
                   "differing_elapsed_only": len(clock),
                   "examples": [list(p) for p in diff[:3]]}
        result["corpora"][name] = {
            "path": path, "sha256": "+".join(sha(p) for p in paths), "statements": len(corpus),
            "counts": dict(sorted(counts.items())), "with_premises": premises,
            "timeouts": summ.get("timeouts", []), "wall_s": summ.get("wall_s"),
            "attempt_heartbeats": summ.get("attempt_heartbeats"), "jobs": summ.get("jobs"),
            "missing_count": summ.get("missing_count", len(summ.get("missing", []))),
            "failed_shards": summ.get("failed_shards", []),
            "missing": summ.get("missing", []), "findings": found, "unchecked": unchecked,
            "nonstandard": nonstandard, "certified_own_proof_nonstandard": own_nonstandard,
            "repeat": rep, "residue_replaced": replaced,
            "residue_path": residues.get(name), "maker": None,
            "residue_unfinished": unfinished.get(name, []) if subset_of is None else [],
            "reports_keyed_again": reused.get(name, 0) if subset_of is None else 0,
            "subset_of": subset_of, "subset_names": subset_names}
        if name in makers:
            res = [x for p in makers[name].split("+") for x in load(p)]
            result["corpora"][name]["maker"] = {
                "model": maker_model.get(name, ""),
                "tasks": len(res), "answered": sum(x["result"] != "no answer" for x in res),
                "accepted": sum(x["result"] == "accepted" for x in res),
                "by_theorem": dict(collections.Counter(
                    x["theorem"].rsplit(".", 1)[-1].split("_")[0] for x in res
                    if x["result"] == "accepted"))}
        concl = {r["decl"]: r.get("conclusion", "") for r in corpus}
        result["corpora"][name]["false"] = [
            {"decl": x["theorem"].rsplit(".", 1)[0], "proof": x["theorem"],
             "axioms": x.get("axioms"), "conclusion": concl.get(x["theorem"].rsplit(".", 1)[0], "")}
            for p in refuted.get(name, "").split("+") if p for x in load(p)
            if x["result"] == "accepted" and x.get("type", "").startswith("¬ Anchor.Spec.Holds")
            and set(x.get("axioms") or ["?"]) <= STD]

    for spec in a.run:
        name, path = spec.split("=", 1)
        paths = path.split("+")
        rows, summs, seen = [], [], set()
        for p in paths:
            rows += load(p, seen)
            sp = p[:-len(".jsonl")] + ".summary.json"
            summs.append(json.load(open(sp)) if os.path.exists(sp) else {})
        again = sum(1 for r in rows if r.get("decl", "").endswith(" (again)"))
        print(f"{name}: {again} reports keyed (again), a name reported more than once")
        reused[name] = again
        if name in expects:
            want = collections.Counter(
                ln.split("\t")[0].strip() for p in expects[name].split("+")
                for ln in open(p, encoding="utf-8") if ln.strip())
            have = collections.Counter(r["decl"].split(" (again)")[0] for r in rows)
            off = sorted(k for k in want.keys() | have.keys() if want[k] != have[k])
            print(f"{name}: {sum(have.values())} reports against {sum(want.values())} input "
                  f"rows; {len(off)} names differ"
                  + (f", first {off[0]} ({have[off[0]]} reports, {want[off[0]]} rows)"
                     if off else ""))
            if off:
                return 2
        replaced = 0
        if name in residues:
            got = load(residues[name])
            second = {r["decl"]: r for r in got if "error" not in r}
            unfinished[name] = sorted({r["decl"] for r in got if "error" in r} - set(second))
            known = {r["decl"] for r in rows}
            if not {r["decl"] for r in got} <= known:
                print(f"{name}: residue run reports statements the first pass did not")
                return 2
            replaced = len(second)
            rows = [second.get(r["decl"], r) for r in rows]
        budgets = sorted({s.get("attempt_heartbeats") for s in summs} - {None})
        summ = {"timeouts": [t for s in summs for t in s.get("timeouts", [])],
                "wall_s": sum(s.get("wall_s") or 0 for s in summs) or None,
                "attempt_heartbeats": "/".join(map(str, budgets)) or None,
                "jobs": "/".join(str(s["jobs"]) for s in summs if s.get("jobs")) or None,
                "missing_count": sum(s.get("missing_count", 0) for s in summs),
                "failed_shards": [x for s in summs for x in s.get("failed_shards", [])],
                "missing": [m for s in summs for m in s.get("missing", [])]}
        for r in rows:
            if r["decl"] in by_label:
                planted_seen[r["decl"]] = (name, r)
        loaded[name] = (rows, summ, path, paths, replaced)
        entry(name, rows, summ, path, paths, replaced)
    for spec in a.subset:
        name, rest = spec.split("=", 1)
        run, names_path = rest.split(":", 1)
        if run not in loaded:
            print(f"{name}: no run named {run}")
            return 2
        keep = {ln.strip() for ln in open(names_path) if ln.strip()}
        rows, summ, path, paths, replaced = loaded[run]
        sub = [r for r in rows if r["decl"].split(" (again)")[0] in keep]
        summ = dict(summ, timeouts=[t for t in summ["timeouts"] if t.get("decl") in keep],
                    missing=[m for m in summ["missing"] if m in keep],
                    missing_count=len([m for m in summ["missing"] if m in keep]))
        entry(name, sub, summ, path, paths, replaced, subset_of=run, subset_names=len(keep))
    if labels:
        rows = []
        for lab in labels:
            got = planted_seen.get(lab["name"])
            ok, why = judge(lab, got[1] if got else None)
            rows.append({"name": lab["name"], "category": lab["category"], "ok": ok,
                         "why": why, "run": got[0] if got else None})
        result["planted"] = {"recovered": sum(r["ok"] for r in rows), "total": len(rows),
                             "rows": rows}
    with open(a.json, "w", encoding="utf-8") as f:
        json.dump(result, f, indent=1, sort_keys=True, ensure_ascii=False)
        f.write("\n")
    with open(a.html, "w", encoding="utf-8") as f:
        f.write(render(result))
    runs = [c for c in result["corpora"].values() if c["subset_of"] is None]
    bad = sum(len(c["unchecked"]) for c in runs)
    ns = sum(len(c["nonstandard"]) for c in runs)
    print(f"wrote {a.html} and {a.json}; findings without a listed proof: {bad}; "
          f"set aside as resting on non-standard axioms: {ns}")
    return 1 if bad else 0


LABELS = [("certified", "Certified"), ("decorative", "Removable hypothesis, model found"),
          ("uncertified_removable", "Removable hypothesis, no model found"),
          ("vacuous", "Vacuous"),
          ("contradiction", "Contradiction lemma (conclusion False, vacuous by design)"),
          ("trivial", "Conclusion true outright"),
          ("uncertified_open", "Model found, some hypothesis unsettled"),
          ("uncertified_no_model", "Uncertified: no model, no vacuity proof"),
          ("statement_only", "Statement only (no proof read)"),
          ("no_hypotheses", "No hypothesis to test (none, or only untested premises)"),
          ("unsupported", "Unsupported"),
          ("error", "Error"), ("other", "Other")]


def esc(s):
    return html.escape(str(s))


def render(res):
    corp = res["corpora"]
    names = list(corp)
    css = """
body{font:15px/1.5 -apple-system,Segoe UI,Helvetica,Arial,sans-serif;max-width:1100px;
margin:2em auto;padding:0 1em;color:#111}
h1{font-size:1.6em;margin-bottom:.2em}h2{margin-top:1.8em;font-size:1.25em}
table{border-collapse:collapse;width:100%;margin:.6em 0}
th,td{border:1px solid #ccc;padding:4px 8px;text-align:left;vertical-align:top}
th{background:#f3f3f3}td.n{text-align:right;font-variant-numeric:tabular-nums}
code{font:13px Menlo,Consolas,monospace;background:#f6f6f6;padding:0 3px}
details{margin:.4em 0}summary{cursor:pointer;font-weight:600}
.small{color:#555;font-size:13px}.ok{color:#0a6b2d}.bad{color:#a40000}"""
    out = [f"<!doctype html><html><head><meta charset='utf-8'><title>Anchor census</title>"
           f"<style>{css}</style></head><body>",
           "<h1>Anchor census</h1>"] + ([res["lead"]] if res.get("lead") else []) + [
           "<p>Each statement was read by <code>anchor_census</code>: its hypotheses and "
           "conclusion extracted with a kernel-checked proof that the encoding says what the "
           "statement says, then each obligation searched for a proof. Every finding below "
           "names the declaration that proves it; the kernel checked each one when it was "
           "added, and each rests only on <code>propext</code>, <code>Classical.choice</code> "
           "and <code>Quot.sound</code>.</p>"]
    if res.get("commit"):
        out.append(f"<p class=small>Anchor code: commit <code>{esc(res['commit'])}</code>.</p>")
    out.append("<h2>Counts</h2><table><tr><th>Verdict</th>" +
               "".join(f"<th>{esc(n)}</th>" for n in names) + "</tr>")
    out.append("<tr><td>Statements</td>" +
               "".join(f"<td class=n>{corp[n]['statements']}</td>" for n in names) + "</tr>")
    for key, lab in LABELS:
        if not any(corp[n]["counts"].get(key) for n in names):
            continue
        out.append(f"<tr><td>{esc(lab)}</td>" +
                   "".join(f"<td class=n>{corp[n]['counts'].get(key, 0)}</td>" for n in names) +
                   "</tr>")
    out.append("<tr><td>With untested premises</td>" +
               "".join(f"<td class=n>{corp[n]['with_premises']}</td>" for n in names) + "</tr>")
    out.append("<tr><td>Wall-clock timeouts</td>" +
               "".join(f"<td class=n>{len(corp[n]['timeouts'])}</td>" for n in names) + "</tr>")
    out.append("<tr><td>Not reported (missing)</td>" +
               "".join(f"<td class=n>{corp[n]['missing_count']}</td>" for n in names) + "</tr>")
    out.append("<tr><td>Search budget (heartbeats per obligation)</td>" +
               "".join(f"<td class=n>{corp[n]['attempt_heartbeats'] or ''}</td>" for n in names)
               + "</tr>")
    out.append("<tr><td>Parallel processes</td>" +
               "".join(f"<td class=n>{corp[n]['jobs'] or ''}</td>" for n in names) + "</tr>")
    out.append("<tr><td>Wall time (s)</td>" +
               "".join(f"<td class=n>{corp[n]['wall_s'] or ''}</td>" for n in names) + "</tr>")
    out.append("</table>")
    for n in names:
        c = corp[n]
        rem = [f for f in c["findings"] if f["kind"] == "removable"]
        junkn = sum(1 for f in rem if f.get("junk_value"))
        vac = [f for f in c["findings"] if f["kind"] == "vacuous" and not f.get("intended")]
        contra = [f for f in c["findings"] if f["kind"] == "vacuous" and f.get("intended")]
        triv = [f for f in c["findings"] if f["kind"] == "trivial"]
        methods = collections.Counter(f["method"] for f in rem)
        out.append(f"<h2>{esc(n)}</h2>")
        if c.get("subset_of"):
            out.append(f"<p>These are the {c['statements']} statements of the "
                       f"{esc(c['subset_of'])} run whose names are on a list of "
                       f"{c['subset_names']}; they are also counted in that run.</p>")
        def n(k, one, many):
            return f"{k} {one if k == 1 else many}"
        out.append(f"<p>{n(len(vac), 'vacuous statement', 'vacuous statements')}, "
                   f"{n(len(contra), 'contradiction lemma', 'contradiction lemmas')} "
                   f"(conclusion <code>False</code>, vacuous by design), "
                   f"{n(len(triv), 'conclusion', 'conclusions')} true outright, "
                   f"{n(len(rem), 'removable hypothesis', 'removable hypotheses')} "
                   f"({junkn} read as junk-value conventions, "
                   f"{len(rem) - junkn} other). Removable hypotheses by method: " +
                   ", ".join(f"{esc(k)} {v}" for k, v in sorted(methods.items())) + ".</p>")
        if c["repeat"]:
            rp = c["repeat"]
            same_len = rp["lines"][0] == rp["lines"][1]
            if rp["identical"]:
                txt, ok = "byte-identical", True
            elif same_len and rp["differing"] == rp["differing_elapsed_only"]:
                ex = [json.loads(z) for z in rp["examples"][0]] if rp["examples"] else [{}, {}]
                txt, ok = (f"identical in every report; {rp['differing']} error line"
                           f"{'s differ' if rp['differing'] != 1 else ' differs'} only in the elapsed "
                           f"seconds the message states (<code>{esc(ex[0].get('decl', ''))}</code>: "
                           f"“{esc(ex[0].get('error', ''))}” against "
                           f"“{esc(ex[1].get('error', ''))}”)"), True
            else:
                txt, ok = f"differs in {rp['differing']} lines", False
            out.append(f"<p class={'ok' if ok else 'bad'}>Second run into a fresh directory: "
                       f"{txt} (sha256 <code>{esc(rp['sha256'][:16])}</code> and "
                       f"<code>{esc(rp['sha256_repeat'][:16])}</code>).</p>")
        if c.get("maker"):
            mk = c["maker"]
            kinds = ", ".join(f"{esc(k)} {v}" for k, v in sorted(mk["by_theorem"].items()))
            out.append(f"<p>Residue pass: {mk['tasks']} open obligations, sampled by hash of "
                       f"their names, were each given once to a model agent"
                       f"{' (' + esc(mk['model']) + ')' if mk.get('model') else ''} with no "
                       f"access to Lean. {mk['answered']} were answered and {mk['accepted']} answers "
                       f"compiled at the obligation's type on the standard axioms"
                       f"{' (' + kinds + ')' if kinds else ''}. "
                       f"{c['residue_replaced']} statements were then analysed again with "
                       "those proofs supplied; their reports above are the second ones."
                       + (f" {len(c['residue_unfinished'])} more reached the wall-clock limit "
                          "in the second analysis and keep their first report ("
                          + ", ".join(f"<code>{esc(d)}</code>" for d in c["residue_unfinished"])
                          + ")." if c.get("residue_unfinished") else "") + "</p>")
        if c.get("false"):
            nf = len(c["false"])
            out.append(f"<p>{nf} statement{' is' if nf == 1 else 's are'} false as written: "
                       "Lean accepted a proof of the negation of the extracted statement, on the "
                       "standard axioms.</p><table><tr><th>Declaration</th><th>Conclusion</th>"
                       "<th>Proof</th><th>Axioms</th></tr>")
            for f in c["false"]:
                out.append(f"<tr><td><code>{esc(f['decl'])}</code></td>"
                           f"<td>{esc(f['conclusion'][:300])}</td>"
                           f"<td><code>{esc(f['proof'].split('.')[-1])}</code></td>"
                           f"<td>{esc(', '.join(sorted(f['axioms'], key=STD_ORDER.index)))}"
                           "</td></tr>")
            out.append("</table>")
        if c["unchecked"]:
            out.append(f"<p class=bad>{len(c['unchecked'])} findings without a checked proof; "
                       "not counted.</p>")
        if c["nonstandard"]:
            ns_ax = sorted({x for f in c["nonstandard"] for x in f["axioms"]} - STD)
            out.append(f"<p>{len(c['nonstandard'])} further findings have proofs that rest on "
                       f"{esc(', '.join(ns_ax))} (a <code>native_decide</code> in the "
                       "library's own proofs). They are not counted, and the statements they "
                       "belong to are classed as if those obligations were open.</p>")
        if c["certified_own_proof_nonstandard"]:
            out.append(f"<p>{c['certified_own_proof_nonstandard']} certified statements have "
                       "a theorem whose own proof rests on a non-standard axiom; the "
                       "certificate contains that proof, while every obligation Anchor proved "
                       "rests on the standard three.</p>")
        for title, items in [("Vacuous statements", vac),
                             ("Contradiction lemmas (vacuous by design)", contra),
                             ("Conclusions true outright", triv),
                             ("Removable hypotheses, other", [f for f in rem
                                                              if not f.get("junk_value")]),
                             ("Removable hypotheses, junk-value convention",
                              [f for f in rem if f.get("junk_value")])]:
            if not items:
                continue
            out.append(f"<details><summary>{esc(title)} ({len(items)})</summary><table>"
                       "<tr><th>Declaration</th><th>Finding</th><th>Method</th>"
                       "<th>Proof</th></tr>")
            for f in items:
                out.append(f"<tr><td><code>{esc(f['decl'])}</code></td>"
                           f"<td>{esc(f['detail'])}<div class=small>conclusion: "
                           f"{esc(f['conclusion'][:300])}</div></td><td>{esc(f['method'])}</td>"
                           f"<td><code>{esc(f['proof'].split('.')[-1])}</code></td></tr>")
            out.append("</table></details>")
    p = res.get("planted")
    if p:
        out.append("<h2>Planted statements inside the census</h2>")
        out.append(f"<p>{p['recovered']} of {p['total']} planted labels recovered, judged by "
                   "the Phase 1 rule. The planted statements were mixed into the runs and "
                   "analysed by the same processes under the same settings.</p><table>"
                   "<tr><th>Statement</th><th>Label</th><th>Result</th></tr>")
        for r in p["rows"]:
            out.append(f"<tr><td><code>{esc(r['name'].split('.')[-1])}</code></td>"
                       f"<td>{esc(r['category'])}</td><td class={'ok' if r['ok'] else 'bad'}>"
                       f"{esc(r['why'][:160])}</td></tr>")
        out.append("</table>")
    out.append("<h2>How removable hypotheses are split</h2><p>A removable hypothesis is read "
               "as a junk-value convention when it is a side condition such as "
               "<code>b ≠ 0</code> or <code>0 &lt; x</code> and the conclusion uses an "
               "operation that Mathlib defines everywhere by convention, such as division, "
               "<code>log</code>, square root, derivative, integral or infinite sum. Mathlib "
               "often keeps these hypotheses on purpose. The split is a text rule and is not "
               "proved; the removability itself is.</p>")
    out.append("</body></html>\n")
    return "\n".join(out)


if __name__ == "__main__":
    sys.exit(main())
