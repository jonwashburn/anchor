#!/usr/bin/env python3
"""Phase 1 gate checker: compare `anchor_cert` JSON reports with the planted labels.

    python3 scripts/p1_check.py AnchorTest/planted_labels.json <lean output> [--census]

With `--census` the output is a census report file in which the planted statements are mixed
among a corpus; reports for names outside the label file are ignored instead of failing.

A label is recovered when the report carries the proof the label calls for, and that proof
rests only on propext, Classical.choice and Quot.sound:

    certifiable    verdict CERTIFIED and <name>.anchorCertificate
    vacuous        verdict VACUOUS and <name>.anchorVacuous
    decorative     <name>.anchorDrop_<i> for the labelled index i
    no_hypothesis  verdict "NO HYPOTHESES (no certificate)" with no premises
    dependent      the hypothesis the statement depends on is listed as an untested premise
                   (`premises` non-empty) and the verdict is not a plain CERTIFIED

Exit 0 only when every label is recovered. Missing reports, duplicate reports, an empty
output and an empty label file all fail.
"""
import json
import sys

STD = {"propext", "Classical.choice", "Quot.sound"}


def reports(path):
    out = {}
    dup = []
    with open(path, encoding="utf-8") as f:
        for line in f:
            i = line.find("{")
            if i < 0:
                continue
            try:
                r = json.loads(line[i:])
            except json.JSONDecodeError:
                continue
            if not isinstance(r, dict) or "decl" not in r or "verdict" not in r:
                continue
            if r["decl"] in out:
                dup.append(r["decl"])
            out[r["decl"]] = r
    return out, dup


def proof(r, decl):
    for a in r.get("axioms", []):
        if a["decl"] == decl:
            return set(a["axioms"])
    return None


def judge(label, r):
    n, c = label["name"], label["category"]
    if r is None:
        return False, "no report"
    v = r["verdict"]
    if c == "no_hypothesis":
        ps = r.get("premises") or []
        return v == "NO HYPOTHESES (no certificate)" and not ps, f"{v}; premises {ps}"
    if c == "dependent":
        ps = r.get("premises") or []
        return bool(ps) and v != "CERTIFIED", f"{v}; premises {ps}"
    want = {"certifiable": f"{n}.anchorCertificate", "vacuous": f"{n}.anchorVacuous",
            "decorative": f"{n}.anchorDrop_{label.get('decorative_index')}"}.get(c)
    if want is None:
        return False, f"unknown category {c}"
    ax = proof(r, want)
    if ax is None:
        return False, f"{v}; no {want}"
    if not ax <= STD:
        return False, f"{v}; {want} rests on {sorted(ax - STD)}"
    if c == "certifiable" and v != "CERTIFIED":
        return False, v
    if c == "vacuous" and v != "VACUOUS":
        return False, v
    return True, f"{v}; {want} axioms {sorted(ax)}"


def main():
    labels = json.load(open(sys.argv[1], encoding="utf-8"))
    got, dup = reports(sys.argv[2])
    if not labels:
        print("no labels: nothing checked")
        return 2
    if "--census" in sys.argv[3:]:
        # Inside a census the other reports belong to the corpus, not to the suite.
        names = {l["name"] for l in labels}
        got = {k: v for k, v in got.items() if k in names}
        dup = [d for d in dup if d in names]
    ok = 0
    for lab in labels:
        good, why = judge(lab, got.get(lab["name"]))
        ok += good
        print(f"{'ok  ' if good else 'FAIL'} {lab['name']:32s} {lab['category']:14s} {why}")
    extra = sorted(set(got) - {l["name"] for l in labels})
    for e in extra:
        print(f"FAIL {e}: report with no label")
    for d in dup:
        print(f"FAIL {d}: reported twice")
    passed = ok == len(labels) and not extra and not dup
    print(f"{ok}/{len(labels)} labels recovered: {'PASS' if passed else 'FAIL'}")
    return 0 if passed else 1


if __name__ == "__main__":
    sys.exit(main())
