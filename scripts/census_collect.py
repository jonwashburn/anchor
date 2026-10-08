#!/usr/bin/env python3
"""Collect what a stopped census run wrote, so a second run can finish the corpus.

    census_collect.py RUN_DIR CORPUS NAMES_FILE REMAINING_OUT [--jobs N]
                      [--attempt-heartbeats H] [--wall S]

census.py writes NAME.jsonl only when every shard is done. For a run stopped early this
rebuilds NAME.jsonl, NAME.time.tsv and NAME.summary.json from the shard files under the same
rules: every complete report line is kept, and a part that is followed by another part of the
same shard stopped on the name after its last report, which is recorded as a timeout (the next
part starts one name later, and this is checked). Names that no finished part settled,
including the rest of a part still running when the run stopped and every name of a shard that
never started, are written sorted to REMAINING_OUT for a second run with `--names`. This is
counted per shard, so a name a corpus reuses in two modules is remaining while either copy is;
those names are printed, since their rerun needs the imports of their own module. The report
reads the two runs as one corpus (`census_report.py --run NAME=first.jsonl+second.jsonl`).
"""

import collections
import glob
import json
import os
import re
import sys


def read_reports(path):
    got = []
    if not os.path.exists(path):
        return got
    with open(path, encoding="utf-8") as f:
        for ln in f.read().splitlines():
            if not ln.strip():
                continue
            try:
                json.loads(ln)
            except json.JSONDecodeError:
                break
            got.append(ln)
    return got


def main():
    run, corpus, names_file, remaining = sys.argv[1:5]
    opts = dict(zip(sys.argv[5::2], sys.argv[6::2]))
    names = sorted({ln.strip() for ln in open(names_file) if ln.strip()})
    parts = collections.defaultdict(dict)
    for p in glob.glob(os.path.join(run, "shards", "*.txt")):
        m = re.fullmatch(r"(s\d{4}(?:m\d{3})?)_(\d+)\.txt", os.path.basename(p))
        if m:
            parts[m.group(1)][int(m.group(2))] = p[:-len(".txt")]
    out, timeouts, times, left = {}, [], [], set()
    for tag in sorted(parts):
        ps = parts[tag]
        here = set()
        for k in sorted(ps):
            stem = ps[k]
            with open(stem + ".txt") as f:
                todo = [ln for ln in f.read().splitlines() if ln.strip()]
            if k == min(ps):
                full = list(todo)
            got = read_reports(stem + ".jsonl")
            if os.path.exists(stem + ".jsonl.time"):
                with open(stem + ".jsonl.time") as f:
                    times += [ln for ln in f.read().splitlines() if ln.strip()]
            for ln in got:
                d = json.loads(ln)
                here.add(d["decl"])
                key = d["decl"]
                while key in out:
                    key += " (again)"
                out[key] = ln if key == d["decl"] else json.dumps(
                    dict(d, decl=key), sort_keys=True, separators=(",", ":"), ensure_ascii=False)
            if k + 1 in ps:
                with open(ps[k + 1] + ".txt") as f:
                    nxt = [ln for ln in f.read().splitlines() if ln.strip()]
                if nxt != todo[len(got) + 1:]:
                    sys.exit(f"{tag}_{k}: the next part does not start after the stalled name")
                d = todo[len(got)]
                err = "wall-clock timeout or lean exit, no report (collected from shard files)"
                timeouts.append({"decl": d, "error": err, "shard": f"{tag}_{k}"})
                here.add(d)
                key = d
                while key in out:
                    key += " (again)"
                out[key] = json.dumps({"decl": key, "error": err}, sort_keys=True,
                                      separators=(",", ":"))
        left |= set(full) - here
    seen = {k.split(" (again)")[0] for k in out}
    stray = sorted(seen - set(names))
    if stray:
        sys.exit(f"{len(stray)} reported names are not in {names_file}, first {stray[0]}")
    rest = sorted(left | {n for n in names if n not in seen})
    reused = sorted(left & seen)
    if reused:
        print(f"{len(reused)} remaining names are also reported from another module; rerun "
              f"them with the imports of their own shard, first {reused[0]}")
    with open(remaining, "w") as f:
        f.write("\n".join(rest) + ("\n" if rest else ""))
    with open(os.path.join(run, f"{corpus}.jsonl"), "w") as f:
        for key in sorted(out):
            f.write(out[key] + "\n")
    with open(os.path.join(run, f"{corpus}.time.tsv"), "w") as f:
        f.write("\n".join(sorted(times)) + "\n")
    verdicts = collections.Counter()
    for v in out.values():
        d = json.loads(v)
        if "error" in d:
            verdicts["ERROR: " + d["error"].split(" after ")[0][:80]] += 1
        else:
            verdicts[d["verdict"].split(" (")[0].split(" [")[0]] += 1
    summary = {"corpus": corpus, "statements": len(seen), "reports": len(out),
               "missing": [], "missing_count": 0, "stopped_early": True,
               "remaining_count": len(rest), "remaining_file": remaining,
               "timeouts": timeouts, "failed_shards": [], "shards": len(parts),
               "jobs": int(opts["--jobs"]) if "--jobs" in opts else None,
               "attempt_heartbeats": int(opts["--attempt-heartbeats"])
               if "--attempt-heartbeats" in opts else None,
               "wall_s": int(opts["--wall"]) if "--wall" in opts else None,
               "verdicts": dict(sorted(verdicts.items()))}
    with open(os.path.join(run, f"{corpus}.summary.json"), "w") as f:
        json.dump(summary, f, indent=1, sort_keys=True)
    print(f"{len(seen)} statements collected ({len(timeouts)} timeouts), "
          f"{len(rest)} remaining in {remaining}")


if __name__ == "__main__":
    main()
