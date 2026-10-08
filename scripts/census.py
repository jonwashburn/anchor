#!/usr/bin/env python3
"""Run `anchor_census` over one corpus on the build box, in parallel.

    census.py --corpus NAME --lean-path PATH --out DIR
              (--names FILE --imports "Mod1 Mod2" | --tsv FILE [--imports "Extra"])
              [--extra-tsv FILE] [--jobs 48] [--shards 192]
              [--attempt-heartbeats 100000] [--timeout 300] [--import-timeout 900]
              [--limit N] [--supplied FILE]

Input is either a name list (one Lean name per line, as `anchor_list` writes it) analysed with
the same `--imports` in every process, or a TSV whose first two columns are name and module,
where each process imports only the modules of its own names (some corpora reuse a name in
two files, which cannot be imported together). Modules are dealt round-robin into shards;
with `--names` the names themselves are. Each shard is one Lean process that imports `Anchor`
and its modules and runs `anchor_census`.

A statement that runs `--timeout` seconds without producing its report (the first one gets
`--import-timeout` more, for the imports) has its process stopped; it is recorded as a
wall-clock timeout and the rest of that shard runs in a new process. Each obligation already has
a heartbeat budget; this limit catches work that heartbeats do not count. A shard whose imports
fail before any report is split into one process per module. `--extra-tsv` mixes further
statements (the planted suite) into the corpus before sharding, so they are analysed by the
same processes under the same settings.

Output in DIR: `NAME.jsonl` (every report, sorted by declaration name; a name analysed in two
modules keeps both, keyed by module), `NAME.time.tsv` (milliseconds per statement),
`NAME.summary.json` (counts by verdict) and `shards/` (shard files and per-process logs).
A second run into a fresh DIR gives a byte-identical NAME.jsonl apart from timeouts, which
depend on the clock and are listed in the summary.
"""

import argparse
import collections
import json
import os
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor


SUPPLIED = {}


def lean_file(imports, attempt_hb, names_path, out_path, names=()):
    lines = ["import Anchor"] + [f"import {m}" for m in imports] + [""]
    lines += [SUPPLIED[n] + "\n" for n in names if n in SUPPLIED]
    lines += [f"set_option anchor.search.attemptHeartbeats {attempt_hb}",
              f'anchor_census "{names_path}" "{out_path}"', ""]
    return "\n".join(lines)


def count_lines(path):
    try:
        with open(path) as f:
            return sum(1 for ln in f if ln.strip())
    except FileNotFoundError:
        return 0


def run_one(args, tag, imports, names):
    """One shard: run until every name has a report or a recorded timeout."""
    sd = os.path.join(args.out, "shards")
    reports, times, timeouts = [], [], []
    part = 0
    todo = list(names)
    while todo:
        stem = os.path.join(sd, f"{tag}_{part}")
        with open(stem + ".txt", "w") as f:
            f.write("\n".join(todo) + "\n")
        with open(stem + ".lean", "w") as f:
            f.write(lean_file(imports, args.attempt_heartbeats, stem + ".txt", stem + ".jsonl",
                              todo))
        env = dict(os.environ, LEAN_PATH=args.lean_path)
        with open(stem + ".log", "w") as log:
            p = subprocess.Popen([args.lean, stem + ".lean"], stdout=log,
                                 stderr=subprocess.STDOUT, env=env)
            seen, last = 0, time.time()
            limit = args.import_timeout + args.timeout
            code = None
            while code is None:
                try:
                    code = p.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    n = count_lines(stem + ".jsonl")
                    if n > seen:
                        seen, last, limit = n, time.time(), args.timeout
                    elif time.time() - last > limit:
                        p.kill()
                        p.wait()
                        code = "timeout"
        stalled = round(time.time() - last)
        got = []
        if os.path.exists(stem + ".jsonl"):
            with open(stem + ".jsonl") as f:
                got = [ln for ln in f.read().splitlines() if ln.strip()]
        if os.path.exists(stem + ".jsonl.time"):
            with open(stem + ".jsonl.time") as f:
                times += [ln for ln in f.read().splitlines() if ln.strip()]
        if not got and code not in (0, "timeout") and part == 0:
            return None, times, [{"shard": tag, "error": f"lean exited {code} before any report"}]
        reports += got
        done = len(got)
        if done >= len(todo):
            break
        why = (f"wall-clock timeout, no report within {limit} s" if code == "timeout"
               else f"lean exited {code} before its report")
        timeouts.append({"decl": todo[done], "error": why, "elapsed_s": stalled,
                         "shard": f"{tag}_{part}"})
        todo = todo[done + 1:]
        part += 1
    return reports, times, timeouts


def run_shard(args, idx, groups):
    """`groups` is a list of (imports, names). Split per module if the joint import fails."""
    imports = sorted({m for ms, _ in groups for m in ms})
    names = [n for _, ns in groups for n in ns]
    r, t, to = run_one(args, f"s{idx:04d}", imports, names)
    if r is not None or len(groups) == 1:
        return (r or []), t, to
    reports, times, timeouts = [], list(t), list(to)
    for j, (ms, ns) in enumerate(groups):
        r2, t2, to2 = run_one(args, f"s{idx:04d}m{j:03d}", ms, ns)
        reports += r2 or []
        times += t2
        timeouts += to2
    return reports, times, timeouts


def read_tsv(path):
    rows = []
    for ln in open(path):
        parts = ln.rstrip("\n").split("\t")
        if len(parts) < 2 or parts[0] in ("", "name"):
            continue
        rows.append((parts[0], parts[1]))
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--corpus", required=True)
    ap.add_argument("--names")
    ap.add_argument("--tsv")
    ap.add_argument("--extra-tsv")
    ap.add_argument("--imports", default="")
    ap.add_argument("--lean-path", required=True)
    ap.add_argument("--lean", default=os.path.expanduser(
        "~/.elan/toolchains/leanprover--lean4---v4.27.0-rc1/bin/lean"))
    ap.add_argument("--out", required=True)
    ap.add_argument("--jobs", type=int, default=48)
    ap.add_argument("--shards", type=int, default=192)
    ap.add_argument("--attempt-heartbeats", type=int, default=100000)
    ap.add_argument("--timeout", type=int, default=300)
    ap.add_argument("--import-timeout", type=int, default=900)
    ap.add_argument("--limit", type=int, default=0, help="first N statements only (pilot runs)")
    ap.add_argument("--supplied", help="JSONL from maker.py supply: proofs read as supplied")
    args = ap.parse_args()
    extra = args.imports.split()
    if args.supplied:
        for ln in open(args.supplied):
            d = json.loads(ln)
            SUPPLIED[d["decl"]] = d["lean"]

    if args.tsv:
        rows = sorted(set(read_tsv(args.tsv)))
    elif args.names:
        rows = sorted({(ln.strip(), "") for ln in open(args.names) if ln.strip()})
    else:
        ap.error("give --names or --tsv")
    if args.limit:
        rows = rows[:args.limit]
    if args.extra_tsv:
        rows = sorted(set(rows) | set(read_tsv(args.extra_tsv)))
    if not rows:
        print("census: empty input", file=sys.stderr)
        sys.exit(2)
    os.makedirs(os.path.join(args.out, "shards"), exist_ok=False)

    by_mod = collections.defaultdict(list)
    for n, m in rows:
        by_mod[m].append(n)
    if list(by_mod) == [""]:
        k = max(1, min(args.shards, len(rows)))
        names = [n for n, _ in rows]
        shards = [[(extra, names[i::k])] for i in range(k)]
    else:
        mods = sorted(by_mod)
        k = max(1, min(args.shards, len(mods)))
        shards = [[([m] + extra if m else extra, sorted(by_mod[m])) for m in mods[i::k]]
                  for i in range(k)]
    t0 = time.time()
    with ThreadPoolExecutor(max_workers=args.jobs) as ex:
        results = list(ex.map(lambda a: run_shard(args, *a), enumerate(shards)))
    wall = round(time.time() - t0)

    mod_of = collections.defaultdict(list)
    for n, m in rows:
        mod_of[n].append(m)
    out, times, timeouts, failed = {}, [], [], []
    for r, t, to in results:
        times += t
        for ln in r:
            d = json.loads(ln)
            key = d["decl"]
            while key in out:
                key += " (again)"
            out[key] = ln if key == d["decl"] else json.dumps(
                dict(d, decl=key), sort_keys=True, separators=(",", ":"), ensure_ascii=False)
        for x in to:
            if "decl" in x:
                timeouts.append(x)
                key = x["decl"]
                while key in out:
                    key += " (again)"
                out[key] = json.dumps({"decl": key, "error": x["error"]},
                                      sort_keys=True, separators=(",", ":"))
            else:
                failed.append(x)
    seen = {k.split(" (again)")[0] for k in out}
    missing = sorted({n for n, _ in rows} - seen)
    with open(os.path.join(args.out, f"{args.corpus}.jsonl"), "w") as f:
        for key in sorted(out):
            f.write(out[key] + "\n")
    with open(os.path.join(args.out, f"{args.corpus}.time.tsv"), "w") as f:
        f.write("\n".join(sorted(times)) + "\n")
    verdicts = collections.Counter()
    for v in out.values():
        d = json.loads(v)
        if "error" in d:
            verdicts["ERROR: " + d["error"].split(" after ")[0][:80]] += 1
        else:
            verdicts[d["verdict"].split(" (")[0].split(" [")[0]] += 1
    summary = {"corpus": args.corpus, "statements": len(rows), "reports": len(out),
               "missing": missing[:50], "missing_count": len(missing),
               "timeouts": timeouts, "failed_shards": failed, "shards": len(shards),
               "jobs": args.jobs, "attempt_heartbeats": args.attempt_heartbeats,
               "timeout_s": args.timeout, "wall_s": wall, "extra_imports": extra,
               "verdicts": dict(sorted(verdicts.items()))}
    with open(os.path.join(args.out, f"{args.corpus}.summary.json"), "w") as f:
        json.dump(summary, f, indent=1, sort_keys=True)
    print(json.dumps({k: v for k, v in summary.items() if k not in ("timeouts", "missing")},
                     indent=1, sort_keys=True))


if __name__ == "__main__":
    main()
