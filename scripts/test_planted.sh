#!/usr/bin/env bash
# The planted suite: every planted label recovered with its Lean proof, twice, identically.
#
# Run from the root of an anchor checkout:
#   bash scripts/test_planted.sh <output dir> AnchorTest/supplied/planted_supplied.jsonl
#
# The planted statements are analysed by the census runner (one Lean process per statement),
# with kernel-checked proofs for five obligations the search leaves open passed as
# <supplied.jsonl>. The test passes only if both runs recover all 40 labels, the two outputs
# are byte-identical, and every control fails: an empty output, an empty label file, five
# mutated labels, the same suite run without the supplied proofs, a supplied proof of the
# wrong statement (AnchorTest/SuppliedTest.lean), which Anchor must refuse, and a search proof
# that rests on Lean.ofReduceBool (AnchorTest/NativeTest.lean), which must leave its
# obligations open. ANCHOR_JOBS sets the number of Lean processes (default: one per core).
set -u
OUT="${1:?output dir}"
SUP="${2:?supplied.jsonl}"
JOBS="${ANCHOR_JOBS:-$(getconf _NPROCESSORS_ONLN)}"
mkdir -p "$OUT"
if [ -f ~/.elan/env ]; then source ~/.elan/env; fi
L=AnchorTest/planted_labels.json
LP=$(lake env printenv LEAN_PATH)
NAMES="$OUT/planted_names.txt"
python3 -c "import json,sys; print('\n'.join(r['name'] for r in json.load(open(sys.argv[1]))))" "$L" > "$NAMES"
fail=0
: > "$OUT/exits.txt"
note() { echo "$1" >> "$OUT/exits.txt"; }

lake build Anchor AnchorTest.Planted > "$OUT/build.txt" 2>&1
e=$?; note "lake build Anchor AnchorTest.Planted: exit $e"; [ "$e" = 0 ] || fail=1
lake env lean --version >> "$OUT/exits.txt"

census() {  # <dir> [census args]
  local d="$1"; shift
  python3 scripts/census.py --corpus planted --names "$NAMES" --imports AnchorTest.Planted \
    --lean-path "$LP" --out "$d" --jobs "$JOBS" --shards 40 --attempt-heartbeats 2000000 "$@" \
    > "$d.log" 2>&1
}
for run in 1 2; do
  census "$OUT/run$run" --supplied "$SUP"
  e=$?; note "census run $run: exit $e, timeouts $(python3 -c "import json;print(len(json.load(open('$OUT/run$run/planted.summary.json'))['timeouts']))")"
  [ "$e" = 0 ] || fail=1
done
if cmp -s "$OUT/run1/planted.jsonl" "$OUT/run2/planted.jsonl"; then note "run 1 and run 2 byte-identical"
else note "run 1 and run 2 DIFFER"; fail=1; fi
if command -v sha256sum > /dev/null; then SHA=sha256sum; else SHA="shasum -a 256"; fi
$SHA "$OUT/run1/planted.jsonl" "$OUT/run2/planted.jsonl" >> "$OUT/exits.txt"
for run in 1 2; do
  python3 scripts/check_labels.py "$L" "$OUT/run$run/planted.jsonl" > "$OUT/check_run$run.txt" 2>&1
  e=$?; note "check_labels run $run: exit $e (want 0): $(tail -1 "$OUT/check_run$run.txt")"
  [ "$e" = 0 ] || fail=1
done

control() {  # <name> <labels> <output>
  python3 scripts/check_labels.py "$2" "$3" > "$OUT/control_$1.txt" 2>&1
  local e=$?
  note "control $1: exit $e (want nonzero): $(tail -1 "$OUT/control_$1.txt")"
  [ "$e" != 0 ] || fail=1
}
: > "$OUT/empty.jsonl"
echo "[]" > "$OUT/no_labels.json"
python3 - "$L" "$OUT/mutated_labels.json" <<'EOF'
import json, sys
labs = json.load(open(sys.argv[1]))
flip = {"certifiable": "vacuous", "vacuous": "certifiable", "decorative": "certifiable",
        "no_hypothesis": "dependent", "dependent": "no_hypothesis"}
seen = set()
for x in labs:
    if x["category"] not in seen:
        seen.add(x["category"])
        x["category"] = flip[x["category"]]
json.dump(labs, open(sys.argv[2], "w"), indent=1)
EOF
control empty_output "$L" "$OUT/empty.jsonl"
control empty_labels "$OUT/no_labels.json" "$OUT/run1/planted.jsonl"
control mutated_labels "$OUT/mutated_labels.json" "$OUT/run1/planted.jsonl"
census "$OUT/no_supplied"
control no_supplied "$L" "$OUT/no_supplied/planted.jsonl"
W="$OUT/control_supplied_wrong_type.txt"
lake env lean AnchorTest/SuppliedTest.lean > "$W" 2>&1
if grep -q "supplied proof rejected: its type is not the obligation" "$W" \
    && ! grep -q "verdict: DECORATIVE \[1\]" "$W"; then
  note "control supplied_wrong_type: refused (want refused)"
else
  note "control supplied_wrong_type: NOT refused"; fail=1
fi
N="$OUT/control_native_decide.txt"
lake env lean AnchorTest/NativeTest.lean > "$N" 2>&1
if grep -q "the proof found rests on \[Lean\." "$N" && grep -q "verdict: UNCERTIFIED" "$N" \
    && ! grep -q "verdict: TRIVIAL CONCLUSION" "$N"; then
  note "control native_decide: refused (want refused)"
else
  note "control native_decide: NOT refused"; fail=1
fi

if [ "$fail" = 0 ]; then note "PLANTED SUITE: PASS"; else note "PLANTED SUITE: FAIL"; fi
cat "$OUT/exits.txt"
exit "$fail"
