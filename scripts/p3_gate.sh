#!/usr/bin/env bash
# Phase 3 gate: a sign-off goes stale exactly when its review surface changes.
#
# Run from the root of a built anchor tree:  bash scripts/p3_gate.sh <receipt dir>
#
# Two declarations are signed against the base fixture. Each variant is then copied over
# AnchorTest/Signoff/Fixture.lean, rebuilt, and checked. The expected verdict of every
# (variant, declaration) pair is written below before any run. The gate also requires that an
# empty sign-off file fails, that a second full run prints byte-identical output, and that every
# build exits 0.
set -u
OUT="${1:?receipt dir}"
mkdir -p "$OUT"
source ~/.elan/env
F=AnchorTest/Signoff/Fixture.lean
V=AnchorTest/Signoff/variants
S="$OUT/signoffs.jsonl"
BIN=.lake/build/bin/anchor

# variant  double_evenish  three_pos
EXPECTED="V0_base current current
V1_inside STALE current
V2_outside current current
V3_reorder current current
V4_proof current current
V5_binders current current
V6_statement STALE current
V7_pinned_body current current
V8_pinned_spec current STALE"

fail=0
lake build anchor > "$OUT/build_exe.txt" 2>&1; echo "build anchor exe: exit $?" | tee "$OUT/exits.txt"

: > "$OUT/empty.jsonl"
lake env $BIN check --file "$OUT/empty.jsonl" > "$OUT/empty_check.txt" 2>&1
e=$?
echo "check on empty file: exit $e (expected 2)" | tee -a "$OUT/exits.txt"
[ "$e" = 2 ] || fail=1

run() {
  local tag="$1"
  local res="$OUT/run_$tag.txt"
  : > "$res"
  cp "$V/V0_base.lean.txt" "$F"
  lake build AnchorTest.Signoff.Fixture > "$OUT/build_${tag}_V0_sign.txt" 2>&1
  echo "[$tag] build V0 for signing: exit $?" >> "$OUT/exits.txt"
  rm -f "$S"
  lake env $BIN sign --module AnchorTest.Signoff.Fixture --decl AnchorTest.Signoff.double_evenish \
    --reviewer gate --date 2026-10-08 --file "$S" \
    --sentence "Doubling a positive natural number gives a number of the form double k." >> "$res" 2>&1
  lake env $BIN sign --module AnchorTest.Signoff.Fixture --decl AnchorTest.Signoff.three_pos \
    --reviewer gate --date 2026-10-08 --file "$S" \
    --sentence "Any natural number equal to three is positive." >> "$res" 2>&1
  while read -r variant want1 want2; do
    cp "$V/$variant.lean.txt" "$F"
    lake build AnchorTest.Signoff.Fixture > "$OUT/build_${tag}_$variant.txt" 2>&1
    b=$?
    echo "[$tag] build $variant: exit $b" >> "$OUT/exits.txt"
    [ "$b" = 0 ] || fail=1
    out=$(lake env $BIN check --file "$S" 2>&1)
    c=$?
    printf '== %s (check exit %s)\n%s\n' "$variant" "$c" "$out" >> "$res"
    got1=$(echo "$out" | awk '$2=="AnchorTest.Signoff.double_evenish"{print $1}')
    got2=$(echo "$out" | awk '$2=="AnchorTest.Signoff.three_pos"{print $1}')
    if [ "$got1" = "$want1" ] && [ "$got2" = "$want2" ]; then
      echo "[$tag] $variant: double_evenish $got1, three_pos $got2: as expected" >> "$OUT/verdicts.txt"
    else
      echo "[$tag] $variant: double_evenish $got1 (want $want1), three_pos $got2 (want $want2): MISMATCH" >> "$OUT/verdicts.txt"
      fail=1
    fi
    if [ "$want1" = current ] && [ "$want2" = current ]; then want_exit=0; else want_exit=1; fi
    [ "$c" = "$want_exit" ] || { echo "[$tag] $variant: check exit $c, want $want_exit" >> "$OUT/verdicts.txt"; fail=1; }
  done <<< "$EXPECTED"
  cp "$V/V0_base.lean.txt" "$F"
}

: > "$OUT/verdicts.txt"
run 1
run 2
if cmp -s "$OUT/run_1.txt" "$OUT/run_2.txt"; then
  echo "second run identical" >> "$OUT/verdicts.txt"
else
  echo "second run DIFFERS" >> "$OUT/verdicts.txt"; fail=1
fi
lake build AnchorTest.Signoff.Fixture > /dev/null 2>&1
if [ "$fail" = 0 ]; then echo "P3 GATE: PASS" | tee -a "$OUT/verdicts.txt"; else echo "P3 GATE: FAIL" | tee -a "$OUT/verdicts.txt"; fi
exit $fail
