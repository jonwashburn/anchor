# Anchor

[![CI](https://github.com/jonwashburn/anchor/actions/workflows/ci.yml/badge.svg)](https://github.com/jonwashburn/anchor/actions/workflows/ci.yml)

Lean's kernel checks that a proof proves its statement. It cannot check that the statement says what its author meant. Anchor makes part of that checkable, with proofs the kernel accepts:

- **The hypotheses can all hold.** Anchor finds a model of them, or proves they contradict each other.
- **Each hypothesis is needed.** For each one, Anchor finds a model where the others hold, it fails and the conclusion fails, or it proves the hypothesis can be dropped.
- **The conclusion is not trivially true** of every model.
- **What a reader has to read.** The review surface of a declaration lists every definition its statement depends on, down to a trusted library boundary.
- **Sign-offs that expire.** A reviewer's sign-off is bound to a hash of that surface, and goes stale exactly when something on it changes. A proof-only change leaves it current.
- **Pinned definitions.** A uniqueness theorem lets a reader check a definition's specification instead of its construction.
- **The classical price.** Which classical principles a proof actually reaches, with the path to each.

Every claim Anchor makes is a theorem added to the environment, accepted only when `#print axioms` lists nothing beyond `propext`, `Classical.choice` and `Quot.sound`. The extraction and the search are untrusted: an extraction error cannot pass the kernel-checked equivalence `foo.anchorSpec_iff`, and a wrong witness cannot pass the kernel.

## Example

```lean
import Mathlib
import Anchor

theorem pos_sq (x : ℝ) (hx : 0 < x) : 0 < x ^ 2 := pow_pos hx 2
theorem silly (x : ℝ) (h1 : 0 < x) (h2 : x < 0) : x = 7 := by linarith
theorem deco (x : ℝ) (h1 : 0 < x) (h2 : x ≠ 5) : 0 < x ^ 2 := pow_pos h1 2

anchor_cert pos_sq
anchor_cert silly
anchor_cert deco
```

```
anchor: pos_sq
  model: (x : ℝ)
  hypotheses:
    [0] 0 < x
  conclusion: 0 < x ^ 2
  nonvacuous: proved (search: x := 1)
  hypothesis [0] load-bearing: proved (search: x := 0)
  verdict: CERTIFIED
anchor: silly
  hypotheses:
    [0] 0 < x
    [1] x < 0
  vacuous: proved (search)
  verdict: VACUOUS
anchor: deco
  hypotheses:
    [0] 0 < x
    [1] x ≠ 5
  hypothesis [0] load-bearing: proved (search: x := 0)
  hypothesis [1] removable: proved (proof term: the proof never uses this hypothesis)
  verdict: DECORATIVE [1]
```

(Output abridged from `AnchorTest/Smoke.lean`.) After `anchor_cert`, `#print axioms pos_sq.anchorCertificate` shows the certificate rests on the three standard axioms. `silly` has contradictory hypotheses, so it proves nothing about any real number; `deco` carries a hypothesis it never uses.

## What it finds

`AnchorTest/Findings.lean` derives each of these again when it compiles.

- **Mathlib** (the revision in `lake-manifest.json`). Three statements hold with a hypothesis fewer than they state: `midpoint_le_right` without the instance `PosSMulReflectLE k E`, `mul_nonneg_iff_left_nonneg_of_pos` without `PosMulStrictMono R`, and `FractionalIdeal.mul_inv_cancel_of_le_one` without its hypothesis 1, which only guards a junk value of the inverse.
- **miniF2F** ([yangky11/miniF2F-lean4](https://github.com/yangky11/miniF2F-lean4) at 5746b7d). Three problems are changed by natural-number arithmetic, where `1 / k` is `0` for `k > 1` and subtraction is truncated. The hypotheses of `mathd_algebra_275` and `mathd_algebra_289` cannot hold, so both statements are provable and say nothing. `amc12a_2020_p13` is false as written: its equation holds for every input, so it claims `b = 3` for every `b > 1`, and its negation is a theorem.

These come from a census run over a stratified 2,000-theorem sample of Mathlib and all 488 miniF2F statements, using `scripts/census.py`. On the Mathlib sample Anchor certified 82 statements and found the 3 removable hypotheses above; for 1,366 the search found neither a model nor a contradiction within its budget, and 263 reached the wall-clock limit. An uncertified statement is a gap in the search, not a finding.

## Commands

| Command | What it does |
|----|----|
| `#anchor foo` | Analyse `foo` and print the report; keeps no declarations |
| `anchor_cert foo` | The same, keeping every proof it found (`foo.anchorCertificate`, `foo.anchorVacuous`, `foo.anchorDrop_k`, ...) |
| `#anchor_json foo` | The report as one JSON object |
| `anchor_spec foo` | Add only the extracted statement, so an author can supply obligations by name before `anchor_cert` |
| `#surface foo`, `#surface_json foo` | The review surface |
| `@[pinned]`, `#pinned` | Pin a definition by a uniqueness theorem; list the pins in scope |
| `#price foo`, `#price_json foo` | Classical entry points the proof reaches |
| `lake exe anchor sign --module M --decl D --reviewer R --sentence S` | Append a sign-off to `signoffs.jsonl` |
| `lake exe anchor check --file signoffs.jsonl` | Recompute every sign-off; exits 1 if any is stale, 2 if the file holds none |

The verdicts, the declarations Anchor adds and the report fields are specified in [docs/FORMAT.md](docs/FORMAT.md).

## Using it

Anchor builds with Lean `v4.27.0-rc1` and the Mathlib revision pinned in `lake-manifest.json`. A project on the same versions adds

```lean
require anchor from git "https://github.com/jonwashburn/anchor" @ "main"
```

to its lakefile and writes `import Anchor`. To build Anchor itself:

```
lake exe cache get
lake build Anchor
```

## Tests

CI builds the library and the test modules below, each of which runs Anchor as it compiles. Two longer suites run from scripts:

- `scripts/test_planted.sh <output dir> AnchorTest/supplied/planted_supplied.jsonl`: forty planted statements in `AnchorTest/Planted.lean` (ten certifiable, ten vacuous, ten decorative, five with no hypotheses, five with dependent premises), with their expected verdicts in `AnchorTest/planted_labels.json` and a plain-logic answer key in `AnchorTest/PlantedKey.lean`. The script analyses all forty twice and requires byte-identical output with every label recovered. Each control must fail: an empty output, an empty label file, mutated labels, the suite without supplied proofs, a supplied proof of the wrong statement (`AnchorTest/SuppliedTest.lean`) and a proof resting on `Lean.ofReduceBool` (`AnchorTest/NativeTest.lean`). Five obligations the search leaves open are closed by the proofs in `AnchorTest/supplied/`, which the kernel checks like any other.
- `scripts/test_signoff.sh <output dir>`: sign-off staleness over nine variants of one file (`AnchorTest/Signoff/variants/`). Editing the statement, a definition on its surface, or a pinned definition's specification makes the sign-off stale. Reordering the file, renaming bound variables, editing a proof, editing outside the surface or rewriting a pinned definition's body leaves it current.
- `AnchorTest/SHA256Test.lean`, `AnchorTest/SurfaceTest.lean`, `AnchorTest/PriceTest.lean`: the FIPS 180-4 vectors, surface walks and price reports.

## Census tools

`scripts/census.py` runs Anchor over a list of declarations, one Lean process per statement, in parallel shards, and `scripts/census_report.py` turns the results into a report in which every finding names its kernel-checked proof. `scripts/maker.py` writes each obligation the search left open as a task for a person or a model, checks returned answers at the obligation's exact type on the standard axioms, and supplies the accepted ones to a second run. `AnchorTest/Census/mathlib_sample_2000.tsv` is the Mathlib sample, with its selection rule in `mathlib_sample_summary.txt`.

Anchor contains no `sorry`, `admit` or `axiom`.

## License

Apache License 2.0. Copyright 2026 Jonathan Washburn / Recognition Physics Institute.
