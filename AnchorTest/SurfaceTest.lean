import Mathlib
import Anchor.Surface
import Anchor.Pins

/-!
# Planted checks for the review surface and the pinned index

Each check prints `CHECK <name> PASS` or stops the file with an error. The planted pairs:

* `ratio_zero` is true only because real division by zero returns zero. Its surface must show
  `HDiv.hDiv` with the junk-value note. `total_zero` has the same shape without division; its
  surface must show no junk note at all.
* `nat_sub_zero` uses truncated subtraction on `ℕ`, `real_sub_self` uses subtraction on `ℝ`.
  Only the first may carry the truncated-subtraction note.
* `half` is defined with division and pinned by `2 * x = 1`. With pins honored its surface
  shows `half` pinned and no division; with pins ignored it shows `ratio` and the division.
* `fold_target` reaches a structure, a recursive inductive type and a definition by pattern
  matching. Its surface must list exactly those four constants to read, with every generated
  auxiliary folded away.
* A false uniqueness claim cannot be pinned: its proof fails, Lean's error recovery leaves the
  declaration with a placeholder proof, and `@[pinned]` refuses it because that proof depends
  on `sorryAx`. Shape errors and a second pin of the same constant are refused too.
-/

namespace Anchor.SurfaceTest

open Lean Meta Elab Command Anchor.Surface

/-- Division of reals. -/
noncomputable def ratio (a b : ℝ) : ℝ := a / b

/-- Planted positive: true only because real division by zero returns zero. -/
theorem ratio_zero (a : ℝ) : ratio a 0 = 0 := by simp [ratio]

/-- Addition of reals. -/
noncomputable def total (a b : ℝ) : ℝ := a + b

/-- Planted negative: the same shape as `ratio_zero`, without division. -/
theorem total_zero (a : ℝ) : total a 0 = a := by simp [total]

/-- Planted positive for a typed junk value: truncated subtraction on `ℕ`. -/
theorem nat_sub_zero (n : ℕ) : n - (n + 1) = 0 := by omega

/-- Planted negative for a typed junk value: subtraction on `ℝ` is not truncated. -/
theorem real_sub_self (x : ℝ) : x - x = 0 := sub_self x

/-- One half, written with division. -/
noncomputable def half : ℝ := ratio 1 2

/-- `half` is the only real `x` with `2 * x = 1`. -/
@[pinned] theorem half_pinned : Pinned (fun x : ℝ => 2 * x = 1) Eq half := by
  refine ⟨?_, fun b (hb : 2 * b = 1) => ?_⟩
  · show 2 * ratio 1 2 = 1
    simp only [ratio]
    norm_num
  · show b = ratio 1 2
    simp only [ratio]
    linarith

/-- A statement about `half`. -/
theorem half_lt_one : half < 1 := by
  show ratio 1 2 < 1
  simp only [ratio]
  norm_num

/-- A pair of naturals. -/
structure Pair where
  /-- The first part. -/
  fst : ℕ
  /-- The second part. -/
  snd : ℕ

/-- Binary trees. -/
inductive Tree where
  /-- A leaf. -/
  | leaf : Tree
  /-- A node with two subtrees. -/
  | node : Tree → Tree → Tree

/-- The number of leaves and nodes. -/
def Tree.size : Tree → ℕ
  | .leaf => 1
  | .node l r => l.size + r.size + 1

/-- Swap the two parts of a pair. -/
def Pair.swap (p : Pair) : Pair := ⟨p.snd, p.fst⟩

/-- A statement that reaches a structure, a recursive inductive type, a definition by
pattern matching and a definition through a projection. -/
theorem fold_target (t : Tree) (p : Pair) : t.size + p.swap.fst = p.snd + t.size := by
  show t.size + p.snd = p.snd + t.size
  exact Nat.add_comm _ _

/-- One, as a real number. -/
noncomputable def one' : ℝ := 1

/-- `x ^ 2 = 1` does not pin `one'`: `-1` meets it too. -/
theorem false_pin_is_false : ¬ Pinned (fun x : ℝ => x ^ 2 = 1) Eq one' := by
  rintro ⟨_, h⟩
  have h1 := h (-1) (by norm_num)
  simp only [one'] at h1
  norm_num at h1

/-! ## Refused pins -/

/--
error: @[pinned]: Anchor.SurfaceTest.false_pin depends on sorryAx, so its uniqueness claim is not proved; Anchor.SurfaceTest.one' is not pinned
---
error: no proof: -1 also squares to 1
⊢ Pinned (fun x => x ^ 2 = 1) Eq one'
-/
#guard_msgs (ordering := sorted) in
@[pinned] theorem false_pin : Pinned (fun x : ℝ => x ^ 2 = 1) Eq one' := by
  fail "no proof: -1 also squares to 1"

/--
error: @[pinned]: the type of Anchor.SurfaceTest.not_a_pin is
  2 + 2 = 4
which is not of the form Anchor.Pinned spec r c
-/
#guard_msgs in
@[pinned] theorem not_a_pin : (2 : ℝ) + 2 = 4 := by norm_num

/--
error: @[pinned]: the pinned object
  1 + 1
is not a constant
-/
#guard_msgs in
@[pinned] theorem not_a_constant : Pinned (fun x : ℝ => x = 2) Eq ((1 : ℝ) + 1) :=
  ⟨by norm_num, fun b (hb : b = 2) => by rw [hb]; norm_num⟩

/--
error: @[pinned]: Anchor.SurfaceTest.half is already pinned by Anchor.SurfaceTest.half_pinned
-/
#guard_msgs in
@[pinned] theorem half_pinned_again : Pinned (fun x : ℝ => x + x = 1) Eq half := by
  refine ⟨?_, fun b (hb : b + b = 1) => ?_⟩
  · show ratio 1 2 + ratio 1 2 = 1
    simp only [ratio]
    norm_num
  · show b = ratio 1 2
    simp only [ratio]
    linarith

/-! ## Checks -/

/-- Print `CHECK name PASS`, or stop with an error. -/
def check (name : String) (ok : Bool) (detail : String := "") : MetaM Unit := do
  if ok then IO.println s!"CHECK {name} PASS"
  else throwError "CHECK {name} FAIL {detail}"

/-- The entry for `n` on a surface, if any. -/
def entry? (es : Array Entry) (n : Name) : Option Entry :=
  es.find? (·.name == n)

/-- Whether an entry carries the junk-value note. -/
def hasJunkNote (e : Entry) : Bool :=
  match e.note with
  | some s => (s.splitOn "total function with a junk value").length > 1
  | none => false

/-- The names of the entries with a given status, sorted. -/
def namesWith (es : Array Entry) (st : Status) : Array Name :=
  ((es.filter (·.status == st)).map (·.name)).qsort Name.lt

run_meta do
  let es ← compute ``ratio_zero
  let hdiv := entry? es ``HDiv.hDiv
  check "junk_positive_hdiv_listed" hdiv.isSome
  check "junk_positive_hdiv_note" (hdiv.map hasJunkNote |>.getD false)
  check "junk_positive_ratio_read"
    ((entry? es ``ratio).map (·.status == .read) |>.getD false)

run_meta do
  let es ← compute ``total_zero
  check "junk_negative_no_hdiv" (entry? es ``HDiv.hDiv).isNone
  check "junk_negative_no_note" (es.all (!hasJunkNote ·))
  check "junk_negative_total_read"
    ((entry? es ``total).map (·.status == .read) |>.getD false)

run_meta do
  let natSurface ← compute ``nat_sub_zero
  let realSurface ← compute ``real_sub_self
  check "typed_junk_nat_sub_note"
    ((entry? natSurface ``HSub.hSub).map hasJunkNote |>.getD false)
  check "typed_junk_real_sub_listed" (entry? realSurface ``HSub.hSub).isSome
  check "typed_junk_real_sub_no_note" (realSurface.all (!hasJunkNote ·))

run_meta do
  let pinnedView ← compute ``half_lt_one
  let fullView ← compute ``half_lt_one { honorPins := false }
  let h := entry? pinnedView ``half
  check "pin_collapses_half_pinned"
    ((h.map fun e => e.status == .pinned && e.pinnedBy == some ``half_pinned).getD false)
  check "pin_collapses_no_ratio" (entry? pinnedView ``ratio).isNone
  check "pin_collapses_no_hdiv" (entry? pinnedView ``HDiv.hDiv).isNone
  check "pin_ignored_ratio_read"
    ((entry? fullView ``ratio).map (·.status == .read) |>.getD false)
  check "pin_ignored_hdiv_note"
    ((entry? fullView ``HDiv.hDiv).map hasJunkNote |>.getD false)

run_meta do
  let es ← compute ``fold_target
  let got := namesWith es .read
  let want := #[``Pair, ``Pair.swap, ``Tree, ``Tree.size].qsort Name.lt
  check "folding_read_set_exact" (got == want) s!"got {got}"
  check "folding_nothing_pinned" (namesWith es .pinned).isEmpty

run_meta do
  check "empty_roots_empty_surface" (← computeMany #[]).isEmpty
  let a ← compute ``half_lt_one
  let b ← compute ``half_lt_one
  check "rerun_identical"
    (render #[``half_lt_one] a == render #[``half_lt_one] b &&
      (renderJson #[``half_lt_one] {} a).compress == (renderJson #[``half_lt_one] {} b).compress)

run_meta do
  let env ← getEnv
  check "false_pin_refused" (getPin? env ``one').isNone
  check "false_pin_has_placeholder_proof" ((← collectAxioms ``false_pin).contains ``sorryAx)
  check "shape_errors_refused"
    ((allPins env).all fun p => p.thm != ``not_a_pin && p.thm != ``not_a_constant &&
      p.thm != ``half_pinned_again)
  let want := #[``Real, ``Real.goldenRatio, ``half].qsort Name.lt
  let got := (allPins env).map (·.target)
  check "pinned_index_exact" (got == want) s!"got {got}"
  check "pinned_index_axioms_standard"
    ((allPins env).all fun p =>
      p.axioms.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·))

#pinned

#surface ratio_zero

#surface half_lt_one

#surface_json half_lt_one

#print axioms ratio_zero
#print axioms total_zero
#print axioms nat_sub_zero
#print axioms real_sub_self
#print axioms half_pinned
#print axioms half_lt_one
#print axioms fold_target
#print axioms false_pin_is_false
#print axioms not_a_pin
#print axioms not_a_constant
#print axioms half_pinned_again
#print axioms Anchor.Pins.goldenRatio_pinned
#print axioms Anchor.Pins.real_pinned

end Anchor.SurfaceTest
