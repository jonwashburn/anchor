import Mathlib
import Anchor

/-!
# Findings in Mathlib and miniF2F

Compiling this file derives each finding again; `#print axioms` shows what each proof rests on.

Mathlib, at the revision in `lake-manifest.json`. Each statement is true with one hypothesis
fewer than it states, and `anchor_cert` adds the proof:

* `FractionalIdeal.mul_inv_cancel_of_le_one`: hypothesis 1 is not needed. It only rules out a
  junk value of the inverse, so Mathlib may keep it on purpose.
* `midpoint_le_right`: hypothesis 2, the instance `PosSMulReflectLE k E`, is not needed.
* `mul_nonneg_iff_left_nonneg_of_pos`: hypothesis 0, the instance `PosMulStrictMono R`, is
  not needed.

miniF2F, in the Lean 4 port github.com/yangky11/miniF2F-lean4 at commit 5746b7d (MIT License,
Copyright (c) Meta Platforms, Inc. and affiliates). The statements and the `open` line are
copied verbatim; miniF2F proves each by `sorry`, and the proofs here are ours. Each one is
changed by natural-number arithmetic: `1 / k` is `0` for `k > 1`, and `a - b` is `0` when
`b ≥ a`.

* `mathd_algebra_275` (test split): the hypothesis reads `1 = 1 / 5`, so no real number
  satisfies it. The statement is provable and says nothing.
* `mathd_algebra_289` (test split): truncated subtraction makes `k ^ 2 - m * k + n = 0` force
  `n = 0`, which is not prime. The hypotheses cannot all hold.
* `amc12a_2020_p13` (validation split): the equation holds for every input, so the statement
  claims `b = 3` for every `b > 1`. Its negation is a theorem.
-/

set_option anchor.search.attemptHeartbeats 2000000

/-! ## Mathlib -/

anchor_cert FractionalIdeal.mul_inv_cancel_of_le_one
#print axioms FractionalIdeal.mul_inv_cancel_of_le_one.anchorDrop_1

anchor_cert midpoint_le_right
#print axioms midpoint_le_right.anchorDrop_2

anchor_cert mul_nonneg_iff_left_nonneg_of_pos
#print axioms mul_nonneg_iff_left_nonneg_of_pos.anchorDrop_0

/-! ## miniF2F -/

namespace AnchorTest.Findings

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_275
  (x : ℝ)
  (h : ((11:ℝ)^(1 / 4))^(3 * x - 3) = 1 / 5) :
  ((11:ℝ)^(1 / 4))^(6 * x + 2) = 121 / 25 := by
  norm_num at h

anchor_cert mathd_algebra_275
#print axioms mathd_algebra_275.anchorVacuous

theorem mathd_algebra_289
  (k t m n : ℕ)
  (h₀ : Nat.Prime m ∧ Nat.Prime n)
  (h₁ : t < k)
  (h₂ : k^2 - m * k + n = 0)
  (h₃ : t^2 - m * t + n = 0) :
  m^n + n^m + k^t + t^k = 20 := by
  have hn : n = 0 := (Nat.add_eq_zero_iff.mp h₂).2
  exact absurd (hn ▸ h₀.2) Nat.not_prime_zero

anchor_cert mathd_algebra_289
#print axioms mathd_algebra_289.anchorVacuous

/-- The miniF2F statement `amc12a_2020_p13`, with its binders written as implications, is
false: `a = b = c = n = 2` satisfies every hypothesis and `b ≠ 3`. -/
theorem amc12a_2020_p13_false :
    ¬ ∀ (a b c : ℕ) (n : NNReal), n ≠ 1 → (1 < a ∧ 1 < b ∧ 1 < c) →
      (n * (n * n ^ (1 / c)) ^ (1 / b)) ^ (1 / a) = (n ^ 25) ^ (1 / 36) → b = 3 := by
  intro h
  have := h 2 2 2 2 (by norm_num) (by norm_num) (by norm_num)
  exact absurd this (by decide)

#print axioms amc12a_2020_p13_false

end AnchorTest.Findings
