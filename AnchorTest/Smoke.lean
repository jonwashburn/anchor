import Mathlib
import Anchor.Command

/-! Five statements, one of each kind, to exercise `anchor_cert` end to end. -/

namespace AnchorTest.Smoke

theorem pos_sq (x : ℝ) (hx : 0 < x) : 0 < x ^ 2 := pow_pos hx 2

theorem silly (x : ℝ) (h1 : 0 < x) (h2 : x < 0) : x = 7 := by linarith

theorem deco (x : ℝ) (h1 : 0 < x) (h2 : x ≠ 5) : 0 < x ^ 2 := pow_pos h1 2

theorem nohyp (n : ℕ) : n + 0 = n := rfl

theorem dep (n : ℕ) (h : 0 < n) : (⟨0, h⟩ : Fin n).val = 0 := rfl

anchor_cert pos_sq
#print axioms pos_sq.anchorCertificate
#print axioms pos_sq.anchorSpec_iff

anchor_cert silly
#print axioms silly.anchorVacuous

anchor_cert deco
#print axioms deco.anchorDrop_1

anchor_cert nohyp

anchor_cert dep

/-- The model needs `n = 17`, outside the fixed candidates; random testing finds it. -/
theorem far (n : ℕ) (h1 : 12 < n) (h2 : n % 7 = 3) : 3 ≤ n % 7 := by omega

anchor_cert far

/-- The conclusion holds of every real, so the hypothesis does nothing. -/
theorem triv (x : ℝ) (h : 0 < x) : 0 ≤ x ^ 2 := sq_nonneg x

anchor_cert triv

end AnchorTest.Smoke
