import Mathlib
import Anchor.Pinned

/-!
# Example pins

Two Mathlib objects pinned by kernel-checked uniqueness theorems. A statement that mentions
one of them can be read through its specification.

* `Real.goldenRatio` is the only positive real `x` with `x ^ 2 = x + 1`.
* `ℝ` is pinned among types by carrying a conditionally complete linearly ordered field
  structure, up to the relation "any two such structures are order-ring isomorphic"
  (Mathlib's `LinearOrderedField.inducedOrderRingIso`). This is uniqueness up to
  isomorphism, not equality: a statement about `ℝ` transfers to another complete ordered
  field only if it respects order-ring isomorphism.
-/

namespace Anchor.Pins

/-- The golden ratio is the only positive real `x` with `x ^ 2 = x + 1`. The other root of
the equation is `Real.goldenConj`, which is negative. -/
@[pinned] theorem goldenRatio_pinned :
    Pinned (fun x : ℝ => 0 < x ∧ x ^ 2 = x + 1) Eq Real.goldenRatio := by
  refine ⟨⟨Real.goldenRatio_pos, Real.goldenRatio_sq⟩, fun b ⟨hb, hb2⟩ => ?_⟩
  have hsum := Real.goldenRatio_add_goldenConj
  have hprod := Real.goldenRatio_mul_goldenConj
  have hfac : (b - Real.goldenRatio) * (b - Real.goldenConj) = 0 := by
    linear_combination hb2 - b * hsum + hprod
  rcases mul_eq_zero.mp hfac with h | h
  · linarith
  · have := Real.goldenConj_neg
    linarith

/-- The type `X` carries a conditionally complete linearly ordered field structure: a field,
linearly ordered compatibly with its arithmetic, in which every nonempty set with an upper
bound has a least upper bound. -/
def IsCompleteOrderedField (X : Type) : Prop :=
  Nonempty (ConditionallyCompleteLinearOrderedField X)

/-- Any conditionally complete linearly ordered field structures on `X` and on `Y` are
isomorphic as ordered rings: some bijection preserves addition, multiplication and order. -/
def CompleteOrderedFieldIso (X Y : Type) : Prop :=
  ∀ [ConditionallyCompleteLinearOrderedField X] [ConditionallyCompleteLinearOrderedField Y],
    Nonempty (X ≃+*o Y)

/-- The reals are the complete ordered field: `ℝ` carries the structure, and every type that
carries it is order-ring isomorphic to `ℝ`, whichever structures are chosen on the two
types. -/
@[pinned] theorem real_pinned :
    Pinned IsCompleteOrderedField CompleteOrderedFieldIso ℝ :=
  ⟨⟨inferInstance⟩, fun X _ _ _ => ⟨LinearOrderedField.inducedOrderRingIso X ℝ⟩⟩

end Anchor.Pins
