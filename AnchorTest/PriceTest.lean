import Anchor.Price

/-!
# Planted checks for `#price`

One statement, `∀ n : Nat, n = 0 ∨ n ≠ 0`, proved three ways: by case analysis on the numeral
(constructive), by `Classical.em`, and by `Classical.byCases`. The constructive proof must report no
entry point and the classical proofs must report theirs, so the reports differ.

`trivially_true` is the empty input: its report is empty, and an empty report alone must never
pass the test.

`LibEM` is a library's own excluded middle, stated as a proposition and registered with
`@[classical_entry]`. A proof that takes it as a hypothesis reports it with role `stated`.

`twoProofs` is a toy priced calculus with one statement and two proofs, one using `em` and one
using nothing, checking that `IsMinimumPrice` picks the empty set and rejects `[em]`.
-/

namespace AnchorTest.PriceTest

open Anchor.Price

/-- Constructive: case analysis on the numeral, and constructor disjointness. -/
theorem zero_or_ne_constructive : ∀ n : Nat, n = 0 ∨ n ≠ 0 :=
  fun n => Nat.casesOn (motive := fun n => n = 0 ∨ n ≠ 0) n (Or.inl rfl)
    (fun _ => Or.inr (fun h => Nat.noConfusion h))

/-- Classical: excluded middle on `n = 0`. -/
theorem zero_or_ne_classical : ∀ n : Nat, n = 0 ∨ n ≠ 0 :=
  fun n => Classical.em (n = 0)

/-- Classical: `Classical.byCases` on `n = 0`. -/
theorem zero_or_ne_byCases : ∀ n : Nat, n = 0 ∨ n ≠ 0 :=
  fun n => Classical.byCases (p := n = 0) Or.inl Or.inr

/-- The empty input. -/
theorem trivially_true : True := trivial

#price zero_or_ne_constructive
#price_json zero_or_ne_constructive
#price zero_or_ne_classical
#price_json zero_or_ne_classical
#price zero_or_ne_byCases
#price_json zero_or_ne_byCases
#price trivially_true
#price_json trivially_true

/-- A library's own excluded middle, stated as a proposition. -/
def LibEM : Prop := ∀ p : Prop, p ∨ ¬p

attribute [classical_entry] LibEM

/-- Uses the library's excluded middle as a hypothesis; no Lean classical axiom. -/
theorem one_eq_one_or_not (h : LibEM) : (1 = 1) ∨ ¬(1 = 1) := h _

#price one_eq_one_or_not
#price_json one_eq_one_or_not

/-- A toy priced calculus: one statement, two proofs; `true` uses `em`, `false` uses nothing. -/
def twoProofs : PricedCalculus.{0, 0} where
  Stmt := Unit
  Proof _ := Bool
  uses p := match p with
    | true => [`em]
    | false => []

/-- The proof that uses nothing makes the empty set the minimum price. -/
theorem twoProofs_min_nil : twoProofs.IsMinimumPrice () [] :=
  PricedCalculus.isMinimumPrice_nil (C := twoProofs) false rfl

/-- `[em]` is not the minimum price: the proof `false` does not use `em`. -/
theorem twoProofs_not_min_em : ¬ twoProofs.IsMinimumPrice () [`em] :=
  fun ⟨_, hmin⟩ =>
    nomatch (show `em ∈ ([] : List Lean.Name) from hmin false `em (List.Mem.head _))

#print axioms zero_or_ne_constructive
#print axioms zero_or_ne_classical
#print axioms zero_or_ne_byCases
#print axioms trivially_true
#print axioms one_eq_one_or_not
#print axioms twoProofs_min_nil
#print axioms twoProofs_not_min_em
#print axioms PricedCalculus.IsMinimumPrice.mem_iff
#print axioms PricedCalculus.isMinimumPrice_nil

end AnchorTest.PriceTest
