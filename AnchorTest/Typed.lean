import Mathlib
import Anchor

/-!
# Statements drafted as definitions over opaque vocabulary

A paper's claim drafted into Lean is usually `def claim : Prop := ∀ …` over `opaque` objects the
paper names but does not construct. Each case below states the verdict Anchor must reach, and
`#expect_verdict` fails the build if it reaches another, so a regression cannot pass CI.

The two placeholders are the shape Pith's formalizer emitted when it had no statement:
`PaperClaim : Prop := True`, read directly or through an alias. Both must come out trivial.
-/

open Lean Elab Command

/-- Fail unless Anchor's verdict for `decl` starts with `verdict` and it reads exactly
`params` opaque constants as parameters. -/
elab "#expect_verdict " id:ident v:str " params " k:num : command => do
  let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let r ← liftTermElabM <| withoutModifyingEnv (Anchor.analyzeUnbounded c)
  unless r.verdict.startsWith v.getString do
    throwError "{c}: expected verdict {v.getString}, got {r.verdict}\n{r.render}"
  unless r.parameters.size == k.getNat do
    throwError "{c}: expected {k.getNat} parameters, got {r.parameters}\n{r.render}"
  logInfo r.render

/-- Fail if Anchor's verdict for `decl` starts with `verdict`: the control showing that
`#expect_verdict` discriminates. -/
elab "#expect_not_verdict " id:ident v:str : command => do
  let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let r ← liftTermElabM <| withoutModifyingEnv (Anchor.analyzeUnbounded c)
  if r.verdict.startsWith v.getString then
    throwError "{c}: verdict {r.verdict} was expected to differ from {v.getString}"

set_option linter.unusedVariables false

namespace AnchorTest.Typed

/-! ## Placeholders: no content, must be reported trivial -/

def PaperClaim : Prop := True

def central_claim : Prop := PaperClaim

#expect_verdict PaperClaim "TRIVIAL CONCLUSION" params 0
#expect_verdict central_claim "TRIVIAL CONCLUSION" params 0

/-! ## Opaque vocabulary -/

/-- A bandit-style bound: instances, an assumption, two regrets and a constant, all opaque.
Every hypothesis matters under some reading of the vocabulary. -/
opaque Inst : Type
opaque AssumptionA : Inst → Prop
opaque Regret : ℝ → Inst → ℝ
opaque C : ℝ

def bound : Prop :=
  ∀ (T : ℝ) (θ : Inst), 0 < C → AssumptionA θ → 0 < T → Regret T θ ≤ C * T

#expect_verdict bound "NONVACUOUS, EVERY HYPOTHESIS LOAD-BEARING" params 4

/-- The assumption is never used: removing it leaves the bound true. -/
def bound_deco : Prop :=
  ∀ (T : ℝ) (θ : Inst), AssumptionA θ → 0 < Regret T θ → 0 < Regret T θ ^ 2

#expect_verdict bound_deco "DECORATIVE [0]" params 3

/-- Contradictory hypotheses about an opaque constant: no reading satisfies both. -/
def contradictory : Prop :=
  ∀ x : ℝ, 0 < C → C < 0 → x = 0

#expect_verdict contradictory "VACUOUS" params 1

/-- An opaque proposition alone, held for every reading only if its reading is `True`: not
trivial, since a reading as `False` falsifies it. -/
opaque Claimed : Prop

def bare : Prop := Claimed

#expect_verdict bare "NO HYPOTHESES" params 1

/-- A local definition over the vocabulary is unfolded, so its constants are abstracted too. -/
noncomputable def ratio (T : ℝ) (θ : Inst) : ℝ := Regret T θ / C

def via_def : Prop :=
  ∀ (T : ℝ) (θ : Inst), 0 < ratio T θ → 0 < ratio T θ + 1

#expect_verdict via_def "NONVACUOUS, EVERY HYPOTHESIS LOAD-BEARING" params 3

/-- A definition reaching the vocabulary only through another local definition is unfolded
all the way, and the constant used directly beside it is abstracted with the rest. -/
noncomputable def r1 (T : ℝ) (θ : Inst) : ℝ := Regret T θ / C

noncomputable def r2 (T : ℝ) (θ : Inst) : ℝ := r1 T θ + 0

def via_two : Prop :=
  ∀ (T : ℝ) (θ : Inst), 0 < C → 0 < r2 T θ → 0 < r2 T θ + C

#expect_verdict via_two "NONVACUOUS, EVERY HYPOTHESIS LOAD-BEARING" params 3

-- Two constants with the same last name stay two parameters.
namespace Left
opaque K : ℝ
end Left

namespace Right
opaque K : ℝ
end Right

def two_K : Prop := 0 < Left.K → 0 < Right.K → 0 < Left.K + Right.K

#expect_verdict two_K "NONVACUOUS, EVERY HYPOTHESIS LOAD-BEARING" params 2

/-- A theorem over vocabulary whose proof works for every reading keeps its proof. -/
opaque D : ℝ

theorem carried (h : 0 < D) : 0 < D + 1 := by linarith

#expect_verdict carried "CERTIFIED" params 1

/-- An axiom constrains the vocabulary, so the statement is read as written, with its proof,
and no reading of `Q` as `False` makes the hypothesis look load-bearing. The proof rests on
the axiom, so its unused hypothesis is not certified removable either. -/
opaque Q : ℕ → Prop

axiom q0 : Q 0

theorem uses_axiom (h : Q 0) : Q 0 ∧ True := ⟨q0, trivial⟩

#expect_verdict uses_axiom "UNCERTIFIED" params 0
#expect_not_verdict uses_axiom "NONVACUOUS"

/-! ## Statements with no hypotheses -/

/-- A theorem with no hypotheses holds by its proof; that is no finding. -/
theorem comm_nohyp (a b : ℕ) : a + b = b + a := Nat.add_comm a b

#expect_verdict comm_nohyp "NO HYPOTHESES" params 0

/-! ## A definition of a family of propositions, read as a claim only when asked -/

def family (n : ℕ) : Prop := 0 < n → 0 < n * n

set_option anchor.readFamilies true in
#expect_verdict family "NONVACUOUS, EVERY HYPOTHESIS LOAD-BEARING" params 0

/-- A predicate is not a claim: by default it is not read as `∀ n, 0 ≤ n`. -/
def NonNeg (n : ℕ) : Prop := 0 ≤ n

#expect_not_verdict NonNeg "TRIVIAL"
#expect_not_verdict family "NONVACUOUS"

/-! ## Unchanged: a theorem with no vocabulary keeps its proof -/

theorem plain (x : ℝ) (hx : 0 < x) : 0 < x ^ 2 := pow_pos hx 2

#expect_verdict plain "CERTIFIED" params 0

/-! ## Controls: a substantive claim is not trivial, and a placeholder is not certified -/

#expect_not_verdict bound "TRIVIAL"
#expect_not_verdict central_claim "NO HYPOTHESES"
#expect_not_verdict plain "TRIVIAL"

end AnchorTest.Typed
