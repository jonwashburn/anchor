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

/-! ## A definition of a family of propositions -/

def family (n : ℕ) : Prop := 0 < n → 0 < n * n

#expect_verdict family "NONVACUOUS, EVERY HYPOTHESIS LOAD-BEARING" params 0

/-! ## Unchanged: a theorem with no vocabulary keeps its proof -/

theorem plain (x : ℝ) (hx : 0 < x) : 0 < x ^ 2 := pow_pos hx 2

#expect_verdict plain "CERTIFIED" params 0

/-! ## Controls: a substantive claim is not trivial, and a placeholder is not certified -/

#expect_not_verdict bound "TRIVIAL"
#expect_not_verdict central_claim "NO HYPOTHESES"
#expect_not_verdict plain "TRIVIAL"

end AnchorTest.Typed
