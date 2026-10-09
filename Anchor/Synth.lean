import Mathlib.Tactic
import Plausible
import Anchor.Core

/-!
# Witness search

Deterministic search for the proofs a certificate needs.

* `anchor_unfold` turns an obligation about an extracted `Spec` back into the reader's
  variables: `∃ x y, H₁ ∧ H₂`, `¬ ∃ x, …`, `∀ x, H₁ → C`.
* `anchor_search` proves an existential goal by trying small candidate values for each
  variable in turn and closing what remains with `decide`, `norm_num`, `simp`, `omega`,
  `linarith`, `positivity` and `grind`; when no small candidate works, Plausible's random
  testing, with a fixed seed, proposes one. A universal or negated goal goes straight to the
  closers after `push_neg` and `intro`, then to `nlinarith`, `order` and `aesop`. Every
  attempt runs under a fixed heartbeat budget, so the search gives the same answer on every
  run.

A found witness is only a proposal: the obligation counts once the kernel accepts the
proof term.
-/

open Lean Meta Elab Tactic

namespace Anchor.Synth

register_option anchor.search.leafHeartbeats : Nat := {
  defValue := 4000
  descr := "heartbeats (in thousands) for each closing attempt in anchor_search" }

register_option anchor.search.universalHeartbeats : Nat := {
  defValue := 40000
  descr := "heartbeats (in thousands) for each closing tactic on a universal goal, which is \
    tried once per obligation rather than once per candidate" }

register_option anchor.search.attemptHeartbeats : Nat := {
  defValue := 2000000
  descr := "heartbeats (in thousands) for one whole obligation, search included" }

register_option anchor.search.leafBudget : Nat := {
  defValue := 600
  descr := "maximum number of leaf goals anchor_search tries for one obligation" }

/-- `simp only` set that unpacks an obligation on an extracted `Spec`. -/
syntax (name := anchorUnfold) "anchor_unfold" : tactic

macro_rules
  | `(tactic| anchor_unfold) => `(tactic|
      simp only [Anchor.Spec.Nonvacuous, Anchor.Spec.Vacuous, Anchor.Spec.LoadBearing,
        Anchor.Spec.Drop, Anchor.Spec.Holds, Anchor.AllHold, Anchor.AllExcept, Anchor.HypAt,
        Anchor.sigma_exists_iff, Anchor.sigma_forall_iff, Anchor.unit_exists_iff,
        Anchor.unit_forall_iff, Anchor.plift_exists_iff, Anchor.plift_forall_iff, and_true,
        true_and, true_implies, forall_const])

/-- `anchor_unfold` without `forall_const`, which deletes a variable the rest of the goal no
longer mentions. Every model variable keeps its binder, so the goal can be shown with the
reader's names in order. -/
syntax (name := anchorUnfoldNames) "anchor_unfold_names" : tactic

macro_rules
  | `(tactic| anchor_unfold_names) => `(tactic|
      simp only [Anchor.Spec.Nonvacuous, Anchor.Spec.Vacuous, Anchor.Spec.LoadBearing,
        Anchor.Spec.Drop, Anchor.Spec.Holds, Anchor.AllHold, Anchor.AllExcept, Anchor.HypAt,
        Anchor.sigma_exists_iff, Anchor.sigma_forall_iff, Anchor.unit_exists_iff,
        Anchor.unit_forall_iff, Anchor.plift_exists_iff, Anchor.plift_forall_iff, and_true,
        true_and, true_implies])

/-- Run `x` with a fresh heartbeat budget. A timeout becomes an ordinary error, so the
caller's `try` moves on to the next attempt. -/
def withBudget {α} (kHeartbeats : Nat) (x : TacticM α) : TacticM α := do
  let start ← IO.getNumHeartbeats
  withTheReader Core.Context
    (fun ctx => { ctx with maxHeartbeats := kHeartbeats * 1000, initHeartbeats := start })
    (tryCatchRuntimeEx x fun e =>
      if e.isRuntime then throwError "anchor_search: attempt ran out of heartbeats" else throw e)

/-- Run `x` with an empty message log. If it throws or logs an error, fail; either way the
caller's messages are restored and `x`'s are dropped. A search step that "succeeds" by
elaborating a term to an error placeholder (and logging why) is therefore a failure. -/
def quiet {α} (x : TacticM α) : TacticM α := do
  let saved := (← getThe Core.State).messages
  modifyThe Core.State fun st => { st with messages := {} }
  let restore : TacticM Unit := modifyThe Core.State fun st => { st with messages := saved }
  let a ← try x catch e => restore; throw e
  let bad := (← getThe Core.State).messages.hasErrors
  restore
  if bad then throwError "anchor_search: the step logged an error"
  return a

/-- Closing tactics for a goal about concrete values, cheapest first. These run at every leaf
of the candidate search, so they must fail fast. -/
def leafClosers : TacticM (Array Syntax) := do
  return #[← `(tactic| decide), ← `(tactic| (norm_num <;> done)), ← `(tactic| (simp <;> done)),
    ← `(tactic| (constructor <;> norm_num <;> done))]

/-- Closing tactics for a goal with no existential left in front, cheapest first. -/
def closers : TacticM (Array Syntax) := do
  return #[← `(tactic| decide), ← `(tactic| (norm_num <;> done)), ← `(tactic| (simp <;> done)),
    ← `(tactic| omega), ← `(tactic| (constructor <;> norm_num <;> done)),
    ← `(tactic| positivity), ← `(tactic| linarith), ← `(tactic| (simp_all <;> done)),
    ← `(tactic| grind)]

/-- Facts `0 ≤ (x - y) ^ 2`, `0 ≤ (x + y) ^ 2` and `0 ≤ (x ± c) ^ 2` for `c = 1, 2`, over the
real, rational and integer variables in context (at most three), added as hypotheses for
`nlinarith`. -/
def addSquareHints : TacticM Unit := withMainContext do
  let mut xs : Array Expr := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← whnfR d.type
    if (t.isConstOf ``Real || t.isConstOf ``Rat || t.isConstOf ``Int) && xs.size < 3 then
      xs := xs.push d.toExpr
  let mut terms : Array Expr := #[]
  for i in [0:xs.size] do
    let x := xs[i]!
    let ty ← inferType x
    for c in [1, 2] do
      let n ← mkNumeral ty c
      terms := terms.push (← mkAppM ``HSub.hSub #[x, n])
      terms := terms.push (← mkAppM ``HAdd.hAdd #[x, n])
    for j in [i+1:xs.size] do
      terms := terms.push (← mkAppM ``HSub.hSub #[x, xs[j]!])
      terms := terms.push (← mkAppM ``HAdd.hAdd #[x, xs[j]!])
  let mut g ← getMainGoal
  for e in terms do
    let pf ← mkAppM ``sq_nonneg #[e]
    let (_, g') ← (← g.assert `anchor_sq (← inferType pf) pf).intro1P
    g := g'
  replaceMainGoal [g]

/-- `nlinarith` after `addSquareHints`. -/
syntax (name := anchorNlinarith) "anchor_nlinarith" : tactic

@[tactic anchorNlinarith] def evalAnchorNlinarith : Tactic := fun _ => do
  addSquareHints
  evalTactic (← `(tactic| nlinarith))

/-- Extra closers for universal goals, tried after `closers`. -/
def universalClosers : TacticM (Array Syntax) := do
  return #[← `(tactic| nlinarith), ← `(tactic| (intro h; simp_all <;> done)),
    ← `(tactic| (intro h; omega)), ← `(tactic| (intro h; linarith)),
    ← `(tactic| (intro h; nlinarith)), ← `(tactic| order), ← `(tactic| anchor_nlinarith),
    ← `(tactic| (intro h; anchor_nlinarith)), ← `(tactic| aesop), ← `(tactic| trivial)]

/-- Try each tactic on the main goal; succeed with the first that closes it. Each tactic gets
`hb` thousand heartbeats, the leaf budget unless the caller gives another. -/
def firstClosing (tacs : Array Syntax) (hb? : Option Nat := none) : TacticM Bool := do
  let hb := hb?.getD (anchor.search.leafHeartbeats.get (← getOptions))
  for c in tacs do
    let s ← saveState
    try
      quiet (withBudget hb (evalTactic c))
      if (← getUnsolvedGoals).isEmpty then return true
      s.restore
    catch _ => s.restore
  return false

/-- Candidate values for a variable of type `α`, simplest first. Candidates that do not
elaborate at `α` are skipped by the caller. -/
def candidates (α : Expr) : MetaM (Array Term) := do
  let α ← whnfR α
  if α.isProp then
    return #[← `(True), ← `(False)]
  if ← isProp α then
    return #[← `(inferInstance), ← `(by norm_num), ← `(by decide), ← `(by simp),
      ← `(by omega), ← `(by positivity)]
  if α.isSort then
    return #[← `(Nat), ← `(Int), ← `(Rat), ← `(Real), ← `(Bool), ← `(Unit), ← `(Fin 2),
      ← `(Fin 3), ← `(ZMod 2), ← `(ZMod 3), ← `(Multiplicative Int),
      ← `(Equiv.Perm (Fin 3))]
  if (← isClass? α).isSome then
    return #[← `(inferInstance)]
  if α.isForall then
    -- Predicates, type families and functions of several arguments, as vocabulary read as
    -- parameters produces them (`AssumptionA : X → Prop`, `Regret : ℝ → X → ℝ`): constant
    -- functions first.
    let (arity, cod) ← forallTelescopeReducing α fun xs cod => return (xs.size, cod)
    let constFun (b : Term) : MetaM Term := do
      let mut t := b
      for _ in [0:arity] do t ← `(fun _ => $t)
      return t
    if cod.isProp then
      return #[← constFun (← `(True)), ← constFun (← `(False))]
    if cod.isSort then
      return #[← constFun (← `(Nat)), ← constFun (← `(Unit))]
    let mut consts : Array Term := #[]
    if arity ≥ 2 then
      consts := #[← constFun (← `(0)), ← constFun (← `(1)), ← constFun (← `(-1)),
        ← constFun (← `(2))]
    return consts ++ #[← `(fun _ => 0), ← `(fun _ => 1), ← `(fun x => x), ← `(fun x => -x),
      ← `(fun x => x + 1), ← `(fun x => 2 * x), ← `(fun x => x ^ 2), ← `(fun _ => -1),
      ← `(fun x => x ^ 3), ← `(fun x => 1 - x)]
  return #[← `(0), ← `(1), ← `(-1), ← `(2), ← `(-2), ← `(3), ← `(1 / 2), ← `(-1 / 2),
    ← `(Equiv.swap 0 1), ← `(Equiv.swap 1 2), ← `(finRotate 3), ← `(Multiplicative.ofAdd 1),
    ← `(5), ← `(10), ← `(4), ← `(7), ← `(true), ← `(false), ← `([]), ← `([0]), ← `([1]),
    ← `([0, 1]), ← `([1, 2]), ← `(∅), ← `({0}), ← `({1}), ← `({0, 1}), ← `({1, 2}),
    ← `((0, 0)), ← `((1, 0)), ← `((0, 1)), ← `((1, 1))]

/-- Closers for one conjunct of a leaf whose definition is a universal statement or an
implication (`StrictMono f`, `∀ x ∈ l, 0 < x`, `f a ≠ f b`), tried after `leafClosers`. -/
def conjunctClosers : TacticM (Array Syntax) := do
  return #[← `(tactic| fun_prop), ← `(tactic| (intro a b h; simpa using h)),
    ← `(tactic| (intro a b h; simp)), ← `(tactic| (intro a b h; linarith)),
    ← `(tactic| (intro a b h; nlinarith)), ← `(tactic| (intro x hx; simp_all)),
    ← `(tactic| (intro x; simp)), ← `(tactic| (intro x; norm_num)), ← `(tactic| (intro x; omega))]

/-- Predicates defined by a universal statement, unfolded when a leaf conjunct is their
negation so that the counterexample can itself be searched for. -/
syntax (name := anchorNegate) "anchor_negate" : tactic

macro_rules
  | `(tactic| anchor_negate) => `(tactic| ((try simp only [StrictMono, StrictAnti, Monotone,
      Antitone, Function.Injective, Function.Surjective]); push_neg))

/-- After a type has been chosen for an existential variable: whether the next variable, when
it is an instance of a class, has one. A type without the structure the statement asks for
(`Group ℕ`) is skipped and does not count against the search width. -/
def nextInstanceAvailable : TacticM Bool := do
  let g ← getMainGoal
  g.withContext do
    let ty ← whnfR (← instantiateMVars (← g.getType))
    unless ty.isAppOfArity ``Exists 2 do return true
    let β := ty.appFn!.appArg!
    if (← isClass? β).isNone then return true
    try return (← synthInstance? β).isSome catch _ => return false

mutual

/-- Close a leaf: the goal left once every existential variable has a value. The whole goal
is tried first; then each conjunct on its own, where a negated predicate is unfolded and its
counterexample searched for. -/
partial def closeLeaf (budget : IO.Ref Nat) (width : Nat) : TacticM Unit := do
  if (← budget.get) == 0 then throwError "anchor_search: budget exhausted"
  budget.modify (· - 1)
  if ← firstClosing (← leafClosers) then return
  let g ← getMainGoal
  let rest := (← getGoals).drop 1
  setGoals [g]
  quiet (evalTactic (← `(tactic| repeat' apply And.intro)))
  for p in ← getGoals do
    setGoals [p]
    closeConjunct budget width
  setGoals rest

/-- Close one conjunct of a leaf. -/
partial def closeConjunct (budget : IO.Ref Nat) (width : Nat) : TacticM Unit := do
  let hb := anchor.search.leafHeartbeats.get (← getOptions)
  if ← firstClosing (← leafClosers) then return
  let t ← withMainContext do whnfD (← instantiateMVars (← getMainTarget))
  unless t.isForall do throwError "anchor_search: conjunct not closed"
  if ← firstClosing (← conjunctClosers) then return
  let s ← saveState
  try
    quiet (withBudget hb (evalTactic (← `(tactic| anchor_negate))))
    let t' ← whnfR (← instantiateMVars (← getMainTarget))
    if t'.isAppOfArity ``Exists 2 then
      let inner ← IO.mkRef #[]
      searchExists budget inner width
      return
  catch _ => pure ()
  s.restore
  throwError "anchor_search: conjunct not closed"

/-- The search itself. `budget` counts leaf attempts left; `chosen` records the witness;
only the first `width` candidates that elaborate are tried for each variable. -/
partial def searchExists (budget : IO.Ref Nat) (chosen : IO.Ref (Array Term)) (width : Nat) :
    TacticM Unit := do
  let g ← getMainGoal
  let ty ← whnfR (← instantiateMVars (← g.getType))
  if ty.isAppOfArity ``Exists 2 then
    let α := ty.appFn!.appArg!
    let mut tried := 0
    for cand in ← candidates α do
      if tried ≥ width then break
      if (← budget.get) == 0 then throwError "anchor_search: budget exhausted"
      let s ← saveState
      let before ← chosen.get
      try
        quiet (evalTactic (← `(tactic| refine ⟨$cand, ?_⟩)))
      catch _ =>
        s.restore
        continue
      if α.isSort && !(← nextInstanceAvailable) then
        s.restore
        continue
      tried := tried + 1
      try
        chosen.modify (·.push cand)
        searchExists budget chosen width
        return
      catch _ =>
        s.restore
        chosen.set before
    throwError "anchor_search: no witness among the candidates"
  else
    closeLeaf budget width

end

/-- Prove a universal or negated goal. -/
def searchUniversal : TacticM Unit := do
  let hb := anchor.search.leafHeartbeats.get (← getOptions)
  let s ← saveState
  try
    quiet (withBudget hb (evalTactic (← `(tactic| push_neg))))
  catch _ => s.restore
  try quiet (evalTactic (← `(tactic| intros))) catch _ => pure ()
  let ub := anchor.search.universalHeartbeats.get (← getOptions)
  if ← firstClosing (← closers) then return
  if ← firstClosing (← universalClosers) (some ub) then return
  throwError "anchor_search: no closer proved the goal"

/-- The leading existential variables of a goal `∃ x₁ … xₖ, P`, as binder names, and the
proposition `∀ x₁ … xₖ, ¬ P` whose counterexample is a witness. -/
partial def negateExists (ty : Expr) : MetaM (Array Name × Expr) := do
  let rec go (ty : Expr) (xs : Array Expr) (names : Array Name) : MetaM (Array Name × Expr) := do
    let ty ← whnfR ty
    if ty.isAppOfArity ``Exists 2 then
      match ty.appArg! with
      | .lam n t b bi =>
        withLocalDecl n bi t fun x => go (b.instantiate1 x) (xs.push x) (names.push n)
      | p =>
        let t := ty.appFn!.appArg!
        withLocalDeclD `x t fun x => go (mkApp p x) (xs.push x) (names.push `x)
    else
      return (names, ← mkForallFVars xs (mkNot ty))
  go ty #[] #[]

/-- `x := 3` lines from a Plausible counterexample report. -/
def parseCounterexample (msg : String) : List (String × String) :=
  (msg.splitOn "\n").filterMap fun line =>
    match line.trim.splitOn " := " with
    | [v, val] => if v.isEmpty || v.any (· == ' ') then none else some (v, val.trim)
    | _ => none

/-- Ask Plausible for a counterexample to `∀ xs, ¬ P` and use its values as the witness for
`∃ xs, P`. Plausible runs with a fixed seed, so the answer is the same on every run. -/
def plausibleWitness (chosen : IO.Ref (Array Term)) : TacticM Bool := do
  let hb := anchor.search.leafHeartbeats.get (← getOptions)
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let (names, neg) ← g.withContext (negateExists ty)
  if names.isEmpty then return false
  let msg : Option String ← g.withContext do
    let m ← mkFreshExprSyntheticOpaqueMVar neg
    let s ← saveState
    try
      let _ ← withBudget (hb * 4) <| Tactic.run m.mvarId! <| evalTactic (←
        `(tactic| plausible (config := { randomSeed := some 271828, numInst := 300, maxSize := 40 })))
      s.restore
      return none
    catch e =>
      let t ← e.toMessageData.toString
      s.restore
      return some t
  let some msg := msg | return false
  let vals := parseCounterexample msg
  if vals.isEmpty then return false
  let s ← saveState
  let before ← chosen.get
  try
    for n in names do
      let some (_, v) := vals.find? (·.1 == n.toString) | throwError "missing {n}"
      let some stx := (Parser.runParserCategory (← getEnv) `term v).toOption
        | throwError "could not parse {v}"
      let t : Term := ⟨stx⟩
      quiet (evalTactic (← `(tactic| refine ⟨$t, ?_⟩)))
      chosen.modify (·.push t)
    closeLeaf (← IO.mkRef 1) 0
    return true
  catch _ =>
    s.restore
    chosen.set before
    return false

/-- Run the search on the main goal and return the chosen witness terms. -/
def run : TacticM (Array Term) := do
  let budget ← IO.mkRef (anchor.search.leafBudget.get (← getOptions))
  let chosen ← IO.mkRef #[]
  let ty ← whnfR (← instantiateMVars (← getMainTarget))
  if ty.isAppOfArity ``Exists 2 then
    let s ← saveState
    let mut found := false
    let mut err : Exception := .error .missing m!"anchor_search: no witness found"
    for width in [2, 4, 8, 1000] do
      try
        searchExists budget chosen width
        found := true
        break
      catch e =>
        s.restore
        chosen.set #[]
        err := e
      if (← budget.get) == 0 then break
    unless found do
      unless ← plausibleWitness chosen do throw err
  else
    searchUniversal
  chosen.get

/-- Search for a proof of the current goal: candidate witnesses, then closing tactics. -/
syntax (name := anchorSearch) "anchor_search" : tactic

@[tactic anchorSearch] def evalAnchorSearch : Tactic := fun _ => do
  discard run

end Anchor.Synth
