import Lean

/-!
# Opaque vocabulary as parameters

A statement drafted from a paper often names objects it does not construct: `opaque Regret :
ℝ → ℝ`, `opaque AssumptionA : Instance → Prop`. Lean knows nothing about such a constant
except its type, so no witness can be built from it, and a search over the statement as written
cannot show its hypotheses can hold.

What the statement asserts about undefined vocabulary is what it asserts for every reading of
that vocabulary. `generalize` makes this explicit: each opaque constant declared outside the
trusted libraries becomes a leading universally quantified variable of its type, so
`∀ x, P x → Q x` over `opaque P Q` is analysed as `∀ (P Q : X → Prop) x, P x → Q x`. A model of
the hypotheses then includes a reading of the vocabulary, and a hypothesis is load-bearing when
some reading makes it matter.

The generalized statement implies the original (instantiate the variables at the constants),
not conversely, so a proof of the original is not a proof of it. The analysis of a generalized
statement is therefore statement-only, and the report lists the vocabulary read as parameters.

Local definitions whose bodies mention the vocabulary are unfolded first, so that every
occurrence is abstracted. If the generalized statement does not type-check (an instance
declared for an opaque type, say), the statement is analysed as written.
-/

open Lean Meta

namespace Anchor.Opaque

/-- Module prefixes whose opaque constants are library machinery, not a paper's vocabulary. -/
def libraryPrefixes : List Name :=
  [`Init, `Std, `Lean, `Lake, `Mathlib, `Batteries, `Aesop, `Qq, `Plausible, `ProofWidgets,
    `ImportGraph, `LeanSearchClient, `Anchor]

/-- Whether `c` was declared outside the trusted libraries (or in the current file). -/
def isLocal (env : Environment) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | none => true
  | some idx =>
    match env.header.moduleNames[idx.toNat]? with
    | some m => !libraryPrefixes.any (·.isPrefixOf m)
    | none => false

/-- An opaque constant read as a parameter: declared locally, not universe-polymorphic, and
not the opaque shell of a `partial` or `unsafe` definition. -/
def isVocabulary (env : Environment) (c : Name) : Bool :=
  match env.find? c with
  | some (.opaqueInfo o) =>
    o.levelParams.isEmpty && !o.isUnsafe && !env.contains (c ++ `_unsafe_rec) && isLocal env c
  | _ => false

/-- Vocabulary constants used in `e`. -/
def vocabularyIn (env : Environment) (e : Expr) : Array Name :=
  e.getUsedConstants.filter (isVocabulary env)

/-- A local, non-instance definition whose body mentions vocabulary: unfolded before
abstraction. -/
def unfoldable (env : Environment) (c : Name) : Bool :=
  match env.find? c with
  | some (.defnInfo d) =>
    isLocal env c && !isInstanceCore env c && d.levelParams.isEmpty &&
      (vocabularyIn env d.value).size > 0
  | _ => false

/-- The vocabulary of `stmt` closed under the types of its members, ordered so that each
constant's type mentions only earlier ones. -/
def orderedVocabulary (env : Environment) (stmt : Expr) : Array Name := Id.run do
  let mut found : Array Name := vocabularyIn env stmt
  let mut i := 0
  while i < found.size do
    let some ci := env.find? found[i]! | i := i + 1; continue
    for d in vocabularyIn env ci.type do
      if !found.contains d then found := found.push d
    i := i + 1
  let mut placed : Array Name := #[]
  let mut rest := found
  while !rest.isEmpty do
    let ready := rest.filter fun c =>
      match env.find? c with
      | some ci => (vocabularyIn env ci.type).all (fun d => d == c || placed.contains d)
      | none => true
    let ready := if ready.isEmpty then #[rest[0]!] else ready
    placed := placed ++ ready
    rest := rest.filter (!ready.contains ·)
  return placed

/-- Replace each constant in `cs` by the matching free variable. -/
def replaceConsts (cs : Array Name) (xs : Array Expr) (e : Expr) : Expr :=
  e.replace fun
    | .const n _ => (cs.findIdx? (· == n)).bind (xs[·]?)
    | _ => none

/-- The binder name for a vocabulary constant: its last component. -/
def binderName (c : Name) : Name :=
  match c with
  | .str _ s => Name.mkSimple s
  | _ => `v

/-- The statement with its vocabulary read as leading variables, and the vocabulary in order;
`none` when the statement has no vocabulary or the generalization does not type-check. -/
def generalize (stmt : Expr) : MetaM (Option (Expr × Array Name)) := do
  let env ← getEnv
  if (vocabularyIn env stmt).isEmpty && (stmt.getUsedConstants.all (!unfoldable env ·)) then
    return none
  let mut s := stmt
  for _ in [0:8] do
    if !s.getUsedConstants.any (unfoldable env) then break
    s ← deltaExpand s (unfoldable env)
  let cs := orderedVocabulary env s
  if cs.isEmpty then return none
  let rec go (i : Nat) (xs : Array Expr) : MetaM Expr := do
    if h : i < cs.size then
      let ty := replaceConsts cs xs (← getConstInfo cs[i]).type
      withLocalDeclD (binderName cs[i]) ty fun x => go (i + 1) (xs.push x)
    else
      mkForallFVars xs (replaceConsts cs xs s)
  try
    let g ← go 0 #[]
    check g
    unless ← isProp g do return none
    if (vocabularyIn env g).size > 0 then return none
    return some (g, cs)
  catch _ => return none

end Anchor.Opaque
