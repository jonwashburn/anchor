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
not conversely, so a proof of the original is not by itself a proof of it. The proof is carried
over only when, with the same constants abstracted, it type-checks against the generalized
statement; otherwise the analysis is statement-only. The report lists the vocabulary read as
parameters.

Local definitions that reach the vocabulary, directly or through other local definitions, are
unfolded first, so that every occurrence is abstracted. The statement is analysed as written
when an axiom outside the trusted libraries mentions the vocabulary (the vocabulary is then
constrained, not free for every reading), or when the generalized statement does not
type-check (an instance declared for an opaque type, say).
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

/-- A local, non-instance, universe-monomorphic definition whose body reaches vocabulary,
directly or through other such definitions (followed to depth `fuel`): unfolded before
abstraction. -/
def unfoldableAt (env : Environment) : Nat → Name → Bool
  | 0, _ => false
  | fuel + 1, c =>
    match env.find? c with
    | some (.defnInfo d) =>
      isLocal env c && !isInstanceCore env c && d.levelParams.isEmpty &&
        d.value.getUsedConstants.any fun e =>
          isVocabulary env e || (e != c && unfoldableAt env fuel e)
    | _ => false

def unfoldable (env : Environment) (c : Name) : Bool := unfoldableAt env 16 c

/-- A constant that is vocabulary or reaches it through a local definition. -/
def reachesVocabulary (env : Environment) (c : Name) : Bool :=
  isVocabulary env c || (env.find? c matches some (.defnInfo _) && isLocal env c &&
    (env.find? c).any fun ci => ci.value?.any fun v =>
      v.getUsedConstants.any fun e => isVocabulary env e || unfoldable env e)

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

/-- Axioms declared outside the trusted libraries whose statements reach a member of `cs`,
directly or through local definitions. While one exists, that vocabulary is constrained and is
not free for every reading. -/
def constrainingAxioms (cs : Array Name) : MetaM (Array Name) := do
  let env ← getEnv
  let candidate (n : Name) : Option Expr :=
    match env.find? n with
    | some (.axiomInfo a) =>
      if a.type.getUsedConstants.any (reachesVocabulary env) then some a.type else none
    | _ => none
  let mut names : Array Name := #[]
  for h : i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]
    if libraryPrefixes.any (·.isPrefixOf m) then continue
    names := names ++ ((env.header.moduleData[i]?.map (·.constNames)).getD #[])
  for (n, _) in env.constants.map₂.toList do
    names := names.push n
  let mut out : Array Name := #[]
  for n in names do
    let some t := candidate n | continue
    let mut t' := t
    for _ in [0:32] do
      if !t'.getUsedConstants.any (unfoldable env) then break
      t' ← deltaExpand t' (unfoldable env)
    if (orderedVocabulary env t').any cs.contains then out := out.push n
  return out

/-- Replace each constant in `cs` by the matching free variable. -/
def replaceConsts (cs : Array Name) (xs : Array Expr) (e : Expr) : Expr :=
  e.replace fun
    | .const n _ => (cs.findIdx? (· == n)).bind (xs[·]?)
    | _ => none

/-- Binder names declared in `e`, searched to depth `fuel`. -/
def bindersIn : Nat → Expr → Array Name → Array Name
  | 0, _, acc => acc
  | fuel + 1, e, acc =>
    match e with
    | .forallE n t b _ | .lam n t b _ => bindersIn fuel b (bindersIn fuel t (acc.push n))
    | .letE n t v b _ => bindersIn fuel b (bindersIn fuel v (bindersIn fuel t (acc.push n)))
    | .app f a => bindersIn fuel a (bindersIn fuel f acc)
    | .mdata _ b | .proj _ _ b => bindersIn fuel b acc
    | _ => acc

/-- The binder name for each vocabulary constant: its last component, or its full name when
the last component is shared with another constant or with a binder of the statement. -/
def binderNames (cs : Array Name) (stmt : Expr) : Array Name :=
  let short (c : Name) : Name := match c with
    | .str _ s => Name.mkSimple s
    | _ => c
  let taken := bindersIn 256 stmt #[]
  cs.map fun c =>
    let s := short c
    if taken.contains s || (cs.filter (short · == s)).size > 1 then c else s

/-- The statement with its vocabulary read as leading variables, the vocabulary in order, and
the proof carried over when one is given and type-checks for every reading. `none` when the
statement has no vocabulary, when an axiom constrains the vocabulary, or when the
generalization does not type-check. -/
def generalize (stmt : Expr) (proof? : Option Expr := none) :
    MetaM (Option (Expr × Array Name × Option Expr)) := do
  let env ← getEnv
  if !stmt.getUsedConstants.any (reachesVocabulary env) then return none
  let expand (e : Expr) : MetaM Expr := do
    let mut s := e
    for _ in [0:32] do
      if !s.getUsedConstants.any (unfoldable env) then break
      s ← deltaExpand s (unfoldable env)
    return s
  let s ← expand stmt
  let cs := orderedVocabulary env s
  if cs.isEmpty then return none
  unless (← constrainingAxioms cs).isEmpty do return none
  let names := binderNames cs s
  let rec go (i : Nat) (xs : Array Expr) : MetaM (Expr × Option Expr) := do
    if h : i < cs.size then
      let ty := replaceConsts cs xs (← getConstInfo cs[i]).type
      withLocalDeclD names[i]! ty fun x => go (i + 1) (xs.push x)
    else
      let g ← mkForallFVars xs (replaceConsts cs xs s)
      let p? ← match proof? with
        | none => pure none
        | some p => do
          try
            let p' ← mkLambdaFVars xs (replaceConsts cs xs (← expand p))
            if (p'.getUsedConstants.any (reachesVocabulary env)) then return (g, none)
            let ty ← inferType p'
            check p'
            if ← isDefEq ty g then pure (some p') else pure none
          catch _ => pure none
      return (g, p?)
  try
    let (g, p?) ← go 0 #[]
    check g
    unless ← isProp g do return none
    if g.getUsedConstants.any (reachesVocabulary env) then return none
    return some (g, cs, p?)
  catch _ => return none

end Anchor.Opaque
