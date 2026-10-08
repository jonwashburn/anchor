import Lean
import Anchor.Core

/-!
# Extracting a statement from a declaration

`Anchor.Extract.extract` reads a proposition `∀ x₁ … xₖ, H₁ → … → Hₙ → C` and produces an
`Anchor.Spec`: the non-`Prop` binders (variables, types and instances) are packed into one
model type, the `Prop` binders become the hypothesis list, and the remainder is the
conclusion. Binders are read as written; no definition is unfolded.

The extraction is checked, not trusted. Alongside the `Spec` it builds a proof term of
`Spec.Holds S ↔ stmt`, which the kernel checks when it is added to the environment, so the
encoding provably says exactly what the original statement says.

A `Prop` binder that a later binder or the conclusion mentions (an instance argument such as
`[IsDomain R]` used by the conclusion's own instances, or `(h : 0 < n)` in
`(⟨0, h⟩ : Fin n).val = 0`) cannot be removed or negated on its own. It is kept in the model
as a premise, wrapped in `PLift`, and is not tested; the report lists it.
-/

open Lean Meta

namespace Anchor.Extract

/-- Why a statement falls outside what the extractor handles. -/
inductive Unsupported where
  | notAProp
  | dependent (what : String)
  deriving Inhabited

/-- One line of explanation for an unsupported statement. -/
def Unsupported.describe : Unsupported → String
  | .notAProp => "the statement is not a proposition"
  | .dependent w => s!"dependent hypothesis: {w}"

/-- One binder of the statement as the reader wrote it. -/
structure BinderView where
  name : Name
  type : Format
  isHyp : Bool
  /-- A `Prop` binder kept in the model because the rest of the statement mentions it. -/
  premise : Bool := false

/-- The extracted statement, as closed terms. -/
structure Extracted where
  /-- `M : Type level`. -/
  level : Level
  modelType : Expr
  /-- Closed terms of type `M → Prop`, in binder order. -/
  hyps : Array Expr
  /-- Closed term of type `M → Prop`. -/
  concl : Expr
  /-- Closed term of type `Anchor.Spec M`. -/
  spec : Expr
  /-- The original statement. -/
  stmt : Expr
  /-- Closed proof of `Anchor.Spec.Holds spec ↔ stmt`. -/
  iffProof : Expr
  binders : Array BinderView
  conclView : Format

/-- The component type of a model binder, and whether it is a premise: a `Prop` binder is
wrapped in `PLift` so that every component is a type. -/
private def component (x : Expr) : MetaM (Expr × Bool) := do
  let t ← inferType x
  if ← isProp t then return (← mkAppM ``PLift #[t], true) else return (t, false)

/-- The family `fun y => body` over the component type `a` of binder `x`. For a premise the
body reads `x` as `y.down`. -/
private def family (x a body : Expr) : MetaM Expr := do
  if ← isProp (← inferType x) then
    withLocalDeclD `y a fun y => do
      mkLambdaFVars #[y] (body.replaceFVar x (← mkAppM ``PLift.down #[y]))
  else mkLambdaFVars #[x] body

/-- The nested `Sigma` type packing the model binders, built from the right. Returns the
closed type and its universe level `u` with `M : Type u`. -/
private def modelType (models : Array Expr) : MetaM (Expr × Level) := do
  if models.isEmpty then
    return (mkConst ``Unit, levelZero)
  let mut inner := (← component models[models.size - 1]!).1
  let mut i := models.size - 1
  while i > 0 do
    i := i - 1
    let x := models[i]!
    let (a, _) ← component x
    let u ← getDecLevel a
    let v ← getDecLevel inner
    inner := mkApp2 (mkConst ``Sigma [u, v]) a (← family x a inner)
  let lvl ← getDecLevel inner
  return (inner, lvl)

/-- The projections of a model `m` onto the individual model binders `models` (premises
through `PLift.down`). -/
private def projections (models : Array Expr) (m : Expr) : MetaM (Array Expr) := do
  let k := models.size
  if k == 0 then return #[]
  let mut raw := #[]
  let mut cur := m
  for _ in [0:k-1] do
    raw := raw.push (← mkAppM ``Sigma.fst #[cur])
    cur ← mkAppM ``Sigma.snd #[cur]
  raw := raw.push cur
  let mut out := #[]
  for x in models, p in raw do
    out := out.push (← if ← isProp (← inferType x) then mkAppM ``PLift.down #[p] else pure p)
  return out

/-- The model tuple built from the model binders themselves, matching `modelType`. -/
private def tuple (models : Array Expr) : MetaM Expr := do
  if models.isEmpty then return mkConst ``Unit.unit
  let last := models[models.size - 1]!
  let (lastA, lastP) ← component last
  let mut acc ← (if lastP then mkAppM ``PLift.up #[last] else pure last)
  let mut inner := lastA
  let mut i := models.size - 1
  while i > 0 do
    i := i - 1
    let x := models[i]!
    let (a, isP) ← component x
    let u ← getDecLevel a
    let v ← getDecLevel inner
    let fam ← family x a inner
    let xv ← (if isP then mkAppM ``PLift.up #[x] else pure x)
    acc := mkApp4 (mkConst ``Sigma.mk [u, v]) a fam xv acc
    inner := mkApp2 (mkConst ``Sigma [u, v]) a fam
  return acc

/-- `AllHold l m` for a list given by its elements. -/
def allHoldTerm (lvl : Level) (M : Expr) (ps : List Expr) (m : Expr) : MetaM Expr := do
  let l ← mkListLit (← mkArrow M (mkSort levelZero)) ps
  return mkApp3 (mkConst ``Anchor.AllHold [lvl]) M l m

/-- `AllExcept l k m` for a list given by its elements. -/
def allExceptTerm (lvl : Level) (M : Expr) (ps : List Expr) (k : Nat) (m : Expr) :
    MetaM Expr := do
  let l ← mkListLit (← mkArrow M (mkSort levelZero)) ps
  return mkApp4 (mkConst ``Anchor.AllExcept [lvl]) M l (mkNatLit k) m

/-- From `h : AllHold ps m`, a proof of `p m` for each `p` in `ps`. -/
partial def allHoldProjs (lvl : Level) (M : Expr) (ps : List Expr) (m h : Expr) :
    MetaM (Array Expr) := do
  match ps with
  | [] => return #[]
  | p :: rest =>
    let a := mkApp p m
    let b ← allHoldTerm lvl M rest m
    let left := mkApp3 (mkConst ``And.left) a b h
    let right := mkApp3 (mkConst ``And.right) a b h
    return #[left] ++ (← allHoldProjs lvl M rest m right)

/-- From `h : AllExcept ps k m`, a proof of `p m` for each `p` in `ps` other than the one at
position `k` (`none` there). -/
partial def allExceptProjs (lvl : Level) (M : Expr) (ps : List Expr) (k : Nat) (m h : Expr) :
    MetaM (Array (Option Expr)) := do
  match ps, k with
  | [], _ => return #[]
  | _ :: rest, 0 => return #[none] ++ (← allHoldProjs lvl M rest m h).map some
  | p :: rest, k + 1 =>
    let a := mkApp p m
    let b ← allExceptTerm lvl M rest k m
    let left := mkApp3 (mkConst ``And.left) a b h
    let right := mkApp3 (mkConst ``And.right) a b h
    return #[some left] ++ (← allExceptProjs lvl M rest k m right)

/-- A proof of `AllHold ps t` from proofs of each `p t`, given as the original hypotheses. -/
private def allHoldIntro (lvl : Level) (M : Expr) (ps : List Expr) (t : Expr)
    (proofs : List Expr) : MetaM Expr := do
  match ps, proofs with
  | p :: rest, pr :: prs =>
    let a := mkApp p t
    let b ← allHoldTerm lvl M rest t
    return mkApp4 (mkConst ``And.intro) a b pr (← allHoldIntro lvl M rest t prs)
  | _, _ => return mkConst ``True.intro

/-- Read a proposition as an `Anchor.Spec`, with a proof that the encoding is faithful. -/
def extract (stmt : Expr) : MetaM (Except Unsupported Extracted) := do
  let stmt ← instantiateMVars stmt
  unless ← isProp stmt do return .error .notAProp
  forallTelescope stmt fun xs body => do
    let body ← instantiateMVars body
    let types ← xs.mapM fun x => do instantiateMVars (← inferType x)
    let mut models : Array Expr := #[]
    let mut hyps : Array Expr := #[]
    let mut views : Array BinderView := #[]
    for x in xs, t in types do
      let id := x.fvarId!
      let premise := (← isProp t) && (body.containsFVar id || types.any (·.containsFVar id))
      let isHyp := (← isProp t) && !premise
      if isHyp then hyps := hyps.push x else models := models.push x
      views := views.push
        { name := (← x.fvarId!.getDecl).userName.eraseMacroScopes, type := ← ppExpr t, isHyp,
          premise }
    let (M, lvl) ← modelType models
    let (hypCs, conclC) ← withLocalDeclD `m M fun m => do
      let projs ← projections models m
      let hs ← hyps.mapM fun h => do
        mkLambdaFVars #[m] ((← inferType h).replaceFVars models projs)
      let c ← mkLambdaFVars #[m] (body.replaceFVars models projs)
      return (hs, c)
    let predTy ← mkArrow M (mkSort levelZero)
    let hypList ← mkListLit predTy hypCs.toList
    let spec := mkApp3 (mkConst ``Anchor.Spec.mk [lvl]) M hypList conclC
    let holdsTy := mkApp2 (mkConst ``Anchor.Spec.Holds [lvl]) M spec
    -- Holds → stmt: rebuild the model and the hypothesis chain from the original binders.
    let mp ← withLocalDeclD `hs holdsTy fun hs => do
      let t ← tuple models
      let chain ← allHoldIntro lvl M hypCs.toList t hyps.toList
      mkLambdaFVars #[hs] (← mkLambdaFVars xs (mkApp2 hs t chain))
    -- stmt → Holds: apply the statement to the projections and the hypothesis chain.
    let mpr ← withLocalDeclD `st stmt fun st => do
      withLocalDeclD `m M fun m => do
        let hallTy ← allHoldTerm lvl M hypCs.toList m
        withLocalDeclD `hall hallTy fun hall => do
          let projs ← projections models m
          let hps ← allHoldProjs lvl M hypCs.toList m hall
          let mut args := #[]
          let mut mi := 0
          let mut hi := 0
          for v in views do
            if v.isHyp then
              args := args.push hps[hi]!
              hi := hi + 1
            else
              args := args.push projs[mi]!
              mi := mi + 1
          mkLambdaFVars #[st, m, hall] (mkAppN st args)
    let iffProof := mkApp4 (mkConst ``Iff.intro) holdsTy stmt mp mpr
    return .ok {
      level := lvl, modelType := M, hyps := hypCs, concl := conclC, spec, stmt, iffProof,
      binders := views, conclView := ← ppExpr body }

/-- A proof of `Drop k` read off the declaration's own proof term, when that term is a
lambda over every binder whose body never uses hypothesis `k`. -/
def dropFromProof? (e : Extracted) (value : Expr) (k : Nat) : MetaM (Option Expr) := do
  let n := e.binders.size
  lambdaBoundedTelescope value n fun ys body => do
    if ys.size != n then return none
    let mut hypVars := #[]
    let mut modelVars := #[]
    for y in ys, v in e.binders do
      if v.isHyp then hypVars := hypVars.push y else modelVars := modelVars.push y
    let some hk := hypVars[k]? | return none
    let body ← instantiateMVars body
    if body.containsFVar hk.fvarId! then return none
    for y in ys do
      if (← instantiateMVars (← inferType y)).containsFVar hk.fvarId! then return none
    let M := e.modelType
    let lvl := e.level
    let dropTy := mkApp3 (mkConst ``Anchor.Spec.Drop [lvl]) M e.spec (mkNatLit k)
    let proof ← withLocalDeclD `m M fun m => do
      let hTy ← allExceptTerm lvl M e.hyps.toList k m
      withLocalDeclD `h hTy fun h => do
        let projs ← projections modelVars m
        let hps ← allExceptProjs lvl M e.hyps.toList k m h
        let mut subVars := #[]
        let mut subVals := #[]
        for y in modelVars, p in projs do
          subVars := subVars.push y
          subVals := subVals.push p
        for y in hypVars, p? in hps do
          if let some p := p? then
            subVars := subVars.push y
            subVals := subVals.push p
        mkLambdaFVars #[m, h] (body.replaceFVars subVars subVals)
    try
      check proof
      if ← isDefEq (← inferType proof) dropTy then return some proof else return none
    catch _ => return none

end Anchor.Extract
