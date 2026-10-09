import Anchor.Extract
import Anchor.Synth
import Anchor.Opaque

/-!
# `#anchor` and `anchor_cert`

`#anchor foo` reads the statement of `foo`, lists its model, hypotheses and conclusion, and
reports for each obligation whether a proof was found and how:

* a model of all the hypotheses (`Nonvacuous`), or else a proof that there is none
  (`Vacuous`);
* for each hypothesis, a model where the others hold and it and the conclusion fail
  (`LoadBearing`), or else a proof that the statement survives without it (`Drop`);
* the verdict: `CERTIFIED`, `VACUOUS`, `DECORATIVE`, `NO HYPOTHESES`, `UNSUPPORTED`,
  or `UNCERTIFIED` with the open obligations named.

`anchor_cert foo` does the same and keeps the declarations in the environment:
`foo.anchorSpec`, `foo.anchorSpec_iff` (the extraction is faithful), `foo.anchorSpec_holds`,
and `foo.anchorCertificate`, `foo.anchorVacuous` or `foo.anchorDrop_k` as found. Every one
of them is checked by the kernel when it is added. A proof written by hand under one of the
obligation names (`foo.anchorNonvacuous`, `foo.anchorLoadBearing_k`, `foo.anchorVacuous`,
`foo.anchorDrop_k`) after `anchor_spec foo` is used instead of the search.

A declaration whose proof contains `sorryAx` directly, or a definition whose value is a
proposition, is read as a statement only: the report covers the statement's hypotheses and
makes no claim that it holds. A definition of a family of propositions,
`def foo (x : α) : Prop := body`, states `∀ x, body`. A statement that names opaque constants
declared outside the trusted libraries is analysed with that vocabulary read as parameters
(`Anchor.Opaque.generalize`), also as a statement only, and the report lists them.
-/

open Lean Meta Elab Command Term Tactic

namespace Anchor

register_option anchor.json : Bool := {
  defValue := false
  descr := "anchor_cert reports as one line of JSON instead of text" }

register_option anchor.readFamilies : Bool := {
  defValue := false
  descr := "read `def foo (x : α) : Prop := body` as the claim `∀ x, body`" }

/-- What happened to one obligation. -/
inductive Outcome where
  | proved (method : String) (detail : String)
  | notFound (goal : String)
  | skipped
  deriving Inhabited

/-- The obligation was discharged with a kernel-checked proof. -/
def Outcome.isProved : Outcome → Bool
  | .proved .. => true
  | _ => false

/-- A proof that was supplied or found and then refused; the report shows its reason. -/
def Outcome.isRefusal : Outcome → Bool
  | .notFound g => g.startsWith "supplied proof rejected" || g.startsWith "the proof found rests on"
  | _ => false

def Outcome.toJson : Outcome → Json
  | .proved m d => Json.mkObj [("status", Json.str "proved"), ("method", Json.str m),
      ("detail", Json.str d)]
  | .notFound g => Json.mkObj [("status", Json.str "open"), ("goal", Json.str g)]
  | .skipped => Json.mkObj [("status", Json.str "skipped")]

def Outcome.render : Outcome → String
  | .proved m d => if d.isEmpty then s!"proved ({m})" else s!"proved ({m}: {d})"
  | .notFound g => s!"open: {g}"
  | .skipped => "not attempted"

/-- The report for one hypothesis. -/
structure HypReport where
  text : String
  loadBearing : Outcome := .skipped
  drop : Outcome := .skipped
  deriving Inhabited

/-- The full report for one declaration. -/
structure Report where
  decl : Name
  supported : Bool := true
  reason : String := ""
  /-- The universe levels the statement is analysed at, when it has parameters. -/
  universes : String := ""
  model : Array String := #[]
  /-- `Prop` arguments kept in the model because the statement depends on them; untested. -/
  premises : Array String := #[]
  /-- Opaque constants read as universally quantified parameters. -/
  parameters : Array String := #[]
  hyps : Array HypReport := #[]
  conclusion : String := ""
  holds : String := ""
  nonvacuous : Outcome := .skipped
  vacuous : Outcome := .skipped
  trivial : Outcome := .skipped
  verdict : String := ""
  /-- Declarations added and the axioms each depends on. -/
  axioms : Array (Name × Array Name) := #[]
  deriving Inhabited

def Report.toJson (r : Report) : Json :=
  Json.mkObj [
    ("decl", Json.str (toString r.decl)), ("supported", Json.bool r.supported),
    ("reason", Json.str r.reason), ("universes", Json.str r.universes),
    ("model", Json.arr (r.model.map Json.str)),
    ("premises", Json.arr (r.premises.map Json.str)),
    ("parameters", Json.arr (r.parameters.map Json.str)),
    ("hypotheses", Json.arr (r.hyps.map fun h => Json.mkObj [
      ("text", Json.str h.text), ("load_bearing", h.loadBearing.toJson),
      ("drop", h.drop.toJson)])),
    ("conclusion", Json.str r.conclusion), ("holds", Json.str r.holds),
    ("nonvacuous", r.nonvacuous.toJson), ("vacuous", r.vacuous.toJson),
    ("trivial_conclusion", r.trivial.toJson), ("verdict", Json.str r.verdict),
    ("axioms", Json.arr (r.axioms.map fun (n, as) => Json.mkObj [
      ("decl", Json.str (toString n)), ("axioms", Json.arr (as.map (Json.str ∘ toString)))]))]

def Report.render (r : Report) : String := Id.run do
  let mut out := s!"anchor: {r.decl}\n"
  if !r.supported then
    return out ++ s!"  verdict: UNSUPPORTED ({r.reason})\n"
  if !r.universes.isEmpty then
    out := out ++ s!"  universes: {r.universes}\n"
  if !r.parameters.isEmpty then
    out := out ++ s!"  opaque vocabulary read as parameters: {" ".intercalate r.parameters.toList}\n"
  out := out ++ s!"  model: {if r.model.isEmpty then "(none)" else " ".intercalate r.model.toList}\n"
  if !r.premises.isEmpty then
    out := out ++ s!"  premises in the model (untested): {" ".intercalate r.premises.toList}\n"
  out := out ++ "  hypotheses:\n"
  if r.hyps.isEmpty then out := out ++ "    (none)\n"
  for h in r.hyps, i in [0:r.hyps.size] do
    out := out ++ s!"    [{i}] {h.text}\n"
  out := out ++ s!"  conclusion: {r.conclusion}\n"
  out := out ++ s!"  holds: {r.holds}\n"
  if r.vacuous.isProved then
    out := out ++ s!"  vacuous: {r.vacuous.render}\n"
  else
    if r.vacuous.isRefusal then
      out := out ++ s!"  vacuous: {r.vacuous.render}\n"
    out := out ++ s!"  nonvacuous: {r.nonvacuous.render}\n"
  for h in r.hyps, i in [0:r.hyps.size] do
    if h.drop.isProved then
      out := out ++ s!"  hypothesis [{i}] removable: {h.drop.render}\n"
    else
      if h.drop.isRefusal then
        out := out ++ s!"  hypothesis [{i}] removable: {h.drop.render}\n"
      out := out ++ s!"  hypothesis [{i}] load-bearing: {h.loadBearing.render}\n"
  if let .skipped := r.trivial then pure () else
    out := out ++ s!"  conclusion holds outright: {r.trivial.render}\n"
  out := out ++ s!"  verdict: {r.verdict}\n"
  return out

/-- Rename the leading binders of an unfolded obligation to the reader's variable names, in
order. The model's variables come before every hypothesis arrow, and the unfolding keeps one
binder per variable (`anchor_unfold_names`; existential goals under `anchor_unfold`), so the
first binders are exactly the variables, whether or not the rest of the goal mentions them. -/
partial def renameBinders (e : Expr) (names : List Name) : Expr :=
  match names with
  | [] => e
  | n :: ns =>
    match e with
    | .app (.app (.const ``Exists us) α) (.lam _ t b bi) =>
      mkApp2 (.const ``Exists us) α (.lam n t (renameBinders b ns) bi)
    | .forallE _ t b bi => .forallE n t (renameBinders b ns) bi
    | .app (.const ``Not us) a => .app (.const ``Not us) (renameBinders a names)
    | _ => e

/-- `x := 1, y := -1` from the model names and the chosen witnesses. Candidate terms are
built by syntax quotation, so the printer marks their global constants as hygienic (`Rat✝`);
the mark is dropped here. -/
def witnessText (names : List Name) (w : Array String) : String :=
  ", ".intercalate ((names.zip w.toList).map fun (x, v) => s!"{x} := {v.replace "✝" ""}")

/-- A proof found for an obligation, with the readable goal and the chosen witness. -/
structure Found where
  proof : Expr
  witness : Array String

/-- Try to prove `goalTy` with `anchor_unfold` and the witness search. Returns the readable
goal whether or not a proof was found. -/
def attemptCore (goalTy : Expr) (names : List Name) : TermElabM (Option Found × String) := do
  let goalText ← IO.mkRef (toString (← ppExpr goalTy))
  let msgs := (← getThe Core.State).messages
  let saved ← saveState
  let mvar ← mkFreshExprSyntheticOpaqueMVar goalTy
  let res ← tryCatchRuntimeEx (do
      let wit ← IO.mkRef (#[] : Array String)
      let gs ← Tactic.run mvar.mvarId! do
        let s ← saveState
        try
          evalTactic (← `(tactic| anchor_unfold_names))
          let t ← instantiateMVars (← (← getMainGoal).getType)
          goalText.set (toString (← ppExpr (renameBinders t names)))
        catch _ => pure ()
        s.restore
        evalTactic (← `(tactic| anchor_unfold))
        if (← getUnsolvedGoals).isEmpty then return
        let g ← getMainGoal
        let t ← instantiateMVars (← g.getType)
        let g' ← g.replaceTargetDefEq (renameBinders t names)
        replaceMainGoal [g']
        let w ← Synth.run
        wit.set (← w.mapM fun s => return toString (← PrettyPrinter.ppTerm s))
      if !gs.isEmpty then
        saved.restore
        return none
      let pf ← instantiateMVars mvar
      if pf.hasMVar || pf.hasSorry then
        saved.restore
        return none
      return some { proof := pf, witness := ← wit.get })
    (fun _ => do saved.restore; return none)
  modifyThe Core.State fun st => { st with messages := msgs }
  return (res, ← goalText.get)

/-- `attemptCore` with its own heartbeat window, so the obligations of one command do not
share a single limit. -/
def attempt (goalTy : Expr) (names : List Name) : TermElabM (Option Found × String) := do
  let start ← IO.getNumHeartbeats
  let cap := Synth.anchor.search.attemptHeartbeats.get (← getOptions) * 1000
  withTheReader Core.Context (fun ctx => { ctx with initHeartbeats := start, maxHeartbeats := cap })
    (attemptCore goalTy names)

/-- The axioms a proof Anchor reports may rest on. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The declarations' axioms, for the report and the receipts. -/
def axiomsOf (n : Name) : CoreM (Array Name) := do
  let as ← collectAxioms n
  return as.qsort (·.toString < ·.toString)

/-- The universe levels at which a declaration is analysed: `1` for a parameter that appears
as a bare `Sort u` (so that binder ranges over types), `0` for every other. Witnesses such as
`ℕ` live in `Type`, so an obligation over `Type u` is checked at `Type`; the report states
the levels. -/
def analysisLevels (info : ConstantInfo) : List Level :=
  info.levelParams.map fun u =>
    if (info.type.find? (· == .sort (.param u))).isSome then levelOne else levelZero

/-- `u := 0, v := 1`, for the report. -/
def levelsText (info : ConstantInfo) : String :=
  ", ".intercalate ((info.levelParams.zip (analysisLevels info)).map fun (u, l) =>
    s!"{u} := {l}")

/-- Read the statement a declaration makes, at `analysisLevels`: its type, or its value for
a definition of a proposition. The second component says whether a proof of it is
available. -/
def statementOf (c : Name) : MetaM (Expr × Option Expr) := do
  let info ← getConstInfo c
  let us := analysisLevels info
  let inst (e : Expr) := e.instantiateLevelParams info.levelParams us
  match info with
  | .thmInfo t =>
    let usesSorry := (t.value.find? (·.isConstOf ``sorryAx)).isSome
    return (inst t.type, if usesSorry then none else some (Lean.mkConst c us))
  | .defnInfo d =>
    if (← isProp d.type) then
      let usesSorry := (d.value.find? (·.isConstOf ``sorryAx)).isSome
      return (inst d.type, if usesSorry then none else some (Lean.mkConst c us))
    if d.type.isProp then return (inst d.value, none)
    unless anchor.readFamilies.get (← getOptions) do return (inst d.type, none)
    let family ← forallTelescope (inst d.type) fun xs cod => do
      if cod.isProp then
        return some (← mkForallFVars xs (mkAppN (inst d.value) xs).headBeta)
      return none
    if let some s := family then return (s, none)
    return (inst d.type, none)
  | i => return (inst i.type, none)

/-- `statementOf`, with opaque vocabulary read as parameters when the statement has any. The
third component lists that vocabulary; the fourth is the proof term the hypotheses are read
from. A proof is kept only when it carries over to the generalized statement. -/
def readStatement (c : Name) : MetaM (Expr × Option Expr × Array Name × Option Expr) := do
  let (stmt, proof?) ← statementOf c
  let info ← getConstInfo c
  let value? := match proof?, info.value? with
    | some _, some v => some (v.instantiateLevelParams info.levelParams (analysisLevels info))
    | _, _ => none
  match ← Opaque.generalize stmt value? with
  | some (g, cs, p?) => return (g, p?, cs, p?)
  | none => return (stmt, proof?, #[], value?)

/-- Add a theorem to the environment; the kernel checks it here. -/
def addThm (name : Name) (lps : List Name) (type value : Expr) : TermElabM Unit := do
  addDecl (.thmDecl { name, levelParams := lps, type, value })

/-- Analyse `c`, adding the extraction and every proof found to the environment. -/
def analyze (c : Name) : TermElabM Report := do
  let info ← getConstInfo c
  let lps : List Name := []
  let lvls : List Level := []
  let (stmt, proof?, vocab, proofValue?) ← readStatement c
  let mut r : Report :=
    { decl := c, universes := levelsText info, parameters := vocab.map toString }
  let res ← Extract.extract stmt
  let .ok e := res
    | let why := match res with | .error u => u.describe | .ok _ => ""
      return { r with supported := false, reason := why, verdict := "UNSUPPORTED" }
  r := { r with
    model := (e.binders.filter (!·.isHyp)).map fun b => s!"({b.name} : {b.type})"
    premises := (e.binders.filter (·.premise)).map fun b => s!"({b.name} : {b.type})"
    hyps := (e.binders.filter (·.isHyp)).map fun b => { text := toString b.type }
    conclusion := toString e.conclView }
  let modelNames := ((e.binders.filter (!·.isHyp)).map (·.name)).toList
  let M := e.modelType
  let lvl := e.level
  let specName := c ++ `anchorSpec
  let specTy := mkApp (Lean.mkConst ``Anchor.Spec [lvl]) M
  if !(← getEnv).contains specName then
    addDecl <| .defnDecl
      { name := specName, levelParams := lps, type := specTy, value := e.spec
        hints := .abbrev, safety := .safe }
  let specC := Lean.mkConst specName lvls
  let holdsTy := mkApp2 (Lean.mkConst ``Anchor.Spec.Holds [lvl]) M specC
  let iffName := c ++ `anchorSpec_iff
  if !(← getEnv).contains iffName then
    addThm iffName lps (mkApp2 (Lean.mkConst ``Iff) holdsTy stmt) e.iffProof
  let mut added : Array Name := #[iffName]
  let mut holdsC : Option Expr := none
  match proof? with
  | some pc =>
    let holdsName := c ++ `anchorSpec_holds
    if !(← getEnv).contains holdsName then
      addThm holdsName lps holdsTy
        (mkApp4 (Lean.mkConst ``Iff.mpr) holdsTy stmt (Lean.mkConst iffName lvls) pc)
    holdsC := some (Lean.mkConst holdsName lvls)
    added := added.push holdsName
    r := { r with holds := s!"from the proof of {c}" }
  | none => r := { r with holds :=
      if vocab.isEmpty then "statement only: no proof is read"
      else "statement only: opaque vocabulary read as parameters" }
  if !vocab.isEmpty && proof?.isSome then
    r := { r with holds := s!"from the proof of {c}, with opaque vocabulary read as parameters" }
  let n := e.hyps.size
  let ob (head : Name) (args : Array Expr) (onLit : Bool) : Expr :=
    mkAppN (Lean.mkConst head [lvl]) (#[M, if onLit then e.spec else specC] ++ args)
  -- A proof Anchor finds counts only when it rests on the standard axioms. A search that
  -- closes a goal with a library lemma proved by `native_decide` adds its theorem, but the
  -- obligation stays open with the reason.
  let nonstandard (n : Name) : TermElabM (List Name) := do
    return ((← axiomsOf n).filter (!standardAxioms.contains ·)).toList
  let record (nm : Name) (ty : Expr) (f : Found) : TermElabM (Except String Expr) := do
    addThm (c ++ nm) lps ty f.proof
    let bad ← nonstandard (c ++ nm)
    if bad.isEmpty then return .ok (Lean.mkConst (c ++ nm) lvls)
    return .error s!"the proof found rests on {bad}"
  -- A conclusion true of every model: every hypothesis is removable at once.
  let conclAt (s : Expr) : TermElabM Expr := withLocalDeclD `m M fun m =>
    mkForallFVars #[m] (mkApp (mkApp2 (Lean.mkConst ``Anchor.Spec.concl [lvl]) M s) m)
  if n == 0 then
    -- With no hypothesis there is nothing to certify. A statement read without a proof and
    -- without premises whose conclusion holds outright (`True`, or a definition that unfolds
    -- to it) says nothing, and that is a finding. A theorem with a proof holds outright by
    -- its proof, which is no finding.
    r := { r with verdict := "NO HYPOTHESES (no certificate)" }
    unless proof?.isNone && e.binders.all (!·.premise) do
      return { r with axioms := ← added.mapM fun d => return (d, ← axiomsOf d) }
    let (tf?, tg) ← attempt (← conclAt e.spec) modelNames
    r := { r with trivial := .notFound tg }
    if let some f := tf? then
      match ← record `anchorTrivial (← conclAt specC) f with
      | .ok _ =>
        added := added.push (c ++ `anchorTrivial)
        r := { r with trivial := .proved "search" "",
                      verdict := "TRIVIAL CONCLUSION (true outright, with no hypotheses)" }
      | .error why => r := { r with trivial := .notFound why }
    return { r with axioms := ← added.mapM fun d => return (d, ← axiomsOf d) }
  -- A proof supplied under the obligation's name is used first. It must have the obligation
  -- as its type and rest on the standard axioms only; otherwise the obligation stays open,
  -- with the reason, and nothing else is tried under that name.
  let supplied (nm : Name) (ty : Expr) : TermElabM (Option (Except String Expr)) := do
    let some ci := (← getEnv).find? (c ++ nm) | return none
    if !ci.levelParams.isEmpty then return some (.error "universe-polymorphic")
    if !(← isDefEq ci.type ty) then return some (.error "its type is not the obligation")
    let bad := (← axiomsOf (c ++ nm)).filter (!standardAxioms.contains ·)
    if !bad.isEmpty then return some (.error s!"rests on {bad.toList}")
    return some (.ok (Lean.mkConst (c ++ nm) lvls))
  let rejected (why : String) : Outcome := .notFound s!"supplied proof rejected: {why}"
  -- Vacuous, else Nonvacuous. As with each hypothesis below, the two exclude each other and
  -- the cheap universal attempt goes before the existential search.
  let nvTy := ob ``Anchor.Spec.Nonvacuous #[] false
  let vTy := ob ``Anchor.Spec.Vacuous #[] false
  let mut nvC : Option Expr := none
  let mut vacuous := false
  let nvSup ← supplied `anchorNonvacuous nvTy
  let vSup ← supplied `anchorVacuous vTy
  if let some (.ok p) := nvSup then
    nvC := some p
    added := added.push (c ++ `anchorNonvacuous)
    r := { r with nonvacuous := .proved "supplied" s!"{c ++ `anchorNonvacuous}" }
  else if let some (.ok _) := vSup then
    vacuous := true
    r := { r with vacuous := .proved "supplied" s!"{c ++ `anchorVacuous}", verdict := "VACUOUS" }
    added := added.push (c ++ `anchorVacuous)
  else if let some (.error why) := nvSup then
    r := { r with nonvacuous := rejected why }
  else if let some (.error why) := vSup then
    r := { r with vacuous := rejected why }
  else
    let (vf?, vg) ← attempt (ob ``Anchor.Spec.Vacuous #[] true) modelNames
    match vf? with
    | some f =>
      match ← record `anchorVacuous vTy f with
      | .ok _ =>
        vacuous := true
        added := added.push (c ++ `anchorVacuous)
        r := { r with vacuous := .proved "search" "", verdict := "VACUOUS" }
      | .error why => r := { r with vacuous := .notFound why }
    | none =>
      r := { r with vacuous := .notFound vg }
      let (f?, g) ← attempt (ob ``Anchor.Spec.Nonvacuous #[] true) modelNames
      match f? with
      | some f =>
        match ← record `anchorNonvacuous nvTy f with
        | .ok p =>
          nvC := some p
          added := added.push (c ++ `anchorNonvacuous)
          r := { r with nonvacuous := .proved "search" (witnessText modelNames f.witness) }
        | .error why => r := { r with nonvacuous := .notFound why }
      | none => r := { r with nonvacuous := .notFound g }
  -- Drop for hypothesis `k`: a hand-written proof, else the declaration's own proof term when
  -- it never uses the hypothesis, else the search. `true` when a proof is in the environment.
  let dropFor (k : Nat) : TermElabM (Outcome × Bool) := do
    let dropName := (`anchorDrop).appendIndexAfter k
    let dropTy := ob ``Anchor.Spec.Drop #[mkNatLit k] false
    match ← supplied dropName dropTy with
    | some (.ok _) => return (.proved "supplied" "", true)
    | some (.error why) => return (rejected why, false)
    | none => pure ()
    let fromProof ← match proofValue? with
      | some v => Extract.dropFromProof? e v k
      | none => pure none
    -- The proof term rests on whatever the declaration's own proof rests on.
    if let some pf := fromProof then
      if (← nonstandard c).isEmpty then
        addThm (c ++ dropName) lps dropTy pf
        return (.proved "proof term" "the proof never uses this hypothesis", true)
    let (df?, dg) ← attempt (ob ``Anchor.Spec.Drop #[mkNatLit k] true) modelNames
    if let some f := df? then
      match ← record dropName dropTy f with
      | .ok _ => return (.proved "search" "", true)
      | .error why => return (.notFound why, false)
    return (.notFound dg, false)
  if nvC.isNone then
    if !vacuous then
      -- Without a model no hypothesis can be shown load-bearing, but one the statement
      -- survives without is still a fact with a proof.
      let mut hypReports := r.hyps
      let mut drops : Array Nat := #[]
      for k in [0:n] do
        let (o, ok) ← dropFor k
        hypReports := hypReports.modify k (fun h => { h with drop := o })
        if ok then
          drops := drops.push k
          added := added.push (c ++ (`anchorDrop).appendIndexAfter k)
      let base := "UNCERTIFIED (no model found and no proof of vacuity"
      r := { r with hyps := hypReports, verdict :=
        if drops.isEmpty then base ++ ")" else base ++ s!"; removable {drops.toList})" }
    return { r with axioms := ← added.mapM fun d => return (d, ← axiomsOf d) }
  let (tf?, tg) ← attempt (← conclAt e.spec) modelNames
  match tf? with
  | some f =>
    match ← record `anchorTrivial (← conclAt specC) f with
    | .ok _ =>
      added := added.push (c ++ `anchorTrivial)
      let v := "TRIVIAL CONCLUSION (true without any hypothesis; every hypothesis removable)"
      r := { r with trivial := .proved "search" "", verdict := v }
      return { r with axioms := ← added.mapM fun d => return (d, ← axiomsOf d) }
    | .error why => r := { r with trivial := .notFound why }
  | none => r := { r with trivial := .notFound tg }
  -- Each hypothesis: Drop, else LoadBearing. The two exclude each other once the statement
  -- is nonvacuous, so the order changes no verdict; Drop goes first because its attempts are
  -- cheap and a failing counterexample search spends its whole budget.
  let mut lbCs : Array Expr := #[]
  let mut drops : Array Nat := #[]
  let mut hypReports := r.hyps
  for k in [0:n] do
    let lbName := (`anchorLoadBearing).appendIndexAfter k
    let lbTy := ob ``Anchor.Spec.LoadBearing #[mkNatLit k] false
    let sup ← supplied lbName lbTy
    if let some (.ok p) := sup then
      lbCs := lbCs.push p
      added := added.push (c ++ lbName)
      hypReports := hypReports.modify k (fun h => { h with loadBearing := .proved "supplied" "" })
      continue
    if let some (.error why) := sup then
      hypReports := hypReports.modify k (fun h => { h with loadBearing := rejected why })
      continue
    let (o, ok) ← dropFor k
    hypReports := hypReports.modify k (fun h => { h with drop := o })
    if ok then
      drops := drops.push k
      added := added.push (c ++ (`anchorDrop).appendIndexAfter k)
      continue
    let (f?, g) ← attempt (ob ``Anchor.Spec.LoadBearing #[mkNatLit k] true) modelNames
    match f? with
    | some f =>
      match ← record lbName lbTy f with
      | .ok p =>
        lbCs := lbCs.push p
        added := added.push (c ++ lbName)
        let d := witnessText modelNames f.witness
        hypReports := hypReports.modify k (fun h => { h with loadBearing := .proved "search" d })
      | .error why =>
        hypReports := hypReports.modify k (fun h => { h with loadBearing := .notFound why })
    | none => hypReports := hypReports.modify k (fun h => { h with loadBearing := .notFound g })
  r := { r with hyps := hypReports }
  if lbCs.size == n then
    match holdsC, nvC with
    | some hc, some nc =>
      let P := mkApp2 (Lean.mkConst ``Anchor.Spec.LoadBearing [lvl]) M specC
      let mut chain := Lean.mkConst ``True.intro
      for k in [0:n] do
        let a := mkApp2 (Lean.mkConst ``Anchor.ForallBelow) P (mkNatLit k)
        let b := mkApp P (mkNatLit k)
        chain := mkApp4 (Lean.mkConst ``And.intro) a b chain lbCs[k]!
      let predTy ← mkArrow M (mkSort levelZero)
      let restList ← mkListLit predTy (e.hyps.toList.drop 1)
      let hne := mkApp3 (Lean.mkConst ``List.cons_ne_nil [lvl]) predTy e.hyps[0]! restList
      let certTy := mkApp2 (Lean.mkConst ``Anchor.Spec.Certificate [lvl]) M specC
      let certPf := mkAppN (Lean.mkConst ``Anchor.Spec.certificate_of [lvl]) #[M, specC, hne, hc, nc, chain]
      addThm (c ++ `anchorCertificate) lps certTy certPf
      added := added.push (c ++ `anchorCertificate)
      r := { r with verdict := if r.premises.isEmpty then "CERTIFIED" else
        s!"CERTIFIED (premises untested: {r.premises.size})" }
    | _, _ =>
      r := { r with verdict := "NONVACUOUS, EVERY HYPOTHESIS LOAD-BEARING (statement only)" }
  else if !drops.isEmpty then
    r := { r with verdict := s!"DECORATIVE {drops.toList}" }
  else
    let open_ := (List.range n).filter (fun k => !(hypReports[k]!.loadBearing.isProved))
    r := { r with verdict := s!"UNCERTIFIED (open: load-bearing {open_})" }
  return { r with axioms := ← added.mapM fun d => return (d, ← axiomsOf d) }

/-- Run the analysis without the per-command heartbeat limit: each obligation has its own
budget (`anchor.search.attemptHeartbeats`), and the rest is bookkeeping. -/
def analyzeUnbounded (c : Name) : TermElabM Report :=
  withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 0 }) (analyze c)

/-- Add only the extraction: `foo.anchorSpec` and `foo.anchorSpec_iff`, so obligations can be
proved by hand under their names before `anchor_cert foo`. -/
def addSpec (c : Name) : TermElabM Unit := do
  let lps : List Name := []
  let (stmt, _, _) ← readStatement c
  match ← Extract.extract stmt with
  | .error u => throwError "anchor_spec: {u.describe}"
  | .ok e =>
    let specName := c ++ `anchorSpec
    addDecl <| .defnDecl
      { name := specName, levelParams := lps
        type := mkApp (Lean.mkConst ``Anchor.Spec [e.level]) e.modelType, value := e.spec
        hints := .abbrev, safety := .safe }
    let specC := Lean.mkConst specName (lps.map mkLevelParam)
    let holdsTy := mkApp2 (Lean.mkConst ``Anchor.Spec.Holds [e.level]) e.modelType specC
    addThm (c ++ `anchorSpec_iff) lps (mkApp2 (Lean.mkConst ``Iff) holdsTy stmt) e.iffProof

/-- `#anchor foo`: report on the statement of `foo` without changing the environment. -/
elab "#anchor " id:ident : command => do
  let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  liftTermElabM <| withoutModifyingEnv do
    logInfo (← analyzeUnbounded c).render

/-- `#anchor_json foo`: the same report as one line of JSON. -/
elab "#anchor_json " id:ident : command => do
  let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  liftTermElabM <| withoutModifyingEnv do
    logInfo (← analyzeUnbounded c).toJson.compress

/-- `anchor_spec foo`: add `foo.anchorSpec` and the faithfulness theorem. -/
elab "anchor_spec " id:ident : command => do
  let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  liftTermElabM <| addSpec c

/-- `anchor_cert foo`: report, and keep every declaration and proof found. With
`set_option anchor.json true` the report is one line of JSON. -/
elab "anchor_cert " id:ident : command => do
  let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let json := anchor.json.get (← getOptions)
  liftTermElabM do
    let r ← analyzeUnbounded c
    logInfo (if json then r.toJson.compress else r.render)

end Anchor
