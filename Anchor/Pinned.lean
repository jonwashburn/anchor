import Lean
import Anchor.Core

/-!
# Pinned definitions

A definition is pinned when a kernel-checked theorem of type `Anchor.Pinned spec r c` says
that `c` meets `spec` and that everything meeting `spec` is `r`-related to `c`. A reader of a
statement that mentions `c` then needs `spec` and `r`, not the body of `c`: a statement that
respects `r` is true of `c` exactly when it is true of everything meeting `spec`
(`Anchor.pinned_statement_iff`).

`@[pinned]` on such a theorem records `c ↦ (theorem, spec, r)` in an environment extension
that persists across imports. The attribute accepts the theorem only when its type has that
shape, the pinned object is a constant, and the proof does not depend on `sorryAx`. A false
uniqueness claim has no proof, so it cannot be pinned. `#pinned` lists the index;
`Anchor.Surface` reads it.
-/

namespace Anchor

open Lean Meta Elab Command

/-- One entry of the pinned index. -/
structure PinEntry where
  /-- The pinned constant. -/
  target : Name
  /-- The theorem of type `Anchor.Pinned spec r target`. -/
  thm : Name
  /-- The specification `spec`. -/
  spec : Expr
  /-- The relation `r`, up to which the specification determines `target`. -/
  rel : Expr
  /-- The axioms the theorem depends on, as `Lean.collectAxioms` reports them, sorted. -/
  axioms : Array Name
  deriving Inhabited

/-- The pinned index: each pinned constant with its entry. -/
initialize pinnedExt : SimplePersistentEnvExtension PinEntry (NameMap PinEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m e => m.insert e.target e
    addImportedFn := fun ess => ess.foldl (init := {}) fun m es =>
      es.foldl (init := m) fun m e => m.insert e.target e
  }

/-- The pin of `c`, if `c` is pinned. -/
def getPin? (env : Environment) (c : Name) : Option PinEntry :=
  (pinnedExt.getState env).find? c

/-- Every pin in the environment, sorted by the name of the pinned constant. -/
def allPins (env : Environment) : Array PinEntry := Id.run do
  let mut out := #[]
  for (_, p) in pinnedExt.getState env do
    out := out.push p
  return out.qsort fun a b => Name.lt a.target b.target

/-- Check that `decl` is a theorem of type `Anchor.Pinned spec r c` with `c` a constant and a
proof free of `sorryAx`, then record the pin. Every failure is an error, so nothing is pinned
by a theorem that does not pass. -/
def addPin (decl : Name) : MetaM Unit := do
  let info ← getConstInfo decl
  unless info matches .thmInfo _ do
    throwError "@[pinned]: {decl} is not a theorem; a pin is a theorem of type \
      Anchor.Pinned spec r c"
  let ty := info.type.consumeMData
  unless ty.isAppOfArity ``Anchor.Pinned 4 do
    throwError "@[pinned]: the type of {decl} is{indentExpr ty}\nwhich is not of the form \
      Anchor.Pinned spec r c"
  let args := ty.getAppArgs
  let target := args[3]!.consumeMData
  let .const c _ := target
    | throwError "@[pinned]: the pinned object{indentExpr target}\nis not a constant"
  if let some old := getPin? (← getEnv) c then
    throwError "@[pinned]: {c} is already pinned by {old.thm}"
  let axs ← collectAxioms decl
  if axs.contains ``sorryAx then
    throwError "@[pinned]: {decl} depends on sorryAx, so its uniqueness claim is not \
      proved; {c} is not pinned"
  unless ((← getEnv).checked.get.find? decl).isSome do
    throwError "@[pinned]: {decl} is not in the kernel-checked environment; {c} is not pinned"
  modifyEnv fun env => pinnedExt.addEntry env
    { target := c, thm := decl, spec := args[1]!, rel := args[2]!,
      axioms := axs.qsort Name.lt }

initialize registerBuiltinAttribute {
  name := `pinned
  descr := "pin a definition by a kernel-checked theorem `Anchor.Pinned spec r c`"
  add := fun decl stx kind => do
    Attribute.Builtin.ensureNoArgs stx
    unless kind == AttributeKind.global do
      throwError "@[pinned] must be global"
    discard <| (addPin decl).run {} {}
}

/-- `#pinned` lists every pinned constant with its theorem, specification, relation and the
axioms the theorem depends on. -/
elab "#pinned" : command => liftTermElabM do
  let ps := allPins (← getEnv)
  if ps.isEmpty then
    logInfo "no pinned constants"
    return
  let lines := ps.toList.map fun p =>
    m!"{p.target} pinned by {p.thm}\n  spec: {p.spec}\n  up to: {p.rel}\n  axioms: \
      {p.axioms.toList}"
  logInfo (MessageData.joinSep lines "\n")

end Anchor
