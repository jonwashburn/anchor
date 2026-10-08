import Anchor.Command

/-!
# Census commands

`anchor_list "out.txt" P₁ P₂ …` writes the name of every statement declared in a module whose
name starts with one of the prefixes `Pᵢ`, one per line, sorted. A statement is a theorem that a
person wrote: names that are internal or private, theorems the elaborator generated (equation
lemmas, `injEq`, `sizeOf_spec`, auxiliary recursors and the like) and instances are left out.
These are the rules the Mathlib sample uses (`AnchorTest/Census/MathlibSample.lean`).

`anchor_census "names.txt" "out.jsonl"` analyses each name in the file and writes one JSON
report per line, in the file's order. Each statement is analysed in its own copy of the
environment: every declaration the analysis adds is checked by the kernel when it is added,
listed in the report with the axioms it depends on, and then discarded. A failure on one
statement is written as a report with an `error` field and the census continues. Wall-clock
milliseconds go to `out.jsonl.time`, so the report file itself is identical across runs.
-/

open Lean Meta Elab Command

namespace Anchor.Census

/-- `f` holds of some prefix of the name, the name itself included. -/
def anyPrefix (f : Name → Bool) : Name → Bool
  | .anonymous => false
  | n@(.str p _) => f n || anyPrefix f p
  | n@(.num p _) => f n || anyPrefix f p

/-- A theorem a person stated, as opposed to one the system produced. -/
def isStatement (env : Environment) (n : Name) : Bool :=
  let internal := anyPrefix Name.isInternalDetail n || isPrivateName n
  let generated := isReservedName env n || isAuxRecursor env n || isNoConfusion env n ||
    match n with
    | .str p s =>
      ((s == "injEq" || s == "inj" || s == "sizeOf_spec") && env.isConstructor p) ||
        ((s == "brecOn" || s == "binductionOn") && env.find? p matches some (.inductInfo _))
    | _ => false
  !internal && !generated && !isInstanceCore env n

/-- The module that declares `n`, when it was imported. -/
def moduleOf (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!

/-- The statements declared in modules under the given prefixes, sorted by name. -/
def statements (env : Environment) (prefixes : List Name) : Array Name := Id.run do
  let mut out : Array Name := #[]
  for (n, ci) in env.constants.toList do
    let .thmInfo _ := ci | continue
    let some m := moduleOf env n | continue
    unless prefixes.any (·.isPrefixOf m) do continue
    if isStatement env n then out := out.push n
  return out.qsort (fun a b => a.toString < b.toString)

elab "anchor_list " out:str ps:ident+ : command => do
  let env ← getEnv
  let names := statements env (ps.map (·.getId)).toList
  IO.FS.writeFile out.getString (String.intercalate "\n" (names.map toString).toList ++ "\n")
  logInfo m!"anchor_list: {names.size} statements written to {out.getString}"

/-- The report for one name, or a report carrying the error. -/
def reportOf (c : Name) : TermElabM Json := withoutModifyingEnv do
  if !(← getEnv).contains c then
    return Json.mkObj [("decl", Json.str (toString c)), ("error", Json.str "unknown constant")]
  tryCatchRuntimeEx (do return (← analyzeUnbounded c).toJson) fun e => do
    return Json.mkObj [("decl", Json.str (toString c)),
      ("error", Json.str (← e.toMessageData.toString))]

elab "anchor_census " inp:str out:str : command => do
  let lines ← IO.FS.lines inp.getString
  let h ← IO.FS.Handle.mk out.getString .write
  let ht ← IO.FS.Handle.mk (out.getString ++ ".time") .write
  let mut done := 0
  for line in lines do
    let s := line.trim
    if s.isEmpty then continue
    let j ← match Syntax.decodeNameLit ("`" ++ s) with
      | none => pure (Json.mkObj [("decl", Json.str s), ("error", Json.str "name does not parse")])
      | some c => do
        let t0 ← IO.monoMsNow
        let j ← liftTermElabM (reportOf c)
        ht.putStrLn s!"{s}\t{(← IO.monoMsNow) - t0}"
        ht.flush
        pure j
    h.putStrLn j.compress
    h.flush
    done := done + 1
  logInfo m!"anchor_census: {done} reports written to {out.getString}"

end Anchor.Census
