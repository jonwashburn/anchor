import Lean
import Anchor.Surface
import Anchor.SHA256

/-!
# Sign-offs bound to a review surface

A reviewer signs off on a declaration by recording the English sentence they checked it
against, together with a SHA-256 of every constant on its review surface. The sign-off is
current while those hashes are unchanged and stale as soon as one changes, appears or
disappears.

What a constant's hash covers follows what a reader of the statement reads:

* the declaration itself: its type, never its proof;
* a constant the reader must read: its kind and the expressions `Anchor.Surface.exprsOf`
  gives (type and body for a definition, type and constructor types for an inductive), plus
  every compiler-generated auxiliary those expressions reach, which the surface folds away;
* a pinned constant: its type, the pinning theorem's name, specification and relation, but
  not its body, since the reader checks the specification instead;
* a constant of the trusted base: its kind and type.

Expressions are printed structurally: constants by full name with universe levels, bound
variables by de Bruijn index, binder names and metadata dropped. The order of declarations in
a file therefore never enters a hash, and renaming a bound variable does not either.
-/

namespace Anchor.Signoff

open Lean Meta Anchor.Surface

/-- A universe level, normalized and printed. -/
def canonLevel (u : Level) : String := toString (format u.normalize)

/-- Append the structural printing of `e` to `out`. -/
partial def canonInto (e : Expr) (out : String) : String :=
  match e with
  | .bvar i => out ++ s!"#{i} "
  | .fvar f => out ++ s!"(fvar {f.name}) "
  | .mvar m => out ++ s!"(mvar {m.name}) "
  | .sort u => out ++ s!"(sort {canonLevel u}) "
  | .const n ls => out ++ s!"(c {n} {ls.map canonLevel}) "
  | .app f a => canonInto a (canonInto f (out ++ "(@ ")) ++ ") "
  | .lam _ t b bi => canonInto b (canonInto t (out ++ s!"(fun {binfo bi} ")) ++ ") "
  | .forallE _ t b bi => canonInto b (canonInto t (out ++ s!"(pi {binfo bi} ")) ++ ") "
  | .letE _ t v b _ => canonInto b (canonInto v (canonInto t (out ++ "(let "))) ++ ") "
  | .lit (.natVal n) => out ++ s!"(n {n}) "
  | .lit (.strVal s) => out ++ s!"(s {s.quote}) "
  | .mdata _ b => canonInto b out
  | .proj s i b => canonInto b (out ++ s!"(proj {s} {i} ") ++ ") "
where
  binfo : BinderInfo → String
    | .default => "d"
    | .implicit => "i"
    | .strictImplicit => "s"
    | .instImplicit => "c"

/-- The structural printing of `e`. -/
def canon (e : Expr) : String := canonInto e ""

/-- Whether `c` lies in the trusted base of `cfg`. -/
def isTrusted (env : Environment) (cfg : Surface.Config) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | some idx => cfg.trusted.any (·.isPrefixOf env.header.moduleNames[idx.toNat]!)
  | none => false

/-- The printed content of a constant whose expressions the reader reads, followed by the
content of every generated auxiliary those expressions reach. -/
partial def readContent (cfg : Surface.Config) (c : Name) : MetaM String := do
  let env ← getEnv
  let mut out := ""
  let mut seen : NameSet := {}
  let mut todo := #[c]
  while h : 0 < todo.size do
    let d := todo.back
    todo := todo.pop
    if seen.contains d then continue
    seen := seen.insert d
    let ci ← getConstInfo d
    out := out ++ s!"[{d} {kindOf env ci}] "
    let es ← if d == c then (match ci with
        | .thmInfo t => pure #[t.type]
        | _ => exprsOf cfg ci)
      else exprsOf { cfg with followProofs := false } ci
    for e in es do
      out := canonInto e out
      for u in e.getUsedConstants do
        if !seen.contains u && isGenerated env u && !isTrusted env cfg u then
          todo := todo.push u
  return out

/-- The printed content of one surface entry. -/
def entryContent (cfg : Surface.Config) (en : Entry) : MetaM String := do
  let env ← getEnv
  let some ci := env.find? en.name | return s!"missing {en.name}"
  match en.status with
  | .read => readContent cfg en.name
  | .boundary => return s!"[{en.name} {kindOf env ci} boundary] " ++ canon ci.type
  | .pinned =>
    let some p := Anchor.getPin? env en.name | return s!"pin missing {en.name}"
    return s!"[{en.name} {kindOf env ci} pinned by {p.thm}] " ++ canon ci.type ++ canon p.spec ++
      canon p.rel

/-- The hash of each constant on the surface of `decl`, the declaration itself first, the rest
sorted by name. -/
def surfaceHashes (decl : Name) (cfg : Surface.Config := {}) : MetaM (Array (Name × String)) := do
  let es ← compute decl cfg
  let mut hs : Array (Name × String) := #[]
  for en in es do
    hs := hs.push (en.name, SHA256.ofString (← entryContent cfg en))
  let sorted := hs.qsort fun a b => Name.lt a.1 b.1
  return #[(decl, SHA256.ofString (← readContent cfg decl))] ++ sorted

/-- One hash for the whole surface: the SHA-256 of the lines `name hash`, in the order of
`surfaceHashes`. -/
def surfaceHash (hs : Array (Name × String)) : String :=
  SHA256.ofString (String.join (hs.toList.map fun (n, h) => s!"{n} {h}\n"))

/-- A sign-off: who checked which declaration against which sentence, and the surface they
saw. -/
structure Record where
  /-- The declaration signed off. -/
  decl : Name
  /-- The module to import to check it. -/
  module : Name
  /-- The English sentence the reviewer checked the statement against. -/
  sentence : String
  /-- Who signed. -/
  reviewer : String
  /-- When, as `YYYY-MM-DD`. -/
  date : String
  /-- The whole-surface hash. -/
  sha256 : String
  /-- The hash of each constant on the surface. -/
  entries : Array (Name × String)
  deriving Inhabited

/-- A sign-off as a single line of JSON. -/
def Record.toJson (r : Record) : Json :=
  Json.mkObj [("decl", toString r.decl), ("module", toString r.module),
    ("sentence", r.sentence), ("reviewer", r.reviewer), ("date", r.date),
    ("sha256", r.sha256),
    ("entries", Json.arr (r.entries.map fun (n, h) =>
      Json.mkObj [("name", toString n), ("sha256", h)]))]

/-- A name from its printed form. -/
def parseName (s : String) : Name := s.toName

/-- Read a sign-off from JSON. -/
def Record.fromJson? (j : Json) : Except String Record := do
  let entries ← (← j.getObjValAs? (Array Json) "entries").mapM fun e => do
    return (parseName (← e.getObjValAs? String "name"), ← e.getObjValAs? String "sha256")
  return { decl := parseName (← j.getObjValAs? String "decl"),
           module := parseName (← j.getObjValAs? String "module"),
           sentence := ← j.getObjValAs? String "sentence",
           reviewer := ← j.getObjValAs? String "reviewer",
           date := ← j.getObjValAs? String "date",
           sha256 := ← j.getObjValAs? String "sha256",
           entries }

/-- A new sign-off on `decl` as the current environment has it. -/
def sign (decl module : Name) (sentence reviewer date : String) : MetaM Record := do
  let hs ← surfaceHashes decl
  return { decl, module, sentence, reviewer, date, sha256 := surfaceHash hs, entries := hs }

/-- What changed between a sign-off and the current surface. -/
structure Drift where
  /-- Constants on both surfaces whose hash differs. -/
  changed : Array Name := #[]
  /-- Constants on the current surface only. -/
  added : Array Name := #[]
  /-- Constants on the signed surface only. -/
  removed : Array Name := #[]
  deriving Inhabited

/-- No drift at all. -/
def Drift.isEmpty (d : Drift) : Bool := d.changed.isEmpty && d.added.isEmpty && d.removed.isEmpty

/-- The drift as one line. -/
def Drift.render (d : Drift) : String :=
  let part (w : String) (xs : Array Name) : List String :=
    if xs.isEmpty then [] else [s!"{w} {", ".intercalate (xs.toList.map toString)}"]
  "; ".intercalate (part "changed" d.changed ++ part "added" d.added ++ part "removed" d.removed)

/-- Compare a sign-off with the surface of its declaration in the current environment. A
missing declaration is reported as the declaration removed. -/
def check (r : Record) : MetaM Drift := do
  unless (← getEnv).contains r.decl do return { removed := #[r.decl] }
  let now ← surfaceHashes r.decl
  let old : Std.HashMap Name String := r.entries.foldl (init := {}) fun m (n, h) => m.insert n h
  let cur : Std.HashMap Name String := now.foldl (init := {}) fun m (n, h) => m.insert n h
  let mut d : Drift := {}
  for (n, h) in now do
    match old[n]? with
    | some h' => if h != h' then d := { d with changed := d.changed.push n }
    | none => d := { d with added := d.added.push n }
  for (n, _) in r.entries do
    unless cur.contains n do d := { d with removed := d.removed.push n }
  return d

end Anchor.Signoff
