import Lean
import Anchor.Pinned

/-!
# Review surface

The kernel checks that a proof proves its statement. Whether the statement says what its
reader thinks is decided by reading: the statement itself and every definition it reaches.
The review surface of a declaration is that reading list.

`Anchor.Surface.compute` starts from the type of a declaration (its statement) and walks the
constants it uses, breadth first, ties broken by name:

* a constant from a trusted library (by module prefix, `Config.trusted`) is recorded as
  `boundary` and not expanded;
* a pinned constant (`@[pinned]`, see `Anchor.Pinned`) is recorded as `pinned`, and its
  type, specification and relation are walked instead of its body;
* any other definition, abbreviation, opaque constant or instance is `read`, and its type and
  value are walked;
* an inductive type or structure is `read`, and its type and constructor types are walked;
* a theorem reached from a statement contributes its type only, unless `followProofs` is set.

Compiler-generated auxiliaries (matchers, `_proof_n`, equation lemmas, `_sunfold`, `brecOn`,
`below`, `casesOn`, `rec`, `noConfusion`, structure projections) and constructors are walked
through and folded into the constant that reached them; they are not listed. The test for
"generated" is `Name.isInternalDetail`, `Lean.Meta.allowCompletion` and the `injEq` and
`sizeOf_spec` lemmas of constructors, with
projections and constructors added, applied to the user name of a private constant so that
private definitions are listed. Instances are listed with kind `instance`.

Boundary entries that are total functions with a junk value (`x / 0 = 0`, `√x = 0` for
`x < 0`, truncated subtraction on `ℕ`, and similar) carry a note: the statement may be true
only because of the junk value.

`#surface foo` prints the surface as text, `#surface_json foo` as JSON.
-/

namespace Anchor.Surface

open Lean Meta Elab Command

/-- Module prefixes of the default trusted base. -/
def defaultTrusted : Array Name :=
  #[`Init, `Std, `Lean, `Mathlib, `Batteries, `Aesop, `Qq, `Plausible, `ProofWidgets,
    `ImportGraph, `LeanSearchClient]

/-- What the walk treats as trusted and what it follows. -/
structure Config where
  /-- Constants whose module has one of these prefixes are boundary entries. -/
  trusted : Array Name := defaultTrusted
  /-- Also walk the values (proofs) of theorems. This mode exists to compare with
  `scripts/verify_rs.sh`, whose closure follows proofs. -/
  followProofs : Bool := false
  /-- Collapse pinned constants to their specification. -/
  honorPins : Bool := true
  deriving Inhabited

/-- How a constant on the surface is treated. -/
inductive Status where
  /-- The reader must read it. -/
  | read
  /-- Pinned: the reader reads its specification, not its body. -/
  | pinned
  /-- In the trusted base: not expanded. -/
  | boundary
  deriving Inhabited, BEq, Repr

/-- The status as a word. -/
def Status.word : Status → String
  | .read => "read"
  | .pinned => "pinned"
  | .boundary => "boundary"

/-- One constant on the review surface. -/
structure Entry where
  /-- The constant (private constants keep their full private name). -/
  name : Name
  /-- `def`, `abbrev`, `instance`, `opaque`, `theorem`, `inductive`, `structure`, `class`,
  `axiom`, `constructor`, `recursor` or `quot`. -/
  kind : String
  /-- The module that declares it (the main module for constants of the current file). -/
  module : Name
  /-- How the walk treated it. -/
  status : Status
  /-- Its docstring, if it has one. -/
  docstring : Option String
  /-- Breadth-first depth: 1 for constants that occur in the root's own expressions. -/
  depth : Nat
  /-- The listed constant (or root) whose walk reached it first. -/
  via : Name
  /-- For a pinned constant, the theorem that pins it. -/
  pinnedBy : Option Name := none
  /-- A note for the reader, such as a junk-value warning. -/
  note : Option String := none
  deriving Inhabited

/-- The name a reader sees: the user name of a private constant, else the name. -/
def displayName (n : Name) : Name :=
  (privateToUserName? n).getD n

/-- Compiler-generated auxiliaries, folded into the constant that reached them. The test above,
applied to the user name, without the instance clause, with
projections and constructors added (a constructor's type reaches its inductive type, which is
listed and whose constructor types are read with it). -/
def isGenerated (env : Environment) (n : Name) : Bool :=
  (displayName n).isInternalDetail || !Meta.allowCompletion env n || env.isProjectionFn n ||
    env.isConstructor n || underGenerated env n ||
    (match n with
     | .str p s => (s == "injEq" || s == "sizeOf_spec") && env.isConstructor p
     | _ => false)
where
  /-- A constant declared under a generated auxiliary, such as `Tree.brecOn.go` or
  `f.match_1.splitter`: its parent is a constant that `allowCompletion` rejects, or a name that
  is an internal detail. -/
  underGenerated (env : Environment) (n : Name) : Bool :=
    match n with
    | .str p _ =>
      (env.contains p && !Meta.allowCompletion env p) ||
        (match displayName p with
         | q@(.str _ _) => q.isInternalDetail
         | _ => false)
    | _ => false

/-- Generated auxiliaries of the trusted base, not listed. Class projections such as
`HDiv.hDiv` are listed, because junk-value notes attach to them. -/
def isGeneratedBoundary (env : Environment) (n : Name) : Bool :=
  (displayName n).isInternalDetail || !Meta.allowCompletion env n ||
    isGenerated.underGenerated env n ||
    (match n with
     | .str p s => (s == "injEq" || s == "sizeOf_spec") && env.isConstructor p
     | _ => false)

/-- The kind of a constant, as a word. -/
def kindOf (env : Environment) (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo _ => "axiom"
  | .defnInfo d =>
    if isInstanceCore env d.name then "instance"
    else if getReducibilityStatusCore env d.name == .reducible then "abbrev"
    else "def"
  | .opaqueInfo o => if isInstanceCore env o.name then "instance" else "opaque"
  | .thmInfo _ => "theorem"
  | .inductInfo iv =>
    if isClass env iv.name then "class"
    else if isStructure env iv.name then "structure"
    else "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quot"

/-- The expressions a reader of `ci` must read, by kind. -/
def exprsOf (cfg : Config) (ci : ConstantInfo) : MetaM (Array Expr) := do
  match ci with
  | .thmInfo t => return if cfg.followProofs then #[t.type, t.value] else #[t.type]
  | .defnInfo d => return #[d.type, d.value]
  | .opaqueInfo o => return #[o.type, o.value]
  | .inductInfo iv =>
    let mut es := #[iv.type]
    for c in iv.ctors do
      es := es.push (← getConstInfo c).type
    return es
  | ci => return #[ci.type]

/-! ## Junk values -/

/-- Boundary constants that are total functions with a junk value wherever they occur. -/
def alwaysJunk : List (Name × String) :=
  [(`HDiv.hDiv, "x / 0 = 0"), (`Div.div, "x / 0 = 0"), (`Inv.inv, "0⁻¹ = 0"),
   (`HMod.hMod, "x % 0 = x"), (`Nat.div, "n / 0 = 0"), (`Nat.sub, "a - b = 0 when b > a"),
   (`Nat.pred, "pred 0 = 0"), (`Nat.log, "log b 0 = 0"), (`Int.toNat, "a negative integer gives 0"),
   (`List.head!, "the head of [] is a default value"),
   (`List.getLast!, "the last element of [] is a default value"),
   (`List.get!, "an index out of range gives a default value"),
   (`Array.get!, "an index out of range gives a default value"),
   (`Option.get!, "none gives a default value"),
   (`Real.sqrt, "√x = 0 for x < 0"), (`Real.log, "log 0 = 0 and log x = log |x|"),
   (`Real.logb, "logb b 0 = 0 and logb 1 x = 0"),
   (`Real.arcsin, "clamped outside [-1, 1]"), (`Real.arccos, "clamped outside [-1, 1]"),
   (`Real.toNNReal, "a negative real gives 0"), (`ENNReal.toReal, "∞ gives 0"),
   (`ENNReal.toNNReal, "∞ gives 0"), (`ENat.toNat, "⊤ gives 0"), (`EReal.toReal, "±⊤ gives 0"),
   (`deriv, "a non-differentiable function has derivative 0"),
   (`derivWithin, "a non-differentiable function has derivative 0"),
   (`fderiv, "a non-differentiable function has derivative 0"),
   (`fderivWithin, "a non-differentiable function has derivative 0"),
   (`MeasureTheory.integral, "a non-integrable function has integral 0"),
   (`intervalIntegral, "a non-integrable function has integral 0"),
   (`tsum, "a non-summable family has sum 0"), (`tprod, "a non-multipliable family has product 1"),
   (`limUnder, "no limit gives an arbitrary value"),
   (`SupSet.sSup, "over ℝ an unbounded or empty set gives 0"),
   (`InfSet.sInf, "over ℝ an unbounded or empty set gives 0"),
   (`iSup, "over ℝ an unbounded or empty family gives 0"),
   (`iInf, "over ℝ an unbounded or empty family gives 0"),
   (`Polynomial.natDegree, "the zero polynomial has degree 0"),
   (`Polynomial.leadingCoeff, "the zero polynomial has leading coefficient 0")]

/-- Types on which subtraction is truncated. -/
def truncatedTypes : List Name := [`Nat, `NNReal, `ENNReal, `ENat, `PNat]

/-- Boundary constants with a junk value only at some types: the constant, the position of
the type argument, the types, and the junk value. -/
def typedJunk : List (Name × Nat × List Name × String) :=
  [(`HSub.hSub, 0, truncatedTypes, "truncated subtraction: a - b = 0 when b > a"),
   (`Sub.sub, 0, truncatedTypes, "truncated subtraction: a - b = 0 when b > a"),
   (`HPow.hPow, 1, [`Real], "real power: 0 ^ 0 = 1, and a negative base gives a junk value")]

/-- The note for a junk value. -/
def junkNote (detail : String) : String :=
  s!"total function with a junk value ({detail}); check the statement does not depend on it"

/-- Add to `hits` each typed-junk constant that `e` applies at a junk type. `used` is the set
of constants of `e`. -/
def scanJunk (e : Expr) (used : Array Name) (hits : NameSet) : NameSet :=
  typedJunk.foldl (init := hits) fun hits (c, idx, tys, _) =>
    if hits.contains c || !used.contains c then hits
    else
      let atJunkType (x : Expr) : Bool :=
        x.isAppOf c && x.getAppNumArgs > idx &&
          (match (x.getArg! idx).consumeMData with
           | .const n _ => tys.contains n
           | _ => false)
      if (e.find? atJunkType).isSome then hits.insert c else hits

/-! ## The walk -/

/-- The walk behind the review surface: the entries, in breadth-first order with ties broken
by name, and every constant the walk reached (listed, folded or at the boundary, roots
included), sorted by name. Roots are expanded by the rules of their kind and are not listed. -/
def walk (roots : Array Name) (cfg : Config := {}) : MetaM (Array Entry × Array Name) := do
  let env ← getEnv
  let trusted (n : Name) : Bool :=
    match env.getModuleIdxFor? n with
    | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      cfg.trusted.any (·.isPrefixOf m)
    | none => false
  let moduleOf (n : Name) : Name :=
    match env.getModuleIdxFor? n with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => env.mainModule
  let mut visited : NameSet := roots.foldl (init := {}) fun s r => s.insert r
  let mut hits : NameSet := {}
  let mut frontier : Array (Name × Name) := #[]
  for r in roots do
    for e in ← exprsOf cfg (← getConstInfo r) do
      let used := e.getUsedConstants
      hits := scanJunk e used hits
      for d in used do
        unless visited.contains d do
          visited := visited.insert d
          frontier := frontier.push (d, r)
  let mut entries : Array Entry := #[]
  let mut depth := 1
  while !frontier.isEmpty do
    frontier := frontier.qsort fun a b => Name.lt a.1 b.1
    let mut next : Array (Name × Name) := #[]
    for (c, via) in frontier do
      let some ci := env.find? c | continue
      let kind := kindOf env ci
      let mut exprs : Array Expr := #[]
      let mut childVia := c
      let pin? := if cfg.honorPins then getPin? env c else none
      if let some p := pin? then
        entries := entries.push
          { name := c, kind, module := moduleOf c, status := .pinned,
            docstring := ← findDocString? env c, depth, via, pinnedBy := some p.thm }
        exprs := #[ci.type, p.spec, p.rel]
      else if trusted c then
        unless isGeneratedBoundary env c do
          entries := entries.push
            { name := c, kind, module := moduleOf c, status := .boundary,
              docstring := ← findDocString? env c, depth, via }
      else
        let gen := isGenerated env c
        unless gen do
          entries := entries.push
            { name := c, kind, module := moduleOf c, status := .read,
              docstring := ← findDocString? env c, depth, via }
        exprs ← exprsOf cfg ci
        childVia := if gen then via else c
      for e in exprs do
        let used := e.getUsedConstants
        hits := scanJunk e used hits
        for d in used do
          unless visited.contains d do
            visited := visited.insert d
            next := next.push (d, childVia)
    frontier := next
    depth := depth + 1
  let noted := entries.map fun en =>
    if en.status != .boundary then en
    else
      let always := alwaysJunk.lookup en.name
      let typed := typedJunk.find? (fun t => t.1 == en.name && hits.contains en.name)
      match always, typed with
      | some d, _ => { en with note := some (junkNote d) }
      | none, some (_, _, _, d) => { en with note := some (junkNote d) }
      | none, none => en
  let mut reached : Array Name := #[]
  for n in visited do
    reached := reached.push n
  return (noted, reached.qsort Name.lt)

/-- The review surface of several roots at once: every constant a reader of their statements
must read, pin, or trust. -/
def computeMany (roots : Array Name) (cfg : Config := {}) : MetaM (Array Entry) :=
  return (← walk roots cfg).1

/-- The review surface of `c`: every constant a reader of its statement must read, pin, or
trust. `c` itself is expanded by the rules of its kind and is not listed. -/
def compute (c : Name) (cfg : Config := {}) : MetaM (Array Entry) :=
  computeMany #[c] cfg

/-! ## Output -/

/-- The first non-blank line of a docstring, without surrounding whitespace. -/
def firstLine (s : String) : String :=
  let line := ((s.splitOn "\n").find? fun l => l.any (!·.isWhitespace)).getD ""
  String.ofList ((line.toList.dropWhile Char.isWhitespace).reverse.dropWhile
    Char.isWhitespace).reverse

/-- The surface as text: counts, then the entries to read, the pinned entries and the
boundary, each in walk order. -/
def render (roots : Array Name) (es : Array Entry) : String := Id.run do
  let nRead := (es.filter (·.status == .read)).size
  let nPin := (es.filter (·.status == .pinned)).size
  let nBd := (es.filter (·.status == .boundary)).size
  let rootStr := ", ".intercalate (roots.toList.map toString)
  let mut out := s!"surface of {rootStr}: {nRead} to read, {nPin} pinned, {nBd} at the boundary"
  for (st, title) in [(Status.read, "read"), (.pinned, "pinned"), (.boundary, "boundary")] do
    let group := es.filter (·.status == st)
    if group.isEmpty then continue
    out := out ++ s!"\n{title}"
    for e in group do
      let priv := if isPrivateName e.name then " (private)" else ""
      let mut line := s!"\n  {e.kind} {displayName e.name}{priv}  [{e.module}]"
      if let some t := e.pinnedBy then line := line ++ s!"  pinned by {t}"
      if st == .read then
        if let some d := e.docstring then line := line ++ s!"  {firstLine d}"
      if let some n := e.note then line := line ++ s!"\n    note: {n}"
      out := out ++ line
  return out

/-- An entry as JSON. -/
def Entry.toJson (e : Entry) : Json :=
  let opt (o : Option String) : Json := match o with
    | some s => Json.str s
    | none => Json.null
  Json.mkObj
    [("name", Json.str e.name.toString), ("kind", Json.str e.kind),
     ("module", Json.str e.module.toString), ("status", Json.str e.status.word),
     ("docstring", opt e.docstring), ("depth", Json.num e.depth),
     ("via", Json.str e.via.toString), ("pinnedBy", opt (e.pinnedBy.map toString)),
     ("note", opt e.note)]

/-- The surface as JSON. -/
def renderJson (roots : Array Name) (cfg : Config) (es : Array Entry) : Json :=
  Json.mkObj
    [("roots", Json.arr (roots.map fun r => Json.str r.toString)),
     ("followProofs", Json.bool cfg.followProofs), ("honorPins", Json.bool cfg.honorPins),
     ("entries", Json.arr (es.map Entry.toJson))]

/-- `#surface foo` prints the review surface of `foo`. -/
elab "#surface " id:ident : command => liftTermElabM do
  let c ← realizeGlobalConstNoOverloadWithInfo id
  let es ← compute c
  logInfo (render #[c] es)

/-- `#surface_json foo` prints the review surface of `foo` as JSON. -/
elab "#surface_json " id:ident : command => liftTermElabM do
  let c ← realizeGlobalConstNoOverloadWithInfo id
  let es ← compute c
  logInfo ((renderJson #[c] {} es).pretty)

end Anchor.Surface
