import Lean

/-!
# Anchor price: the classical entry points a proof reaches

`#print axioms foo` reports `Classical.choice` whenever a classical step occurs anywhere in the
proof of `foo`. Lean derives excluded middle, decidability of every proposition and the choice
functions from that one axiom, so the axiom report cannot say which classical principle the
proof used or where it entered.

`#price foo` walks the closure that `Lean.collectAxioms` walks: the type and value of every
constant reached from `foo`, transitively, each constant visited once. It reports which classical
entry points the walk meets: the axiom `Classical.choice`, the derived principles of
`Init/Classical.lean`, Mathlib's `Classical.dec` family when Mathlib is loaded, and every constant
tagged `@[classical_entry]`. For each one it prints a shortest path from `foo`, found breadth
first. `#price_json foo` prints the same report as one line of JSON. Both are deterministic: the
constants a node mentions are visited in name order.

An entry point is *first* when some path reaches it without passing through another entry point.
The others are reached only inside the proof of an entry point; a proof through `Classical.em`
also reaches `Classical.choice`, inside `Classical.em`.

Each entry point carries a role. It is *invoked* when the constant is a proof or a function
(`Classical.em`, `Classical.choose`). It is *stated* when the constant's type is syntactically a
sort after its binders, so the constant is itself a proposition or a predicate. That is how a
library writes excluded middle as a definition and takes it as a hypothesis; reaching such an
entry means a statement in the closure mentions the principle. It does not mean any proof
used a classical axiom.

The axioms are printed from `Lean.collectAxioms`, and the command fails if its own walk found a
different set, which checks that both walk the same closure.

The minimum price of a statement over all of its proofs is a different question. It is stated at
the end of this file as an open specification.
-/

namespace Anchor.Price

open Lean Elab Command

/-! ## Entry points -/

/-- The built-in classical entry points: the axiom `Classical.choice`, the derived principles of
`Init/Classical.lean`, and Mathlib's `Classical.dec` family. A name absent from the environment
is never reached; `#price_entries` shows which are declared. -/
def builtinEntries : List Name := [
  `Classical.choice,
  `Classical.indefiniteDescription,
  `Classical.choose,
  `Classical.choose_spec,
  `Classical.em,
  `Classical.propDecidable,
  `Classical.decidableInhabited,
  `Classical.typeDecidableEq,
  `Classical.typeDecidable,
  `Classical.inhabited_of_nonempty,
  `Classical.inhabited_of_exists,
  `Classical.strongIndefiniteDescription,
  `Classical.epsilon,
  `Classical.epsilon_spec,
  `Classical.axiomOfChoice,
  `Classical.skolem,
  `Classical.propComplete,
  `Classical.byCases,
  `Classical.byContradiction,
  `Classical.not_not,
  `Classical.decidable_of_decidable_not,
  `Classical.not_forall,
  `Classical.not_forall_not,
  `Classical.not_exists_not,
  `Classical.forall_or_exists_not,
  `Classical.exists_or_forall_not,
  `Classical.or_iff_not_imp_left,
  `Classical.or_iff_not_imp_right,
  `Classical.not_imp_iff_and_not,
  `Classical.not_and_iff_not_or_not,
  `Classical.not_iff,
  `Classical.not_imp,
  `Exists.choose,
  `Exists.choose_spec,
  `Classical.dec,
  `Classical.decPred,
  `Classical.decRel,
  `Classical.decEq]

/-- The built-in entry points as a set. -/
def builtinEntrySet : NameSet :=
  builtinEntries.foldl (fun s n => s.insert n) {}

/-- Constants registered with `@[classical_entry]`. -/
initialize classicalEntryExt : SimpleScopedEnvExtension Name NameSet ←
  registerSimpleScopedEnvExtension {
    addEntry := fun s n => s.insert n
    initial := {}
  }

/-- `@[classical_entry]` registers a constant as a classical entry point for `#price`, so a
library can name its own excluded-middle principle. It may be applied to an imported constant
with `attribute [classical_entry] foo`. -/
initialize registerBuiltinAttribute {
  name := `classical_entry
  descr := "register a constant as a classical entry point for #price"
  add := fun decl stx kind => do
    Attribute.Builtin.ensureNoArgs stx
    classicalEntryExt.add decl kind
}

/-- The constants registered with `@[classical_entry]` in this environment, in name order. -/
def registeredEntries (env : Environment) : Array Name := Id.run do
  let mut acc : Array Name := #[]
  for n in classicalEntryExt.getState env do
    acc := acc.push n
  return acc.qsort Name.lt

/-- Whether `n` is a classical entry point in `env`. -/
def isEntry (env : Environment) (n : Name) : Bool :=
  builtinEntrySet.contains n || (classicalEntryExt.getState env).contains n

/-! ## The walk -/

private def dedupSorted (xs : Array Name) : Array Name :=
  xs.foldl (fun acc n => if acc.back? == some n then acc else acc.push n) #[]

/-- The constants `c` mentions, in name order without repeats: those in its type and value, and
the constructors of an inductive type. These are the edges `Lean.CollectAxioms.collect`
follows. -/
def edges (kenv : Kernel.Environment) (c : Name) : Array Name :=
  let raw : Array Name :=
    match kenv.find? c with
    | some (.axiomInfo v) => v.type.getUsedConstants
    | some (.defnInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
    | some (.thmInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
    | some (.opaqueInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
    | some (.quotInfo _) => #[]
    | some (.ctorInfo v) => v.type.getUsedConstants
    | some (.recInfo v) => v.type.getUsedConstants
    | some (.inductInfo v) => v.type.getUsedConstants ++ v.ctors.toArray
    | none => #[]
  dedupSorted (raw.qsort Name.lt)

/-- A breadth-first walk: the constants in the order reached, and for each one other than the
root, the constant it was first reached from. -/
structure Walk where
  order : Array Name
  parent : NameMap Name

/-- Walk breadth first from `root`. A constant other than `root` for which `stop` holds is
recorded but not expanded. -/
def walk (kenv : Kernel.Environment) (root : Name) (stop : Name → Bool) : Walk := Id.run do
  let mut seen : NameSet := ({} : NameSet).insert root
  let mut parent : NameMap Name := {}
  let mut order : Array Name := #[root]
  let mut i := 0
  while h : i < order.size do
    let c := order[i]
    i := i + 1
    if c != root && stop c then
      continue
    for d in edges kenv c do
      unless seen.contains d do
        seen := seen.insert d
        parent := parent.insert d c
        order := order.push d
  return { order, parent }

/-- The path from the root to `n` through first-reached parents. -/
def Walk.path (w : Walk) (n : Name) : List Name := Id.run do
  let mut path := [n]
  let mut cur := n
  for _ in [0:w.order.size] do
    match w.parent.find? cur with
    | some p =>
      path := p :: path
      cur := p
    | none => break
  return path

/-! ## The report -/

/-- One reached entry point. -/
structure Entry where
  name : Name
  kind : String
  role : String
  first : Bool
  registered : Bool
  path : List Name

/-- The price report of one declaration. -/
structure Report where
  decl : Name
  axioms : Array Name
  entries : Array Entry
  registeredInScope : Array Name
  visited : Nat

/-- The kind of a constant, in words. -/
def kindOf : Option ConstantInfo → String
  | some (.axiomInfo _) => "axiom"
  | some (.defnInfo _) => "definition"
  | some (.thmInfo _) => "theorem"
  | some (.opaqueInfo _) => "opaque"
  | some (.quotInfo _) => "quotient"
  | some (.ctorInfo _) => "constructor"
  | some (.recInfo _) => "recursor"
  | some (.inductInfo _) => "inductive"
  | none => "unknown"

/-- `stated` when the type is a sort after its binders (a proposition or a predicate),
`invoked` otherwise (a proof or a function). -/
def roleOf : Option ConstantInfo → String
  | some ci => if ci.type.getForallBody.isSort then "stated" else "invoked"
  | none => "invoked"

private def entryLt (a b : Entry) : Bool :=
  (a.first && !b.first) || (a.first == b.first && Name.lt a.name b.name)

/-- The price of `root` in `env`. -/
def price (env : Environment) (root : Name) : Report :=
  let kenv := env.checked.get
  let full := walk kenv root (fun _ => false)
  let firstWalk := walk kenv root (isEntry env)
  let axioms := (full.order.filter fun n =>
    match kenv.find? n with
    | some (.axiomInfo _) => true
    | _ => false).qsort Name.lt
  let reg := classicalEntryExt.getState env
  let entries := (full.order.filter fun n => n != root && isEntry env n).map fun n =>
    let ci := kenv.find? n
    let first := firstWalk.parent.contains n
    { name := n
      kind := kindOf ci
      role := roleOf ci
      first
      registered := reg.contains n
      path := if first then firstWalk.path n else full.path n : Entry }
  { decl := root
    axioms
    entries := entries.qsort entryLt
    registeredInScope := registeredEntries env
    visited := full.order.size }

private def joinNames (xs : List Name) (sep : String) : String :=
  sep.intercalate (xs.map toString)

private def Entry.toText (e : Entry) : String :=
  let reg := if e.registered then ", registered with @[classical_entry]" else ""
  s!"    {e.name} ({e.kind}, {e.role}{reg})\n      path: {joinNames e.path " -> "}\n"

/-- The report as text. -/
def Report.toText (r : Report) : String := Id.run do
  let axs := if r.axioms.isEmpty then "none" else joinNames r.axioms.toList ", "
  let mut s := s!"price of {r.decl}\n  axioms: {axs}\n"
  let firsts := r.entries.filter (·.first)
  let inner := r.entries.filter (!·.first)
  if r.entries.isEmpty then
    s := s ++ "  classical entry points: none\n"
  else
    s := s ++ "  classical entry points reached first (no other entry point on the path):\n"
    for e in firsts do
      s := s ++ e.toText
    unless inner.isEmpty do
      s := s ++ "  classical entry points reached only inside another entry point:\n"
      for e in inner do
        s := s ++ e.toText
  unless r.registeredInScope.isEmpty do
    s := s ++ s!"  registered with @[classical_entry]: {joinNames r.registeredInScope.toList ", "}\n"
  s := s ++ s!"  constants visited: {r.visited}"
  return s

private def namesJson (xs : Array Name) : Json :=
  Json.arr (xs.map fun n => Json.str n.toString)

/-- One entry as JSON. -/
def Entry.toJson (e : Entry) : Json :=
  Json.mkObj [
    ("name", Json.str e.name.toString),
    ("kind", Json.str e.kind),
    ("role", Json.str e.role),
    ("first", Json.bool e.first),
    ("registered", Json.bool e.registered),
    ("path", namesJson e.path.toArray)]

/-- The report as JSON. Object keys print in sorted order. -/
def Report.toJson (r : Report) : Json :=
  Json.mkObj [
    ("report", Json.str "anchor.price/1"),
    ("decl", Json.str r.decl.toString),
    ("axioms", namesJson r.axioms),
    ("entries", Json.arr (r.entries.map Entry.toJson)),
    ("registered_in_scope", namesJson r.registeredInScope),
    ("visited", Lean.ToJson.toJson r.visited)]

private def priceCommand (id : Syntax) (asJson : Bool) : CommandElabM Unit := do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let r := price (← getEnv) n
  let ax := (← liftCoreM <| Lean.collectAxioms n).qsort Name.lt
  unless ax == r.axioms do
    throwError "#price: the walk found axioms {r.axioms.toList} but collectAxioms reports {ax.toList}"
  if asJson then
    logInfo r.toJson.compress
  else
    logInfo r.toText

/-- `#price foo` prints the classical entry points the proof of `foo` reaches, a shortest path
to each, and the axioms. -/
elab "#price " id:ident : command => priceCommand id false

/-- `#price_json foo` prints the report of `#price foo` as one line of JSON. -/
elab "#price_json " id:ident : command => priceCommand id true

/-- `#price_entries` lists the classical entry points in force and whether each is declared in
the current environment. -/
elab "#price_entries" : command => do
  let env ← getEnv
  let reg := registeredEntries env
  let mut s := "classical entry points\n"
  for n in builtinEntries do
    let st := if env.contains n then "declared" else "not declared here"
    s := s ++ s!"  {n} (built in, {st})\n"
  for n in reg do
    s := s ++ s!"  {n} (registered with @[classical_entry])\n"
  logInfo s

/-! ## The minimum price, an open specification

`#price` reports what one proof costs. A statement can have many proofs, and the question that
matters to a reader is the least it can cost. -/

universe u v

/-- A proof calculus whose proofs record the entry points they use. -/
structure PricedCalculus where
  /-- The statements. -/
  Stmt : Type u
  /-- The proofs of a statement. -/
  Proof : Stmt → Type v
  /-- The entry points a proof uses. -/
  uses : {s : Stmt} → Proof s → List Name

namespace PricedCalculus

variable (C : PricedCalculus.{u, v})

/-- `E` is a price of `s`: some proof of `s` uses exactly the entry points in `E`. -/
def IsPrice (s : C.Stmt) (E : List Name) : Prop :=
  ∃ p : C.Proof s, ∀ n, n ∈ C.uses p ↔ n ∈ E

/-- `E` is the minimum price of `s`, the least set of entry points over all proofs of `s`: some
proof uses exactly `E`, and every proof of `s` uses every entry point in `E`. -/
def IsMinimumPrice (s : C.Stmt) (E : List Name) : Prop :=
  C.IsPrice s E ∧ ∀ p : C.Proof s, ∀ n, n ∈ E → n ∈ C.uses p

/-- **Open specification, not a claim.** Every provable statement of the calculus has a minimum
price.

For Lean, take the statements to be closed propositions, the proofs of `s` the terms the kernel
accepts at type `s`, and the uses of a proof the entry points `#price` reports. `#price` gives the
price of the proof in hand, an upper bound. Whether every theorem has a least price, and which set
it is, is open for Lean. It can fail for a calculus in which a statement has two proofs with
incomparable entry sets and no proof using less, so it is a property a calculus may or may not
have.

A calculus in which each certificate carries a ledger of the principles it uses can answer the
question: there `0 = 0 ∨ ¬(0 = 0)` has one accepted certificate whose ledger is excluded middle
and one whose ledger is empty, so the minimum price of that formula is empty and the price of the
first certificate overstates it.

No theorem in Anchor asserts this specification. -/
def MinimumPriceSpec : Prop :=
  ∀ s : C.Stmt, Nonempty (C.Proof s) → ∃ E : List Name, C.IsMinimumPrice s E

variable {C}

/-- Two minimum prices of one statement name the same entry points. -/
theorem IsMinimumPrice.mem_iff {s : C.Stmt} {E E' : List Name}
    (h : C.IsMinimumPrice s E) (h' : C.IsMinimumPrice s E') (n : Name) : n ∈ E ↔ n ∈ E' := by
  obtain ⟨⟨p, hp⟩, hmin⟩ := h
  obtain ⟨⟨p', hp'⟩, hmin'⟩ := h'
  exact ⟨fun hn => (hp' n).mp (hmin p' n hn), fun hn => (hp n).mp (hmin' p n hn)⟩

/-- A proof that uses no entry point makes the empty set the minimum price. -/
theorem isMinimumPrice_nil {s : C.Stmt} (p : C.Proof s) (h : C.uses p = []) :
    C.IsMinimumPrice s [] :=
  ⟨⟨p, fun _ => h ▸ Iff.rfl⟩, fun _ _ hn => nomatch hn⟩

end PricedCalculus

end Anchor.Price
