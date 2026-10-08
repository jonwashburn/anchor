/-!
# Anchor core: statement certificates

Lean's kernel checks that a proof proves its statement. It does not check that the
statement is the one its reader meant. This module states, as ordinary propositions the
kernel checks, three ways a proved statement can still fail its reader, and the evidence
that rules each one out.

* The hypotheses have no model, so the statement holds for no reason
  (`Statement.holds_of_vacuous`). Ruled out by `Statement.Nonvacuous`.
* A hypothesis is decorative: removing it leaves the statement true
  (`Statement.not_loadBearing_of_drop`). Ruled out by `Statement.LoadBearing`: a model where
  every other hypothesis holds, this one fails, and the conclusion fails.
* The conclusion is true of every model. A load-bearing hypothesis supplies a model where it
  fails (`Statement.discriminating_of_loadBearing`).

`Certificate` bundles the proof with these witnesses; a statement with no hypotheses gets
none. `Pinned` is the companion notion for definitions: a statement about a pinned object is
true exactly when it is true of everything meeting the specification (`pinned_statement_iff`).

`Spec` is the encoding the extractor produces from a Lean declaration: a list of hypotheses
over one model type. `Spec.certificate_iff` proves that a certificate for the encoding is a
certificate for the statement it encodes, so the machine form and the definition agree.

This file uses Lean core only.
-/

namespace Anchor

universe u v

/-- A statement with named hypotheses: over models `M`, hypotheses indexed by `ι` and one
conclusion. It asserts `∀ m, (∀ i, hyp i m) → concl m`. -/
structure Statement (M : Type u) (ι : Type v) where
  hyp : ι → M → Prop
  concl : M → Prop

namespace Statement

variable {M : Type u} {ι : Type v} (S : Statement M ι)

/-- What the statement asserts. -/
def Holds : Prop := ∀ m, (∀ i, S.hyp i m) → S.concl m

/-- Some model satisfies every hypothesis. -/
def Nonvacuous : Prop := ∃ m, ∀ i, S.hyp i m

/-- No model satisfies every hypothesis. -/
def Vacuous : Prop := ¬ S.Nonvacuous

/-- The statement with hypothesis `i` removed. -/
def Drop (i : ι) : Prop := ∀ m, (∀ j, j ≠ i → S.hyp j m) → S.concl m

/-- Hypothesis `i` carries content: in some model every other hypothesis holds, `i` fails,
and the conclusion fails. -/
def LoadBearing (i : ι) : Prop :=
  ∃ m, (∀ j, j ≠ i → S.hyp j m) ∧ ¬ S.hyp i m ∧ ¬ S.concl m

/-- The conclusion is false of some model. -/
def Discriminating : Prop := ∃ m, ¬ S.concl m

/-- A vacuous statement holds. A proof alone certifies nothing about the hypotheses. -/
theorem holds_of_vacuous (h : S.Vacuous) : S.Holds :=
  fun m hm => absurd ⟨m, hm⟩ h

/-- A load-bearing hypothesis cannot be removed: without it the statement is false. -/
theorem not_drop_of_loadBearing {i : ι} (h : S.LoadBearing i) : ¬ S.Drop i :=
  fun hd => match h with
    | ⟨m, hothers, _, hc⟩ => hc (hd m hothers)

/-- A hypothesis whose removal leaves the statement true is not load-bearing. -/
theorem not_loadBearing_of_drop {i : ι} (h : S.Drop i) : ¬ S.LoadBearing i :=
  fun hl => S.not_drop_of_loadBearing hl h

/-- A load-bearing hypothesis exhibits a model where the conclusion fails. -/
theorem discriminating_of_loadBearing {i : ι} (h : S.LoadBearing i) : S.Discriminating :=
  match h with
  | ⟨m, _, _, hc⟩ => ⟨m, hc⟩

end Statement

/-- A statement certificate: at least one hypothesis, the proof, a model of all the
hypotheses, and for every hypothesis a model showing it carries content. -/
structure Certificate {M : Type u} {ι : Type v} (S : Statement M ι) : Prop where
  hasHypothesis : Nonempty ι
  holds : S.Holds
  nonvacuous : S.Nonvacuous
  loadBearing : ∀ i, S.LoadBearing i

namespace Certificate

variable {M : Type u} {ι : Type v} {S : Statement M ι}

/-- A certified statement has a conclusion that some model violates. -/
theorem discriminating (c : Certificate S) : S.Discriminating :=
  match c.hasHypothesis with
  | ⟨i⟩ => S.discriminating_of_loadBearing (c.loadBearing i)

/-- No hypothesis of a certified statement can be removed. -/
theorem no_drop (c : Certificate S) (i : ι) : ¬ S.Drop i :=
  S.not_drop_of_loadBearing (c.loadBearing i)

/-- A vacuous statement has no certificate. -/
theorem not_of_vacuous (h : S.Vacuous) : ¬ Certificate S :=
  fun c => h c.nonvacuous

/-- A statement with a removable hypothesis has no certificate. -/
theorem not_of_drop {i : ι} (h : S.Drop i) : ¬ Certificate S :=
  fun c => c.no_drop i h

end Certificate

/-- `a` is pinned by `spec` up to `r`: it meets the specification, and every object meeting
the specification is `r`-related to `a`. With `r = Eq` this is uniqueness. -/
def Pinned {α : Sort u} (spec : α → Prop) (r : α → α → Prop) (a : α) : Prop :=
  spec a ∧ ∀ b, spec b → r b a

/-- For a pinned object, a statement that respects `r` is true of the object exactly when
it is true of everything meeting the specification. -/
theorem pinned_statement_iff {α : Sort u} {spec : α → Prop} {r : α → α → Prop} {a : α}
    (ha : Pinned spec r a) (P : α → Prop) (hP : ∀ x y, r x y → (P x ↔ P y)) :
    P a ↔ ∀ b, spec b → P b :=
  ⟨fun hPa b hb => (hP b a (ha.2 b hb)).mpr hPa, fun h => h a ha.1⟩

/-! ## The list encoding produced by the extractor -/

/-- Every predicate in the list holds at `m`. -/
def AllHold {M : Type u} : List (M → Prop) → M → Prop
  | [], _ => True
  | p :: ps, m => p m ∧ AllHold ps m

/-- Every predicate in the list, except the one at position `k`, holds at `m`. -/
def AllExcept {M : Type u} : List (M → Prop) → Nat → M → Prop
  | [], _, _ => True
  | _ :: ps, 0, m => AllHold ps m
  | p :: ps, k + 1, m => p m ∧ AllExcept ps k m

/-- The predicate at position `k`; `True` past the end of the list. -/
def HypAt {M : Type u} : List (M → Prop) → Nat → M → Prop
  | [], _, _ => True
  | p :: _, 0, m => p m
  | _ :: ps, k + 1, m => HypAt ps k m

/-- A statement as the extractor produces it: hypotheses in binder order over one model type. -/
structure Spec (M : Type u) where
  hyps : List (M → Prop)
  concl : M → Prop

namespace Spec

variable {M : Type u} (S : Spec M)

/-- What the statement asserts. -/
def Holds : Prop := ∀ m, AllHold S.hyps m → S.concl m

/-- Some model satisfies every hypothesis. -/
def Nonvacuous : Prop := ∃ m, AllHold S.hyps m

/-- No model satisfies every hypothesis. -/
def Vacuous : Prop := ¬ S.Nonvacuous

/-- The statement with the hypothesis at position `k` removed. -/
def Drop (k : Nat) : Prop := ∀ m, AllExcept S.hyps k m → S.concl m

/-- The hypothesis at position `k` carries content. Past the end of the list this is false,
because `HypAt` is `True` there. -/
def LoadBearing (k : Nat) : Prop :=
  ∃ m, AllExcept S.hyps k m ∧ ¬ HypAt S.hyps k m ∧ ¬ S.concl m

/-- A certificate for the encoded statement. -/
structure Certificate : Prop where
  hasHypothesis : S.hyps ≠ []
  holds : S.Holds
  nonvacuous : S.Nonvacuous
  loadBearing : ∀ k, k < S.hyps.length → S.LoadBearing k

/-- The statement the encoding stands for. -/
def toStatement : Statement M (Fin S.hyps.length) where
  hyp i m := S.hyps.get i m
  concl := S.concl

end Spec

theorem allHold_iff {M : Type u} : ∀ (l : List (M → Prop)) (m : M),
    AllHold l m ↔ ∀ i : Fin l.length, l.get i m
  | [], _ => ⟨fun _ i => absurd i.isLt (Nat.not_lt_zero _), fun _ => trivial⟩
  | p :: ps, m => by
    show p m ∧ AllHold ps m ↔ _
    rw [allHold_iff ps m]
    constructor
    · intro h i
      match i, h with
      | ⟨0, _⟩, ⟨hp, _⟩ => exact hp
      | ⟨i + 1, hi⟩, ⟨_, hps⟩ => exact hps ⟨i, Nat.lt_of_succ_lt_succ hi⟩
    · intro h
      exact ⟨h ⟨0, Nat.succ_pos _⟩, fun ⟨i, hi⟩ => h ⟨i + 1, Nat.succ_lt_succ hi⟩⟩

theorem allExcept_iff {M : Type u} : ∀ (l : List (M → Prop)) (k : Nat) (m : M),
    AllExcept l k m ↔ ∀ i : Fin l.length, i.val ≠ k → l.get i m
  | [], _, _ => ⟨fun _ i => absurd i.isLt (Nat.not_lt_zero _), fun _ => trivial⟩
  | p :: ps, 0, m => by
    show AllHold ps m ↔ _
    rw [allHold_iff ps m]
    constructor
    · intro h i hi
      match i, hi with
      | ⟨0, _⟩, hi => exact absurd rfl hi
      | ⟨i + 1, hlt⟩, _ => exact h ⟨i, Nat.lt_of_succ_lt_succ hlt⟩
    · intro h i
      exact h ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ (Nat.succ_ne_zero _)
  | p :: ps, k + 1, m => by
    show p m ∧ AllExcept ps k m ↔ _
    rw [allExcept_iff ps k m]
    constructor
    · intro h i hi
      match i, h, hi with
      | ⟨0, _⟩, ⟨hp, _⟩, _ => exact hp
      | ⟨i + 1, hlt⟩, ⟨_, hps⟩, hi =>
        exact hps ⟨i, Nat.lt_of_succ_lt_succ hlt⟩ (fun e => hi (congrArg Nat.succ e))
    · intro h
      refine ⟨h ⟨0, Nat.succ_pos _⟩ (Nat.succ_ne_zero k).symm, fun i hi => ?_⟩
      exact h ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ (fun e => hi (Nat.succ.inj e))

theorem hypAt_get {M : Type u} : ∀ (l : List (M → Prop)) (i : Fin l.length) (m : M),
    HypAt l i.val m ↔ l.get i m
  | [], i, _ => absurd i.isLt (Nat.not_lt_zero _)
  | _ :: _, ⟨0, _⟩, _ => Iff.rfl
  | _ :: ps, ⟨i + 1, hi⟩, m => hypAt_get ps ⟨i, Nat.lt_of_succ_lt_succ hi⟩ m

namespace Spec

variable {M : Type u} (S : Spec M)

theorem holds_iff : S.Holds ↔ S.toStatement.Holds :=
  ⟨fun h m hm => h m ((allHold_iff S.hyps m).mpr hm),
   fun h m hm => h m ((allHold_iff S.hyps m).mp hm)⟩

theorem nonvacuous_iff : S.Nonvacuous ↔ S.toStatement.Nonvacuous :=
  ⟨fun ⟨m, hm⟩ => ⟨m, (allHold_iff S.hyps m).mp hm⟩,
   fun ⟨m, hm⟩ => ⟨m, (allHold_iff S.hyps m).mpr hm⟩⟩

private theorem fin_ne_iff {n : Nat} {i j : Fin n} : j ≠ i ↔ j.val ≠ i.val :=
  ⟨fun h e => h (Fin.ext e), fun h e => h (congrArg Fin.val e)⟩

private theorem others_iff (i : Fin S.hyps.length) (m : M) :
    AllExcept S.hyps i.val m ↔ ∀ j, j ≠ i → S.toStatement.hyp j m := by
  rw [allExcept_iff]
  exact ⟨fun h j hj => h j (fin_ne_iff.mp hj), fun h j hj => h j (fin_ne_iff.mpr hj)⟩

theorem drop_iff (i : Fin S.hyps.length) : S.Drop i.val ↔ S.toStatement.Drop i :=
  ⟨fun h m hm => h m ((S.others_iff i m).mpr hm),
   fun h m hm => h m ((S.others_iff i m).mp hm)⟩

theorem loadBearing_iff (i : Fin S.hyps.length) :
    S.LoadBearing i.val ↔ S.toStatement.LoadBearing i :=
  ⟨fun ⟨m, ho, hi, hc⟩ =>
      ⟨m, (S.others_iff i m).mp ho, fun h => hi ((hypAt_get S.hyps i m).mpr h), hc⟩,
   fun ⟨m, ho, hi, hc⟩ =>
      ⟨m, (S.others_iff i m).mpr ho, fun h => hi ((hypAt_get S.hyps i m).mp h), hc⟩⟩

private theorem ne_nil_iff (l : List (M → Prop)) : l ≠ [] ↔ Nonempty (Fin l.length) :=
  match l with
  | [] => ⟨fun h => absurd rfl h, fun ⟨i⟩ => absurd i.isLt (Nat.not_lt_zero _)⟩
  | _ :: _ => ⟨fun _ => ⟨⟨0, Nat.succ_pos _⟩⟩, fun _ => List.cons_ne_nil _ _⟩

/-- A certificate for the encoding is a certificate for the statement it encodes. -/
theorem certificate_iff : S.Certificate ↔ Anchor.Certificate S.toStatement :=
  ⟨fun c =>
    { hasHypothesis := (ne_nil_iff S.hyps).mp c.hasHypothesis
      holds := S.holds_iff.mp c.holds
      nonvacuous := S.nonvacuous_iff.mp c.nonvacuous
      loadBearing := fun i => (S.loadBearing_iff i).mp (c.loadBearing i.val i.isLt) },
   fun c =>
    { hasHypothesis := (ne_nil_iff S.hyps).mpr c.hasHypothesis
      holds := S.holds_iff.mpr c.holds
      nonvacuous := S.nonvacuous_iff.mpr c.nonvacuous
      loadBearing := fun k hk => (S.loadBearing_iff ⟨k, hk⟩).mpr (c.loadBearing ⟨k, hk⟩) }⟩

theorem vacuous_iff : S.Vacuous ↔ S.toStatement.Vacuous :=
  ⟨fun h h' => h (S.nonvacuous_iff.mpr h'), fun h h' => h (S.nonvacuous_iff.mp h')⟩

/-- A vacuous encoded statement has no certificate. -/
theorem not_certificate_of_vacuous (h : S.Vacuous) : ¬ S.Certificate :=
  fun c => h c.nonvacuous

/-- An encoded statement with a removable hypothesis has no certificate. -/
theorem not_certificate_of_drop {k : Nat} (hk : k < S.hyps.length) (h : S.Drop k) :
    ¬ S.Certificate := fun c =>
  match c.loadBearing k hk with
  | ⟨m, ho, _, hc⟩ => hc (h m ho)

/-- A statement with no hypotheses has no certificate. -/
theorem not_certificate_of_nil (h : S.hyps = []) : ¬ S.Certificate :=
  fun c => c.hasHypothesis h

/-- A conclusion true of every model makes every hypothesis removable. -/
theorem drop_of_trivial (h : ∀ m, S.concl m) (k : Nat) : S.Drop k :=
  fun m _ => h m

end Spec

/-! ## Rewriting a model tuple into separate variables

The extractor packs the model binders into nested `Sigma` types. These lemmas let `simp`
unpack an obligation back into the variables the reader wrote. -/

theorem sigma_exists_iff {α : Type u} {β : α → Type v} {P : Sigma β → Prop} :
    (∃ p, P p) ↔ ∃ a b, P ⟨a, b⟩ :=
  ⟨fun ⟨⟨a, b⟩, h⟩ => ⟨a, b, h⟩, fun ⟨a, b, h⟩ => ⟨⟨a, b⟩, h⟩⟩

theorem sigma_forall_iff {α : Type u} {β : α → Type v} {P : Sigma β → Prop} :
    (∀ p, P p) ↔ ∀ a b, P ⟨a, b⟩ :=
  ⟨fun h a b => h ⟨a, b⟩, fun h ⟨a, b⟩ => h a b⟩

theorem unit_exists_iff {P : Unit → Prop} : (∃ m, P m) ↔ P () :=
  ⟨fun ⟨(), h⟩ => h, fun h => ⟨(), h⟩⟩

theorem unit_forall_iff {P : Unit → Prop} : (∀ m, P m) ↔ P () :=
  ⟨fun h => h (), fun h () => h⟩

theorem plift_exists_iff {p : Prop} {P : PLift p → Prop} : (∃ x, P x) ↔ ∃ h : p, P ⟨h⟩ :=
  ⟨fun ⟨⟨h⟩, hp⟩ => ⟨h, hp⟩, fun ⟨h, hp⟩ => ⟨⟨h⟩, hp⟩⟩

theorem plift_forall_iff {p : Prop} {P : PLift p → Prop} : (∀ x, P x) ↔ ∀ h : p, P ⟨h⟩ :=
  ⟨fun H h => H ⟨h⟩, fun H ⟨h⟩ => H h⟩

/-! ## Assembling a certificate from separate proofs -/

/-- `P k` for every `k < n`, as a nested conjunction the kernel checks term by term. -/
def ForallBelow (P : Nat → Prop) : Nat → Prop
  | 0 => True
  | n + 1 => ForallBelow P n ∧ P n

theorem forallBelow_iff (P : Nat → Prop) : ∀ n, ForallBelow P n ↔ ∀ k, k < n → P k
  | 0 => ⟨fun _ k hk => absurd hk (Nat.not_lt_zero k), fun _ => trivial⟩
  | n + 1 => by
    show ForallBelow P n ∧ P n ↔ _
    rw [forallBelow_iff P n]
    constructor
    · intro h k hk
      match Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk), h with
      | Or.inl hk, ⟨h, _⟩ => exact h k hk
      | Or.inr hk, ⟨_, hn⟩ => exact hk ▸ hn
    · intro h
      exact ⟨fun k hk => h k (Nat.lt_succ_of_lt hk), h n (Nat.lt_succ_self n)⟩

/-- A certificate from its parts, with the load-bearing witnesses given one per hypothesis. -/
theorem Spec.certificate_of {M : Type u} (S : Spec M) (hne : S.hyps ≠ []) (hh : S.Holds)
    (hn : S.Nonvacuous) (hl : ForallBelow S.LoadBearing S.hyps.length) : S.Certificate :=
  ⟨hne, hh, hn, (forallBelow_iff _ _).mp hl⟩

end Anchor
