# Anchor certificate format

Version 0.1, 8 October 2026. Lean v4.27.0-rc1, Mathlib d7ea567.

Lean's kernel checks that a proof proves its statement. Anchor adds kernel-checked facts about the statement itself: whether its hypotheses can all hold, whether each one is needed, which definitions a reader has to read, and which classical principles the proof uses. This page specifies what Anchor extracts, the declarations it adds, and the reports and records it writes. Every claim Anchor makes is a theorem in the environment, and it is accepted only when `#print axioms` lists nothing beyond `propext`, `Classical.choice` and `Quot.sound`. A proof that reaches `Lean.ofReduceBool` through a library lemma proved by `native_decide` leaves its obligation open, with that reason in the report. The certificate also contains the theorem's own proof, and its axioms are listed with it.

## 1. The statement as data

A statement is a model type `M`, a list of hypotheses `M → Prop` in binder order, and a conclusion `M → Prop`:

    structure Anchor.Spec (M : Type u) where
      hyps  : List (M → Prop)
      concl : M → Prop

Extraction opens the theorem's type with `forallTelescope` and sorts its binders:

- A binder whose type is not a proposition (a number, a type, a structure, an instance of a data class) becomes a component of the model. Components are packed into nested `Sigma` types, so later components may depend on earlier ones.
- A propositional binder that the conclusion or a later binder type mentions is a *premise*. It stays in the model, wrapped as `PLift p`, because the statement cannot be written without it. Premises are listed in the report and are not tested for content.
- Every other propositional binder is a hypothesis.

A universe parameter that occurs as a bare `Sort u` is set to 1 and every other one to 0, so all generated declarations are monomorphic; the report records the choice in its `universes` field.

For a theorem `foo`, Anchor adds `foo.anchorSpec` and `foo.anchorSpec_iff`, a kernel-checked proof that `foo.anchorSpec.Holds` is equivalent to the type of `foo`. The encoding is therefore checked, not trusted.

## 2. The notions

For `S : Spec M`, with `AllHold` meaning every hypothesis in the list holds and `AllExcept k` every hypothesis except the one at position `k`:

| Notion | Definition |
|----|----|
| `Holds` | `∀ m, AllHold S.hyps m → S.concl m` |
| `Nonvacuous` | `∃ m, AllHold S.hyps m` |
| `Vacuous` | `¬ Nonvacuous` |
| `Drop k` | `∀ m, AllExcept S.hyps k m → S.concl m` |
| `LoadBearing k` | `∃ m, AllExcept S.hyps k m ∧ ¬ HypAt S.hyps k m ∧ ¬ S.concl m` |
| `Certificate` | at least one hypothesis, `Holds`, `Nonvacuous`, and `LoadBearing k` for every position |

A load-bearing hypothesis cannot be dropped (`Spec.not_drop_of_loadBearing`), a vacuous statement has no certificate, and a certified statement has a conclusion some model violates. All of these are theorems in `Anchor.Core`.

The same notions exist over an arbitrary index type as `Anchor.Statement`.

## 3. Declarations Anchor adds

| Name | Type | When |
|----|----|----|
| `foo.anchorSpec` | the extracted `Spec` | always |
| `foo.anchorSpec_iff` | `foo.anchorSpec.Holds ↔ (type of foo)` | always |
| `foo.anchorSpec_holds` | `foo.anchorSpec.Holds` | always |
| `foo.anchorNonvacuous` | `Nonvacuous` | a model was found |
| `foo.anchorVacuous` | `Vacuous` | the hypotheses contradict each other |
| `foo.anchorDrop_k` | `Drop k` | hypothesis `k` is not needed |
| `foo.anchorLoadBearing_k` | `LoadBearing k` | a counter-model for `k` was found |
| `foo.anchorTrivial` | the conclusion holds of every model | the conclusion needs no hypothesis |
| `foo.anchorCertificate` | `foo.anchorSpec.Certificate` | every obligation is proved |

`#anchor foo` reports without keeping declarations; `anchor_cert foo` keeps them. After `anchor_spec foo`, an author may supply any obligation under the names above, and Anchor uses it instead of searching. A supplied proof counts exactly like a found one, because the kernel checks both.

### How obligations are discharged

For each obligation Anchor tries, in order: a declaration already supplied under the obligation's name; for `Drop k`, the original proof term, when it is a lambda over every binder whose body and later binder types never use hypothesis `k`; then a search that builds candidate models from small literals and instances and closes the resulting goals with `decide`, `norm_num`, `simp`, `omega`, `linarith`, `positivity` and `grind`. When no small candidate works, Plausible's random testing proposes one, with a fixed seed. A universal goal (`Drop k`, `Vacuous`) goes to the same closers after `push_neg` and `intro`, then to `nlinarith`, `order` and `aesop`. Every attempt runs under a fixed heartbeat budget (`anchor.search.attemptHeartbeats` for a whole obligation), so the same input gives byte-identical output.

## 4. Verdicts

| Verdict | Meaning |
|----|----|
| `CERTIFIED` | `foo.anchorCertificate` was added |
| `CERTIFIED (premises untested: N)` | the same, with N premises kept in the model |
| `VACUOUS` | `foo.anchorVacuous` was added |
| `DECORATIVE [k, ...]` | a model exists, and `foo.anchorDrop_k` was added for each listed position |
| `TRIVIAL CONCLUSION (...)` | `foo.anchorTrivial` was added: the conclusion holds of every model, so every hypothesis is removable |
| `NO HYPOTHESES (no certificate)` | nothing to certify; the conclusion stands alone |
| `NONVACUOUS, EVERY HYPOTHESIS LOAD-BEARING (statement only)` | no proof of the theorem is read (it is `sorry`), so `Holds` is unavailable; `Nonvacuous` and every `LoadBearing k` were proved |
| `UNCERTIFIED (...)` | some obligation is neither proved nor refuted; the parenthesis lists which, and any hypotheses proved removable |
| `UNSUPPORTED (...)` | the statement could not be extracted; the reason is given |

Every verdict except `NO HYPOTHESES`, `UNCERTIFIED` and `UNSUPPORTED` is a claim, and the report names the declarations that prove it. An `UNCERTIFIED` verdict marks a gap in the search, never a finding; the hypotheses it lists as removable are proved.

## 5. The report

`#anchor_json foo` prints one JSON object per statement with keys `decl`, `supported`, `reason`, `universes`, `model`, `premises`, `hypotheses` (each with `text`, `load_bearing` and `drop`), `conclusion`, `holds`, `nonvacuous`, `vacuous`, `trivial_conclusion`, `verdict` and `axioms`. Each obligation is `{"status":"proved","method":...}`, `{"status":"open","goal":...}` or `{"status":"skipped"}`, where the method is `supplied`, `proof term` or `search`. `axioms` lists every added declaration with its `#print axioms` output.

## 6. Pinned definitions

    def Anchor.Pinned {α : Sort u} (spec : α → Prop) (r : α → α → Prop) (a : α) : Prop :=
      spec a ∧ ∀ b, spec b → r b a

`@[pinned]` on a theorem of type `Anchor.Pinned spec r c`, with `c` a constant, records `c ↦ (theorem, spec, r)` in an environment extension that persists across imports. The attribute refuses any other shape and any proof that depends on `sorryAx`. A reader of a statement mentioning `c` then checks `spec` and `r` instead of the body of `c`: a statement that respects `r` holds of `c` exactly when it holds of everything meeting `spec` (`Anchor.pinned_statement_iff`). `#pinned` prints the index.

## 7. Review surfaces

The review surface of a declaration is the list of definitions a reader has to read to know what its statement says. `#surface foo` walks the constants reached from the type of `foo`, breadth first, ties broken by name. Each entry is `read` (a definition, instance or inductive the reader must read; its body is walked), `pinned` (its specification is walked instead of its body), or `boundary` (a trusted library, by module prefix; not expanded). Theorems contribute their type only. Compiler-generated auxiliaries are folded into the constant that reached them. Boundary functions with a junk value (`x / 0 = 0`, truncated subtraction, `√x = 0` for `x < 0`) carry a note. `#surface_json` prints the same list as JSON.

## 8. Sign-offs

A sign-off is one JSON line:

    {"decl": ..., "module": ..., "sentence": ..., "reviewer": ..., "date": ...,
     "sha256": ..., "entries": [{"name": ..., "sha256": ...}, ...]}

`sentence` is the English claim the reviewer checked the statement against. Each entry hashes one constant of the review surface: the declaration's type (never its proof); for a read constant its kind and the expressions the surface walks; for a pinned constant its type and the pinning theorem's name, specification and relation; for a boundary constant its kind and type. Expressions are printed structurally, with bound variables as de Bruijn indices and binder names dropped, so reordering a file or renaming a bound variable changes nothing. `sha256` is the hash of the entry list.

`lake exe anchor check --file signoffs.jsonl` recomputes every entry and prints `current` or `STALE` with the constants changed, added and removed. It exits 0 when everything is current, 1 when anything is stale, and 2 on an empty file. SHA-256 is implemented in Lean and checked against the FIPS 180-4 test vectors.

## 9. The classical price

`#price foo` walks the closure `Lean.collectAxioms` walks and reports each classical entry point it meets: the axiom `Classical.choice`, the principles `Init/Classical.lean` derives from it, Mathlib's `Classical.dec` family, and any constant tagged `@[classical_entry]`. Each entry carries a shortest path from `foo`, whether it is reached first (not only inside another entry's proof), and a role: *invoked* when a proof or function uses it, *stated* when the constant is a proposition that a statement mentions. `#price_json foo` emits report `anchor.price/1` with keys `decl`, `axioms`, `entries`, `registered_in_scope` and `visited`. The command fails if its walk and `Lean.collectAxioms` disagree on the axioms.

## 10. Trust

Anchor's claims rest on the Lean kernel and on the three standard axioms. The extraction, the search and the report generator are untrusted: an extraction error cannot pass `anchorSpec_iff`, a wrong witness cannot pass the kernel, and a report line names the declaration that backs it. The package contains no `sorry`, `admit` or `axiom`.
