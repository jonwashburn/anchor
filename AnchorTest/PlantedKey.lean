import Mathlib
import AnchorTest.Planted

/-!
# Answer key for the planted statements

Every label in `planted_labels.json` for a statement that has hypotheses and does not depend on
a hypothesis proof is proved here in plain logic, over the statement's own model variables.

* certifiable (`cert_NN_key`): a model of all the hypotheses, then for each hypothesis in binder
  order a model where the other hypotheses hold, that one fails, and the conclusion fails;
* vacuous (`vac_NN_key`): no model satisfies all the hypotheses;
* decorative (`dec_NN_key`): a model of all the hypotheses, and the statement with the named
  hypothesis removed. `dec_NN_others` gives a load-bearing model for each remaining hypothesis.

Each `example` checks that the key reads the planted theorem's statement as written: the planted
proof must have exactly the type spelled out next to its key. Anchor never imports this file.
-/

namespace AnchorTest.PlantedKey

open AnchorTest.Planted

/-! ## cert -/

example : ∀ n : ℕ, 2 ∣ n → 3 ∣ n → 6 ∣ n := cert_01

theorem cert_01_key :
    (∃ n : ℕ, 2 ∣ n ∧ 3 ∣ n) ∧
    (∃ n : ℕ, ¬ 2 ∣ n ∧ 3 ∣ n ∧ ¬ 6 ∣ n) ∧
    (∃ n : ℕ, 2 ∣ n ∧ ¬ 3 ∣ n ∧ ¬ 6 ∣ n) :=
  ⟨⟨6, by decide, by decide⟩, ⟨3, by decide, by decide, by decide⟩,
    ⟨2, by decide, by decide, by decide⟩⟩

example : ∀ a b c : ℤ, a ∣ b → a ∣ c → a ∣ b + c := cert_02

theorem cert_02_key :
    (∃ a b c : ℤ, a ∣ b ∧ a ∣ c) ∧
    (∃ a b c : ℤ, ¬ a ∣ b ∧ a ∣ c ∧ ¬ a ∣ b + c) ∧
    (∃ a b c : ℤ, a ∣ b ∧ ¬ a ∣ c ∧ ¬ a ∣ b + c) :=
  ⟨⟨1, 0, 0, one_dvd 0, one_dvd 0⟩, ⟨2, 1, 0, by norm_num, dvd_zero 2, by norm_num⟩,
    ⟨2, 0, 1, dvd_zero 2, by norm_num, by norm_num⟩⟩

example : ∀ x : ℚ, 1 < x → x < 2 → 1 < x ^ 2 ∧ x ^ 2 < 4 := cert_03

theorem cert_03_key :
    (∃ x : ℚ, 1 < x ∧ x < 2) ∧
    (∃ x : ℚ, ¬ 1 < x ∧ x < 2 ∧ ¬ (1 < x ^ 2 ∧ x ^ 2 < 4)) ∧
    (∃ x : ℚ, 1 < x ∧ ¬ x < 2 ∧ ¬ (1 < x ^ 2 ∧ x ^ 2 < 4)) :=
  ⟨⟨3 / 2, by norm_num, by norm_num⟩, ⟨0, by norm_num, by norm_num, by norm_num⟩,
    ⟨2, by norm_num, by norm_num, by norm_num⟩⟩

example : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x ^ 2 = y ^ 2 → x = y := cert_04

theorem cert_04_key :
    (∃ x y : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ x ^ 2 = y ^ 2) ∧
    (∃ x y : ℝ, ¬ 0 ≤ x ∧ 0 ≤ y ∧ x ^ 2 = y ^ 2 ∧ ¬ x = y) ∧
    (∃ x y : ℝ, 0 ≤ x ∧ ¬ 0 ≤ y ∧ x ^ 2 = y ^ 2 ∧ ¬ x = y) ∧
    (∃ x y : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ ¬ x ^ 2 = y ^ 2 ∧ ¬ x = y) :=
  ⟨⟨0, 0, le_rfl, le_rfl, rfl⟩,
    ⟨-1, 1, by norm_num, by norm_num, by norm_num, by norm_num⟩,
    ⟨1, -1, by norm_num, by norm_num, by norm_num, by norm_num⟩,
    ⟨0, 1, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

example : ∀ s t : Finset ℕ, s ⊆ t → t.card ≤ s.card → s = t := cert_05

theorem cert_05_key :
    (∃ s t : Finset ℕ, s ⊆ t ∧ t.card ≤ s.card) ∧
    (∃ s t : Finset ℕ, ¬ s ⊆ t ∧ t.card ≤ s.card ∧ ¬ s = t) ∧
    (∃ s t : Finset ℕ, s ⊆ t ∧ ¬ t.card ≤ s.card ∧ ¬ s = t) :=
  ⟨⟨∅, ∅, by decide, by decide⟩, ⟨{0}, {1}, by decide, by decide, by decide⟩,
    ⟨∅, {0}, by decide, by decide, by decide⟩⟩

example : ∀ l : List ℕ, (∀ x ∈ l, 0 < x) → l ≠ [] → 0 < l.sum := cert_06

theorem cert_06_key :
    (∃ l : List ℕ, (∀ x ∈ l, 0 < x) ∧ l ≠ []) ∧
    (∃ l : List ℕ, ¬ (∀ x ∈ l, 0 < x) ∧ l ≠ [] ∧ ¬ 0 < l.sum) ∧
    (∃ l : List ℕ, (∀ x ∈ l, 0 < x) ∧ ¬ l ≠ [] ∧ ¬ 0 < l.sum) :=
  ⟨⟨[1], by decide, by decide⟩, ⟨[0], by decide, by decide, by decide⟩,
    ⟨[], by decide, by decide, by decide⟩⟩

example : ∀ f : ℝ → ℝ, StrictMono f → ∀ a b : ℝ, f a < f b → a < b := cert_07

theorem cert_07_key :
    (∃ (f : ℝ → ℝ) (a b : ℝ), StrictMono f ∧ f a < f b) ∧
    (∃ (f : ℝ → ℝ) (a b : ℝ), ¬ StrictMono f ∧ f a < f b ∧ ¬ a < b) ∧
    (∃ (f : ℝ → ℝ) (a b : ℝ), StrictMono f ∧ ¬ f a < f b ∧ ¬ a < b) := by
  refine ⟨⟨id, 0, 1, strictMono_id, by norm_num⟩,
    ⟨fun x => -x, 1, 0, ?_, by norm_num, by norm_num⟩,
    ⟨id, 0, 0, strictMono_id, lt_irrefl _, lt_irrefl _⟩⟩
  intro hf
  have h := hf (show (0 : ℝ) < 1 by norm_num)
  norm_num at h

example : ∀ {G : Type} [Group G] (a b : G), a * b = b * a → a ^ 2 = 1 → b ^ 2 = 1 →
    (a * b) ^ 2 = 1 := @cert_08

theorem cert_08_key :
    (∃ (G : Type) (_ : Group G) (a b : G), a * b = b * a ∧ a ^ 2 = 1 ∧ b ^ 2 = 1) ∧
    (∃ (G : Type) (_ : Group G) (a b : G),
      ¬ a * b = b * a ∧ a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ ¬ (a * b) ^ 2 = 1) ∧
    (∃ (G : Type) (_ : Group G) (a b : G),
      a * b = b * a ∧ ¬ a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ ¬ (a * b) ^ 2 = 1) ∧
    (∃ (G : Type) (_ : Group G) (a b : G),
      a * b = b * a ∧ a ^ 2 = 1 ∧ ¬ b ^ 2 = 1 ∧ ¬ (a * b) ^ 2 = 1) :=
  ⟨⟨Equiv.Perm (Fin 3), inferInstance, 1, 1, by decide, by decide, by decide⟩,
    ⟨Equiv.Perm (Fin 3), inferInstance, Equiv.swap 0 1, Equiv.swap 1 2,
      by decide, by decide, by decide, by decide⟩,
    ⟨Equiv.Perm (Fin 3), inferInstance, Equiv.swap 0 1 * Equiv.swap 1 2, 1,
      by decide, by decide, by decide, by decide⟩,
    ⟨Equiv.Perm (Fin 3), inferInstance, 1, Equiv.swap 0 1 * Equiv.swap 1 2,
      by decide, by decide, by decide, by decide⟩⟩

example : ∀ {M : Type} [Monoid M] (a b c : M), a * b = 1 → c * a = 1 → b = c := @cert_09

theorem cert_09_key :
    (∃ (M : Type) (_ : Monoid M) (a b c : M), a * b = 1 ∧ c * a = 1) ∧
    (∃ (M : Type) (_ : Monoid M) (a b c : M), ¬ a * b = 1 ∧ c * a = 1 ∧ ¬ b = c) ∧
    (∃ (M : Type) (_ : Monoid M) (a b c : M), a * b = 1 ∧ ¬ c * a = 1 ∧ ¬ b = c) :=
  ⟨⟨ℕ, inferInstance, 1, 1, 1, by decide, by decide⟩,
    ⟨ℕ, inferInstance, 1, 2, 1, by decide, by decide, by decide⟩,
    ⟨ℕ, inferInstance, 1, 1, 2, by decide, by decide, by decide⟩⟩

example : ∀ f : ℝ → ℝ, Monotone f → Antitone f → f 0 = f 1 := cert_10

theorem cert_10_key :
    (∃ f : ℝ → ℝ, Monotone f ∧ Antitone f) ∧
    (∃ f : ℝ → ℝ, ¬ Monotone f ∧ Antitone f ∧ ¬ f 0 = f 1) ∧
    (∃ f : ℝ → ℝ, Monotone f ∧ ¬ Antitone f ∧ ¬ f 0 = f 1) := by
  refine ⟨⟨fun _ => 0, monotone_const, antitone_const⟩,
    ⟨fun x => -x, ?_, ?_, by norm_num⟩, ⟨id, monotone_id, ?_, by norm_num⟩⟩
  · intro hm
    have h := hm (zero_le_one : (0 : ℝ) ≤ 1)
    norm_num at h
  · intro a b h
    exact neg_le_neg h
  · intro ha
    have h := ha (zero_le_one : (0 : ℝ) ≤ 1)
    norm_num at h

/-! ## vac -/

example : ∀ {α : Type} [Preorder α] (a b : α), a < b → b ≤ a → a = b := @vac_01

theorem vac_01_key : ¬ ∃ (α : Type) (_ : Preorder α) (a b : α), a < b ∧ b ≤ a := by
  rintro ⟨α, _, a, b, hab, hba⟩
  exact lt_irrefl a (lt_of_lt_of_le hab hba)

example : ∀ n : ℕ, Even n → Even (n + 1) → n ^ 2 = n := vac_02

theorem vac_02_key : ¬ ∃ n : ℕ, Even n ∧ Even (n + 1) := by
  rintro ⟨n, h1, h2⟩
  exact Nat.even_add_one.1 h2 h1

example : ∀ x y : ℝ, x ^ 2 + y ^ 2 < 2 * x * y → x = y := vac_03

theorem vac_03_key : ¬ ∃ x y : ℝ, x ^ 2 + y ^ 2 < 2 * x * y := by
  rintro ⟨x, y, h⟩
  nlinarith [sq_nonneg (x - y)]

example : ∀ a : ℤ, 6 ∣ a → 4 ∣ a + 1 → a = 3 := vac_04

theorem vac_04_key : ¬ ∃ a : ℤ, 6 ∣ a ∧ 4 ∣ a + 1 := by
  rintro ⟨a, h6, h4⟩
  omega

example : ∀ s : Finset ℕ, s ⊆ Finset.range 3 → 4 ≤ s.card → s.sum id = 0 := vac_05

theorem vac_05_key : ¬ ∃ s : Finset ℕ, s ⊆ Finset.range 3 ∧ 4 ≤ s.card := by
  rintro ⟨s, hs, hcard⟩
  have h := Finset.card_le_card hs
  rw [Finset.card_range] at h
  omega

example : ∀ θ : ℝ, Real.sin θ ^ 2 + Real.cos θ ^ 2 = 2 → θ = 0 := vac_06

theorem vac_06_key : ¬ ∃ θ : ℝ, Real.sin θ ^ 2 + Real.cos θ ^ 2 = 2 := by
  rintro ⟨θ, h⟩
  rw [Real.sin_sq_add_cos_sq] at h
  norm_num at h

example : ∀ p : ℕ, p.Prime → p ∣ 1 → p = 2 := vac_07

theorem vac_07_key : ¬ ∃ p : ℕ, p.Prime ∧ p ∣ 1 := by
  rintro ⟨p, hp, h⟩
  exact hp.not_dvd_one h

example : ∀ a b c : ℚ, a < b → b < c → c < a → a = b := vac_08

theorem vac_08_key : ¬ ∃ a b c : ℚ, a < b ∧ b < c ∧ c < a := by
  rintro ⟨a, b, c, hab, hbc, hca⟩
  linarith

example : ∀ f : ℕ → ℕ, (∀ n, f n < f (n + 1)) → f 5 < f 2 → f 0 = 0 := vac_09

theorem vac_09_key : ¬ ∃ f : ℕ → ℕ, (∀ n, f n < f (n + 1)) ∧ f 5 < f 2 := by
  rintro ⟨f, hf, h⟩
  have h25 : f 2 < f 5 := strictMono_nat_of_lt_succ hf (by norm_num)
  omega

example : ∀ l : List ℕ, l.length = 2 → l.sum = 5 → (∀ x ∈ l, x ≤ 2) → l = [2, 3] := vac_10

theorem vac_10_key : ¬ ∃ l : List ℕ, l.length = 2 ∧ l.sum = 5 ∧ ∀ x ∈ l, x ≤ 2 := by
  rintro ⟨l, hlen, hsum, hle⟩
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.1 hlen
  have ha := hle a (by simp)
  have hb := hle b (by simp)
  simp only [List.sum_cons, List.sum_nil] at hsum
  omega

/-! ## dec -/

example : ∀ {K : Type} [Field K] (a b : K), a / b = 1 → b ≠ 0 → a = b := @dec_01

/-- Hypothesis 1 (`b ≠ 0`) is removable. -/
theorem dec_01_key :
    (∃ (K : Type) (_ : Field K) (a b : K), a / b = 1 ∧ b ≠ 0) ∧
    (∀ (K : Type) [Field K] (a b : K), a / b = 1 → a = b) := by
  refine ⟨⟨ℚ, inferInstance, 1, 1, by norm_num, by norm_num⟩, ?_⟩
  intro K _ a b h
  by_cases hb : b = 0
  · subst hb
    simp at h
  · exact (div_eq_one_iff_eq hb).1 h

theorem dec_01_others :
    ∃ (K : Type) (_ : Field K) (a b : K), ¬ a / b = 1 ∧ b ≠ 0 ∧ ¬ a = b :=
  ⟨ℚ, inferInstance, 0, 1, by norm_num, by norm_num, by norm_num⟩

example : ∀ n : ℕ, 0 < n → 2 ≤ n → n + 1 < n ^ 2 := dec_02

/-- Hypothesis 0 (`0 < n`) is removable. -/
theorem dec_02_key :
    (∃ n : ℕ, 0 < n ∧ 2 ≤ n) ∧ (∀ n : ℕ, 2 ≤ n → n + 1 < n ^ 2) :=
  ⟨⟨2, by norm_num, le_rfl⟩, fun n h2 => by nlinarith⟩

theorem dec_02_others : ∃ n : ℕ, 0 < n ∧ ¬ 2 ≤ n ∧ ¬ n + 1 < n ^ 2 :=
  ⟨1, by norm_num, by norm_num, by norm_num⟩

example : ∀ x : ℝ, x ^ 3 = 8 → 0 < x → x = 2 := dec_03

/-- Hypothesis 1 (`0 < x`) is removable. -/
theorem dec_03_key :
    (∃ x : ℝ, x ^ 3 = 8 ∧ 0 < x) ∧ (∀ x : ℝ, x ^ 3 = 8 → x = 2) := by
  refine ⟨⟨2, by norm_num, by norm_num⟩, fun x h => ?_⟩
  have hf : (x - 2) * (x ^ 2 + 2 * x + 4) = 0 := by linear_combination h
  rcases mul_eq_zero.1 hf with h1 | h1
  · linarith
  · exfalso
    nlinarith [sq_nonneg (x + 1)]

theorem dec_03_others : ∃ x : ℝ, ¬ x ^ 3 = 8 ∧ 0 < x ∧ ¬ x = 2 :=
  ⟨1, by norm_num, by norm_num, by norm_num⟩

example : ∀ s t : Finset ℕ, s ⊆ t → s.Nonempty → s.card ≤ t.card := dec_04

/-- Hypothesis 1 (`s.Nonempty`) is removable. -/
theorem dec_04_key :
    (∃ s t : Finset ℕ, s ⊆ t ∧ s.Nonempty) ∧
    (∀ s t : Finset ℕ, s ⊆ t → s.card ≤ t.card) :=
  ⟨⟨{0}, {0}, Finset.Subset.refl _, ⟨0, by simp⟩⟩, fun s t h => Finset.card_le_card h⟩

theorem dec_04_others : ∃ s t : Finset ℕ, ¬ s ⊆ t ∧ s.Nonempty ∧ ¬ s.card ≤ t.card :=
  ⟨{0, 1}, {0}, by decide, ⟨0, by simp⟩, by decide⟩

example : ∀ (l : List ℕ) (a : ℕ), l ≠ [] → a ∈ l → a ∈ l.reverse := dec_05

/-- Hypothesis 0 (`l ≠ []`) is removable. -/
theorem dec_05_key :
    (∃ (l : List ℕ) (a : ℕ), l ≠ [] ∧ a ∈ l) ∧
    (∀ (l : List ℕ) (a : ℕ), a ∈ l → a ∈ l.reverse) :=
  ⟨⟨[0], 0, by decide, by decide⟩, fun l a h => List.mem_reverse.2 h⟩

theorem dec_05_others : ∃ (l : List ℕ) (a : ℕ), l ≠ [] ∧ ¬ a ∈ l ∧ ¬ a ∈ l.reverse :=
  ⟨[1], 0, by decide, by decide, by decide⟩

example : ∀ a b : ℤ, a ∣ b → 0 < b → a ≠ 0 → a.natAbs ≤ b.natAbs := dec_06

/-- Hypothesis 2 (`a ≠ 0`) is removable. -/
theorem dec_06_key :
    (∃ a b : ℤ, a ∣ b ∧ 0 < b ∧ a ≠ 0) ∧
    (∀ a b : ℤ, a ∣ b → 0 < b → a.natAbs ≤ b.natAbs) :=
  ⟨⟨1, 1, one_dvd 1, one_pos, one_ne_zero⟩,
    fun _ _ h hb => Int.natAbs_le_of_dvd_ne_zero h hb.ne'⟩

theorem dec_06_others :
    (∃ a b : ℤ, ¬ a ∣ b ∧ 0 < b ∧ a ≠ 0 ∧ ¬ a.natAbs ≤ b.natAbs) ∧
    (∃ a b : ℤ, a ∣ b ∧ ¬ 0 < b ∧ a ≠ 0 ∧ ¬ a.natAbs ≤ b.natAbs) :=
  ⟨⟨2, 1, by norm_num, by norm_num, by norm_num, by decide⟩,
    ⟨2, 0, dvd_zero 2, by norm_num, by norm_num, by decide⟩⟩

example : ∀ f : ℝ → ℝ, StrictMono f → Continuous f → ∀ a b : ℝ, f a = f b → a = b := dec_07

/-- Hypothesis 1 (`Continuous f`) is removable. -/
theorem dec_07_key :
    (∃ (f : ℝ → ℝ) (a b : ℝ), StrictMono f ∧ Continuous f ∧ f a = f b) ∧
    (∀ f : ℝ → ℝ, StrictMono f → ∀ a b : ℝ, f a = f b → a = b) :=
  ⟨⟨id, 0, 0, strictMono_id, continuous_id, rfl⟩, fun _ hf _ _ h => hf.injective h⟩

theorem dec_07_others :
    (∃ (f : ℝ → ℝ) (a b : ℝ), ¬ StrictMono f ∧ Continuous f ∧ f a = f b ∧ ¬ a = b) ∧
    (∃ (f : ℝ → ℝ) (a b : ℝ), StrictMono f ∧ Continuous f ∧ ¬ f a = f b ∧ ¬ a = b) := by
  refine ⟨⟨fun _ => 0, 0, 1, ?_, continuous_const, rfl, by norm_num⟩,
    ⟨id, 0, 1, strictMono_id, continuous_id, by norm_num, by norm_num⟩⟩
  intro hm
  have h := hm (show (0 : ℝ) < 1 by norm_num)
  simp at h

example : ∀ {G : Type} [Group G] (a b : G), a * b = b * a → a * b = 1 → b * a = 1 := @dec_08

/-- Hypothesis 0 (`a * b = b * a`) is removable. -/
theorem dec_08_key :
    (∃ (G : Type) (_ : Group G) (a b : G), a * b = b * a ∧ a * b = 1) ∧
    (∀ (G : Type) [Group G] (a b : G), a * b = 1 → b * a = 1) := by
  refine ⟨⟨Equiv.Perm (Fin 3), inferInstance, 1, 1, rfl, by decide⟩, ?_⟩
  intro G _ a b h
  rw [eq_inv_of_mul_eq_one_left h]
  simp

theorem dec_08_others :
    ∃ (G : Type) (_ : Group G) (a b : G), a * b = b * a ∧ ¬ a * b = 1 ∧ ¬ b * a = 1 :=
  ⟨Equiv.Perm (Fin 3), inferInstance, Equiv.swap 0 1, 1, by decide, by decide, by decide⟩

example : ∀ {α : Type} [LinearOrder α] (a b c : α), a < b → b ≤ c → a ≠ c → a < c := @dec_09

/-- Hypothesis 2 (`a ≠ c`) is removable. -/
theorem dec_09_key :
    (∃ (α : Type) (_ : LinearOrder α) (a b c : α), a < b ∧ b ≤ c ∧ a ≠ c) ∧
    (∀ (α : Type) [LinearOrder α] (a b c : α), a < b → b ≤ c → a < c) := by
  refine ⟨⟨ℕ, inferInstance, 0, 1, 1, by decide, by decide, by decide⟩, ?_⟩
  intro α _ a b c hab hbc
  exact lt_of_lt_of_le hab hbc

theorem dec_09_others :
    (∃ (α : Type) (_ : LinearOrder α) (a b c : α), ¬ a < b ∧ b ≤ c ∧ a ≠ c ∧ ¬ a < c) ∧
    (∃ (α : Type) (_ : LinearOrder α) (a b c : α), a < b ∧ ¬ b ≤ c ∧ a ≠ c ∧ ¬ a < c) :=
  ⟨⟨ℕ, inferInstance, 1, 0, 0, by decide, by decide, by decide, by decide⟩,
    ⟨ℕ, inferInstance, 1, 2, 0, by decide, by decide, by decide, by decide⟩⟩

example : ∀ x y : ℚ, 0 < y → x ≠ y → x < y → x / y < 1 := dec_10

/-- Hypothesis 1 (`x ≠ y`) is removable. -/
theorem dec_10_key :
    (∃ x y : ℚ, 0 < y ∧ x ≠ y ∧ x < y) ∧ (∀ x y : ℚ, 0 < y → x < y → x / y < 1) :=
  ⟨⟨0, 1, by norm_num, by norm_num, by norm_num⟩, fun x y hy h => (div_lt_one hy).2 h⟩

theorem dec_10_others :
    (∃ x y : ℚ, ¬ 0 < y ∧ x ≠ y ∧ x < y ∧ ¬ x / y < 1) ∧
    (∃ x y : ℚ, 0 < y ∧ x ≠ y ∧ ¬ x < y ∧ ¬ x / y < 1) :=
  ⟨⟨-2, -1, by norm_num, by norm_num, by norm_num, by norm_num⟩,
    ⟨2, 1, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

end AnchorTest.PlantedKey

/-! ## Axiom audit -/

#print axioms AnchorTest.PlantedKey.cert_01_key
#print axioms AnchorTest.PlantedKey.cert_02_key
#print axioms AnchorTest.PlantedKey.cert_03_key
#print axioms AnchorTest.PlantedKey.cert_04_key
#print axioms AnchorTest.PlantedKey.cert_05_key
#print axioms AnchorTest.PlantedKey.cert_06_key
#print axioms AnchorTest.PlantedKey.cert_07_key
#print axioms AnchorTest.PlantedKey.cert_08_key
#print axioms AnchorTest.PlantedKey.cert_09_key
#print axioms AnchorTest.PlantedKey.cert_10_key
#print axioms AnchorTest.PlantedKey.vac_01_key
#print axioms AnchorTest.PlantedKey.vac_02_key
#print axioms AnchorTest.PlantedKey.vac_03_key
#print axioms AnchorTest.PlantedKey.vac_04_key
#print axioms AnchorTest.PlantedKey.vac_05_key
#print axioms AnchorTest.PlantedKey.vac_06_key
#print axioms AnchorTest.PlantedKey.vac_07_key
#print axioms AnchorTest.PlantedKey.vac_08_key
#print axioms AnchorTest.PlantedKey.vac_09_key
#print axioms AnchorTest.PlantedKey.vac_10_key
#print axioms AnchorTest.PlantedKey.dec_01_key
#print axioms AnchorTest.PlantedKey.dec_01_others
#print axioms AnchorTest.PlantedKey.dec_02_key
#print axioms AnchorTest.PlantedKey.dec_02_others
#print axioms AnchorTest.PlantedKey.dec_03_key
#print axioms AnchorTest.PlantedKey.dec_03_others
#print axioms AnchorTest.PlantedKey.dec_04_key
#print axioms AnchorTest.PlantedKey.dec_04_others
#print axioms AnchorTest.PlantedKey.dec_05_key
#print axioms AnchorTest.PlantedKey.dec_05_others
#print axioms AnchorTest.PlantedKey.dec_06_key
#print axioms AnchorTest.PlantedKey.dec_06_others
#print axioms AnchorTest.PlantedKey.dec_07_key
#print axioms AnchorTest.PlantedKey.dec_07_others
#print axioms AnchorTest.PlantedKey.dec_08_key
#print axioms AnchorTest.PlantedKey.dec_08_others
#print axioms AnchorTest.PlantedKey.dec_09_key
#print axioms AnchorTest.PlantedKey.dec_09_others
#print axioms AnchorTest.PlantedKey.dec_10_key
#print axioms AnchorTest.PlantedKey.dec_10_others

/-! The planted theorems themselves. -/

#print axioms AnchorTest.Planted.cert_01
#print axioms AnchorTest.Planted.cert_02
#print axioms AnchorTest.Planted.cert_03
#print axioms AnchorTest.Planted.cert_04
#print axioms AnchorTest.Planted.cert_05
#print axioms AnchorTest.Planted.cert_06
#print axioms AnchorTest.Planted.cert_07
#print axioms AnchorTest.Planted.cert_08
#print axioms AnchorTest.Planted.cert_09
#print axioms AnchorTest.Planted.cert_10
#print axioms AnchorTest.Planted.vac_01
#print axioms AnchorTest.Planted.vac_02
#print axioms AnchorTest.Planted.vac_03
#print axioms AnchorTest.Planted.vac_04
#print axioms AnchorTest.Planted.vac_05
#print axioms AnchorTest.Planted.vac_06
#print axioms AnchorTest.Planted.vac_07
#print axioms AnchorTest.Planted.vac_08
#print axioms AnchorTest.Planted.vac_09
#print axioms AnchorTest.Planted.vac_10
#print axioms AnchorTest.Planted.dec_01
#print axioms AnchorTest.Planted.dec_02
#print axioms AnchorTest.Planted.dec_03
#print axioms AnchorTest.Planted.dec_04
#print axioms AnchorTest.Planted.dec_05
#print axioms AnchorTest.Planted.dec_06
#print axioms AnchorTest.Planted.dec_07
#print axioms AnchorTest.Planted.dec_08
#print axioms AnchorTest.Planted.dec_09
#print axioms AnchorTest.Planted.dec_10
#print axioms AnchorTest.Planted.nohyp_1
#print axioms AnchorTest.Planted.nohyp_2
#print axioms AnchorTest.Planted.nohyp_3
#print axioms AnchorTest.Planted.nohyp_4
#print axioms AnchorTest.Planted.nohyp_5
#print axioms AnchorTest.Planted.depd_1
#print axioms AnchorTest.Planted.depd_2
#print axioms AnchorTest.Planted.depd_3
#print axioms AnchorTest.Planted.depd_4
#print axioms AnchorTest.Planted.depd_5
