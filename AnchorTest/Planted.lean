import Mathlib

/-!
# Planted statements

Forty proved theorems for testing Anchor. Each was labelled before any tool ran on it. The
labels are in `planted_labels.json`, and `PlantedKey.lean` proves every label that concerns
hypotheses.

The statements are the kind found in a library or a textbook. A hypothesis is a leading binder
of a theorem's type whose type is a proposition; variables, types and instances belong to the
model. Everything after the leading binders is the conclusion.
-/

set_option linter.unusedVariables false

namespace AnchorTest.Planted

/-! ## cert -/

/-- A natural number divisible by 2 and by 3 is divisible by 6. -/
theorem cert_01 (n : ℕ) (h2 : 2 ∣ n) (h3 : 3 ∣ n) : 6 ∣ n := by
  omega

/-- A common divisor of two integers divides their sum. -/
theorem cert_02 (a b c : ℤ) (hb : a ∣ b) (hc : a ∣ c) : a ∣ b + c :=
  dvd_add hb hc

/-- A rational strictly between 1 and 2 has its square strictly between 1 and 4. -/
theorem cert_03 (x : ℚ) (h1 : 1 < x) (h2 : x < 2) : 1 < x ^ 2 ∧ x ^ 2 < 4 :=
  ⟨by nlinarith, by nlinarith⟩

/-- Nonnegative reals with equal squares are equal. -/
theorem cert_04 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x ^ 2 = y ^ 2) : x = y :=
  (pow_left_inj₀ hx hy two_ne_zero).1 h

/-- A subset at least as large as its superset is the whole superset. -/
theorem cert_05 (s t : Finset ℕ) (h : s ⊆ t) (hcard : t.card ≤ s.card) : s = t :=
  Finset.eq_of_subset_of_card_le h hcard

/-- A nonempty list of positive natural numbers has positive sum. -/
theorem cert_06 (l : List ℕ) (hpos : ∀ x ∈ l, 0 < x) (hne : l ≠ []) : 0 < l.sum := by
  cases l with
  | nil => exact absurd rfl hne
  | cons a t =>
    have ha : 0 < a := hpos a (by simp)
    simp only [List.sum_cons]
    omega

/-- A strictly increasing function on the reals reflects strict order. -/
theorem cert_07 (f : ℝ → ℝ) (hf : StrictMono f) (a b : ℝ) (h : f a < f b) : a < b :=
  hf.lt_iff_lt.1 h

/-- In a group, if two commuting elements each square to the identity, so does their
product. -/
theorem cert_08 {G : Type} [Group G] (a b : G) (hab : a * b = b * a) (ha : a ^ 2 = 1)
    (hb : b ^ 2 = 1) : (a * b) ^ 2 = 1 := by
  rw [(show Commute a b from hab).mul_pow, ha, hb, one_mul]

/-- In a monoid, a right inverse and a left inverse of the same element agree. -/
theorem cert_09 {M : Type} [Monoid M] (a b c : M) (hab : a * b = 1) (hca : c * a = 1) :
    b = c :=
  (left_inv_eq_right_inv hca hab).symm

/-- A real function that is both monotone and antitone takes the same value at 0 and 1. -/
theorem cert_10 (f : ℝ → ℝ) (hf : Monotone f) (hg : Antitone f) : f 0 = f 1 :=
  le_antisymm (hf zero_le_one) (hg zero_le_one)

/-! ## vac -/

/-- In a preorder, `a < b` together with `b ≤ a` gives `a = b`. -/
theorem vac_01 {α : Type} [Preorder α] (a b : α) (hab : a < b) (hba : b ≤ a) : a = b :=
  absurd (lt_of_lt_of_le hab hba) (lt_irrefl a)

/-- If `n` and `n + 1` are both even, then `n ^ 2 = n`. -/
theorem vac_02 (n : ℕ) (h1 : Even n) (h2 : Even (n + 1)) : n ^ 2 = n :=
  absurd h1 (Nat.even_add_one.1 h2)

/-- Reals with `x ^ 2 + y ^ 2 < 2 * x * y` are equal. -/
theorem vac_03 (x y : ℝ) (h : x ^ 2 + y ^ 2 < 2 * x * y) : x = y := by
  exfalso
  nlinarith [sq_nonneg (x - y)]

/-- An integer divisible by 6 whose successor is divisible by 4 equals 3. -/
theorem vac_04 (a : ℤ) (h6 : 6 ∣ a) (h4 : 4 ∣ a + 1) : a = 3 := by
  omega

/-- A subset of `range 3` with at least four elements has sum zero. -/
theorem vac_05 (s : Finset ℕ) (hs : s ⊆ Finset.range 3) (hcard : 4 ≤ s.card) :
    s.sum id = 0 := by
  have h := Finset.card_le_card hs
  rw [Finset.card_range] at h
  omega

/-- An angle with `sin θ ^ 2 + cos θ ^ 2 = 2` is zero. -/
theorem vac_06 (θ : ℝ) (h : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 2) : θ = 0 := by
  rw [Real.sin_sq_add_cos_sq] at h
  norm_num at h

/-- A prime dividing 1 equals 2. -/
theorem vac_07 (p : ℕ) (hp : p.Prime) (h : p ∣ 1) : p = 2 :=
  absurd h hp.not_dvd_one

/-- Rationals with `a < b`, `b < c` and `c < a` satisfy `a = b`. -/
theorem vac_08 (a b c : ℚ) (hab : a < b) (hbc : b < c) (hca : c < a) : a = b := by
  exfalso
  linarith

/-- A sequence of naturals that increases at every step and has `f 5 < f 2` starts at 0. -/
theorem vac_09 (f : ℕ → ℕ) (hf : ∀ n, f n < f (n + 1)) (h : f 5 < f 2) : f 0 = 0 := by
  have h25 : f 2 < f 5 := strictMono_nat_of_lt_succ hf (by norm_num)
  omega

/-- A list of two naturals, each at most 2, with sum 5 is `[2, 3]`. -/
theorem vac_10 (l : List ℕ) (hlen : l.length = 2) (hsum : l.sum = 5)
    (hle : ∀ x ∈ l, x ≤ 2) : l = [2, 3] := by
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.1 hlen
  have ha := hle a (by simp)
  have hb := hle b (by simp)
  simp only [List.sum_cons, List.sum_nil] at hsum
  exfalso
  omega

/-! ## dec -/

/-- In a field, `a / b = 1` with `b ≠ 0` gives `a = b`. -/
theorem dec_01 {K : Type} [Field K] (a b : K) (h : a / b = 1) (hb : b ≠ 0) : a = b :=
  (div_eq_one_iff_eq hb).1 h

/-- For a positive natural number at least 2, `n + 1 < n ^ 2`. -/
theorem dec_02 (n : ℕ) (hpos : 0 < n) (h2 : 2 ≤ n) : n + 1 < n ^ 2 := by
  nlinarith

/-- A positive real whose cube is 8 equals 2. -/
theorem dec_03 (x : ℝ) (h : x ^ 3 = 8) (hx : 0 < x) : x = 2 := by
  have h8 : (2 : ℝ) ^ 3 = 8 := by norm_num
  exact (pow_left_inj₀ hx.le (by norm_num) (by norm_num : (3 : ℕ) ≠ 0)).1 (h.trans h8.symm)

/-- A nonempty subset has cardinality at most that of its superset. -/
theorem dec_04 (s t : Finset ℕ) (hst : s ⊆ t) (hs : s.Nonempty) : s.card ≤ t.card :=
  Finset.card_le_card hst

/-- A member of a nonempty list is a member of its reverse. -/
theorem dec_05 (l : List ℕ) (a : ℕ) (hne : l ≠ []) (ha : a ∈ l) : a ∈ l.reverse :=
  List.mem_reverse.2 ha

/-- A nonzero divisor of a positive integer is at most it in absolute value. -/
theorem dec_06 (a b : ℤ) (h : a ∣ b) (hb : 0 < b) (ha : a ≠ 0) : a.natAbs ≤ b.natAbs :=
  Int.natAbs_le_of_dvd_ne_zero h hb.ne'

/-- A continuous strictly increasing real function is injective. -/
theorem dec_07 (f : ℝ → ℝ) (hmono : StrictMono f) (hf : Continuous f) (a b : ℝ)
    (h : f a = f b) : a = b :=
  hmono.injective h

/-- In a group, if `a` and `b` commute and `a * b = 1`, then `b * a = 1`. -/
theorem dec_08 {G : Type} [Group G] (a b : G) (hab : a * b = b * a) (h : a * b = 1) :
    b * a = 1 := by
  rw [← hab]
  exact h

/-- In a linear order, `a < b ≤ c` with `a ≠ c` gives `a < c`. -/
theorem dec_09 {α : Type} [LinearOrder α] (a b c : α) (hab : a < b) (hbc : b ≤ c)
    (hne : a ≠ c) : a < c :=
  lt_of_lt_of_le hab hbc

/-- For rationals with `0 < y`, `x ≠ y` and `x < y`, the quotient `x / y` is below 1. -/
theorem dec_10 (x y : ℚ) (hy : 0 < y) (hxy : x ≠ y) (h : x < y) : x / y < 1 :=
  (div_lt_one hy).2 h

/-! ## nohyp -/

/-- Addition of natural numbers is commutative. -/
theorem nohyp_1 (a b : ℕ) : a + b = b + a :=
  Nat.add_comm a b

/-- The inverse of a product in a group is the product of inverses in reverse order. -/
theorem nohyp_2 {G : Type} [Group G] (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
  mul_inv_rev a b

/-- No real square is negative. -/
theorem nohyp_3 (x : ℝ) : ¬ x ^ 2 < 0 :=
  not_lt.2 (sq_nonneg x)

/-- Reversing a list twice gives the list back. -/
theorem nohyp_4 (l : List ℕ) : l.reverse.reverse = l :=
  List.reverse_reverse l

/-- No natural number equals its successor. -/
theorem nohyp_5 (n : ℕ) : n ≠ n + 1 :=
  Nat.ne_of_lt (Nat.lt_succ_self n)

/-! ## depd -/

/-- The last element of `Fin n`, built from `0 < n`, has value `n - 1`. -/
theorem depd_1 (n : ℕ) (h : 0 < n) :
    (⟨n - 1, Nat.sub_lt h Nat.one_pos⟩ : Fin n).val + 1 = n := by
  show n - 1 + 1 = n
  omega

/-- The head of a nonempty list is a member of it. -/
theorem depd_2 (l : List ℕ) (h : l ≠ []) : l.head h ∈ l :=
  List.head_mem h

/-- If the head of a nonempty list is 0, then 0 is a member. -/
theorem depd_3 (l : List ℕ) (h : l ≠ []) (hhead : l.head h = 0) : 0 ∈ l := by
  rw [← hhead]
  exact List.head_mem h

/-- The minimum of a nonempty finite set is at most its maximum. -/
theorem depd_4 (s : Finset ℕ) (h : s.Nonempty) : s.min' h ≤ s.max' h :=
  Finset.min'_le s _ (Finset.max'_mem s h)

/-- If the first entry of a vector bounds every entry, the sum is at most `n` times it. -/
theorem depd_5 (n : ℕ) (hn : 0 < n) (v : Fin n → ℝ) (hv : ∀ i, v i ≤ v ⟨0, hn⟩) :
    ∑ i, v i ≤ n * v ⟨0, hn⟩ := by
  calc ∑ i, v i ≤ ∑ _i : Fin n, v ⟨0, hn⟩ := Finset.sum_le_sum fun i _ => hv i
    _ = n * v ⟨0, hn⟩ := by simp

end AnchorTest.Planted
