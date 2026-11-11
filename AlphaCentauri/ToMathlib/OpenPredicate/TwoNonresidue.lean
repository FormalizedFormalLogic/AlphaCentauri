module

public import AlphaCentauri.ToMathlib.OpenPredicate
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum

/-!
# Two is a quadratic nonresidue modulo $m \equiv 3, 5 \pmod 8$

In a discretely ordered ring satisfying `LeastNumberPrinciple`, the congruence
`w² ≡ 2 (mod m)` has no solution when `m` is `3` or `5` modulo `8` (`not_exists_sq_eq_two_add_mul`),
and consequently `m` divides no `x⁴ + 1` when `m` is `5` modulo `8` (`not_dvd_pow_four_add_one`).

- [Smi93, Lemma 3.5(i), Question 5.3]
-/

@[expose] public section

namespace OpenPredicate

variable {R : Type*} [CommRing R] [LinearOrder R]

private def sqrtTwoPredicate (w : Fin 5 → R) : Prop :=
  0 ≤ w 1 ∧ (w 0 = 8 * w 1 + 3 ∨ w 0 = 8 * w 1 + 5) ∧ 0 ≤ w 2 ∧ w 3 = 2 * w 2 + 1 ∧
    w 3 < w 0 ∧ w 3 * w 3 = 2 + w 4 * w 0

private lemma isOpen_sqrtTwoPredicate : IsOpen (sqrtTwoPredicate (R := R)) := by
  unfold sqrtTwoPredicate
  is_open

/-- `a` is `3` or `5` modulo `8`. -/
def IsThreeOrFiveModEight (a : R) : Prop := ∃ q, 0 ≤ q ∧ (a = 8 * q + 3 ∨ a = 8 * q + 5)

variable [IsStrictOrderedRing R]

lemma IsThreeOrFiveModEight.three_le {a : R} (h : IsThreeOrFiveModEight a) : 3 ≤ a := by
  obtain ⟨q, hq, rfl | rfl⟩ := h <;> linarith

variable [DiscretelyOrdered R]

lemma add_one_le_of_lt {x y : R} (h : x < y) : x + 1 ≤ y := by
  linarith [DiscretelyOrdered.one_le_of_pos (y - x) (sub_pos.2 h)]

lemma exists_natCast_eq (n : ℕ) {r : R} (h₀ : 0 ≤ r) (h : r < n) : ∃ i : ℕ, i < n ∧ r = i := by
  induction n generalizing r with
  | zero => simp at h; linarith
  | succ n ih =>
    rcases h₀.eq_or_lt with rfl | hpos
    · use 0
      simp
    · have := add_one_le_of_lt hpos
      obtain ⟨i, hi, e⟩ := ih (r := r - 1) (by linarith) (by push_cast at h; linarith)
      use i + 1
      and_intros
      · omega
      · push_cast
        linarith

lemma lt_of_sq_eq_two_add_mul {a w k : R} (ha : 3 ≤ a) (hw₀ : 1 ≤ w) (hwa : w < a)
    (h : w * w = 2 + k * a) : 0 ≤ k ∧ k < a := by
  have h₁ : 1 ≤ w * w := by nlinarith
  have h₂ : w * w < a * a := mul_self_lt_mul_self (by linarith) hwa
  and_intros
  · by_contra hk
    have := add_one_le_of_lt (not_le.1 hk)
    nlinarith
  · by_contra hk
    nlinarith

variable (hL : LeastNumberPrinciple R)

include hL

lemma exists_ediv_natCast (z : R) (n : ℕ) (hn : 0 < n) :
    ∃ (q : R) (i : ℕ), z = q * n + i ∧ i < n := by
  obtain ⟨q, r, h, hr₀, hr⟩ := exists_ediv hL z n (by exact_mod_cast hn)
  obtain ⟨i, hi, rfl⟩ := exists_natCast_eq n hr₀ hr
  use q, i

lemma exists_mul_add_one_eq (t : R) : ∃ s, t * (t + 1) = 2 * s := by
  obtain ⟨u, i, rfl, hi⟩ := exists_ediv_natCast hL t 2 (by norm_num)
  interval_cases i
  · use u * (2 * u + 1)
    push_cast
    ring
  · use (2 * u + 1) * (u + 1)
    push_cast
    ring

lemma isThreeOrFiveModEight_of_mul {x k s : R} (hx : IsThreeOrFiveModEight x) (hk : 0 ≤ k)
    (h : k * x = 8 * s - 1) : IsThreeOrFiveModEight k := by
  obtain ⟨q, hq, hx⟩ := hx
  obtain ⟨p, i, rfl, hi⟩ := exists_ediv_natCast hL k 8 (by norm_num)
  have hi' : (i : R) ≤ 7 := by exact_mod_cast (by omega : i ≤ 7)
  have hi₀ : (0 : R) ≤ i := Nat.cast_nonneg i
  have hp : 0 ≤ p := by
    by_contra hp
    have := add_one_le_of_lt (not_le.1 hp)
    push_cast at hk
    linarith
  have key (c : ℕ) (hc : c ≤ 5) (hxc : x = 8 * q + c) : ∃ j : ℕ, i * c + 1 = 8 * j := by
    have e : 8 * (s - (8 * p * q + p * c + i * q)) = i * c + 1 := by
      subst hxc
      push_cast at h
      linear_combination (-1) * h
    have hc' : (c : R) ≤ 5 := by exact_mod_cast hc
    have hc₀ : (0 : R) ≤ c := Nat.cast_nonneg c
    have h₁ : (0 : R) ≤ i * c := by positivity
    have h₂ : (i : R) * c ≤ 35 := by nlinarith
    obtain ⟨j, -, hj⟩ := exists_natCast_eq 5 (r := s - (8 * p * q + p * c + i * q))
      (by linarith) (by push_cast; linarith)
    use j
    have : ((i * c + 1 : ℕ) : R) = ((8 * j : ℕ) : R) := by
      push_cast
      linarith
    exact_mod_cast this
  use p
  and_intros
  · exact hp
  rcases hx with hx | hx
  · obtain ⟨j, hj⟩ := key 3 (by norm_num) (by simpa using hx)
    obtain rfl : i = 5 := by omega
    right
    push_cast
    ring
  · obtain ⟨j, hj⟩ := key 5 (by norm_num) (by simpa using hx)
    obtain rfl : i = 3 := by omega
    left
    push_cast
    ring

lemma exists_sq_eq_two_add_mul_lt {a w k : R} (ha : 0 < a) (h : w * w = 2 + k * a) :
    ∃ r k', 0 ≤ r ∧ r < a ∧ r * r = 2 + k' * a := by
  obtain ⟨u, r, rfl, hr₀, hr⟩ := exists_ediv hL w a ha
  use r, k - u * u * a - 2 * u * r
  and_intros
  · exact hr₀
  · exact hr
  · linear_combination h

lemma exists_odd_sq_eq_two_add_mul {a w k : R} (ha : IsThreeOrFiveModEight a) (hw₀ : 0 ≤ w)
    (hwa : w < a) (h : w * w = 2 + k * a) :
    ∃ t w' k', 0 ≤ t ∧ w' = 2 * t + 1 ∧ w' < a ∧ w' * w' = 2 + k' * a := by
  have ha₃ := ha.three_le
  obtain ⟨c, hc⟩ : ∃ c, a = 2 * c + 1 := by
    obtain ⟨q, -, rfl | rfl⟩ := ha
    · use 4 * q + 1
      ring
    · use 4 * q + 2
      ring
  obtain ⟨t, i, rfl, hi⟩ := exists_ediv_natCast hL w 2 (by norm_num)
  interval_cases i
  · have hw : 0 < t * 2 := by
      rcases hw₀.eq_or_lt with h₀ | h₀
      · exfalso
        rcases le_or_gt 0 k with hk | hk
        · push_cast at h h₀
          nlinarith [mul_nonneg hk (by linarith : 0 ≤ a)]
        · have := add_one_le_of_lt hk
          push_cast at h h₀
          nlinarith
      · simpa using h₀
    push_cast at h hw₀ hwa hw
    use c - t, a - t * 2, a - 2 * (t * 2) + k
    and_intros
    · by_contra ht
      have := add_one_le_of_lt (not_le.1 ht)
      linarith
    · linarith
    · linarith
    · linear_combination h
  · push_cast at h hw₀ hwa
    use t, t * 2 + 1, k
    and_intros
    · by_contra ht
      have := add_one_le_of_lt (not_le.1 ht)
      linarith
    · ring
    · exact hwa
    · exact h

lemma exists_normal_form {a w k : R} (ha : IsThreeOrFiveModEight a) (h : w * w = 2 + k * a) :
    ∃ q t w k, 0 ≤ q ∧ (a = 8 * q + 3 ∨ a = 8 * q + 5) ∧ 0 ≤ t ∧ w = 2 * t + 1 ∧ w < a ∧
      w * w = 2 + k * a ∧ |q| ≤ a ∧ |t| ≤ a ∧ |w| ≤ a ∧ |k| ≤ a := by
  have ha₃ := ha.three_le
  obtain ⟨r, k₁, hr₀, hra, hr⟩ := exists_sq_eq_two_add_mul_lt hL (by linarith) h
  obtain ⟨t, w', k₂, ht, hw, hwa, hk⟩ := exists_odd_sq_eq_two_add_mul hL ha hr₀ hra hr
  obtain ⟨hk₀, hk₁⟩ := lt_of_sq_eq_two_add_mul ha₃ (by linarith) hwa hk
  obtain ⟨q, hq, hq'⟩ := ha
  use q, t, w', k₂
  and_intros
  any_goals assumption
  · rw [abs_of_nonneg hq]
    rcases hq' with rfl | rfl <;> linarith
  · rw [abs_of_nonneg ht]
    linarith
  · rw [abs_of_nonneg (by linarith)]
    linarith
  · rw [abs_of_nonneg hk₀]
    linarith

/-- The descent step: the quotient `k` is smaller, and `2` is a square modulo `k`. -/
lemma descent {a q t w k : R} (hq : 0 ≤ q)
    (ha : a = 8 * q + 3 ∨ a = 8 * q + 5) (ht : 0 ≤ t) (hw : w = 2 * t + 1) (hwa : w < a)
    (h : w * w = 2 + k * a) :
    IsThreeOrFiveModEight k ∧ 0 ≤ k ∧ k < a ∧ ∃ w' k', w' * w' = 2 + k' * k := by
  have ha₃ : 3 ≤ a := by rcases ha with rfl | rfl <;> linarith
  obtain ⟨s, hs⟩ := exists_mul_add_one_eq hL t
  have hs₀ : 0 ≤ s := by nlinarith
  have hka : k * a = 8 * s - 1 := by
    subst hw
    linear_combination (-1) * h + 4 * hs
  obtain ⟨hk₀, hk₁⟩ := lt_of_sq_eq_two_add_mul ha₃ (by linarith) hwa h
  have hk : IsThreeOrFiveModEight k :=
    isThreeOrFiveModEight_of_mul hL ⟨q, hq, ha⟩ hk₀ hka
  and_intros
  any_goals assumption
  · obtain ⟨r, k', -, -, hr⟩ := exists_sq_eq_two_add_mul_lt hL (a := k) (w := w) (k := a)
      (by linarith [hk.three_le]) (by linarith)
    use r, k'

private lemma boundedExists_sqrtTwoPredicate {b B : R} (hb : IsThreeOrFiveModEight b)
    (h : ∃ w k, w * w = 2 + k * b) (hB : b < B) : BoundedExists B sqrtTwoPredicate b := by
  obtain ⟨w, k, h⟩ := h
  obtain ⟨q, t, w, k, hq, hbq, ht, hw, hwb, hk, hqb, htb, hwb', hkb⟩ :=
    exists_normal_form hL hb h
  use ![q, t, w, k]
  constructor
  · intro j
    fin_cases j
    · exact lt_of_le_of_lt hqb hB
    · exact lt_of_le_of_lt htb hB
    · exact lt_of_le_of_lt hwb' hB
    · exact lt_of_le_of_lt hkb hB
  · change sqrtTwoPredicate ![b, q, t, w, k]
    exact ⟨hq, hbq, ht, hw, hwb, hk⟩

/-- `2` is a quadratic nonresidue modulo every `a` that is `3` or `5` modulo `8`.
- [Smi93, Lemma 3.5(i)] -/
lemma not_exists_sq_eq_two_add_mul {a : R} (ha : IsThreeOrFiveModEight a) :
    ¬∃ w k, w * w = 2 + k * a := by
  intro h
  have ha₀ : 0 ≤ a := by linarith [ha.three_le]
  obtain ⟨x, hx₀, hx, hmin⟩ := hL 4 sqrtTwoPredicate isOpen_sqrtTwoPredicate (a + 1) a ha₀
    (boundedExists_sqrtTwoPredicate hL ha h (by linarith))
  have hxa : x ≤ a := not_lt.1 fun hlt =>
    hmin a ha₀ hlt (boundedExists_sqrtTwoPredicate hL ha h (by linarith))
  obtain ⟨ys, -, hq, hx', ht, hw, hwx, hk⟩ := hx
  obtain ⟨hkk, hk₀, hkx, w', k', hk'⟩ :=
    descent hL (a := x) (q := ys 0) (t := ys 1) (w := ys 2) (k := ys 3) hq hx' ht hw hwx hk
  exact hmin (ys 3) hk₀ hkx
    (boundedExists_sqrtTwoPredicate hL hkk ⟨w', k', hk'⟩ (by linarith))

/-- No `x ^ 4 + 1` is divisible by an `m` that is `5` modulo `8`.
- [Smi93, Question 5.3] -/
lemma not_dvd_pow_four_add_one {m x : R} (hm : ∃ q, 0 ≤ q ∧ m = 8 * q + 5) :
    ¬m ∣ x ^ 4 + 1 := by
  obtain ⟨q, hq, hm⟩ := hm
  rintro ⟨c, hc⟩
  apply not_exists_sq_eq_two_add_mul hL (a := m)
  · use q
    and_intros
    · exact hq
    · right
      exact hm
  · use (x ^ 2 + 1) * x ^ 3, c * (x ^ 6 + 2 * x ^ 4 - 2)
    linear_combination (x ^ 6 + 2 * x ^ 4 - 2) * hc

end OpenPredicate
