module

public import AlphaCentauri.ToMathlib.NumberTheory.EisensteinInteger.Basic
public import Mathlib.RingTheory.Bezout
public import Mathlib.Tactic.LinearCombination

/-!
# The prime `λ = ω - 1` of Eisenstein integers

`λ = ω - 1` has norm `3`, and over a discretely ordered ring with the least number principle,
`EisensteinInteger R` has a Euclidean division with respect to the norm, is a Bézout domain, and
`λ` is a prime element with residue classes `0` and `±1`.
-/

@[expose] public section

open QuadraticAlgebra OpenPredicate

namespace EisensteinInteger

variable {R : Type*} [CommRing R] {V : Type*} {a b c z : EisensteinInteger R}
  {F G : (V → R) → EisensteinInteger R}

/-- `λ = ω - 1`, the prime above `3`. -/
abbrev lambda : EisensteinInteger R := ω - 1

lemma norm_lambda : norm (lambda : EisensteinInteger R) = 3 := by
  rw [norm_eq]; simp [re_omega, im_omega]; norm_num

lemma three_eq : (3 : EisensteinInteger R) = lambda ^ 2 * -ω ^ 2 := by
  simp only [lambda]
  linear_combination omega_sq (R := R) + (ω - 2) * omega_cube (R := R)

lemma lambda_dvd_of_re_add_im {k : R} (h : z.re + z.im = 3 * k) : lambda ∣ z := by
  use ⟨k - z.re, -k⟩
  ext <;> simp [lambda, re_omega, im_omega]
  linear_combination h

lemma exists_of_lambda_dvd (h : lambda ∣ z) : ∃ k : R, z.re + z.im = 3 * k := by
  obtain ⟨s, rfl⟩ := h
  use -s.im
  simp [lambda, re_omega, im_omega]
  ring


variable [LinearOrder R]

variable [IsStrictOrderedRing R]

lemma lambda_ne_zero : (lambda : EisensteinInteger R) ≠ 0 := fun h => by
  simpa [lambda, im_omega] using congrArg QuadraticAlgebra.im h

variable [DiscretelyOrdered R] (hL : LeastNumberPrinciple R)

lemma not_lambda_dvd_one : ¬lambda ∣ (1 : EisensteinInteger R) := by
  intro h
  obtain ⟨k, hk⟩ := exists_of_lambda_dvd h
  simp at hk
  rcases le_or_gt k 0 with hk0 | hk0
  · linarith
  · linarith [DiscretelyOrdered.one_le_of_pos k hk0]

lemma not_lambda_dvd_two : ¬lambda ∣ (2 : EisensteinInteger R) := fun h => not_lambda_dvd_one <| by
  convert ((dvd_pow_self lambda two_ne_zero).trans (Dvd.intro _ three_eq.symm)).sub h using 1
  norm_num

lemma not_lambda_pow_four_dvd_one : ¬lambda ^ 4 ∣ (1 : EisensteinInteger R) :=
  fun h => not_lambda_dvd_one ((dvd_pow_self lambda (by norm_num)).trans h)

lemma not_lambda_pow_four_dvd_three : ¬lambda ^ 4 ∣ (3 : EisensteinInteger R) := by
  intro h
  rw [three_eq, show (lambda : EisensteinInteger R) ^ 4 = lambda ^ 2 * lambda ^ 2 by ring,
    mul_dvd_mul_iff_left (pow_ne_zero 2 lambda_ne_zero)] at h
  have h1 := (dvd_pow_self lambda (by norm_num : (2 : ℕ) ≠ 0)).trans (dvd_mul_of_dvd_left h (-ω))
  rw [show -(ω : EisensteinInteger R) ^ 2 * -ω = 1 by linear_combination omega_cube (R := R)] at h1
  exact not_lambda_dvd_one h1

include hL

lemma exists_mod (a b : EisensteinInteger R) (hb : b ≠ 0) :
    ∃ q r, a = q * b + r ∧ norm r < norm b := by
  have hn := norm_pos hb
  obtain ⟨q₁, r₁, h₁, hr₁⟩ := exists_round hL (a * star b).re (norm b) hn
  obtain ⟨q₂, r₂, h₂, hr₂⟩ := exists_round hL (a * star b).im (norm b) hn
  use ⟨q₁, q₂⟩, a - ⟨q₁, q₂⟩ * b
  refine ⟨by ring, ?_⟩
  have key : (a - ⟨q₁, q₂⟩ * b) * star b = ⟨r₁, r₂⟩ := by
    rw [sub_mul, mul_assoc, ← algebraMap_norm_eq_mul_star]
    ext <;> simp at h₁ h₂ ⊢ <;> linarith
  have hN := congrArg norm key
  rw [norm_mul, show norm (star b) = norm b from QuadraticAlgebra.norm_star b,
    (norm_eq _ : norm ⟨r₁, r₂⟩ = r₁ ^ 2 - r₁ * r₂ + r₂ ^ 2)] at hN
  have e₁ := mul_le_mul hr₁ hr₁ (by positivity) hn.le
  have e₂ := mul_le_mul hr₂ hr₂ (by positivity) hn.le
  have e₃ := mul_le_mul hr₁ hr₂ (by positivity) hn.le
  nlinarith [sq_abs r₁, sq_abs r₂, abs_mul r₁ r₂, neg_abs_le (r₁ * r₂)]

lemma exists_gcd (α β : EisensteinInteger R) (hβ : β ≠ 0) :
    ∃ δ, δ ∣ α ∧ δ ∣ β ∧ ∃ x y, δ = x * α + y * β := by
  let Φ : (Fin 5 → R) → Prop := fun w => 0 < w 0 ∧
    norm (⟨w 1, w 2⟩ : EisensteinInteger R) ≤ norm β ∧
    norm (⟨w 3, w 4⟩ : EisensteinInteger R) ≤ 2 * norm α + 1 ∧
    w 0 = norm ((⟨w 1, w 2⟩ : EisensteinInteger R) * α + ⟨w 3, w 4⟩ * β)
  have hΦ (m : R) : BoundedExists (4 * (norm α + norm β) + 4) Φ m ↔ ∃ x y : EisensteinInteger R,
      0 < m ∧ norm x ≤ norm β ∧ norm y ≤ 2 * norm α + 1 ∧ m = norm (x * α + y * β) := by
    constructor
    · rintro ⟨ys, -, h⟩
      use ⟨ys 0, ys 1⟩, ⟨ys 2, ys 3⟩
      exact h
    · rintro ⟨x, y, h⟩
      use ![x.re, x.im, y.re, y.im]
      constructor
      · have := abs_re_le x; have := abs_im_le x; have := abs_re_le y; have := abs_im_le y
        have := norm_nonneg α; have := norm_nonneg β
        intro j; fin_cases j <;> simp <;> linarith
      · simpa [Φ] using h
  have hβ' : BoundedExists (4 * (norm α + norm β) + 4) Φ (norm β) := by
    apply (hΦ _).2
    use 0, 1
    exact ⟨norm_pos hβ, by simp [norm_nonneg], by simp [norm_nonneg], by simp⟩
  obtain ⟨m, -, hm, hmin⟩ := hL 4 Φ (by is_open) _ _ (norm_nonneg β) hβ'
  obtain ⟨x, y, hpos, -, -, rfl⟩ := (hΦ _).1 hm
  have hle : norm (x * α + y * β) ≤ norm β := not_lt.1 fun h => hmin _ (norm_nonneg β) h hβ'
  have hdvd (c d : EisensteinInteger R) : x * α + y * β ∣ c * α + d * β := by
    obtain ⟨q, r, hq, hr⟩ := exists_mod hL (c * α + d * β) (x * α + y * β) (by
      rintro h
      simp [h] at hpos)
    obtain ⟨s, t, hs, ht⟩ := exists_mod hL (c - q * x) β hβ
    have e : r = t * α + (s * α + d - q * y) * β := by linear_combination -hq + α * hs
    suffices r = 0 by
      use q
      rw [hq, this, add_zero, mul_comm]
    by_contra hr0
    have h₁ := norm_add_le r (-(t * α))
    rw [norm_neg, show r + -(t * α) = (s * α + d - q * y) * β by rw [e]; ring, norm_mul,
      norm_mul] at h₁
    have h₂ : norm (s * α + d - q * y) < 2 * norm α + 2 := by
      refine lt_of_mul_lt_mul_right ?_ (norm_nonneg β)
      nlinarith [norm_nonneg α, mul_le_mul_of_nonneg_right ht.le (norm_nonneg α)]
    apply hmin _ (norm_nonneg r) hr
    apply (hΦ _).2
    use t, s * α + d - q * y
    have := DiscretelyOrdered.one_le_of_pos _ (sub_pos.2 h₂)
    exact ⟨norm_pos hr0, ht.le, by linarith, e ▸ rfl⟩
  use x * α + y * β
  exact ⟨by simpa using hdvd 1 0, by simpa using hdvd 0 1, by use x, y⟩

lemma isBezout : IsBezout (EisensteinInteger R) := by
  apply IsBezout.iff_span_pair_isPrincipal.mpr
  intro α β
  by_cases hβ : β = 0
  · subst hβ
    use α
    simp [Set.pair_comm]
  obtain ⟨δ, hα, hβ, x, y, rfl⟩ := exists_gcd hL α β hβ
  use x * α + y * β
  apply le_antisymm
  · rw [Ideal.span_le, Set.pair_subset_iff]
    exact ⟨Ideal.mem_span_singleton.2 hα, Ideal.mem_span_singleton.2 hβ⟩
  · rw [Ideal.submodule_span_eq, Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_span_pair.2 ⟨x, y, rfl⟩

lemma lambda_dvd_or (z : EisensteinInteger R) : lambda ∣ z ∨ lambda ∣ z - 1 ∨ lambda ∣ z + 1 := by
  obtain ⟨q, r, hqr, hr0, hr3⟩ := exists_ediv hL (z.re + z.im) 3 (by norm_num)
  have hr : r = 0 ∨ r = 1 ∨ r = 2 := by
    by_contra! hne
    have h₁ := DiscretelyOrdered.one_le_of_pos r (hr0.lt_of_ne hne.1.symm)
    have h₂ := DiscretelyOrdered.one_le_of_pos (r - 1) (sub_pos.2 (h₁.lt_of_ne hne.2.1.symm))
    have h₃ : 2 < r := (show (2 : R) ≤ r by linarith).lt_of_ne hne.2.2.symm
    linarith [DiscretelyOrdered.one_le_of_pos (r - 2) (sub_pos.2 h₃)]
  rcases hr with rfl | rfl | rfl
  · exact Or.inl (lambda_dvd_of_re_add_im (k := q) (by linear_combination hqr))
  · exact Or.inr (Or.inl (lambda_dvd_of_re_add_im (k := q) (by simp; linear_combination hqr)))
  · exact Or.inr (Or.inr (lambda_dvd_of_re_add_im (k := q + 1) (by simp; linear_combination hqr)))

lemma exists_unit_mod (hz : ¬lambda ∣ z) :
    ∃ e : EisensteinInteger R, (e = 1 ∨ e = -1) ∧ lambda ∣ z - e := by
  rcases lambda_dvd_or hL z with h | h | h
  · exact absurd h hz
  · use 1
    exact ⟨Or.inl rfl, h⟩
  · use -1
    exact ⟨Or.inr rfl, by rwa [sub_neg_eq_add]⟩

lemma prime_lambda : Prime (lambda : EisensteinInteger R) := by
  refine ⟨lambda_ne_zero, fun hu => not_lambda_dvd_one hu.dvd, ?_⟩
  intro p q hpq
  by_contra hcon
  push Not at hcon
  obtain ⟨e, he, hpe⟩ := exists_unit_mod hL hcon.1
  obtain ⟨f, hf, hqf⟩ := exists_unit_mod hL hcon.2
  have hef : lambda ∣ e * f := by
    convert dvd_sub hpq ((hpe.mul_right q).add (hqf.mul_left e)) using 1
    ring
  apply absurd hef
  rcases he with rfl | rfl <;> rcases hf with rfl | rfl <;> simp [dvd_neg, not_lambda_dvd_one]

end EisensteinInteger
