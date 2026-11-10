module

public import AlphaCentauri.ToMathlib.NumberTheory.EisensteinInteger.Lambda
public import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Cubes of Eisenstein integers modulo `λ`

Cubes of Eisenstein integers modulo `λ`, and the normalization of a solution of `a³ + b³ = u c³`
with `λ ∣ c`.
-/

@[expose] public section

open QuadraticAlgebra OpenPredicate

namespace EisensteinInteger

variable {R : Type*} [CommRing R] {V : Type*} {a b c z : EisensteinInteger R}
  {F G : (V → R) → EisensteinInteger R}

variable [LinearOrder R]
variable [IsStrictOrderedRing R]
variable [DiscretelyOrdered R] (hL : LeastNumberPrinciple R)
include hL

lemma lambda_pow_four_dvd_cube_sub_one (h : lambda ∣ z - 1) : lambda ^ 4 ∣ z ^ 3 - 1 := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨s, hs⟩ : lambda ∣ t ^ 3 - ω ^ 2 * t - ω ^ 2 * lambda * t ^ 2 := by
    have h3 : lambda ∣ (t - 1) * t * (t + 1) := by
      rcases lambda_dvd_or hL t with h | h | h
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h _) _
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _
      · exact dvd_mul_of_dvd_right h _
    convert dvd_add h3 (dvd_mul_right lambda (-(ω + 1) * t - ω ^ 2 * t ^ 2)) using 1
    simp only [lambda]; ring
  use s
  linear_combination (z ^ 2 + z * (1 + lambda * t) + (1 + lambda * t) ^ 2) * ht
    + (lambda * t + lambda ^ 2 * t ^ 2) * three_eq (R := R) + lambda ^ 3 * hs

lemma exists_cube_mod (hz : ¬lambda ∣ z) :
    ∃ e : EisensteinInteger R, (e = 1 ∨ e = -1) ∧ lambda ^ 4 ∣ z ^ 3 - e := by
  rcases lambda_dvd_or hL z with h | h | h
  · exact absurd h hz
  · use 1
    exact ⟨Or.inl rfl, lambda_pow_four_dvd_cube_sub_one hL h⟩
  · use -1
    have := lambda_pow_four_dvd_cube_sub_one hL (z := -z) (by convert dvd_neg.2 h using 1; ring)
    exact ⟨Or.inr rfl, by convert dvd_neg.2 this using 1; ring⟩

lemma case_one (ha : ¬lambda ∣ a) (hb : ¬lambda ∣ b) (hc : ¬lambda ∣ c) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  intro h
  obtain ⟨e₁, he₁, h₁⟩ := exists_cube_mod hL ha
  obtain ⟨e₂, he₂, h₂⟩ := exists_cube_mod hL hb
  obtain ⟨e₃, he₃, h₃⟩ := exists_cube_mod hL hc
  have hd : lambda ^ 4 ∣ e₁ + e₂ - e₃ := by
    rw [show e₁ + e₂ - e₃ = (c ^ 3 - e₃) - (a ^ 3 - e₁) - (b ^ 3 - e₂) by linear_combination h]
    exact dvd_sub (dvd_sub h₃ h₁) h₂
  rcases he₁ with rfl | rfl <;> rcases he₂ with rfl | rfl <;> rcases he₃ with rfl | rfl <;>
    norm_num at hd <;>
    first
    | exact not_lambda_pow_four_dvd_one hd
    | exact not_lambda_pow_four_dvd_three hd

lemma exists_normalize {a b c u : EisensteinInteger R} (ha : ¬lambda ∣ a) (hb : ¬lambda ∣ b)
    (hc : lambda ∣ c) (h : a ^ 3 + b ^ 3 = u * c ^ 3) :
    lambda ^ 2 ∣ a + b ∨ lambda ^ 2 ∣ a + ω * b ∨ lambda ^ 2 ∣ a + ω ^ 2 * b := by
  have hp := prime_lambda hL
  have e₁ : a + ω * b = (a + b) + lambda * b := by simp only [lambda]; ring
  have e₂ : a + ω ^ 2 * b = (a + b) + lambda * ((ω + 1) * b) := by simp only [lambda]; ring
  have h1 : lambda ∣ a ^ 3 + b ^ 3 :=
    (dvd_pow_self lambda three_ne_zero).trans (h ▸ (pow_dvd_pow_of_dvd hc 3).mul_left u)
  have hab : lambda ∣ a + b := hp.dvd_of_dvd_pow (n := 3) <| by
    rw [show (a + b) ^ 3 = a ^ 3 + b ^ 3 + lambda * (lambda * -ω ^ 2 * (a * b * (a + b))) by
      linear_combination (a * b * (a + b)) * three_eq (R := R)]
    exact dvd_add h1 (dvd_mul_right _ _)
  have h4 : lambda ^ 4 ∣ a ^ 3 + b ^ 3 := by
    obtain ⟨f₁, hf₁, k₁⟩ := exists_cube_mod hL ha
    obtain ⟨f₂, hf₂, k₂⟩ := exists_cube_mod hL hb
    have hs : lambda ^ 4 ∣ a ^ 3 + b ^ 3 - (f₁ + f₂) := by
      convert dvd_add k₁ k₂ using 1
      ring
    have hs1 : lambda ∣ f₁ + f₂ := by
      convert dvd_sub h1 ((dvd_pow_self lambda four_ne_zero).trans hs) using 1
      ring
    rcases hf₁ with rfl | rfl <;> rcases hf₂ with rfl | rfl <;> norm_num at hs hs1 <;>
      first | exact absurd hs1 not_lambda_dvd_two | exact hs
  obtain ⟨q, hq⟩ := hab
  rw [sum_cubes_eq, e₁, e₂, hq, pow_succ,
    show lambda * q * (lambda * q + lambda * b) * (lambda * q + lambda * ((ω + 1) * b)) =
      lambda ^ 3 * (q * (q + b) * (q + (ω + 1) * b)) by ring,
    mul_dvd_mul_iff_left (pow_ne_zero 3 lambda_ne_zero)] at h4
  rw [e₁, e₂, hq, ← mul_add, ← mul_add, sq]
  simp only [mul_dvd_mul_iff_left (lambda_ne_zero (R := R))]
  rcases hp.dvd_or_dvd h4 with h' | h'
  · exact (hp.dvd_or_dvd h').imp_right Or.inl
  · exact .inr (.inr h')

end EisensteinInteger
