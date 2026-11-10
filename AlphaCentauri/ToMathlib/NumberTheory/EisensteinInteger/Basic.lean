module

public import AlphaCentauri.ToMathlib.OpenPredicate
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# Eisenstein integers over a ring

`EisensteinInteger R` is `R[ω]` with `ω² = -1 - ω`, with norm `re² - re·im + im²`. Over a
discretely ordered ring, the elements of norm `1` are the units.
-/

@[expose] public section

open QuadraticAlgebra OpenPredicate

/-- The Eisenstein integers over `R`: `R[ω]` with `ω² = -1 - ω`. -/
abbrev EisensteinInteger (R : Type*) [CommRing R] := QuadraticAlgebra R (-1) (-1)

namespace EisensteinInteger

variable {R : Type*} [CommRing R] (z w : EisensteinInteger R)

/-- The norm `re² - re·im + im²`. -/
abbrev norm : R := QuadraticAlgebra.norm z

lemma norm_eq : norm z = z.re ^ 2 - z.re * z.im + z.im ^ 2 := by
  simp only [norm, QuadraticAlgebra.norm_def]; ring

lemma norm_mul : norm (z * w) = norm z * norm w := map_mul _ _ _

lemma norm_one : norm (1 : EisensteinInteger R) = 1 := QuadraticAlgebra.norm_one

lemma norm_neg : norm (-z) = norm z := QuadraticAlgebra.norm_neg z

lemma norm_pow (n : ℕ) : norm (z ^ n) = norm z ^ n := map_pow _ _ _

lemma four_mul_norm : 4 * norm z = (2 * z.re - z.im) ^ 2 + 3 * z.im ^ 2 := by
  linear_combination 4 * norm_eq z

lemma omega_sq : (ω : EisensteinInteger R) ^ 2 = -1 - ω := by
  ext <;> simp [sq, re_omega, im_omega]

lemma omega_cube : (ω : EisensteinInteger R) ^ 3 = 1 := by
  linear_combination (ω - 1) * omega_sq (R := R)

lemma one_add_omega_add_omega_sq : (1 : EisensteinInteger R) + ω + ω ^ 2 = 0 := by
  linear_combination omega_sq (R := R)

lemma isUnit_omega : IsUnit (ω : EisensteinInteger R) := .of_pow_eq_one omega_cube (by norm_num)

lemma norm_omega : norm (ω : EisensteinInteger R) = 1 := by
  simp [norm_eq, re_omega, im_omega]

lemma sum_cubes_eq : z ^ 3 + w ^ 3 = (z + w) * (z + ω * w) * (z + ω ^ 2 * w) := by
  linear_combination (-(z ^ 2 * w + ω * z * w ^ 2 + (ω - 1) * w ^ 3)) * omega_sq (R := R)

variable [LinearOrder R] [IsStrictOrderedRing R]

lemma norm_nonneg : 0 ≤ norm z := by
  nlinarith [four_mul_norm z, sq_nonneg (2 * z.re - z.im), sq_nonneg z.im]

variable {z} in
lemma norm_eq_zero_iff : norm z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have h4 := four_mul_norm z
    have him : z.im = 0 := by nlinarith [sq_nonneg (2 * z.re - z.im), sq_nonneg z.im]
    have hre : z.re = 0 := by nlinarith [sq_nonneg z.re]
    ext <;> simp [hre, him]
  · rintro rfl
    simp [norm]

variable {z} in
lemma norm_pos (hz : z ≠ 0) : 0 < norm z :=
  (norm_nonneg z).lt_of_ne (Ne.symm (mt norm_eq_zero_iff.mp hz))

instance : NoZeroDivisors (EisensteinInteger R) where
  eq_zero_or_eq_zero_of_mul_eq_zero {z w} h := by
    simpa [← norm_eq_zero_iff (z := z), ← norm_eq_zero_iff (z := w), norm_mul] using
      congrArg norm h

instance : IsDomain (EisensteinInteger R) := NoZeroDivisors.to_isDomain _

lemma norm_add_le : norm (z + w) ≤ 2 * norm z + 2 * norm w := by
  have : norm (z + w) + norm (z - w) = 2 * norm z + 2 * norm w := by
    simp only [norm_eq, re_add, im_add, re_sub, im_sub]; ring
  linarith [norm_nonneg (z - w)]

lemma abs_re_le : |z.re| ≤ 2 * norm z + 1 := by
  nlinarith [norm_eq z, sq_abs z.re, sq_nonneg (2 * |z.re| - 1), sq_nonneg (2 * z.im - z.re),
    norm_nonneg z]

lemma abs_im_le : |z.im| ≤ 2 * norm z + 1 := by
  nlinarith [four_mul_norm z, sq_abs z.im, sq_nonneg (2 * |z.im| - 1), sq_nonneg (2 * z.re - z.im),
    norm_nonneg z]

variable [DiscretelyOrdered R] {z}

lemma one_le_norm (hz : z ≠ 0) : 1 ≤ norm z := DiscretelyOrdered.one_le_of_pos _ (norm_pos hz)

lemma isUnit_iff_norm_eq_one : IsUnit z ↔ norm z = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have := congrArg norm u.mul_inv
    rw [norm_mul, norm_one] at this
    nlinarith [one_le_norm u.ne_zero, one_le_norm u⁻¹.ne_zero]
  · intro h
    apply isUnit_iff_exists_inv.mpr
    use star z
    rw [← algebraMap_norm_eq_mul_star, show QuadraticAlgebra.norm z = 1 from h, map_one]

end EisensteinInteger
