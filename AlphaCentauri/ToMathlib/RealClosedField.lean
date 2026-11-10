module

public import AlphaCentauri.ToMathlib.FieldExtension
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.FieldTheory.IsRealClosed.Basic
public import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.GroupTheory.Sylow

/-!
# The intermediate value property of real closed fields
-/

@[expose] public section

open Polynomial Module

namespace IsRealClosed

variable {R : Type*} [Field R] [IsRealClosed R]

lemma finrank_eq_one_of_odd {F : Type*} [Field F] [Algebra R F] [FiniteDimensional R F]
    (h : Odd (finrank R F)) : finrank R F = 1 := by
  rw [← IntermediateField.bot_eq_top_iff_finrank_eq_one]
  apply IntermediateField.bot_eq_top_of_finrank_adjoin_eq_one
  intro x
  have hx := IsIntegral.of_finite R x
  rw [IntermediateField.adjoin.finrank hx]
  obtain ⟨r, hr⟩ := exists_isRoot_of_odd_natDegree (h.of_dvd_nat (minpoly.degree_dvd hx))
  exact natDegree_eq_of_degree_eq_some <| degree_eq_one_of_irreducible_of_root
    (minpoly.irreducible hx) hr

lemma exists_finrank_eq_two_pow {L : Type*} [Field L] [Algebra R L] [FiniteDimensional R L]
    [IsGalois R L] : ∃ k, finrank R L = 2 ^ k := by
  obtain ⟨P⟩ : Nonempty (Sylow 2 Gal(L/R)) := inferInstance
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
  use k
  have h₁ := Module.finrank_mul_finrank R (IntermediateField.fixedField P.toSubgroup) L
  rw [IntermediateField.finrank_fixedField_eq_card, hk] at h₁
  have h₂ := P.index_mul_card
  rw [hk, IsGalois.card_aut_eq_finrank, ← h₁] at h₂
  have h₃ := Nat.eq_of_mul_eq_mul_right (pow_pos two_pos k) h₂
  have h₄ : Odd (finrank R (IntermediateField.fixedField P.toSubgroup)) := by
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero, ← h₃]
    exact P.not_dvd_index
  rw [← h₁, finrank_eq_one_of_odd h₄, one_mul]

variable [LinearOrder R] [IsStrictOrderedRing R]

lemma isSquare_of_finrank_eq_two {E : Type*} [Field E] [Algebra R E] (h : finrank R E = 2)
    (z : E) : IsSquare z := by
  have : Algebra.IsQuadraticExtension R E := ⟨h⟩
  have key (y : E) (hy : y ∉ Set.range (algebraMap R E)) :
      Algebra.trace R E y ^ 2 - 4 * Algebra.norm R y < 0 := by
    by_contra! hD
    have : Invertible (2 : R) := invertibleOfNonzero two_ne_zero
    obtain ⟨r, hr⟩ := QuadraticAlgebra.exists_sq_eq_iff_isSquare_discr.mpr
      (show IsSquare (QuadraticAlgebra.discr (-Algebra.norm R y) (Algebra.trace R E y)) by
        rw [QuadraticAlgebra.discr_def]
        convert IsSquare.of_nonneg hD using 1
        ring)
    exact hy <| Algebra.IsQuadraticExtension.mem_range_of_sq_eq hr
  by_cases hz : z ∈ Set.range (algebraMap R E)
  · obtain ⟨x, rfl⟩ := hz
    rcases le_or_gt 0 x with hx | hx
    · obtain ⟨s, rfl⟩ := IsSquare.of_nonneg hx
      exact ⟨algebraMap R E s, map_mul _ _ _⟩
    · obtain ⟨θ, hθ⟩ := exists_notMem_range_of_finrank_ne_one (K := R) (M := E) <| by omega
      have hD := key θ hθ
      obtain ⟨s, hs⟩ := IsSquare.of_nonneg <| div_nonneg_of_nonpos hx.le hD.le
      have h₁ := Algebra.IsQuadraticExtension.sq_eq_trace_smul_sub_norm R θ
      rw [Algebra.smul_def] at h₁
      have h₂ : x = (Algebra.trace R E θ ^ 2 - 4 * Algebra.norm R θ) * (s * s) := by
        rw [← hs]
        field_simp [hD.ne]
      use (2 * θ - algebraMap R E (Algebra.trace R E θ)) * algebraMap R E s
      rw [h₂]
      simp only [map_mul, map_sub, map_pow, map_ofNat]
      linear_combination (-4 * algebraMap R E s * algebraMap R E s) * h₁
  · have hD := key z hz
    set t := Algebra.trace R E z
    set n := Algebra.norm R z
    obtain ⟨q, hq⟩ := IsSquare.of_nonneg (show 0 ≤ n by nlinarith [sq_nonneg t])
    have hq' : n = |q| * |q| := by rw [abs_mul_abs_self, hq]
    have hm : 0 < 2 * |q| + t := by nlinarith [abs_nonneg q]
    obtain ⟨β, hβ⟩ := IsSquare.of_nonneg (inv_pos.mpr hm).le
    have h₁ := Algebra.IsQuadraticExtension.sq_eq_trace_smul_sub_norm R z
    rw [Algebra.smul_def] at h₁
    have h₂ := congrArg (algebraMap R E) hq'
    have h₃ := congrArg (algebraMap R E) (show β * β * (2 * |q| + t) = 1 by
      rw [← hβ, inv_mul_cancel₀ hm.ne'])
    simp only [map_mul, map_add, map_ofNat, map_one] at h₂ h₃
    use algebraMap R E (β * |q|) + algebraMap R E β * z
    rw [map_mul]
    linear_combination (-(algebraMap R E β) ^ 2) * h₁ + (algebraMap R E β) ^ 2 * h₂ - z * h₃

lemma finrank_le_two_of_isGalois {L : Type*} [Field L] [Algebra R L] [FiniteDimensional R L]
    [IsGalois R L] : finrank R L ≤ 2 := by
  obtain ⟨k, hk⟩ := exists_finrank_eq_two_pow (R := R) (L := L)
  match k, hk with
  | 0, hk => simp [hk]
  | 1, hk => simp [hk]
  | k + 2, hk =>
    obtain ⟨E, hE, hEL⟩ := IsGalois.exists_intermediateField_finrank_eq_prime (p := 2) hk
    obtain ⟨M, hM, -⟩ := IsGalois.exists_intermediateField_finrank_eq_prime (K := E) (p := 2) hEL
    exact absurd hM <| finrank_ne_two_of_forall_isSquare <| isSquare_of_finrank_eq_two hE

/-- An irreducible polynomial over a real closed field has degree at most two. -/
theorem natDegree_le_two_of_irreducible {f : R[X]} (hf : Irreducible f) : f.natDegree ≤ 2 := by
  have : IsGalois R f.SplittingField := {}
  exact (Nat.le_of_dvd finrank_pos (hf.natDegree_dvd_finrank (SplittingField.splits f))).trans
    finrank_le_two_of_isGalois

lemma eval_mul_eval_pos_of_irreducible {f : R[X]} (hf : Irreducible f) {a b : R} (hab : a ≤ b)
    (hroot : ∀ x ∈ Set.Icc a b, ¬ f.IsRoot x) : 0 < f.eval a * f.eval b := by
  have heval (x : R) : f.eval x = f.coeff 2 * (x * x) + f.coeff 1 * x + f.coeff 0 := by
    rw [eval_eq_sum_range' (n := 3) (by have := natDegree_le_two_of_irreducible hf; omega)]
    simp [Finset.sum_range_succ]
    ring
  simp only [IsRoot.def, heval] at hroot ⊢
  have hdeg := natDegree_le_two_of_irreducible hf
  rcases (show f.natDegree = 1 ∨ f.natDegree = 2 by have := hf.natDegree_pos; omega) with h | h
  · have h₂ : f.coeff 2 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    have h₁ : f.coeff 1 ≠ 0 := by rw [← h]; exact leadingCoeff_ne_zero.mpr hf.ne_zero
    set r := -f.coeff 0 / f.coeff 1
    have hr : f.coeff 1 * r + f.coeff 0 = 0 := by simp only [r]; field_simp; ring
    have hr' : r < a ∨ b < r := by
      by_contra! hc
      exact hroot r hc (by rw [h₂]; linear_combination hr)
    have e : (f.coeff 1 * a + f.coeff 0) * (f.coeff 1 * b + f.coeff 0) =
        f.coeff 1 ^ 2 * ((a - r) * (b - r)) := by
      linear_combination (f.coeff 1 * a + f.coeff 1 * b - f.coeff 1 * r + f.coeff 0) * hr
    simp only [h₂, zero_mul, zero_add, e]
    exact mul_pos (by positivity) (by rcases hr' with hr' | hr' <;> nlinarith)
  · have hw : f.coeff 2 ≠ 0 := by rw [← h]; exact leadingCoeff_ne_zero.mpr hf.ne_zero
    have hne (x : R) : f.coeff 2 * (x * x) + f.coeff 1 * x + f.coeff 0 ≠ 0 := by
      intro hx
      have := degree_eq_one_of_irreducible_of_root hf (x := x) (by rw [IsRoot.def, heval]; exact hx)
      rw [degree_eq_natDegree hf.ne_zero, h] at this
      exact absurd this (by decide)
    have hD : discrim (f.coeff 2) (f.coeff 1) (f.coeff 0) < 0 := by
      by_contra! hD
      obtain ⟨s, hs⟩ := IsSquare.of_nonneg hD
      obtain ⟨x, hx⟩ := exists_quadratic_eq_zero hw ⟨s, hs⟩
      exact hne x hx
    have hpos (x : R) : 0 < f.coeff 2 * (f.coeff 2 * (x * x) + f.coeff 1 * x + f.coeff 0) := by
      rw [discrim] at hD
      nlinarith [sq_nonneg (2 * f.coeff 2 * x + f.coeff 1)]
    have := mul_pos (hpos a) (hpos b)
    nlinarith [sq_nonneg (f.coeff 2)]

lemma eval_mul_eval_pos {f : R[X]} {a b : R} (hab : a ≤ b)
    (hroot : ∀ x ∈ Set.Icc a b, ¬ f.IsRoot x) : 0 < f.eval a * f.eval b := by
  induction f using WfDvdMonoid.induction_on_irreducible with
  | zero => exact absurd eval_zero (hroot a ⟨le_rfl, hab⟩)
  | unit u hu =>
    obtain ⟨c, hc, rfl⟩ := Polynomial.isUnit_iff.mp hu
    simpa using mul_self_pos.mpr hc.ne_zero
  | mul g i _ hi ih =>
    have h₁ := eval_mul_eval_pos_of_irreducible hi hab fun x hx h ↦
      hroot x hx (root_mul.mpr (.inl h))
    have h₂ := ih fun x hx h ↦ hroot x hx (root_mul.mpr (.inr h))
    rw [eval_mul, eval_mul]
    convert mul_pos h₁ h₂ using 1
    ring

/-- A polynomial over a real closed ordered field that changes sign on an interval has a root
inside it.
- [BCR98, §1.2] -/
theorem exists_mem_Ioo_isRoot {f : R[X]} {a b : R} (hab : a < b) (ha : f.eval a < 0)
    (hb : 0 < f.eval b) : ∃ c ∈ Set.Ioo a b, f.IsRoot c := by
  by_contra! h
  refine (mul_neg_of_neg_of_pos ha hb).not_gt (eval_mul_eval_pos hab.le ?_)
  intro x ⟨h₁, h₂⟩ hx
  rcases h₁.eq_or_lt with rfl | h₁
  · exact ha.ne hx
  rcases h₂.eq_or_lt with rfl | h₂
  · exact hb.ne' hx
  exact h x ⟨h₁, h₂⟩ hx

end IsRealClosed
