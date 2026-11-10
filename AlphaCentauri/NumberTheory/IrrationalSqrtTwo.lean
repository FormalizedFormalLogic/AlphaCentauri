module

public import AlphaCentauri.Model.IntegerConstantPolynomial
public import AlphaCentauri.Model.OpenInduction
public import AlphaCentauri.NumberTheory.FLT3
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.LinearCombination

/-!
# The irrationality of $\sqrt{2}$ in $\mathsf{IOpen}$

$\mathsf{IOpen}$ together with Bézout's theorem proves the irrationality of $\sqrt{2}$, while
$\mathsf{IOpen}$ alone does not.

In the non-negative part of the $\mathbb{Z}$-ring of real polynomials with integer constant term,
$x = \sqrt{2} X$ and $y = X$ satisfy $x^2 = 2 y^2$ with $y \ne 0$. Since the irrationality of
$\sqrt{2}$ is a universal sentence, $\mathsf{IOpen}$ does not prove it.
-/

@[expose] public section

open FFL FirstOrder Polynomial Semiformula

namespace FFL.FirstOrder

/-- The irrationality of $\sqrt{2}$: $x^2 = 2 y^2$ implies $y = 0$. -/
def Arithmetic.irrationalSqrtTwo : ArithmeticSentence := “∀ x y, x * x = 2 * (y * y) → y = 0”

/-- $\mathsf{IOpen}$ does not prove the irrationality of $\sqrt{2}$.
- [She64]
- [DAq05, §2]
- [Wil78] -/
theorem not_provable_irrationalSqrtTwo_IOpen : 𝗜𝗢𝗽𝗲𝗻 ⊬ Arithmetic.irrationalSqrtTwo := by
  rw [show Arithmetic.irrationalSqrtTwo =
      ∀¹* (“y x. x * x = 2 * (y * y) → y = 0” : ArithmeticSemisentence 2) by
    simp [Arithmetic.irrationalSqrtTwo, allClosure_succ]]
  have := IntegerConstantPolynomial.models_ZRing ℝ
  have hy : 0 ≤ IntegerConstantPolynomial.X ℝ := by
    rw [LeadingCoeffOrder.nonneg_iff]
    simp [IntegerConstantPolynomial.X]
  let x : IntegerConstantPolynomial ℝ :=
    ⟨C (Real.sqrt 2) * Polynomial.X, IntegerConstantPolynomial.mem_iff.mpr ⟨0, by simp⟩⟩
  have hx : 0 ≤ x := by
    rw [LeadingCoeffOrder.nonneg_iff]
    simp [x]
  apply Arithmetic.not_provable_IOpen_allClosure (M := Nonneg (IntegerConstantPolynomial ℝ))
    (e := ![⟨_, hy⟩, ⟨x, hx⟩]) (by simp)
  simp only [Evalb, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
    LogicalConnective.HomClass.map_imply, eval_operator, Matrix.comp₂, Semiterm.val_operator,
    Semiterm.val_bvar, Matrix.cons_val_one, Fin.Fin1.eq_one, Matrix.cons_val_fin_one,
    Tarski.Structure.Mul.mul, Nonneg.mk_mul_mk, Matrix.comp₀, Tarski.Structure.numeral_eq_numeral,
    Arithmetic.numeral_two_eq_two, Matrix.cons_val_zero, Tarski.Structure.eq_iff_eq,
    ORingStructure.zero_eq_zero, Nonneg.mk_eq_zero, LogicalConnective.Prop.arrow_eq, not_imp]
  and_intros
  · have h₁ : C (Real.sqrt 2) * C (Real.sqrt 2) = (2 : ℝ[X]) := by
      rw [← C_mul, Real.mul_self_sqrt (by norm_num)]
      exact map_ofNat C 2
    have h₂ : ((2 : IntegerConstantPolynomial ℝ) : ℝ[X]) = 2 :=
      map_ofNat (IntegerConstantPolynomial ℝ).subtype 2
    apply Subtype.ext
    apply Subtype.ext
    simp only [x, IntegerConstantPolynomial.X, Subring.coe_mul, Nonneg.coe_mul]
    rw [Nonneg.coe_ofNat_foundation, h₂]
    linear_combination (Polynomial.X * Polynomial.X) * h₁
  · apply ne_of_gt
    simpa using IntegerConstantPolynomial.natCast_lt_X (K := ℝ) 0

namespace Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

lemma false_of_mul_self_eq_two_mul_of_bezout {x y : V} (hbez : V↓[ℒₒᵣ] ⊧ bezout) (hy : y ≠ 0)
    (h : x * x = 2 * (y * y)) : False := by
  replace hbez : ∀ x y : V, y ≠ 0 → ∃ z s t, s * y = t * x + z ∧ z ∣ x ∧ z ∣ y := by
    simpa [models_iff, bezout] using hbez
  obtain ⟨z, s, t, e, ⟨x', rfl⟩, ⟨y', rfl⟩⟩ := hbez x y hy
  have hz : z ≠ 0 := by rintro rfl; simp at hy
  have h₁ : x' * x' = 2 * (y' * y') := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hz)
    grind
  have h₂ : s * y' = t * x' + 1 := by
    apply mul_left_cancel₀ hz
    grind
  obtain ⟨a, rfl⟩ : 2 ∣ x' := (two_prime (V := V)).dvd_of_dvd_pow (n := 2) ⟨y' * y', by grind⟩
  have h₃ : y' * y' = 2 * (a * a) := by
    apply mul_left_cancel₀ (two_ne_zero (α := V))
    grind
  obtain ⟨b, rfl⟩ : 2 ∣ y' := (two_prime (V := V)).dvd_of_dvd_pow (n := 2) ⟨a * a, by grind⟩
  have h₄ : (1 + t * (2 * a)) % 2 = 0 := mod_eq_zero_iff_dvd.mpr ⟨s * b, by grind⟩
  simp [mod_add_remove_right_of_dvd (b := t * (2 * a)) (m := 2) ⟨t * a, by grind⟩ (by simp)] at h₄

/-- $\mathsf{IOpen} + \mathrm{Bez}$ proves the irrationality of $\sqrt{2}$.
- [DAq05, §2]
- [Smi92b, Theorem 1.14] -/
theorem provable_irrationalSqrtTwo_IOpen_bezout :
    insert bezout 𝗜𝗢𝗽𝗲𝗻 ⊢ irrationalSqrtTwo := by
  have : 𝗜𝗢𝗽𝗲𝗻 ⪯ insert bezout 𝗜𝗢𝗽𝗲𝗻 := Entailment.WeakerThan.ofSubset (Set.subset_insert _ _)
  have : 𝗘𝗤 ℒₒᵣ ⪯ insert bezout 𝗜𝗢𝗽𝗲𝗻 :=
    Entailment.WeakerThan.trans (𝓣 := 𝗜𝗢𝗽𝗲𝗻) inferInstance inferInstance
  apply complete
  intro (V : Type) _ hV
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := insert bezout 𝗜𝗢𝗽𝗲𝗻) hV
  suffices ∀ x y : V, x * x = 2 * (y * y) → y = 0 by
    simpa [models_iff, irrationalSqrtTwo]
  intro x y h
  by_contra hy
  exact false_of_mul_self_eq_two_mul_of_bezout
    (models_of_mem (T := insert bezout 𝗜𝗢𝗽𝗲𝗻) (Set.mem_insert _ _)) hy h

/-- $\mathsf{IOpen}$ is strictly weaker than $\mathsf{IOpen} + \mathrm{Bez}$.
- [DAq05, §2]
- [Smi92b, Theorem 1.14] -/
theorem IOpen_strictlyWeakerThan_IOpen_bezout : 𝗜𝗢𝗽𝗲𝗻 ⪱ insert bezout 𝗜𝗢𝗽𝗲𝗻 := by
  constructor
  · exact Entailment.WeakerThan.ofSubset (Set.subset_insert _ _)
  · intro h
    exact not_provable_irrationalSqrtTwo_IOpen (h.pbl provable_irrationalSqrtTwo_IOpen_bezout)

end Arithmetic

end FFL.FirstOrder
