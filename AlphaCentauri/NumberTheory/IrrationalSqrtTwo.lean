module

public import AlphaCentauri.Model.IntegerConstantPolynomial
public import AlphaCentauri.Model.OpenInduction
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.LinearCombination

/-!
# The irrationality of $\sqrt{2}$ is not provable in $\mathsf{IOpen}$

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
theorem not_provable_irrationalSqrtTwo_IOpen : ¬ 𝗜𝗢𝗽𝗲𝗻 ⊢ Arithmetic.irrationalSqrtTwo := by
  have : Arithmetic.irrationalSqrtTwo =
      ∀¹* (“y x. x * x = 2 * (y * y) → y = 0” : ArithmeticSemisentence 2) := by
    simp [Arithmetic.irrationalSqrtTwo, allClosure_succ]
  rw [this]
  have := IntegerConstantPolynomial.models_ZRing ℝ
  have hy : 0 ≤ IntegerConstantPolynomial.X ℝ := by
    rw [IntegerConstantPolynomial.nonneg_iff]
    simp [IntegerConstantPolynomial.X]
  let x : IntegerConstantPolynomial ℝ :=
    ⟨C (Real.sqrt 2) * Polynomial.X, IntegerConstantPolynomial.mem_iff.mpr ⟨0, by simp⟩⟩
  have hx : 0 ≤ x := by
    rw [IntegerConstantPolynomial.nonneg_iff]
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
  · apply Subtype.ext
    apply Subtype.ext
    have h : C (Real.sqrt 2) * C (Real.sqrt 2) = (C 2 : ℝ[X]) := by
      rw [← C_mul, Real.mul_self_sqrt (by norm_num)]
    have key : C (Real.sqrt 2) * Polynomial.X * (C (Real.sqrt 2) * Polynomial.X) =
        C 2 * (Polynomial.X * Polynomial.X) := by
      linear_combination (Polynomial.X * Polynomial.X) * h
    simp only [x, IntegerConstantPolynomial.X, MulMemClass.coe_mul, Nonneg.coe_mul]
    convert key using 3
    change (((@Nat.cast (Nonneg (IntegerConstantPolynomial ℝ))
      Arithmetic.instCommSemiring_foundation.toNatCast 2 : Nonneg _) :
        IntegerConstantPolynomial ℝ) : ℝ[X]) = C 2
    rw [Nonneg.natCast_foundation]
    exact coeff_inj.mp rfl
  · exact (by simpa using IntegerConstantPolynomial.natCast_lt_X (K := ℝ) 0 :
      (0 : IntegerConstantPolynomial ℝ) < _).ne'

end FFL.FirstOrder
