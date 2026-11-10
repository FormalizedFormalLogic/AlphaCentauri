module

public import AlphaCentauri.Model.OpenInduction
public import AlphaCentauri.NumberTheory.FLT3
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Non-provability of Fermat's Last Theorem in $\mathsf{IOpen}$

A nonzero solution of $x^n + y^n = z^n$ in a discretely ordered ring is a counterexample to
Fermat's Last Theorem in its non-negative part. In the $\mathbb{Z}$-ring of real polynomials with
integer constant term, $x = y = X$ and $z = 2^{1/n} X$ is such a solution, and $\mathsf{IOpen}$
proves only the universal sentences true in every model of $\mathsf{ZR}$.

- [She64]
- [Smi92b, Introduction]
- [DAq05, §2]
-/

@[expose] public section

open FFL FirstOrder Polynomial Semiformula

private lemma map_pow_of_map_mul {M S : Type*} [CommSemiring M] [CommSemiring S] (f : M → S)
    (hone : f 1 = 1) (hmul : ∀ a b, f (a * b) = f a * f b) (a : M) (k : ℕ) :
    f (a ^ k) = f a ^ k :=
  map_pow ({ toFun := f, map_one' := hone, map_mul' := hmul } : M →* S) a k

lemma not_evalb_fermatLastTheorem_of_pow_add_pow {R : Type*} [CommRing R]
    [LinearOrder R] [IsStrictOrderedRing R] [OpenPredicate.DiscretelyOrdered R] {n : ℕ}
    {a b c : R} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (ha₀ : a ≠ 0) (hb₀ : b ≠ 0)
    (hc₀ : c ≠ 0) (h : a ^ n + b ^ n = c ^ n) :
    ¬ Evalb (M := Nonneg R) ![⟨c, hc⟩, ⟨b, hb⟩, ⟨a, ha⟩]
      (“#2 ^' n + #1 ^' n = #0 ^' n → #2 = 0 ∨ #1 = 0 ∨ #0 = 0” : ArithmeticSemisentence 3) := by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Evalb, Fin.isValue,
    LogicalConnective.HomClass.map_imply, eval_operator, Matrix.comp₂, Semiterm.val_operator,
    Matrix.comp₁, Semiterm.val_bvar, Matrix.cons_app_two, Matrix.cons_val_one, Fin.Fin1.eq_one,
    Matrix.cons_val_fin_one, Arithmetic.val_npow, Matrix.cons_val_zero, Tarski.Structure.Add.add,
    Tarski.Structure.eq_iff_eq, LogicalConnective.HomClass.map_or, Matrix.comp₀,
    Tarski.Structure.numeral_eq_numeral, ORingStructure.zero_eq_zero, Nonneg.mk_eq_zero,
    LogicalConnective.Prop.or_eq, LogicalConnective.Prop.arrow_eq, not_imp, not_or]
  and_intros
  · let F : CommSemiring (Nonneg R) := Arithmetic.instCommSemiring_foundation
    have hpow (p : Nonneg R) :=
      @map_pow_of_map_mul (Nonneg R) R F _ Subtype.val rfl (fun _ _ ↦ rfl) p n
    exact Subtype.ext <| (congrArg₂ (· + ·) (hpow ⟨a, ha⟩) (hpow ⟨b, hb⟩)).trans
      (h.trans (hpow ⟨c, hc⟩).symm)
  all_goals assumption

namespace FFL.FirstOrder

/-- $\mathsf{IOpen}$ does not prove Fermat's Last Theorem for any exponent $n \ge 3$.
- [She64]
- [Smi92b, Introduction]
- [DAq05, §2] -/
theorem not_provable_fermatLastTheorem_IOpen {n : ℕ} (hn : 3 ≤ n) :
    𝗜𝗢𝗽𝗲𝗻 ⊬ Arithmetic.fermatLastTheorem n := by
  have hF : Arithmetic.fermatLastTheorem n = ∀¹*
      (“#2 ^' n + #1 ^' n = #0 ^' n → #2 = 0 ∨ #1 = 0 ∨ #0 = 0” : ArithmeticSemisentence 3) :=
    rfl
  obtain ⟨c, hc₀, hc⟩ : ∃ c : ℝ, 0 < c ∧ c ^ n = 2 :=
    ⟨(2 : ℝ) ^ (n : ℝ)⁻¹, Real.rpow_pos_of_pos (by norm_num) _,
      Real.rpow_inv_natCast_pow (by norm_num) (by omega)⟩
  let z : IntegerConstantPolynomial ℝ :=
    ⟨C c * Polynomial.X, IntegerConstantPolynomial.mem_iff.mpr ⟨0, by simp⟩⟩
  have hx : 0 ≤ IntegerConstantPolynomial.X ℝ := by
    rw [LeadingCoeffOrder.nonneg_iff]
    simp [IntegerConstantPolynomial.X]
  have hz : 0 ≤ z := by
    rw [LeadingCoeffOrder.nonneg_iff]
    simp [z, hc₀.le]
  have := IntegerConstantPolynomial.models_ZRing ℝ
  rw [hF]
  apply Arithmetic.not_provable_IOpen_allClosure (M := Nonneg (IntegerConstantPolynomial ℝ))
    (e := ![⟨z, hz⟩, ⟨_, hx⟩, ⟨_, hx⟩]) (by simp)
  apply not_evalb_fermatLastTheorem_of_pow_add_pow hx hx hz
  · simp [Subtype.ext_iff, IntegerConstantPolynomial.X]
  · simp [Subtype.ext_iff, IntegerConstantPolynomial.X]
  · simp [Subtype.ext_iff, z, hc₀.ne']
  · apply Subtype.ext
    simp only [z, IntegerConstantPolynomial.X, AddMemClass.coe_add, SubmonoidClass.coe_pow]
    rw [mul_pow, ← C_pow, hc, C_ofNat]
    ring

end FFL.FirstOrder
