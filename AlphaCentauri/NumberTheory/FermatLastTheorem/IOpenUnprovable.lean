module

public import AlphaCentauri.Model.IntegerConstantPolynomial
public import AlphaCentauri.Model.NonnegativePart
public import AlphaCentauri.Model.OpenInduction
public import AlphaCentauri.NumberTheory.FermatLastTheorem.Basic
public import AlphaCentauri.ToMathlib.OpenPredicate.IntegerConstantPolynomial
public import AlphaCentauri.ToMathlib.OpenPredicate.PadicIntegralPolynomial
public import Foundation.FirstOrder.Arithmetic.IOpen.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.NumberTheory.Padics.Hensel

/-!
# Non-provability of Fermat's Last Theorem in $\mathsf{IOpen}$

$\mathsf{IOpen}$ does not prove Fermat's Last Theorem for any exponent $n \ge 3$, and does not
prove Case I of it for some exponent. A nonzero solution of $x^n + y^n = z^n$ in a discretely
ordered ring is a counterexample to Fermat's Last Theorem in its non-negative part, and
$\mathsf{IOpen}$ proves only the universal sentences true in every model of $\mathsf{ZR}$.

- [She64]
- [Smi92b]
- [DAq05]
- [Wil78]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

variable {n : ℕ}

open Tarski.Structure in
/-- A model of $\mathsf{ZR}$ with a solution of $x^n + y^n = z^n$ for which $x y z$ leaves a
non-zero remainder modulo $n$ embeds into a model of $\mathsf{IOpen}$ refuting Case I of Fermat's
Last Theorem for exponent $n$.
- [Wil78, Lemma 3.2] -/
lemma not_provable_fermatLastTheoremCaseOne_IOpen_of_models_ZRing {M : Type} [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* ZRing] {r : ℕ} (hr₀ : 0 < r) (hr : r < n) {x y z w : M}
    (h : x ^ n + y ^ n = z ^ n) (hxyz : x * y * z = w * n + r) :
    𝗜𝗢𝗽𝗲𝗻 ⊬ fermatLastTheoremCaseOne n := by
  obtain ⟨W, _, hW, ⟨Θ⟩⟩ := exists_embedding_models_IOpen M
  intro hp
  have hC : ∀ a b c : W, a ^ n + b ^ n = c ^ n → (n : W) ∣ a * b * c := by
    simpa [models_iff, fermatLastTheoremCaseOne, numeral_eq_natCast] using
      models_of_provable hW hp
  let f : M →+* W :=
    { toFun := Θ
      map_zero' := by simpa [Function.comp_def] using HomClass.func Θ Language.Zero.zero ![]
      map_one' := by simpa [Function.comp_def] using HomClass.func Θ Language.One.one ![]
      map_add' a b := by simpa [Function.comp_def] using HomClass.func Θ Language.Add.add ![a, b]
      map_mul' a b := by simpa [Function.comp_def] using HomClass.func Θ Language.Mul.mul ![a, b] }
  have e₁ : f x ^ n + f y ^ n = f z ^ n := by simpa using congrArg f h
  have e₂ : f x * f y * f z = f w * n + r := by simpa using congrArg f hxyz
  have := hC _ _ _ e₁
  rw [e₂, ← mod_eq_zero_iff_dvd, mod_mul_add_of_lt _ _ (by exact_mod_cast hr)] at this
  exact hr₀.ne' (by exact_mod_cast this)

end FFL.FirstOrder.Arithmetic

namespace FFL.FirstOrder

open Polynomial Semiformula IntermediateField OpenPredicate

private lemma map_pow_of_map_mul {M S : Type*} [CommSemiring M] [CommSemiring S] (f : M → S)
    (hone : f 1 = 1) (hmul : ∀ a b, f (a * b) = f a * f b) (a : M) (k : ℕ) :
    f (a ^ k) = f a ^ k :=
  map_pow ({ toFun := f, map_one' := hone, map_mul' := hmul } : M →* S) a k

private lemma not_evalb_fermatLastTheorem_of_pow_add_pow {R : Type*} [CommRing R]
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

private lemma irreducible_X_pow_seven_sub_C : Irreducible (X ^ 7 - C (5 ^ 7 - 1 : ℚ)) := by
  apply X_pow_sub_C_irreducible_of_prime (by decide : Nat.Prime 7)
  intro b hb
  have hden : b.den = 1 := by
    have := Rat.den_pow b 7
    rw [hb] at this
    simpa using this.symm
  rw [← Rat.coe_int_num_of_den_eq_one hden] at hb
  have hn : b.num ^ 7 = 5 ^ 7 - 1 := by exact_mod_cast hb
  have h₁ : b.num < 5 := by
    by_contra h
    have : (5 : ℤ) ^ 7 ≤ b.num ^ 7 := pow_le_pow_left₀ (by norm_num) (not_lt.mp h) 7
    omega
  have h₂ : 4 < b.num := by
    by_contra h
    have : b.num ^ 7 ≤ 4 ^ 7 := (Odd.pow_le_pow (by decide)).mpr (not_lt.mp h)
    omega
  omega

private lemma exists_padicInt_pow_seven_eq [Fact (Nat.Prime 7)] :
    ∃ y : ℤ_[7], y ^ 7 = 5 ^ 7 - 1 ∧ (7 : ℤ_[7]) ∣ y - 4 := by
  have h₇ : ‖(7 : ℤ_[7])‖ = 7⁻¹ := by exact_mod_cast PadicInt.norm_p (p := 7)
  have hu (k : ℤ) (hk : ¬(7 : ℤ) ∣ k) : ‖(k : ℤ_[7])‖ = 1 :=
    le_antisymm (PadicInt.norm_le_one _)
      (not_lt.mp ((PadicInt.norm_int_lt_one_iff_dvd k).not.mpr hk))
  have e₁ : (X ^ 7 - C (5 ^ 7 - 1) : ℤ_[7][X]).eval 4 = 7 ^ 3 * ((-180 : ℤ) : ℤ_[7]) := by
    simp only [eval_sub, eval_pow, eval_X, eval_C]
    norm_num
  have e₂ : (derivative (X ^ 7 - C (5 ^ 7 - 1) : ℤ_[7][X])).eval 4 = 7 * ((4096 : ℤ) : ℤ_[7]) := by
    rw [derivative_sub, derivative_X_pow, derivative_C, sub_zero]
    simp
    norm_num
  have hd : ‖(derivative (X ^ 7 - C (5 ^ 7 - 1) : ℤ_[7][X])).eval 4‖ = 7⁻¹ := by
    rw [e₂, norm_mul, h₇, hu _ (by decide), mul_one]
  obtain ⟨y, hy, hy₄, -⟩ := hensels_lemma (R := ℤ_[7]) (F := X ^ 7 - C (5 ^ 7 - 1)) (a := 4) <| by
    change ‖eval 4 _‖ < ‖eval 4 _‖ ^ 2
    rw [hd, e₁, norm_mul, norm_pow, h₇, hu _ (by decide)]
    norm_num
  simp only [coe_aeval_eq_eval] at hy hy₄
  rw [hd] at hy₄
  use y
  and_intros
  · simpa [sub_eq_zero] using hy
  · exact (PadicInt.norm_lt_one_iff_dvd _).mp (hy₄.trans (by norm_num))

/-- $\mathsf{IOpen}$ does not prove Case I of Fermat's Last Theorem for exponent $7$: some model of
$\mathsf{IOpen}$ has $x^7 + y^7 = z^7$ with $x y z \equiv 6 \pmod 7$.
- [Smi92b, Question 5.1]
- [Wil78, Lemma 3.2] -/
theorem not_provable_fermatLastTheoremCaseOne_seven_IOpen :
    𝗜𝗢𝗽𝗲𝗻 ⊬ Arithmetic.fermatLastTheoremCaseOne 7 := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨y₀, hy₀, t, ht⟩ := exists_padicInt_pow_seven_eq
  have hy₀' : (y₀ : ℚ_[7]) ^ 7 = 5 ^ 7 - 1 := by
    have := congrArg ((↑) : ℤ_[7] → ℚ_[7]) hy₀
    push_cast at this
    exact this
  have ht' : (y₀ : ℚ_[7]) = 7 * t + 4 := by
    have := congrArg ((↑) : ℤ_[7] → ℚ_[7]) (show y₀ = 7 * t + 4 by linear_combination ht)
    push_cast at this
    exact this
  obtain ⟨σ, hσ, hσ₇⟩ : ∃ σ : ℝ, 0 < σ ∧ σ ^ 7 = 5 ^ 7 - 1 :=
    ⟨_, Real.rpow_pos_of_pos (by norm_num) ((7 : ℕ) : ℝ)⁻¹,
      Real.rpow_inv_natCast_pow (by norm_num) (by norm_num)⟩
  have hmonic := monic_X_pow_sub_C (5 ^ 7 - 1 : ℚ) (by norm_num : 7 ≠ 0)
  have hroot : aeval σ (X ^ 7 - C (5 ^ 7 - 1 : ℚ)) = 0 := by simp [hσ₇]
  have hint : IsIntegral ℚ σ := ⟨_, hmonic, by simpa [aeval_def] using hroot⟩
  have hmin : minpoly ℚ σ = X ^ 7 - C (5 ^ 7 - 1) :=
    (minpoly.eq_of_irreducible_of_monic irreducible_X_pow_seven_sub_C hroot hmonic).symm
  let χ : ℚ⟮σ⟯ →ₐ[ℚ] ℚ_[7] := (algHomAdjoinIntegralEquiv ℚ hint).symm ⟨(y₀ : ℚ_[7]), by
    rw [hmin, mem_aroots]
    and_intros
    · exact X_pow_sub_C_ne_zero (by norm_num) _
    · simp [hy₀']⟩
  let s := AdjoinSimple.gen ℚ σ
  have hχs : χ s = y₀ := algHomAdjoinIntegralEquiv_symm_apply_gen ℚ hint _
  have hs : 0 < s := hσ
  have hs₇ : s ^ 7 = 5 ^ 7 - 1 := by
    apply (algebraMap ℚ⟮σ⟯ ℝ).injective
    rw [map_pow, map_sub, map_pow, map_ofNat, map_one, AdjoinSimple.algebraMap_gen, hσ₇]
  let R := PadicIntegralPolynomial (χ : ℚ⟮σ⟯ →+* ℚ_[7])
  let x : R := ⟨Polynomial.X, by
    rw [PadicIntegralPolynomial.mem_iff]
    and_intros
    · use 0, 0
      simp
    · simp⟩
  let y : R := ⟨C s * Polynomial.X, by
    rw [PadicIntegralPolynomial.mem_iff]
    and_intros
    · use 0, 0
      simp
    · simpa [hχs] using y₀.2⟩
  let w : R := ⟨C (5 * s / 7) * Polynomial.X ^ 3 - C (6 / 7), by
    rw [PadicIntegralPolynomial.mem_iff]
    and_intros
    · use 1, -6
      simp
      ring
    · have : χ (5 * s / 7 - 6 / 7) = (5 * t + 2 : ℤ_[7]) := by
        rw [(by norm_cast : ((5 * t + 2 : ℤ_[7]) : ℚ_[7]) = 5 * t + 2)]
        simp only [map_sub, map_div₀, map_mul, map_ofNat, hχs, ht']
        ring
      simpa [this] using (5 * t + 2).2⟩
  have hx : 0 ≤ x := by
    rw [LeadingCoeffOrder.nonneg_iff]
    simp [x]
  have hy : 0 ≤ y := by
    rw [LeadingCoeffOrder.nonneg_iff]
    simpa [y] using hs.le
  have hw : 0 ≤ w := by
    have ha : 5 * s / 7 ≠ 0 := by positivity
    rw [LeadingCoeffOrder.nonneg_iff]
    simp only [w]
    rw [leadingCoeff_sub_of_degree_lt, leadingCoeff_C_mul_X_pow]
    · positivity
    · rw [degree_C_mul_X_pow 3 ha]
      exact degree_C_le.trans_lt (by norm_num)
  have hz : 0 ≤ 5 * x := mul_nonneg (by norm_num) hx
  have h₅ : ((5 : R) : Polynomial ℚ⟮σ⟯) = 5 := map_ofNat R.subtype 5
  have h : x ^ 7 + y ^ 7 = (5 * x) ^ 7 := by
    apply Subtype.ext
    simp only [x, y, Subring.coe_add, Subring.coe_pow, Subring.coe_mul, h₅]
    rw [mul_pow, mul_pow, ← C_pow, hs₇, map_sub, map_pow, map_one, map_ofNat]
    ring
  have hxyz : x * y * (5 * x) = w * (7 : ℕ) + (6 : ℕ) := by
    have e₁ : (7 : Polynomial ℚ⟮σ⟯) * C (5 * s / 7) = 5 * C s := by
      rw [← map_ofNat C 7, ← map_ofNat C 5, ← C_mul, ← C_mul]
      congr 1
      ring
    have e₂ : (7 : Polynomial ℚ⟮σ⟯) * C (6 / 7) = 6 := by
      rw [← map_ofNat C 7, ← map_ofNat C 6, ← C_mul]
      congr 1
      ring
    apply Subtype.ext
    simp only [x, y, w, Subring.coe_add, Subring.coe_mul, Subring.coe_natCast, h₅]
    push_cast
    linear_combination (-Polynomial.X ^ 3) * e₁ + e₂
  have := Nonneg.models_ZRing (R := R) PadicIntegralPolynomial.exists_eq_mul_add_of_pos
  let F : CommSemiring (Nonneg R) := Arithmetic.instCommSemiring_foundation
  have hpow (a : Nonneg R) (k : ℕ) :=
    @map_pow_of_map_mul (Nonneg R) R F _ Subtype.val rfl (fun _ _ ↦ rfl) a k
  apply Arithmetic.not_provable_fermatLastTheoremCaseOne_IOpen_of_models_ZRing (M := Nonneg R)
    (r := 6) (by norm_num) (by norm_num) (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) (z := ⟨5 * x, hz⟩)
    (w := ⟨w, hw⟩)
  · exact Subtype.ext <| (congrArg₂ (· + ·) (hpow ⟨x, hx⟩ 7) (hpow ⟨y, hy⟩ 7)).trans
      (h.trans (hpow ⟨5 * x, hz⟩ 7).symm)
  · rw [Nonneg.natCast_foundation, Nonneg.natCast_foundation]
    exact Subtype.ext hxyz

/-- $\mathsf{IOpen}$ does not prove Case I of Fermat's Last Theorem for some exponent $n \ge 3$.
- [Smi92b, Question 5.1] -/
theorem exists_not_provable_fermatLastTheoremCaseOne_IOpen :
    ∃ n : ℕ, 3 ≤ n ∧ 𝗜𝗢𝗽𝗲𝗻 ⊬ Arithmetic.fermatLastTheoremCaseOne n := by
  use 7
  and_intros
  · norm_num
  · exact not_provable_fermatLastTheoremCaseOne_seven_IOpen

end FFL.FirstOrder
