module

public import AlphaCentauri.Model.IntegerConstantPolynomial
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

open FFL FirstOrder Polynomial

private lemma map_pow_of_map_mul {M S : Type*} [CommSemiring M] [CommSemiring S] (f : M → S)
    (hone : f 1 = 1) (hmul : ∀ a b, f (a * b) = f a * f b) (a : M) (k : ℕ) :
    f (a ^ k) = f a ^ k :=
  map_pow ({ toFun := f, map_one' := hone, map_mul' := hmul } : M →* S) a k

lemma not_models_fermatLastTheorem_of_pow_add_pow {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] [OpenPredicate.DiscretelyOrdered R] {n : ℕ} {a b c : R}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (ha₀ : a ≠ 0) (hb₀ : b ≠ 0) (hc₀ : c ≠ 0)
    (h : a ^ n + b ^ n = c ^ n) : ¬ (Nonneg R)↓[ℒₒᵣ] ⊧ Arithmetic.fermatLastTheorem n := by
  simp [Arithmetic.fermatLastTheorem, models_iff]
  let F : CommSemiring (Nonneg R) := Arithmetic.instCommSemiring_foundation
  have hpow (p : Nonneg R) :=
    @map_pow_of_map_mul (Nonneg R) R F _ Subtype.val rfl (fun _ _ ↦ rfl) p n
  have h₁ := congrArg₂ (· + ·) (hpow ⟨a, ha⟩) (hpow ⟨b, hb⟩)
  exact ⟨a, ha, b, hb, c, ⟨hc, Subtype.ext <| h₁.trans (h.trans (hpow ⟨c, hc⟩).symm)⟩,
    ha₀, hb₀, hc₀⟩

/-- $\mathsf{IOpen}$ does not prove Fermat's Last Theorem for any exponent $n \ge 3$.
- [She64]
- [Smi92b, Introduction]
- [DAq05, §2] -/
theorem _root_.FFL.FirstOrder.Arithmetic.not_provable_fermatLastTheorem_IOpen {n : ℕ}
    (hn : 3 ≤ n) : ¬ 𝗜𝗢𝗽𝗲𝗻 ⊢ Arithmetic.fermatLastTheorem n := by
  have hF : Arithmetic.fermatLastTheorem n = ∀¹*
      (“#2 ^' n + #1 ^' n = #0 ^' n → #2 = 0 ∨ #1 = 0 ∨ #0 = 0” : ArithmeticSemiformula Empty 3) :=
    rfl
  have := IntegerConstantPolynomial.models_ZRing ℝ
  rw [hF]
  apply Arithmetic.not_provable_IOpen_allClosure (by simp) (Nonneg (IntegerConstantPolynomial ℝ))
  rw [← hF]
  obtain ⟨c, hc₀, hc⟩ : ∃ c : ℝ, 0 < c ∧ c ^ n = 2 :=
    ⟨(2 : ℝ) ^ (n : ℝ)⁻¹, Real.rpow_pos_of_pos (by norm_num) _,
      Real.rpow_inv_natCast_pow (by norm_num) (by omega)⟩
  let z : IntegerConstantPolynomial ℝ :=
    ⟨C c * Polynomial.X, IntegerConstantPolynomial.mem_iff.mpr ⟨0, by simp⟩⟩
  apply not_models_fermatLastTheorem_of_pow_add_pow (a := IntegerConstantPolynomial.X ℝ)
    (b := IntegerConstantPolynomial.X ℝ) (c := z)
  · simp [IntegerConstantPolynomial.nonneg_iff, IntegerConstantPolynomial.X]
  · simp [IntegerConstantPolynomial.nonneg_iff, IntegerConstantPolynomial.X]
  · simp [IntegerConstantPolynomial.nonneg_iff, z, hc₀.le]
  · simp [Subtype.ext_iff, IntegerConstantPolynomial.X]
  · simp [Subtype.ext_iff, IntegerConstantPolynomial.X]
  · simp [Subtype.ext_iff, z, hc₀.ne']
  · apply Subtype.ext
    simp only [z, IntegerConstantPolynomial.X, AddMemClass.coe_add, SubmonoidClass.coe_pow]
    rw [mul_pow, ← C_pow, hc, C_ofNat]
    ring
