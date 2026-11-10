module

public import AlphaCentauri.Model.NonnegativePart
public import AlphaCentauri.Schemata.PeanoMinusSmu
public import AlphaCentauri.Schemata.ZRing
public import AlphaCentauri.ToFoundation.EventualAgreement
public import AlphaCentauri.ToMathlib.IntegerConstantDyadicPolynomial

/-!
# The non-negative part of the $\mathbb{Z}$-ring of dyadic polynomials with integer constant term

The non-negative part of `IntegerConstantDyadicPolynomial` is a model of
$\mathsf{PA}^-_{\mathrm{smu}}$ in which every universal sentence true in `ℕ` holds and in which `X`
cannot be divided by `3` with remainder. The universal sentences are transferred from `ℕ` by
evaluating the polynomials at $2^n$ for large `n`.
-/

@[expose] public noncomputable section

open FFL FirstOrder Polynomial Filter

namespace IntegerConstantDyadicPolynomial

local notation "𝔻" => IntegerConstantDyadicPolynomial

/-- The value at $2^n$, as a natural number. -/
def evalTwoPow (n : ℕ) (x : Nonneg 𝔻) : ℕ := ⌊((x : 𝔻) : ℚ[X]).eval (2 ^ n)⌋.toNat

lemma eventually_evalTwoPow (x : Nonneg 𝔻) :
    ∀ᶠ n in atTop, (evalTwoPow n x : ℚ) = ((x : 𝔻) : ℚ[X]).eval (2 ^ n) := by
  filter_upwards [eventually_eval_two_pow_eq_natCast x.2] with n ⟨m, hm⟩
  simp [evalTwoPow, hm]

lemma eventually_evalTwoPow_func {k : ℕ} (f : Language.Func ℒₒᵣ k) (v : Fin k → Nonneg 𝔻) :
    ∀ᶠ n in atTop, evalTwoPow n (Tarski.Structure.func f v) =
      Tarski.Structure.func f (evalTwoPow n ∘ v) := by
  cases f
  · exact .of_forall fun n ↦ by simp [evalTwoPow, Tarski.Structure.func]
  · exact .of_forall fun n ↦ by simp [evalTwoPow, Tarski.Structure.func]
  · filter_upwards [eventually_evalTwoPow (v 0), eventually_evalTwoPow (v 1),
      eventually_evalTwoPow (v 0 + v 1)] with n h₀ h₁ h
    change evalTwoPow n (v 0 + v 1) = evalTwoPow n (v 0) + evalTwoPow n (v 1)
    have : (evalTwoPow n (v 0 + v 1) : ℚ) = evalTwoPow n (v 0) + evalTwoPow n (v 1) := by
      rw [h, h₀, h₁]
      simp
    exact_mod_cast this
  · filter_upwards [eventually_evalTwoPow (v 0), eventually_evalTwoPow (v 1),
      eventually_evalTwoPow (v 0 * v 1)] with n h₀ h₁ h
    change evalTwoPow n (v 0 * v 1) = evalTwoPow n (v 0) * evalTwoPow n (v 1)
    have : (evalTwoPow n (v 0 * v 1) : ℚ) = evalTwoPow n (v 0) * evalTwoPow n (v 1) := by
      rw [h, h₀, h₁]
      simp
    exact_mod_cast this

lemma eventually_evalTwoPow_rel {k : ℕ} (r : Language.Rel ℒₒᵣ k) (v : Fin k → Nonneg 𝔻) :
    ∀ᶠ n in atTop, (Tarski.Structure.rel r v ↔ Tarski.Structure.rel r (evalTwoPow n ∘ v)) := by
  cases r
  · change ∀ᶠ n in atTop, (v 0 = v 1 ↔ evalTwoPow n (v 0) = evalTwoPow n (v 1))
    by_cases h : v 0 = v 1
    · exact .of_forall fun n ↦ by simp [h]
    have hp : ((v 1 : 𝔻) : ℚ[X]) - ((v 0 : 𝔻) : ℚ[X]) ≠ 0 := by
      rw [sub_ne_zero]
      intro e
      exact h (Subtype.ext (Subtype.ext e.symm))
    filter_upwards [eventually_evalTwoPow (v 0), eventually_evalTwoPow (v 1),
      eventually_eval_two_pow_ne_zero hp] with n h₀ h₁ hne
    simp only [h, false_iff]
    intro e
    apply hne
    rw [eval_sub, ← h₀, ← h₁, e, sub_self]
  · change ∀ᶠ n in atTop, (v 0 < v 1 ↔ evalTwoPow n (v 0) < evalTwoPow n (v 1))
    filter_upwards [eventually_evalTwoPow (v 0), eventually_evalTwoPow (v 1),
      (((v 1 : 𝔻) : ℚ[X]) - ((v 0 : 𝔻) : ℚ[X])).eventually_pos_eval_two_pow_iff] with n h₀ h₁ hpos
    rw [← Subtype.coe_lt_coe, ← sub_pos, LeadingCoeffOrder.pos_iff, AddSubgroupClass.coe_sub,
      ← hpos, eval_sub, ← h₀, ← h₁, sub_pos, Nat.cast_lt]

/-- Every universal sentence true in `ℕ` is true in the non-negative part of
`IntegerConstantDyadicPolynomial`.
- [Kat26a, Theorem 10] -/
lemma models_univCl_of_open {φ : ArithmeticSemiformula ℕ 0} (hφ : φ.Open)
    (h : ℕ↓[ℒₒᵣ] ⊧ φ.univCl) : (Nonneg 𝔻)↓[ℒₒᵣ] ⊧ φ.univCl :=
  FirstOrder.models_univCl_of_open eventually_evalTwoPow_func eventually_evalTwoPow_rel hφ h

/-- The non-negative part of `IntegerConstantDyadicPolynomial` is a model of
$\mathsf{PA}^-_{\mathrm{smu}}$.
- [Kat26a, Theorem 10] -/
lemma models_PeanoMinusSmu : (Nonneg 𝔻)↓[ℒₒᵣ] ⊧* Arithmetic.PeanoMinusSmu := by
  apply Arithmetic.models_PeanoMinusSmu_iff.mpr
  constructor
  · apply Arithmetic.models_powersExistence_iff.mpr
    intro x
    obtain ⟨u, e, h, hu, h₁, h₂⟩ := exists_le_add_one_lt_two_mul x
    use u
    simp only [Arithmetic.le_def, Nonneg.ofNat_foundation]
    exact ⟨eq_one_or_exists_mul_two_eq hu, le_iff_eq_or_lt.mp h₁, h₂⟩
  · apply Arithmetic.models_powersDivision_iff.mpr
    intro x y hx hy hxy
    simp only [Nonneg.ofNat_foundation] at hx hy
    obtain ⟨a, h, ha⟩ := exists_eq_C_two_zpow_mul_X_pow hx
    obtain ⟨b, k, hb⟩ := exists_eq_C_two_zpow_mul_X_pow hy
    exact exists_mul_eq_of_le ha hb (le_iff_eq_or_lt.mpr (Arithmetic.le_def.mp hxy))

/-- In the non-negative part of `IntegerConstantDyadicPolynomial`, `X` cannot be divided by `3`
with remainder.
- [Kat26a, Theorem 10] -/
lemma not_models_standardEuclideanDivisionBy_three :
    ¬(Nonneg 𝔻)↓[ℒₒᵣ] ⊧ Arithmetic.standardEuclideanDivisionBy 3 := by
  rw [Arithmetic.models_standardEuclideanDivisionBy_iff, Nonneg.natCast_foundation]
  intro h
  obtain ⟨q, r, hr, e⟩ := h ⟨IntegerConstantDyadicPolynomial.X, X_nonneg⟩
  have hr : (r : 𝔻) < 3 := by
    have := Subtype.coe_lt_coe.mpr hr
    rwa [Nonneg.coe_natCast, Nat.cast_ofNat] at this
  have e := congrArg Subtype.val e
  rw [Nonneg.coe_add, Nonneg.coe_mul, Nonneg.coe_natCast, Nat.cast_ofNat] at e
  exact X_ne_three_mul_add q r r.2 hr e

end IntegerConstantDyadicPolynomial
