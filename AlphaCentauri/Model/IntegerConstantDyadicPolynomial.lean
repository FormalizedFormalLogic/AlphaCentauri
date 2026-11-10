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

/-- Every universal sentence true in `ℕ` is true in the non-negative part of
`IntegerConstantDyadicPolynomial`.
- [Kat26a, Theorem 10] -/
lemma models_univCl_of_open {φ : ArithmeticSemiformula ℕ 0} (hφ : φ.Open)
    (h : ℕ↓[ℒₒᵣ] ⊧ φ.univCl) : (Nonneg 𝔻)↓[ℒₒᵣ] ⊧ φ.univCl := by
  have hev (x : Nonneg 𝔻) :
      ∀ᶠ n in atTop, (evalTwoPow n x : ℚ) = ((x : 𝔻) : ℚ[X]).eval (2 ^ n) := by
    filter_upwards [eventually_eval_two_pow_eq_natCast x.2] with n ⟨m, hm⟩
    simp [evalTwoPow, hm]
  have hlt (x y : Nonneg 𝔻) : ∀ᶠ n in atTop, (x < y ↔ evalTwoPow n x < evalTwoPow n y) := by
    filter_upwards [hev x, hev y,
      (((y : 𝔻) : ℚ[X]) - ((x : 𝔻) : ℚ[X])).eventually_pos_eval_two_pow_iff] with n hx hy hpos
    rw [← Subtype.coe_lt_coe, ← sub_pos, LeadingCoeffOrder.pos_iff, AddSubgroupClass.coe_sub,
      ← hpos, eval_sub, ← hx, ← hy, sub_pos, Nat.cast_lt]
  apply FirstOrder.models_univCl_of_open (l := atTop) (π := evalTwoPow) _ _ hφ h
  · intro k f v
    filter_upwards [hev (Tarski.Structure.func f v),
      eventually_all.mpr fun i ↦ hev (v i)] with n h hv
    apply Nat.cast_injective (R := ℚ)
    cases f <;> simp_all [Tarski.Structure.func]
  · intro k r v
    cases r
    · filter_upwards [hlt (v 0) (v 1), hlt (v 1) (v 0)] with n h₀ h₁
      change v 0 = v 1 ↔ evalTwoPow n (v 0) = evalTwoPow n (v 1)
      simp only [le_antisymm_iff, ← not_lt, h₀, h₁]
    · exact hlt (v 0) (v 1)

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
  rw [← Subtype.coe_lt_coe, Nonneg.coe_natCast, Nat.cast_ofNat] at hr
  rw [← Subtype.coe_inj, Nonneg.coe_add, Nonneg.coe_mul, Nonneg.coe_natCast, Nat.cast_ofNat] at e
  exact X_ne_three_mul_add q r r.2 hr e

end IntegerConstantDyadicPolynomial
