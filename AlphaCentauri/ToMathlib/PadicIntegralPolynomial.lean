module

public import AlphaCentauri.ToMathlib.LeadingCoeffOrder
public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.NumberTheory.Padics.RingHoms

/-!
# A $\mathbb{Z}$-ring of polynomials with a $p$-adic condition

For a field `K`, a prime `p` and a ring homomorphism `χ : K →+* ℚ_[p]`, the polynomials `f` over `K`
with `f(0) ∈ ℤ[1/p]` and `χ(f(1)) ∈ ℤ_[p]` form a subring `PadicIntegralPolynomial χ` of `K[X]`.
When `K` is an ordered field, it is discretely ordered by the sign of the leading coefficient, and
every element can be divided with remainder by every positive natural number.
-/

@[expose] public noncomputable section

open Polynomial OpenPredicate

variable {K : Type*} [Field K] {p : ℕ} [hp : Fact p.Prime]

/-- The polynomials `f` over `K` such that `pᵏ f(0)` is an integer for some `k` and `χ(f(1))` is a
`p`-adic integer. -/
def PadicIntegralPolynomial (χ : K →+* ℚ_[p]) : Subring K[X] where
  carrier := {f | (∃ k : ℕ, ∃ a : ℤ, (p : K) ^ k * f.eval 0 = a) ∧ ‖χ (f.eval 1)‖ ≤ 1}
  mul_mem' := by
    rintro f g ⟨⟨k, a, hf⟩, hf₁⟩ ⟨⟨l, b, hg⟩, hg₁⟩
    and_intros
    · use k + l, a * b
      rw [eval_mul, pow_add, Int.cast_mul, ← hf, ← hg]
      ring
    · rw [eval_mul, map_mul, norm_mul]
      simpa using mul_le_mul hf₁ hg₁ (norm_nonneg _) zero_le_one
  one_mem' := ⟨⟨0, 1, by simp⟩, by simp⟩
  add_mem' := by
    rintro f g ⟨⟨k, a, hf⟩, hf₁⟩ ⟨⟨l, b, hg⟩, hg₁⟩
    and_intros
    · use k + l, a * p ^ l + b * p ^ k
      rw [eval_add, pow_add]
      push_cast
      rw [← hf, ← hg]
      ring
    · rw [eval_add, map_add]
      exact (Padic.nonarchimedean _ _).trans (max_le hf₁ hg₁)
  zero_mem' := ⟨⟨0, 0, by simp⟩, by simp⟩
  neg_mem' := by
    rintro f ⟨⟨k, a, hf⟩, hf₁⟩
    and_intros
    · use k, -a
      rw [eval_neg, Int.cast_neg, ← hf, mul_neg]
    · simpa using hf₁

namespace PadicIntegralPolynomial

variable {χ : K →+* ℚ_[p]}

lemma mem_iff {f : K[X]} : f ∈ PadicIntegralPolynomial χ ↔
    (∃ k : ℕ, ∃ a : ℤ, (p : K) ^ k * f.eval 0 = a) ∧ ‖χ (f.eval 1)‖ ≤ 1 := Iff.rfl

variable [LinearOrder K] [IsStrictOrderedRing K]

open scoped LeadingCoeffOrder

instance : LinearOrder (PadicIntegralPolynomial χ) := inferInstance

instance : IsStrictOrderedRing (PadicIntegralPolynomial χ) := inferInstance

instance : DiscretelyOrdered (PadicIntegralPolynomial χ) :=
  LeadingCoeffOrder.discretelyOrdered fun f hf hd ↦ by
    obtain ⟨⟨k, a, ha⟩, h₁⟩ := mem_iff.mp hf
    rw [eq_C_of_natDegree_eq_zero hd] at ha h₁ ⊢
    rw [eval_C] at ha h₁
    have hχ : (p : ℚ_[p]) ^ k * χ (f.coeff 0) = a := by simpa using congrArg χ ha
    have : ‖(a : ℚ_[p])‖ ≤ (p : ℝ) ^ (-k : ℤ) := by
      rw [← hχ, norm_mul, norm_pow, Padic.norm_p, zpow_neg, zpow_natCast, inv_pow]
      exact mul_le_of_le_one_right (by positivity) h₁
    obtain ⟨b, rfl⟩ := (Padic.norm_int_le_pow_iff_dvd a k).mp this
    use b
    have hpk : (p : K) ^ k ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero)
    rw [← C_eq_intCast]
    congr 1
    apply mul_left_cancel₀ hpk
    rw [ha]
    push_cast
    rfl

lemma exists_eq_mul_add_of_pos (f : PadicIntegralPolynomial χ) {n : ℕ} (hn : 0 < n) :
    ∃ q r : PadicIntegralPolynomial χ, 0 ≤ r ∧ r < n ∧ f = n * q + r := by
  suffices ∀ n : ℕ, 0 < n → ∀ f : PadicIntegralPolynomial χ, ∃ q, ∃ r : ℕ, r < n ∧ f = n * q + r by
    obtain ⟨q, r, hr, e⟩ := this n hn f
    use q, r
    exact ⟨Nat.cast_nonneg r, by exact_mod_cast hr, e⟩
  intro n
  induction n using Nat.recOnMul with
  | zero => intro h; omega
  | one => intro _ f; use f, 0; simp
  | prime l hl =>
    intro _ f
    obtain ⟨⟨k, a, ha⟩, h₁⟩ := mem_iff.mp f.2
    have hl₀ : (l : K) ≠ 0 := by
      intro h
      have := congrArg χ h
      rw [map_natCast, map_zero, Nat.cast_eq_zero] at this
      exact hl.ne_zero this
    suffices ∃ r < l, (∃ k : ℕ, ∃ a : ℤ, (p : K) ^ k * ((f.1.eval 0 - r) / l) = a) ∧
        ‖χ ((f.1.eval 1 - r) / l)‖ ≤ 1 by
      obtain ⟨r, hr, hq⟩ := this
      use ⟨C (l : K)⁻¹ * (f - r), by simpa [mem_iff, div_eq_inv_mul] using hq⟩, r
      and_intros
      · exact hr
      · apply Subtype.ext
        push_cast
        rw [← C_eq_natCast, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hl₀, C_1, one_mul,
          sub_add_cancel]
    let u : ℤ_[p] := ⟨χ (f.1.eval 1), h₁⟩
    by_cases hlp : l = p
    · subst hlp
      obtain ⟨t, ht⟩ := (PadicInt.norm_lt_one_iff_dvd _).mp <|
        PadicInt.mem_nonunits.mp (PadicInt.sub_zmodRepr_mem u)
      use PadicInt.zmodRepr u
      and_intros
      · exact PadicInt.zmodRepr_lt_p u
      · use k + 1, a - l ^ k * PadicInt.zmodRepr u
        push_cast
        rw [← ha]
        field_simp
        ring
      · have : χ ((f.1.eval 1 - PadicInt.zmodRepr u) / l) = t := by
          rw [map_div₀, map_sub, map_natCast, map_natCast]
          have := congrArg ((↑) : ℤ_[l] → ℚ_[l]) ht
          push_cast at this
          rw [this]
          exact mul_div_cancel_left₀ _ (by exact_mod_cast hl.ne_zero)
        rw [this]
        exact t.2
    · have hpl : (p : ZMod l) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        exact fun h ↦ hlp ((Nat.prime_dvd_prime_iff_eq hl hp.out).mp h)
      have : NeZero l := ⟨hl.ne_zero⟩
      let r := ((a : ZMod l) * ((p : ZMod l) ^ k)⁻¹).val
      obtain ⟨b, hb⟩ : (l : ℤ) ∣ a - p ^ k * r := by
        have := Fact.mk hl
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [ZMod.natCast_val, ZMod.cast_id', id, mul_left_comm,
          mul_inv_cancel₀ (pow_ne_zero _ hpl), mul_one, sub_self]
      use r
      and_intros
      · exact ZMod.val_lt _
      · use k, b
        have : ((a - p ^ k * r : ℤ) : K) = l * b := by rw [hb]; push_cast; ring
        push_cast at this
        rw [mul_div_assoc', mul_sub, ha, this]
        field_simp
      · have hl₁ : ‖(l : ℚ_[p])‖ = 1 :=
          Padic.norm_natCast_eq_one_iff.mpr ((Nat.coprime_primes hp.out hl).mpr (Ne.symm hlp))
        rw [map_div₀, norm_div, map_natCast, hl₁, div_one, map_sub, map_natCast, sub_eq_add_neg]
        exact (Padic.nonarchimedean _ _).trans <| max_le h₁ <| by
          rw [norm_neg]
          exact PadicInt.norm_le_one (r : ℤ_[p])
  | mul a b iha ihb =>
    intro hab f
    obtain ⟨q, r, hr, rfl⟩ := iha (Nat.pos_of_mul_pos_right hab) f
    obtain ⟨q', r', hr', rfl⟩ := ihb (Nat.pos_of_mul_pos_left hab) q
    use q', a * r' + r
    and_intros
    · nlinarith
    · push_cast
      ring

end PadicIntegralPolynomial
