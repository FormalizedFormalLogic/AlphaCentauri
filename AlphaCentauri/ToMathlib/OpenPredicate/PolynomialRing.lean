module

public import AlphaCentauri.ToMathlib.OpenPredicate
public import Mathlib.Algebra.Order.Ring.Cone
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Discretely ordered rings of polynomials

For an ordered field `K`, every subring `S` of `K[X]` is ordered by the sign of the leading
coefficient, so that `X` is greater than every constant. The order is a scoped instance in
`Polynomial.LeadingCoeffOrder`; it is discrete when every constant polynomial in `S` is an integer.

`IntegerConstantPolynomial K` is the subring of the polynomials over `K` whose constant term is an
integer. Ordered by the sign of the leading coefficient, it is a discretely ordered ring in which
`X` is greater than every natural number, and every element can be divided with remainder by every
positive natural number.

For a field `K`, a prime `p` and a ring homomorphism `χ : K →+* ℚ_[p]`, the polynomials `f` over
`K` with `f(0) ∈ ℤ[1/p]` and `χ(f(1)) ∈ ℤ_[p]` form a subring `PadicIntegralPolynomial χ` of
`K[X]`. When `K` is an ordered field, it is discretely ordered by the sign of the leading
coefficient, and every element can be divided with remainder by every positive natural number.
-/

@[expose] public noncomputable section

open Polynomial OpenPredicate

namespace Polynomial

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

lemma leadingCoeff_add_nonneg {p q : K[X]} (hp : 0 ≤ p.leadingCoeff)
    (hq : 0 ≤ q.leadingCoeff) : 0 ≤ (p + q).leadingCoeff := by
  rcases lt_trichotomy p.degree q.degree with h | h | h
  · rwa [leadingCoeff_add_of_degree_lt h]
  · by_cases hpq : p.leadingCoeff + q.leadingCoeff = 0
    · obtain rfl : p = 0 := leadingCoeff_eq_zero.mp (by linarith)
      simpa using hq
    · rw [leadingCoeff_add_of_degree_eq h hpq]
      exact add_nonneg hp hq
  · rwa [leadingCoeff_add_of_degree_lt' h]

/-- The polynomials in `S` with non-negative leading coefficient. -/
def leadingCoeffCone (S : Subring K[X]) : RingCone S where
  carrier := {p | 0 ≤ (p : K[X]).leadingCoeff}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := leadingCoeff_add_nonneg
  mul_mem' hp hq := by simpa [leadingCoeff_mul] using mul_nonneg hp hq
  eq_zero_of_mem_of_neg_mem' {p} hp hnp := by
    have : (p : K[X]).leadingCoeff = 0 := le_antisymm (by simpa using hnp) hp
    exact Subtype.ext (leadingCoeff_eq_zero.mp this)

instance (S : Subring K[X]) : HasMemOrNegMem (leadingCoeffCone S) where
  mem_or_neg_mem p := by
    rcases le_total 0 (p : K[X]).leadingCoeff with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa [leadingCoeffCone] using h)

namespace LeadingCoeffOrder

variable {S : Subring K[X]}

open Classical in
scoped instance : LinearOrder S := LinearOrder.mkOfAddGroupCone (leadingCoeffCone S)

scoped instance : IsStrictOrderedRing S :=
  haveI : IsOrderedRing S := IsOrderedRing.mkOfCone (leadingCoeffCone S)
  inferInstance

variable {p q : S}

lemma le_iff : p ≤ q ↔ 0 ≤ ((q - p : S) : K[X]).leadingCoeff := Iff.rfl

lemma nonneg_iff : 0 ≤ p ↔ 0 ≤ (p : K[X]).leadingCoeff := by simp [le_iff]

lemma pos_iff : 0 < p ↔ 0 < (p : K[X]).leadingCoeff := by
  simp [lt_iff_le_and_ne, nonneg_iff, eq_comm (a := (0 : K)), eq_comm (a := (0 : S))]

/-- `S` is discretely ordered when each of its constant polynomials is an integer. -/
lemma discretelyOrdered (h : ∀ p ∈ S, p.natDegree = 0 → ∃ n : ℤ, p = n) : DiscretelyOrdered S where
  one_le_of_pos p hp := by
    rw [pos_iff] at hp
    rw [← sub_nonneg, nonneg_iff, AddSubgroupClass.coe_sub, OneMemClass.coe_one]
    by_cases hd : (p : K[X]).natDegree = 0
    · obtain ⟨n, hn⟩ := h p p.2 hd
      rw [hn, ← C_eq_intCast, leadingCoeff_C] at hp
      rw [hn, ← C_eq_intCast, ← C_1, ← C_sub, leadingCoeff_C]
      have : (0 : ℤ) < n := by exact_mod_cast hp
      exact_mod_cast sub_nonneg.mpr (by omega : (1 : ℤ) ≤ n)
    · rw [sub_eq_add_neg, leadingCoeff_add_of_degree_lt']
      · exact hp.le
      · simpa using natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hd)

end LeadingCoeffOrder

end Polynomial

/-- The polynomials over `K` whose constant term is an integer.
- [DAq05, §2]
- [Raf10, Introduction] -/
def IntegerConstantPolynomial (K : Type*) [Field K] : Subring K[X] :=
  (Int.castRingHom K).range.comap constantCoeff

namespace IntegerConstantPolynomial

variable {K : Type*} [Field K]

lemma mem_iff {p : K[X]} : p ∈ IntegerConstantPolynomial K ↔ ∃ n : ℤ, p.coeff 0 = n := by
  simp [IntegerConstantPolynomial, eq_comm]

variable (K) in
def X : IntegerConstantPolynomial K := ⟨Polynomial.X, mem_iff.mpr ⟨0, by simp⟩⟩

variable [LinearOrder K] [IsStrictOrderedRing K]

open scoped LeadingCoeffOrder

instance : LinearOrder (IntegerConstantPolynomial K) := inferInstance

instance : IsStrictOrderedRing (IntegerConstantPolynomial K) := inferInstance

instance : DiscretelyOrdered (IntegerConstantPolynomial K) :=
  LeadingCoeffOrder.discretelyOrdered fun p hp hd ↦ by
    obtain ⟨n, hn⟩ := mem_iff.mp hp
    use n
    rw [eq_C_of_natDegree_eq_zero hd, hn, C_eq_intCast]

lemma natCast_lt_X (n : ℕ) : (n : IntegerConstantPolynomial K) < X K := by
  rw [← sub_pos, LeadingCoeffOrder.pos_iff]
  simp [IntegerConstantPolynomial.X, ← C_eq_natCast, -map_natCast]

lemma exists_eq_mul_add_of_pos (a : IntegerConstantPolynomial K) {n : ℕ} (hn : 0 < n) :
    ∃ q r : IntegerConstantPolynomial K, 0 ≤ r ∧ r < n ∧ a = n * q + r := by
  obtain ⟨m, hm⟩ := mem_iff.mp a.2
  have hn' : (n : K) ≠ 0 := by exact_mod_cast hn.ne'
  have hmod : ((m % n : ℤ) : K) + n * ((m / n : ℤ) : K) = m := by
    exact_mod_cast Int.emod_add_mul_ediv m n
  let r : IntegerConstantPolynomial K := ⟨C ((m % n : ℤ) : K), mem_iff.mpr ⟨m % n, by simp⟩⟩
  have hq : (C (n : K)⁻¹ * ((a : K[X]) - r)).coeff 0 = ((m / n : ℤ) : K) := by
    have : (m : K) - ((m % n : ℤ) : K) = n * ((m / n : ℤ) : K) := by linarith
    simp only [coeff_C_mul, coeff_sub, hm, r, coeff_C_zero]
    rw [this, ← mul_assoc, inv_mul_cancel₀ hn', one_mul]
  let q : IntegerConstantPolynomial K := ⟨_, mem_iff.mpr ⟨m / n, hq⟩⟩
  have hr : (r : K[X]) = C ((m % n : ℤ) : K) := rfl
  have hn_coe : ((n : IntegerConstantPolynomial K) : K[X]) = C (n : K) := by simp
  have h₁ : 0 ≤ r := by
    rw [LeadingCoeffOrder.nonneg_iff, hr, leadingCoeff_C]
    exact_mod_cast Int.emod_nonneg m (b := n) (by exact_mod_cast hn.ne')
  have h₂ : r < n := by
    rw [← sub_pos, LeadingCoeffOrder.pos_iff, AddSubgroupClass.coe_sub, hn_coe, hr, ← C_sub,
      leadingCoeff_C]
    exact_mod_cast sub_pos.mpr (Int.emod_lt_of_pos m (by exact_mod_cast hn))
  have h₃ : a = n * q + r := by
    apply Subtype.ext
    rw [AddMemClass.coe_add, MulMemClass.coe_mul, hn_coe, ← mul_assoc, ← C_mul,
      mul_inv_cancel₀ hn']
    simp [hr]
  use q, r

end IntegerConstantPolynomial

section

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
        intro h
        exact hlp ((Nat.prime_dvd_prime_iff_eq hl hp.out).mp h)
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

end
