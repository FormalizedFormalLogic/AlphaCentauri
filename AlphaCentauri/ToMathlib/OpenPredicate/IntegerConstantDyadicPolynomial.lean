module

public import AlphaCentauri.ToMathlib.OpenPredicate.AddMonoidHomToInt
public import AlphaCentauri.ToMathlib.OpenPredicate.IntegerConstantPolynomial
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Data.Int.Log
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# The $\mathbb{Z}$-ring of dyadic polynomials with integer constant term

`DyadicRational` is the ring $\mathbb{Z}[1/2]$ of dyadic rationals, and
`IntegerConstantDyadicPolynomial` is the ring $\mathbb{Z} + X \mathbb{Z}[1/2][X]$ of polynomials
over the dyadic rationals with integer constant term, ordered by the sign of the leading
coefficient. Along the powers of two, each of its elements eventually takes integer values, of the
sign of its leading coefficient.

In its non-negative part, the elements all of whose divisors are `1` or even are exactly the
monomials $2^e X^h$; each `x` lies between such a monomial `u` and `2 * u` in the sense
`u ≤ x + 1 < 2 * u`, any two of them comparable are divisible one by the other, and `X` cannot be
divided by `3` with remainder.
-/

@[expose] public noncomputable section

open Polynomial Filter

/-- The dyadic rationals $\mathbb{Z}[1/2]$. -/
def DyadicRational : Subring ℚ where
  carrier := {c | ∃ k : ℕ, ∃ m : ℤ, 2 ^ k * c = m}
  mul_mem' := by
    rintro a b ⟨k, m, hm⟩ ⟨k', m', hm'⟩
    use k + k', m * m'
    push_cast [← hm, ← hm']
    ring
  one_mem' := ⟨0, 1, by simp⟩
  add_mem' := by
    rintro a b ⟨k, m, hm⟩ ⟨k', m', hm'⟩
    use k + k', 2 ^ k' * m + 2 ^ k * m'
    push_cast [← hm, ← hm']
    ring
  zero_mem' := ⟨0, 0, by simp⟩
  neg_mem' := by
    rintro a ⟨k, m, hm⟩
    use k, -m
    simp [← hm]

namespace DyadicRational

lemma mem_iff {c : ℚ} : c ∈ DyadicRational ↔ ∃ k : ℕ, ∃ m : ℤ, 2 ^ k * c = m := Iff.rfl

lemma two_zpow_mem (e : ℤ) : (2 : ℚ) ^ e ∈ DyadicRational := by
  rcases e.eq_nat_or_neg with ⟨n, rfl | rfl⟩
  · use 0, 2 ^ n
    simp
  · use n, 1
    simp

lemma exists_eq_two_zpow_mul_odd {c : ℚ} (hc : c ∈ DyadicRational) (h₀ : c ≠ 0) :
    ∃ e m : ℤ, Odd m ∧ c = 2 ^ e * m := by
  obtain ⟨k, m, hm⟩ := hc
  obtain ⟨j, n, hn, hjn⟩ := Nat.exists_eq_two_pow_mul_odd <| m.natAbs_ne_zero.mpr <| by
    rintro rfl
    simp_all
  obtain rfl : c = m / 2 ^ k := by
    rw [← hm]
    field_simp
  rcases m.natAbs_eq with h | h
  · use j - k, n
    and_intros
    · exact_mod_cast hn
    · rw [h, hjn, zpow_sub₀ two_ne_zero, zpow_natCast, zpow_natCast]
      push_cast
      ring
  · use j - k, -n
    and_intros
    · exact (Int.odd_coe_nat n |>.mpr hn).neg
    · rw [h, hjn, zpow_sub₀ two_ne_zero, zpow_natCast, zpow_natCast]
      push_cast
      ring

/-- A positive integer `c` such that `2 ^ e / c` is dyadic is `1` or even. -/
lemma eq_one_or_two_dvd {c : ℤ} (hc : 0 < c) {e : ℤ} (h : (2 : ℚ) ^ e / c ∈ DyadicRational) :
    c = 1 ∨ 2 ∣ c := by
  obtain ⟨k, m, hm⟩ := h
  have hkm : (2 : ℚ) ^ ((k : ℤ) + e) = m * c := by
    rw [zpow_add₀ two_ne_zero, zpow_natCast, ← hm]
    field_simp
  obtain ⟨n, hdvd⟩ : ∃ n : ℕ, c ∣ 2 ^ n := by
    rcases ((k : ℤ) + e).eq_nat_or_neg with ⟨n, hn | hn⟩
    · rw [hn, zpow_natCast] at hkm
      exact ⟨n, Dvd.intro_left m (by exact_mod_cast hkm.symm)⟩
    · rw [hn, zpow_neg, zpow_natCast] at hkm
      field_simp at hkm
      exact ⟨0, Dvd.intro_left (2 ^ n * m) (by exact_mod_cast hkm.symm)⟩
  have : c.natAbs ∣ 2 ^ n := by simpa [Int.natAbs_pow] using Int.natAbs_dvd_natAbs.mpr hdvd
  obtain ⟨_ | i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp this
  · left
    omega
  · exact Or.inr <| Int.ofNat_dvd_left.mpr <| hi ▸ dvd_pow_self 2 i.succ_ne_zero

end DyadicRational

/-- Along the powers of two, the values of a rational polynomial eventually have the sign of its
leading coefficient. -/
lemma Polynomial.eventually_pos_eval_two_pow_iff (p : ℚ[X]) :
    ∀ᶠ n : ℕ in atTop, (0 < p.eval (2 ^ n) ↔ 0 < p.leadingCoeff) := by
  have h₂ : Tendsto (fun n : ℕ ↦ (2 : ℚ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt one_lt_two
  rcases le_or_gt p.degree 0 with hd | hd
  · rw [eq_C_of_degree_le_zero hd]
    simp
  rcases lt_or_ge 0 p.leadingCoeff with hl | hl
  · filter_upwards [((p.tendsto_atTop_of_leadingCoeff_nonneg hd hl.le).comp h₂).eventually_gt_atTop
      0] with n hn
    simpa [hl] using hn
  · filter_upwards [((p.tendsto_atBot_of_leadingCoeff_nonpos hd hl).comp h₂).eventually_lt_atBot
      0] with n hn
    simp only [Function.comp_apply] at hn
    simp [hn.le, hl.not_gt, not_lt.mpr]

/-- The polynomials over the dyadic rationals whose constant term is an integer. -/
def IntegerConstantDyadicPolynomial : Subring ℚ[X] :=
  IntegerConstantPolynomial ℚ ⊓ liftsRing DyadicRational.subtype

namespace IntegerConstantDyadicPolynomial

local notation "𝔻" => IntegerConstantDyadicPolynomial

lemma mem_iff {p : ℚ[X]} :
    p ∈ 𝔻 ↔ (∃ n : ℤ, p.coeff 0 = n) ∧ ∀ i, p.coeff i ∈ DyadicRational := by
  simp [IntegerConstantDyadicPolynomial, Subring.mem_inf, IntegerConstantPolynomial.mem_iff,
    ← lifts_iff_liftsRing, lifts_iff_coeff_lifts]

lemma C_mul_X_pow_mem {c : ℚ} (hc : c ∈ DyadicRational) {h : ℕ} (hh : 0 < h) :
    C c * X ^ h ∈ 𝔻 := by
  rw [mem_iff]
  and_intros
  · use 0
    simp [hh.ne]
  · intro i
    rw [coeff_C_mul_X_pow]
    split_ifs
    exacts [hc, zero_mem _]

lemma C_two_zpow_mul_X_pow_mem {e : ℤ} {h : ℕ} (he : 0 < h ∨ 0 ≤ e) :
    C (2 ^ e) * X ^ h ∈ 𝔻 := by
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (he.resolve_left (lt_irrefl 0))
    simpa [map_ofNat C 2] using intCast_mem 𝔻 (2 ^ n)
  · exact C_mul_X_pow_mem (DyadicRational.two_zpow_mem e) hh

open scoped LeadingCoeffOrder

instance : LinearOrder 𝔻 := inferInstance

instance : IsStrictOrderedRing 𝔻 := inferInstance

instance : OpenPredicate.DiscretelyOrdered 𝔻 :=
  LeadingCoeffOrder.discretelyOrdered fun p hp hd ↦ by
    obtain ⟨n, hn⟩ := (mem_iff.mp hp).1
    use n
    rw [eq_C_of_natDegree_eq_zero hd, hn, C_eq_intCast]

variable {p q : 𝔻}

/-- Along the powers of two, each element eventually takes integer values. -/
lemma eventually_eval_two_pow_mem_range (p : 𝔻) :
    ∀ᶠ n : ℕ in atTop, (p : ℚ[X]).eval (2 ^ n) ∈ (Int.castRingHom ℚ).range := by
  obtain ⟨⟨m₀, h₀⟩, hc⟩ := mem_iff.mp p.2
  have : ∀ i ∈ (p : ℚ[X]).support, ∀ᶠ n : ℕ in atTop,
      (p : ℚ[X]).coeff i * (2 ^ n) ^ i ∈ (Int.castRingHom ℚ).range := by
    intro i _
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · exact .of_forall fun n ↦ ⟨m₀, by simp [h₀]⟩
    obtain ⟨k, m, hm⟩ := hc i
    filter_upwards [eventually_ge_atTop k] with n hn
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le (hn.trans (Nat.le_mul_of_pos_right n hi))
    use m * 2 ^ t
    push_cast [eq_intCast, ← pow_mul, ht, pow_add, ← hm]
    ring
  filter_upwards [(eventually_all_finset _).mpr this] with n hn
  rw [eval_eq_sum, Polynomial.sum_def]
  exact Subring.sum_mem _ hn

/-- Along the powers of two, each non-negative element eventually takes natural number values. -/
lemma eventually_eval_two_pow_eq_natCast (hp : 0 ≤ p) :
    ∀ᶠ n : ℕ in atTop, ∃ m : ℕ, (p : ℚ[X]).eval (2 ^ n) = m := by
  filter_upwards [eventually_eval_two_pow_mem_range p,
    (p : ℚ[X]).eventually_pos_eval_two_pow_iff] with n ⟨m, hm⟩ hpos
  rw [eq_intCast] at hm
  have : 0 ≤ m := by
    rcases (LeadingCoeffOrder.nonneg_iff.mp hp).lt_or_eq with hl | hl
    · exact_mod_cast (hm ▸ hpos.mpr hl).le
    · rw [leadingCoeff_eq_zero.mp hl.symm, eval_zero] at hm
      exact_mod_cast hm.ge
  lift m to ℕ using this
  use m
  exact_mod_cast hm.symm

section Nonneg

variable {x y : Nonneg 𝔻}

@[simp] lemma coe_ofNat (n : ℕ) [n.AtLeastTwo] :
    ((((no_index (OfNat.ofNat n)) : Nonneg 𝔻) : 𝔻) : ℚ[X]) = OfNat.ofNat n := by
  change (((n : Nonneg 𝔻) : 𝔻) : ℚ[X]) = (n : ℚ[X])
  simp

lemma coeff_zero_ne_of_mul_two_eq {w : Nonneg 𝔻} (h : w * 2 = y) {m : ℤ} (hm : Odd m) :
    ((y : 𝔻) : ℚ[X]).coeff 0 ≠ m := by
  obtain ⟨n, hn⟩ := (mem_iff.mp (w : 𝔻).2).1
  rw [← h]
  intro hc
  have : n * 2 = m := by exact_mod_cast (by simpa [hn] using hc : (n : ℚ) * 2 = m)
  exact Int.not_even_iff_odd.mpr hm ⟨n, by omega⟩

/-- An element of the non-negative part all of whose divisors are `1` or even is a monomial
$2^e X^h$. -/
lemma exists_eq_C_two_zpow_mul_X_pow
    (hx : ∀ y : Nonneg 𝔻, (∃ z, z * y = x) → y = 1 ∨ ∃ w, w * 2 = y) :
    ∃ (e : ℤ) (h : ℕ), ((x : 𝔻) : ℚ[X]) = C (2 ^ e) * X ^ h := by
  by_cases hp : ((x : 𝔻) : ℚ[X]) = 0
  · exfalso
    rcases hx 3 ⟨0, (zero_mul _).trans (Subtype.ext <| Subtype.ext hp).symm⟩ with h | ⟨w, hw⟩
    · norm_num at h
    · exact coeff_zero_ne_of_mul_two_eq hw (m := 3) (by decide) (by simp)
  obtain ⟨q, hq, hqX⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd _ hp 0
  simp only [map_zero, sub_zero, X_dvd_iff] at hq hqX
  set r := rootMultiplicity 0 ((x : 𝔻) : ℚ[X])
  have hqc (i : ℕ) : q.coeff i ∈ DyadicRational := by
    have := (mem_iff.mp (x : 𝔻).2).2 (i + r)
    rwa [hq, mul_comm, coeff_mul_X_pow] at this
  obtain ⟨e, m, hm, hqm⟩ := DyadicRational.exists_eq_two_zpow_mul_odd (hqc 0) hqX
  have hC : C ((2 : ℚ) ^ e) * C (2 ^ (-e)) = 1 := by
    rw [← C_mul, zpow_neg, mul_inv_cancel₀ (by positivity), C_1]
  have h₀ : (C (2 ^ (-e)) * q).coeff 0 = (m : ℚ) := by
    rw [coeff_C_mul, hqm, zpow_neg, inv_mul_cancel_left₀ (by positivity)]
  have ho : C (2 ^ (-e)) * q ∈ 𝔻 := by
    rw [mem_iff]
    and_intros
    · use m
    · intro i
      rw [coeff_C_mul]
      exact mul_mem (DyadicRational.two_zpow_mem _) (hqc i)
  have he : 0 < r ∨ 0 ≤ e := by
    rcases Nat.eq_zero_or_pos r with hr | hr
    · right
      by_contra he
      obtain ⟨n, hn⟩ := (mem_iff.mp (x : 𝔻).2).1
      obtain ⟨k, rfl⟩ : ∃ k : ℕ, e = -((k + 1 : ℕ) : ℤ) := ⟨(-e - 1).toNat, by omega⟩
      rw [hq, hr, pow_zero, one_mul] at hn
      rw [coeff_C_mul, hn, neg_neg, zpow_natCast] at h₀
      have : m = 2 ^ (k + 1) * n := by exact_mod_cast h₀.symm
      exact Int.not_even_iff_odd.mpr hm ⟨2 ^ k * n, by linear_combination this⟩
    · exact Or.inl hr
  let o : Nonneg 𝔻 := ⟨⟨_, ho⟩, LeadingCoeffOrder.nonneg_iff.mpr <| by
    simpa [hq, leadingCoeff_mul, mul_nonneg_iff_of_pos_left, zpow_pos] using
      LeadingCoeffOrder.nonneg_iff.mp x.2⟩
  let z : Nonneg 𝔻 := ⟨⟨_, C_two_zpow_mul_X_pow_mem he⟩,
    LeadingCoeffOrder.nonneg_iff.mpr (by rw [leadingCoeff_C_mul_X_pow]; positivity)⟩
  have hzo : z * o = x := by
    apply Subtype.ext
    apply Subtype.ext
    simp only [z, o, Nonneg.coe_mul, Subring.coe_mul, hq]
    linear_combination (X ^ r * q) * hC
  rcases hx o ⟨z, hzo⟩ with h | ⟨w, hw⟩
  · use e, r
    have h : C (2 ^ (-e)) * q = 1 := congrArg (fun y : Nonneg 𝔻 ↦ ((y : 𝔻) : ℚ[X])) h
    rw [hq]
    linear_combination (C (2 ^ e) * X ^ r) * h - (X ^ r * q) * hC
  · exact (coeff_zero_ne_of_mul_two_eq hw hm h₀).elim

/-- The divisors of a monomial $2^e X^h$ in the non-negative part are `1` or even. -/
lemma eq_one_or_exists_mul_two_eq {e : ℤ} {h : ℕ} (hx : ((x : 𝔻) : ℚ[X]) = C (2 ^ e) * X ^ h)
    (y : Nonneg 𝔻) (hy : ∃ z, z * y = x) : y = 1 ∨ ∃ w, w * 2 = y := by
  obtain ⟨z, hzy⟩ := hy
  have hzy : ((z : 𝔻) : ℚ[X]) * ((y : 𝔻) : ℚ[X]) = C (2 ^ e) * X ^ h := by
    rw [← hx, ← hzy]
    rfl
  have hdvd : ((y : 𝔻) : ℚ[X]) ∣ X ^ h := by
    rw [← (isUnit_C.mpr (IsUnit.mk0 _ (zpow_ne_zero e two_ne_zero))).dvd_mul_left, ← hzy]
    exact dvd_mul_left _ _
  obtain ⟨i, -, hu⟩ := (dvd_prime_pow prime_X h).mp hdvd
  obtain ⟨u, hu⟩ := hu.symm
  obtain ⟨c, hc, hcu⟩ := Polynomial.isUnit_iff.mp u.isUnit
  have hy : ((y : 𝔻) : ℚ[X]) = C c * X ^ i := by rw [← hu, ← hcu, mul_comm]
  have hc₀ : 0 < c := lt_of_le_of_ne (by simpa [hy] using LeadingCoeffOrder.nonneg_iff.mp y.2)
    hc.ne_zero.symm
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · obtain ⟨n, rfl⟩ : ∃ n : ℤ, c = n := by simpa [hy] using (mem_iff.mp (y : 𝔻).2).1
    have hn₀ : 0 < n := by exact_mod_cast hc₀
    have hz : ((z : 𝔻) : ℚ[X]).coeff h * n = 2 ^ e := by
      simpa [hy] using congrArg (coeff · h) hzy
    rcases DyadicRational.eq_one_or_two_dvd hn₀ <|
      eq_div_of_mul_eq (by positivity) hz ▸ (mem_iff.mp (z : 𝔻).2).2 h with rfl | ⟨k, rfl⟩
    · exact Or.inl <| Subtype.ext <| Subtype.ext <| by simp [hy]
    · right
      use ⟨k, Int.cast_nonneg_iff.mpr (by omega)⟩
      apply Subtype.ext
      apply Subtype.ext
      simp [hy, mul_comm, map_ofNat C 2]
  · right
    have hcD : c / 2 ∈ DyadicRational := by
      simpa [hy, div_eq_mul_inv] using
        mul_mem ((mem_iff.mp (y : 𝔻).2).2 i) (DyadicRational.two_zpow_mem (-1))
    use ⟨⟨_, C_mul_X_pow_mem hcD hi⟩,
      LeadingCoeffOrder.nonneg_iff.mpr (by rw [leadingCoeff_C_mul_X_pow]; positivity)⟩
    apply Subtype.ext
    apply Subtype.ext
    simp only [Nonneg.coe_mul, Subring.coe_mul, coe_ofNat, hy]
    rw [mul_right_comm, ← map_ofNat C 2, ← C_mul, div_mul_cancel₀ c two_ne_zero]

/-- Every element `x` of the non-negative part has a monomial $u = 2^e X^h$ with
`u ≤ x + 1 < 2 * u`. -/
lemma exists_le_add_one_lt_two_mul (x : Nonneg 𝔻) :
    ∃ (u : Nonneg 𝔻) (e : ℤ) (h : ℕ),
      ((u : 𝔻) : ℚ[X]) = C (2 ^ e) * X ^ h ∧ u ≤ x + 1 ∧ x + 1 < 2 * u := by
  set A : ℚ[X] := (((x + 1 : Nonneg 𝔻) : 𝔻) : ℚ[X]) with hA
  have hA₁ : (1 : 𝔻) ≤ ((x + 1 : Nonneg 𝔻) : 𝔻) := by simpa using x.2
  rcases Nat.eq_zero_or_pos A.natDegree with hd | hd
  · obtain ⟨n, hn⟩ := (mem_iff.mp ((x + 1 : Nonneg 𝔻) : 𝔻).2).1
    have hxn : ((x + 1 : Nonneg 𝔻) : 𝔻) = (n : 𝔻) := by
      apply Subtype.ext
      rw [Subring.coe_intCast, ← C_eq_intCast, ← hn, ← hA, ← eq_C_of_natDegree_eq_zero hd]
    have hn₁ : 1 ≤ n := by exact_mod_cast hxn ▸ hA₁
    lift n to ℕ using by omega
    use (2 ^ Nat.log 2 n : ℕ), Nat.log 2 n, 0
    refine ⟨by simp [map_ofNat C 2], ?_, ?_⟩
    · rw [← Subtype.coe_le_coe, Nonneg.coe_natCast, hxn]
      exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    · rw [← Subtype.coe_lt_coe, hxn]
      norm_cast
      exact_mod_cast (pow_succ' 2 _) ▸ Nat.lt_pow_succ_log_self one_lt_two n
  set b := A.leadingCoeff
  have hb : 0 < b := LeadingCoeffOrder.pos_iff.mp (zero_lt_one.trans_le hA₁)
  set a := Int.log 2 b
  have hmem (t : ℤ) : C (2 ^ t) * X ^ A.natDegree ∈ 𝔻 := C_two_zpow_mul_X_pow_mem (Or.inl hd)
  let m (t : ℤ) : Nonneg 𝔻 := ⟨⟨_, hmem t⟩, LeadingCoeffOrder.nonneg_iff.mpr (by
    rw [leadingCoeff_C_mul_X_pow]
    positivity)⟩
  have hsub {c : ℚ} (hc : c ≠ b) : (C c * X ^ A.natDegree - A).leadingCoeff = c - b := by
    by_cases hc₀ : c = 0
    · simp [hc₀, b]
    rw [leadingCoeff_sub_of_degree_eq, leadingCoeff_C_mul_X_pow]
    · rw [degree_C_mul_X_pow _ hc₀, degree_eq_natDegree]
      intro h₀
      simp [h₀] at hd
    · rwa [leadingCoeff_C_mul_X_pow]
  have hlt : x + 1 < m (a + 1) := by
    change ((x + 1 : Nonneg 𝔻) : 𝔻) < ⟨_, hmem (a + 1)⟩
    rw [← sub_pos, LeadingCoeffOrder.pos_iff, AddSubgroupClass.coe_sub]
    have : b < 2 ^ (a + 1) := by exact_mod_cast Int.lt_zpow_succ_log_self one_lt_two b
    rwa [hsub this.ne', sub_pos]
  have htwo (t : ℤ) : 2 * m t = m (t + 1) := by
    apply Subtype.ext
    apply Subtype.ext
    simp only [m, Nonneg.coe_mul, Subring.coe_mul, coe_ofNat, zpow_add_one₀ (two_ne_zero' ℚ),
      C_mul, map_ofNat]
    ring
  by_cases hle : m a ≤ x + 1
  · use m a, a, A.natDegree
    refine ⟨rfl, hle, ?_⟩
    rwa [htwo]
  · use m (a - 1), a - 1, A.natDegree
    refine ⟨rfl, ?_, ?_⟩
    · change (⟨_, hmem (a - 1)⟩ : 𝔻) ≤ ((x + 1 : Nonneg 𝔻) : 𝔻)
      rw [LeadingCoeffOrder.le_iff]
      have h₁ : (2 : ℚ) ^ a ≤ b := by exact_mod_cast Int.zpow_log_le_self one_lt_two hb
      have h₂ : (2 : ℚ) ^ (a - 1) < 2 ^ a := zpow_lt_zpow_right₀ one_lt_two (by omega)
      have := hsub (h₂.trans_le h₁).ne
      rw [← neg_sub, leadingCoeff_neg] at this
      change 0 ≤ (A - C (2 ^ (a - 1)) * X ^ A.natDegree).leadingCoeff
      linarith
    · rw [htwo, sub_add_cancel]
      exact not_le.mp hle

/-- Of two comparable monomials $2^a X^h \le 2^b X^k$ in the non-negative part, the first
divides the second. -/
lemma exists_mul_eq_of_le {a b : ℤ} {h k : ℕ} (hx : ((x : 𝔻) : ℚ[X]) = C (2 ^ a) * X ^ h)
    (hy : ((y : 𝔻) : ℚ[X]) = C (2 ^ b) * X ^ k) (hxy : x ≤ y) : ∃ z, z * x = y := by
  have hxy : 0 ≤ (C ((2 : ℚ) ^ b) * X ^ k - C (2 ^ a) * X ^ h).leadingCoeff := by
    rw [← hx, ← hy]
    exact LeadingCoeffOrder.le_iff.mp hxy
  have hhk : h ≤ k := by
    by_contra hkh
    rw [leadingCoeff_sub_of_degree_lt', leadingCoeff_C_mul_X_pow] at hxy
    · have : (0 : ℚ) < 2 ^ a := by positivity
      linarith
    · rw [degree_C_mul_X_pow _ (by positivity), degree_C_mul_X_pow _ (by positivity)]
      exact_mod_cast not_le.mp hkh
  have hz : 0 < k - h ∨ 0 ≤ b - a := by
    rcases hhk.lt_or_eq with hhk | rfl
    · exact Or.inl (by omega)
    · right
      rw [← sub_mul, ← C_sub, leadingCoeff_C_mul_X_pow, sub_nonneg] at hxy
      have := (zpow_le_zpow_iff_right₀ one_lt_two).mp hxy
      omega
  use ⟨⟨_, C_two_zpow_mul_X_pow_mem hz⟩, LeadingCoeffOrder.nonneg_iff.mpr (by
    rw [leadingCoeff_C_mul_X_pow]
    positivity)⟩
  apply Subtype.ext
  apply Subtype.ext
  simp only [Nonneg.coe_mul, Subring.coe_mul, hx, hy]
  rw [mul_mul_mul_comm, ← C_mul, ← zpow_add₀ two_ne_zero, sub_add_cancel, ← pow_add,
    Nat.sub_add_cancel hhk]

end Nonneg

/-- The indeterminate `X`. -/
def X : 𝔻 := ⟨Polynomial.X, by simpa using C_mul_X_pow_mem (one_mem DyadicRational) one_pos⟩

lemma X_nonneg : 0 ≤ IntegerConstantDyadicPolynomial.X := by
  rw [LeadingCoeffOrder.nonneg_iff]
  exact leadingCoeff_X (R := ℚ) ▸ zero_le_one

/-- `X` cannot be divided by `3` with remainder. -/
lemma X_ne_three_mul_add (a r : 𝔻) (hr₀ : 0 ≤ r) (hr : r < 3) :
    IntegerConstantDyadicPolynomial.X ≠ 3 * a + r := by
  obtain ⟨n, -, rfl⟩ :=
    OpenPredicate.DiscretelyOrdered.exists_eq_natCast hr₀ (q := 3) (by simpa using hr)
  intro h
  obtain ⟨k, m, hm⟩ := (mem_iff.mp a.2).2 1
  have h₃ : ((3 : 𝔻) : ℚ[X]) = 3 := map_ofNat (Subring.subtype 𝔻) 3
  have h₁ : 1 = 3 * (a : ℚ[X]).coeff 1 := by
    simpa [IntegerConstantDyadicPolynomial.X, h₃] using congrArg (fun p : 𝔻 ↦ (p : ℚ[X]).coeff 1) h
  have h₂ : (2 : ℚ) ^ k = 3 * m := by linear_combination (2 : ℚ) ^ k * h₁ + 3 * hm
  have := Int.prime_three.dvd_of_dvd_pow ⟨m, (by exact_mod_cast h₂ : (2 : ℤ) ^ k = 3 * m)⟩
  norm_num at this

end IntegerConstantDyadicPolynomial
