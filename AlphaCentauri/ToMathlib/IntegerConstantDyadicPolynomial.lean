module

public import AlphaCentauri.ToMathlib.IntegerConstantPolynomial
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Data.Int.Log
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# The $\mathbb{Z}$-ring of dyadic polynomials with integer constant term

`DyadicRational` is the ring $\mathbb{Z}[1/2]$ of dyadic rationals, and
`IntegerConstantDyadicPolynomial` is the ring $\mathbb{Z} + X \mathbb{Z}[1/2][X]$ of polynomials
over the dyadic rationals with integer constant term, ordered by the sign of the leading
coefficient as a subring of `IntegerConstantPolynomial ℚ`. Along the powers of two, each of its
elements eventually takes integer values, of the sign of its leading coefficient.

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
    push_cast
    rw [← hm, ← hm', pow_add]
    ring
  one_mem' := ⟨0, 1, by simp⟩
  add_mem' := by
    rintro a b ⟨k, m, hm⟩ ⟨k', m', hm'⟩
    use k + k', 2 ^ k' * m + 2 ^ k * m'
    push_cast
    rw [← hm, ← hm', pow_add]
    ring
  zero_mem' := ⟨0, 0, by simp⟩
  neg_mem' := by
    rintro a ⟨k, m, hm⟩
    use k, -m
    push_cast
    rw [← hm]
    ring

namespace DyadicRational

lemma mem_iff {c : ℚ} : c ∈ DyadicRational ↔ ∃ k : ℕ, ∃ m : ℤ, 2 ^ k * c = m := Iff.rfl

lemma two_zpow_mem (e : ℤ) : (2 : ℚ) ^ e ∈ DyadicRational := by
  rcases e.eq_nat_or_neg with ⟨n, rfl | rfl⟩
  · exact ⟨0, 2 ^ n, by simp⟩
  · exact ⟨n, 1, by simp⟩

lemma div_two_mem {c : ℚ} (hc : c ∈ DyadicRational) : c / 2 ∈ DyadicRational := by
  obtain ⟨k, m, hm⟩ := hc
  use k + 1, m
  rw [← hm, pow_succ]
  ring

lemma exists_eq_two_zpow_mul_odd {c : ℚ} (hc : c ∈ DyadicRational) (h₀ : c ≠ 0) :
    ∃ e m : ℤ, Odd m ∧ c = 2 ^ e * m := by
  obtain ⟨k, m, hm⟩ := hc
  have hm₀ : m ≠ 0 := by
    rintro rfl
    exact h₀ <| by simpa using hm
  obtain ⟨j, n, hn, hjn⟩ := Nat.exists_eq_two_pow_mul_odd (Int.natAbs_ne_zero.mpr hm₀)
  have hc : c = 2 ^ (-(k : ℤ)) * m := by
    rw [zpow_neg, zpow_natCast, ← hm]
    field_simp
  have hjk : (2 : ℚ) ^ (-(k : ℤ)) * 2 ^ j = 2 ^ ((j : ℤ) - k) := by
    rw [zpow_sub₀ two_ne_zero, zpow_neg, zpow_natCast, zpow_natCast]
    ring
  rcases Int.natAbs_eq m with h | h
  · use j - k, n
    and_intros
    · exact Int.odd_coe_nat n |>.mpr hn
    · rw [hc, h, hjn, ← hjk]
      push_cast
      ring
  · use j - k, -n
    and_intros
    · exact (Int.odd_coe_nat n |>.mpr hn).neg
    · rw [hc, h, hjn, ← hjk]
      push_cast
      ring

lemma not_mem_of_three_mul_eq_one {c : ℚ} (h : 3 * c = 1) : c ∉ DyadicRational := by
  rintro ⟨k, m, hm⟩
  have : (2 : ℤ) ^ k = 3 * m := by
    have : (2 : ℚ) ^ k = 3 * m := by rw [← hm, ← mul_assoc, mul_comm 3, mul_assoc, h, mul_one]
    exact_mod_cast this
  have h₃ : 2 ^ k = 3 * m.natAbs := by
    simpa [Int.natAbs_mul, Int.natAbs_pow] using congrArg Int.natAbs this
  have h₃ : 3 ∣ 2 ^ k := Dvd.intro _ h₃.symm
  have := Nat.prime_three.dvd_of_dvd_pow h₃
  norm_num at this

/-- A positive integer `c` such that `2 ^ e / c` is dyadic is `1` or even. -/
lemma eq_one_or_two_dvd {c : ℤ} (hc : 0 < c) {e : ℤ} (h : (2 : ℚ) ^ e / c ∈ DyadicRational) :
    c = 1 ∨ 2 ∣ c := by
  obtain ⟨k, m, hm⟩ := h
  have hc' : (c : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
  have hkm : (2 : ℚ) ^ ((k : ℤ) + e) = m * c := by
    rw [zpow_add₀ two_ne_zero, zpow_natCast, ← hm]
    field_simp
  obtain ⟨n, hdvd⟩ : ∃ n : ℕ, c ∣ 2 ^ n := by
    rcases ((k : ℤ) + e).eq_nat_or_neg with ⟨n, hn | hn⟩
    · rw [hn, zpow_natCast] at hkm
      exact ⟨n, Dvd.intro_left m (by exact_mod_cast hkm.symm)⟩
    · rw [hn, zpow_neg, zpow_natCast] at hkm
      have : (2 : ℤ) ^ n * m * c = 1 := by
        have : (2 : ℚ) ^ n * m * c = 1 := by
          rw [mul_assoc, ← hkm, mul_inv_cancel₀ (by positivity)]
        exact_mod_cast this
      exact ⟨0, Dvd.intro_left _ (by simpa using this)⟩
  have : c.natAbs ∣ 2 ^ n := by simpa [Int.natAbs_pow] using Int.natAbs_dvd_natAbs.mpr hdvd
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp this
  rcases i with _ | i
  · left
    omega
  · right
    apply Int.natAbs_dvd_natAbs.mp
    rw [hi, pow_succ]
    exact Dvd.intro_left _ rfl

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

lemma Polynomial.eventually_eval_two_pow_ne_zero {p : ℚ[X]} (hp : p ≠ 0) :
    ∀ᶠ n : ℕ in atTop, p.eval (2 ^ n) ≠ 0 := by
  rcases (leadingCoeff_ne_zero.mpr hp).lt_or_gt with hl | hl
  · filter_upwards [(-p).eventually_pos_eval_two_pow_iff] with n hn
    simpa using (hn.mpr (by simpa using hl)).ne'
  · filter_upwards [p.eventually_pos_eval_two_pow_iff] with n hn
    exact (hn.mpr hl).ne'

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
  refine mem_iff.mpr ⟨⟨0, by simp [hh.ne]⟩, fun i ↦ ?_⟩
  rw [coeff_C_mul_X_pow]
  split_ifs
  exacts [hc, zero_mem _]

lemma C_two_zpow_mul_X_pow_mem {e : ℤ} {h : ℕ} (he : 0 < h ∨ 0 ≤ e) :
    C (2 ^ e) * X ^ h ∈ 𝔻 := by
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (he.resolve_left (lt_irrefl 0))
    have := intCast_mem 𝔻 (2 ^ n)
    rwa [← C_eq_intCast, Int.cast_pow, Int.cast_ofNat, ← zpow_natCast, ← mul_one (C _),
      ← pow_zero X] at this
  · exact C_mul_X_pow_mem (DyadicRational.two_zpow_mem e) hh

/-- The inclusion into the ring of rational polynomials with integer constant term. -/
def inclusion : 𝔻 →+* IntegerConstantPolynomial ℚ := Subring.inclusion inf_le_left

instance : LinearOrder 𝔻 := LinearOrder.lift' inclusion (Subring.inclusion_injective _)

instance : IsStrictOrderedRing 𝔻 :=
  Function.Injective.isStrictOrderedRing inclusion (map_zero _) (map_one _) (map_add _)
    (map_mul _) Iff.rfl Iff.rfl

instance : OpenPredicate.DiscretelyOrdered 𝔻 where
  one_le_of_pos p hp := by
    change inclusion 1 ≤ inclusion p
    rw [map_one]
    apply OpenPredicate.DiscretelyOrdered.one_le_of_pos
    simpa using (show inclusion 0 < inclusion p from hp)

variable {p q : 𝔻}

lemma le_iff : p ≤ q ↔ 0 ≤ ((q : ℚ[X]) - p).leadingCoeff := Iff.rfl

lemma lt_iff : p < q ↔ 0 < ((q : ℚ[X]) - p).leadingCoeff := by
  rw [← sub_pos]
  exact IntegerConstantPolynomial.pos_iff

lemma nonneg_iff : 0 ≤ p ↔ 0 ≤ (p : ℚ[X]).leadingCoeff := by simp [le_iff]

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
    rw [← pow_mul, ht, pow_add, eq_intCast]
    push_cast
    rw [← hm]
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
    rcases (nonneg_iff.mp hp).lt_or_eq with hl | hl
    · exact_mod_cast (hm ▸ hpos.mpr hl).le
    · rw [eq_comm, leadingCoeff_eq_zero] at hl
      rw [hl, eval_zero] at hm
      exact_mod_cast hm.ge
  lift m to ℕ using this
  exact ⟨m, by rw [← hm]; norm_cast⟩

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
  have : n * 2 = m := by
    have : (n : ℚ) * 2 = m := by simpa [hn] using hc
    exact_mod_cast this
  exact Int.not_even_iff_odd.mpr hm ⟨n, by omega⟩

/-- An element of the non-negative part all of whose divisors are `1` or even is a monomial
$2^e X^h$. -/
lemma exists_eq_C_two_zpow_mul_X_pow
    (hx : ∀ y : Nonneg 𝔻, (∃ z, z * y = x) → y = 1 ∨ ∃ w, w * 2 = y) :
    ∃ (e : ℤ) (h : ℕ), ((x : 𝔻) : ℚ[X]) = C (2 ^ e) * X ^ h := by
  by_cases hp : ((x : 𝔻) : ℚ[X]) = 0
  · exfalso
    rcases hx 3 ⟨0, by rw [zero_mul]; exact (Subtype.ext <| Subtype.ext hp).symm⟩ with h | ⟨w, hw⟩
    · norm_num at h
    · exact coeff_zero_ne_of_mul_two_eq hw (m := 3) (by decide) (by simp)
  obtain ⟨q, hq, hqX⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd _ hp 0
  simp only [map_zero, sub_zero, X_dvd_iff] at hq hqX
  set r := rootMultiplicity 0 ((x : 𝔻) : ℚ[X])
  have hqc (i : ℕ) : q.coeff i ∈ DyadicRational := by
    have := (mem_iff.mp (x : 𝔻).2).2 (i + r)
    rwa [hq, mul_comm, coeff_mul_X_pow] at this
  obtain ⟨e, m, hm, hqm⟩ := DyadicRational.exists_eq_two_zpow_mul_odd (hqc 0) hqX
  have hlc : 0 ≤ q.leadingCoeff := by
    simpa [hq, leadingCoeff_mul] using nonneg_iff.mp x.2
  have ho : C (2 ^ (-e)) * q ∈ 𝔻 := by
    refine mem_iff.mpr ⟨⟨m, ?_⟩, fun i ↦ ?_⟩
    · rw [coeff_C_mul, hqm, ← mul_assoc, ← zpow_add₀ two_ne_zero, neg_add_cancel, zpow_zero,
        one_mul]
    · rw [coeff_C_mul]
      exact mul_mem (DyadicRational.two_zpow_mem _) (hqc i)
  have he : 0 < r ∨ 0 ≤ e := by
    rcases Nat.eq_zero_or_pos r with hr | hr
    · right
      by_contra he
      obtain ⟨n, hn⟩ := (mem_iff.mp (x : 𝔻).2).1
      obtain ⟨k, rfl⟩ : ∃ k : ℕ, e = -((k + 1 : ℕ) : ℤ) := ⟨(-e - 1).toNat, by omega⟩
      have : (m : ℚ) = 2 ^ (k + 1) * n := by
        rw [hq, hr, pow_zero, one_mul, hqm, zpow_neg, zpow_natCast] at hn
        field_simp at hn
        linear_combination hn
      have : m = 2 ^ (k + 1) * n := by exact_mod_cast this
      exact Int.not_even_iff_odd.mpr hm ⟨2 ^ k * n, by rw [this, pow_succ]; ring⟩
    · exact Or.inl hr
  let o : Nonneg 𝔻 := ⟨⟨_, ho⟩, nonneg_iff.mpr <| by
    rw [leadingCoeff_mul, leadingCoeff_C]
    exact mul_nonneg (by positivity) hlc⟩
  let z : Nonneg 𝔻 := ⟨⟨_, C_two_zpow_mul_X_pow_mem he⟩,
    nonneg_iff.mpr (by rw [leadingCoeff_C_mul_X_pow]; positivity)⟩
  have hzo : z * o = x := by
    apply Subtype.ext
    apply Subtype.ext
    simp only [z, o, Nonneg.coe_mul, Subring.coe_mul]
    rw [hq, mul_mul_mul_comm, ← C_mul, ← zpow_add₀ two_ne_zero, add_neg_cancel, zpow_zero, C_1,
      one_mul]
  rcases hx o ⟨z, hzo⟩ with h | ⟨w, hw⟩
  · use e, r
    have h : C (2 ^ (-e)) * q = 1 := congrArg (fun y : Nonneg 𝔻 ↦ ((y : 𝔻) : ℚ[X])) h
    have : q = C (2 ^ e) := by
      calc q = C (2 ^ e) * (C (2 ^ (-e)) * q) := by
            rw [← mul_assoc, ← C_mul, ← zpow_add₀ two_ne_zero, add_neg_cancel, zpow_zero, C_1,
              one_mul]
        _ = C (2 ^ e) := by rw [h, mul_one]
    rw [hq, this, mul_comm]
  · exfalso
    apply coeff_zero_ne_of_mul_two_eq hw hm
    simp only [o, coeff_C_mul, hqm, ← mul_assoc]
    rw [← zpow_add₀ two_ne_zero, neg_add_cancel, zpow_zero, one_mul]

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
  obtain ⟨i, -, u, hu⟩ := (dvd_prime_pow prime_X h).mp hdvd
  obtain ⟨c, hc, hcu⟩ := Polynomial.isUnit_iff.mp (u⁻¹).isUnit
  have hy : ((y : 𝔻) : ℚ[X]) = C c * X ^ i := by
    rw [hcu, ← hu, mul_comm, mul_assoc, Units.mul_inv, mul_one]
  have hc₀ : 0 < c := by
    have := nonneg_iff.mp y.2
    rw [hy, leadingCoeff_C_mul_X_pow] at this
    exact this.lt_of_ne hc.ne_zero.symm
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · obtain ⟨n, hn⟩ := (mem_iff.mp (y : 𝔻).2).1
    rw [hy, pow_zero, mul_one, coeff_C_zero] at hn
    subst hn
    have hn₀ : 0 < n := by exact_mod_cast hc₀
    have hz : ((z : 𝔻) : ℚ[X]) = C ((2 : ℚ) ^ e / n) * X ^ h := by
      have : (n : ℚ) ≠ 0 := by positivity
      apply mul_right_cancel₀ (C_ne_zero.mpr this)
      rw [hy, pow_zero, mul_one] at hzy
      rw [hzy, mul_right_comm, ← C_mul, div_mul_cancel₀ _ this]
    have := (mem_iff.mp (z : 𝔻).2).2 h
    rw [hz, coeff_C_mul_X_pow] at this
    simp only [↓reduceIte] at this
    rcases DyadicRational.eq_one_or_two_dvd hn₀ this with rfl | ⟨k, rfl⟩
    · left
      apply Subtype.ext
      apply Subtype.ext
      simp [hy]
    · right
      use ⟨k, Int.cast_nonneg_iff.mpr (by omega)⟩
      apply Subtype.ext
      apply Subtype.ext
      simp [hy, mul_comm, map_ofNat C 2]
  · right
    have hcD : c ∈ DyadicRational := by
      have := (mem_iff.mp (y : 𝔻).2).2 i
      rw [hy, coeff_C_mul_X_pow] at this
      simpa using this
    use ⟨⟨_, C_mul_X_pow_mem (DyadicRational.div_two_mem hcD) hi⟩,
      nonneg_iff.mpr (by rw [leadingCoeff_C_mul_X_pow]; positivity)⟩
    apply Subtype.ext
    apply Subtype.ext
    simp only [Nonneg.coe_mul, Subring.coe_mul, coe_ofNat, hy]
    rw [mul_right_comm, show (2 : ℚ[X]) = C 2 from (map_ofNat C 2).symm, ← C_mul,
      div_mul_cancel₀ c two_ne_zero]

end Nonneg

end IntegerConstantDyadicPolynomial
