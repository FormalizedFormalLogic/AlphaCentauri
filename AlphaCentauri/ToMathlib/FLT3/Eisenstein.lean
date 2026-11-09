module

public import AlphaCentauri.ToMathlib.EisensteinInteger
public import AlphaCentauri.ToMathlib.OpenPredicate
public import Mathlib.RingTheory.Bezout

/-!
# Euclidean division and `λ`-arithmetic of the Eisenstein integers

When `R` is discretely ordered and satisfies `LeastNumberPrinciple`, `EisensteinInteger R` has a
Euclidean division with respect to the norm, is a Bézout domain, and `λ = ω - 1` is a prime with
residue classes `0` and `±1`.
-/

@[expose] public section

open QuadraticAlgebra OpenPredicate

namespace EisensteinInteger

variable {R : Type*} [CommRing R] {V : Type*} {a b c z : EisensteinInteger R}
  {F G : (V → R) → EisensteinInteger R}

/-- `λ = ω - 1`, the prime above `3`. -/
abbrev lambda : EisensteinInteger R := ω - 1

lemma norm_lambda : norm (lambda : EisensteinInteger R) = 3 := by
  rw [norm_eq]; simp [re_omega, im_omega]; norm_num

lemma norm_lambda_sq : norm ((lambda : EisensteinInteger R) ^ 2) = 9 := by
  rw [norm_pow, norm_lambda]; norm_num

lemma three_eq : (3 : EisensteinInteger R) = lambda ^ 2 * -ω ^ 2 := by
  simp only [lambda]
  linear_combination omega_sq (R := R) + (ω - 2) * omega_cube (R := R)

lemma lambda_dvd_of_re_add_im {k : R} (h : z.re + z.im = 3 * k) : lambda ∣ z := by
  use ⟨k - z.re, -k⟩
  ext <;> simp [lambda, re_omega, im_omega]
  linear_combination h

lemma exists_of_lambda_dvd (h : lambda ∣ z) : ∃ k : R, z.re + z.im = 3 * k := by
  obtain ⟨s, rfl⟩ := h
  use -s.im
  simp [lambda, re_omega, im_omega]
  ring

/-- Eisenstein-valued functions that are polynomial in the real and imaginary parts. -/
def IsEisensteinPolynomial (F : (V → R) → EisensteinInteger R) : Prop :=
  IsPolynomial (fun w => (F w).re) ∧ IsPolynomial (fun w => (F w).im)

namespace IsEisensteinPolynomial

lemma mk {f g : (V → R) → R} (hf : IsPolynomial f) (hg : IsPolynomial g) :
    IsEisensteinPolynomial fun w => (⟨f w, g w⟩ : EisensteinInteger R) := ⟨hf, hg⟩

lemma const (z : EisensteinInteger R) : IsEisensteinPolynomial (V := V) fun _ => z :=
  ⟨IsPolynomial.const _, IsPolynomial.const _⟩

lemma add (hF : IsEisensteinPolynomial F) (hG : IsEisensteinPolynomial G) :
    IsEisensteinPolynomial fun w => F w + G w := ⟨hF.1.add hG.1, hF.2.add hG.2⟩

lemma neg (hF : IsEisensteinPolynomial F) : IsEisensteinPolynomial fun w => -F w :=
  ⟨hF.1.neg, hF.2.neg⟩

lemma sub (hF : IsEisensteinPolynomial F) (hG : IsEisensteinPolynomial G) :
    IsEisensteinPolynomial fun w => F w - G w := ⟨hF.1.sub hG.1, hF.2.sub hG.2⟩

lemma mul (hF : IsEisensteinPolynomial F) (hG : IsEisensteinPolynomial G) :
    IsEisensteinPolynomial fun w => F w * G w :=
  ⟨((hF.1.mul hG.1).add ((IsPolynomial.const (-1)).mul (hF.2.mul hG.2))).of_eq fun _ => by simp,
    (((hF.1.mul hG.2).add (hF.2.mul hG.1)).add ((IsPolynomial.const (-1)).mul
      (hF.2.mul hG.2))).of_eq fun _ => by simp⟩

lemma pow (hF : IsEisensteinPolynomial F) (n : ℕ) : IsEisensteinPolynomial fun w => F w ^ n := by
  induction n with
  | zero => simpa using IsEisensteinPolynomial.const (V := V) (1 : EisensteinInteger R)
  | succ n ih => simpa [pow_succ] using ih.mul hF

lemma norm (hF : IsEisensteinPolynomial F) :
    IsPolynomial fun w => EisensteinInteger.norm (F w) :=
  (((hF.1.pow 2).sub (hF.1.mul hF.2)).add (hF.2.pow 2)).of_eq fun _ => (norm_eq _).symm

end IsEisensteinPolynomial

variable [LinearOrder R]

lemma IsEisensteinPolynomial.isOpen_eq (hF : IsEisensteinPolynomial F)
    (hG : IsEisensteinPolynomial G) : IsOpen fun w => F w = G w :=
  ((IsOpen.eq hF.1 hG.1).and (IsOpen.eq hF.2 hG.2)).of_iff fun _ =>
    ⟨fun h => QuadraticAlgebra.ext h.1 h.2, fun h => ⟨congrArg _ h, congrArg _ h⟩⟩

macro_rules
  | `(tactic| is_open_step) => `(tactic| first
    | apply IsEisensteinPolynomial.isOpen_eq | apply IsEisensteinPolynomial.norm
    | apply IsEisensteinPolynomial.const | apply IsEisensteinPolynomial.mk
    | apply IsEisensteinPolynomial.sub | apply IsEisensteinPolynomial.add
    | apply IsEisensteinPolynomial.mul | apply IsEisensteinPolynomial.neg
    | apply IsEisensteinPolynomial.pow)

variable [IsStrictOrderedRing R]

lemma lambda_ne_zero : (lambda : EisensteinInteger R) ≠ 0 := fun h => by
  simpa [lambda, im_omega] using congrArg QuadraticAlgebra.im h

variable [DiscretelyOrdered R] (hL : LeastNumberPrinciple R)

lemma not_lambda_dvd_one : ¬lambda ∣ (1 : EisensteinInteger R) := by
  intro h
  obtain ⟨k, hk⟩ := exists_of_lambda_dvd h
  simp at hk
  rcases le_or_gt k 0 with hk0 | hk0
  · linarith
  · linarith [DiscretelyOrdered.one_le_of_pos k hk0]

lemma not_lambda_dvd_two : ¬lambda ∣ (2 : EisensteinInteger R) := fun h => not_lambda_dvd_one <| by
  convert ((dvd_pow_self lambda two_ne_zero).trans (Dvd.intro _ three_eq.symm)).sub h using 1
  norm_num

lemma not_lambda_pow_four_dvd_one : ¬lambda ^ 4 ∣ (1 : EisensteinInteger R) :=
  fun h => not_lambda_dvd_one ((dvd_pow_self lambda (by norm_num)).trans h)

lemma not_lambda_pow_four_dvd_three : ¬lambda ^ 4 ∣ (3 : EisensteinInteger R) := by
  intro h
  rw [three_eq, show (lambda : EisensteinInteger R) ^ 4 = lambda ^ 2 * lambda ^ 2 by ring,
    mul_dvd_mul_iff_left (pow_ne_zero 2 lambda_ne_zero)] at h
  have h1 := (dvd_pow_self lambda (by norm_num : (2 : ℕ) ≠ 0)).trans (dvd_mul_of_dvd_left h (-ω))
  rw [show -(ω : EisensteinInteger R) ^ 2 * -ω = 1 by linear_combination omega_cube (R := R)] at h1
  exact not_lambda_dvd_one h1

include hL

lemma exists_mod (a b : EisensteinInteger R) (hb : b ≠ 0) :
    ∃ q r, a = q * b + r ∧ norm r < norm b := by
  have hn := norm_pos hb
  obtain ⟨q₁, r₁, h₁, hr₁⟩ := exists_round hL (a * star b).re (norm b) hn
  obtain ⟨q₂, r₂, h₂, hr₂⟩ := exists_round hL (a * star b).im (norm b) hn
  use ⟨q₁, q₂⟩, a - ⟨q₁, q₂⟩ * b
  refine ⟨by ring, ?_⟩
  have key : (a - ⟨q₁, q₂⟩ * b) * star b = ⟨r₁, r₂⟩ := by
    rw [sub_mul, mul_assoc, ← algebraMap_norm_eq_mul_star]
    ext <;> simp at h₁ h₂ ⊢ <;> linarith
  have hN := congrArg norm key
  rw [norm_mul, show norm (star b) = norm b from QuadraticAlgebra.norm_star b,
    (norm_eq _ : norm ⟨r₁, r₂⟩ = r₁ ^ 2 - r₁ * r₂ + r₂ ^ 2)] at hN
  have e₁ := mul_le_mul hr₁ hr₁ (by positivity) hn.le
  have e₂ := mul_le_mul hr₂ hr₂ (by positivity) hn.le
  have e₃ := mul_le_mul hr₁ hr₂ (by positivity) hn.le
  nlinarith [sq_abs r₁, sq_abs r₂, abs_mul r₁ r₂, neg_abs_le (r₁ * r₂)]

lemma exists_gcd (α β : EisensteinInteger R) (hβ : β ≠ 0) :
    ∃ δ, δ ∣ α ∧ δ ∣ β ∧ ∃ x y, δ = x * α + y * β := by
  let Φ : (Fin 5 → R) → Prop := fun w => 0 < w 0 ∧
    norm (⟨w 1, w 2⟩ : EisensteinInteger R) ≤ norm β ∧
    norm (⟨w 3, w 4⟩ : EisensteinInteger R) ≤ 2 * norm α + 1 ∧
    w 0 = norm ((⟨w 1, w 2⟩ : EisensteinInteger R) * α + ⟨w 3, w 4⟩ * β)
  have hΦ (m : R) : BoundedExists (4 * (norm α + norm β) + 4) Φ m ↔ ∃ x y : EisensteinInteger R,
      0 < m ∧ norm x ≤ norm β ∧ norm y ≤ 2 * norm α + 1 ∧ m = norm (x * α + y * β) := by
    constructor
    · rintro ⟨ys, -, h⟩
      use ⟨ys 0, ys 1⟩, ⟨ys 2, ys 3⟩
      exact h
    · rintro ⟨x, y, h⟩
      use ![x.re, x.im, y.re, y.im]
      constructor
      · have := abs_re_le x; have := abs_im_le x; have := abs_re_le y; have := abs_im_le y
        have := norm_nonneg α; have := norm_nonneg β
        intro j; fin_cases j <;> simp <;> linarith
      · simpa [Φ] using h
  have hβ' : BoundedExists (4 * (norm α + norm β) + 4) Φ (norm β) := by
    apply (hΦ _).2
    use 0, 1
    exact ⟨norm_pos hβ, by simp [norm_nonneg], by simp [norm_nonneg], by simp⟩
  obtain ⟨m, -, hm, hmin⟩ := hL 4 Φ (by is_open) _ _ (norm_nonneg β) hβ'
  obtain ⟨x, y, hpos, -, -, rfl⟩ := (hΦ _).1 hm
  have hle : norm (x * α + y * β) ≤ norm β := not_lt.1 fun h => hmin _ (norm_nonneg β) h hβ'
  have hdvd (c d : EisensteinInteger R) : x * α + y * β ∣ c * α + d * β := by
    obtain ⟨q, r, hq, hr⟩ := exists_mod hL (c * α + d * β) (x * α + y * β) (by
      rintro h
      simp [h] at hpos)
    obtain ⟨s, t, hs, ht⟩ := exists_mod hL (c - q * x) β hβ
    have e : r = t * α + (s * α + d - q * y) * β := by linear_combination -hq + α * hs
    suffices r = 0 by
      use q
      rw [hq, this, add_zero, mul_comm]
    by_contra hr0
    have h₁ := norm_add_le r (-(t * α))
    rw [norm_neg, show r + -(t * α) = (s * α + d - q * y) * β by rw [e]; ring, norm_mul,
      norm_mul] at h₁
    have h₂ : norm (s * α + d - q * y) < 2 * norm α + 2 := by
      refine lt_of_mul_lt_mul_right ?_ (norm_nonneg β)
      nlinarith [norm_nonneg α, mul_le_mul_of_nonneg_right ht.le (norm_nonneg α)]
    apply hmin _ (norm_nonneg r) hr
    apply (hΦ _).2
    use t, s * α + d - q * y
    have := DiscretelyOrdered.one_le_of_pos _ (sub_pos.2 h₂)
    exact ⟨norm_pos hr0, ht.le, by linarith, e ▸ rfl⟩
  use x * α + y * β
  exact ⟨by simpa using hdvd 1 0, by simpa using hdvd 0 1, by use x, y⟩

lemma isBezout : IsBezout (EisensteinInteger R) := by
  apply IsBezout.iff_span_pair_isPrincipal.mpr
  intro α β
  by_cases hβ : β = 0
  · subst hβ
    use α
    simp [Set.pair_comm]
  obtain ⟨δ, hα, hβ, x, y, rfl⟩ := exists_gcd hL α β hβ
  use x * α + y * β
  apply le_antisymm
  · rw [Ideal.span_le, Set.pair_subset_iff]
    exact ⟨Ideal.mem_span_singleton.2 hα, Ideal.mem_span_singleton.2 hβ⟩
  · rw [Ideal.submodule_span_eq, Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_span_pair.2 ⟨x, y, rfl⟩

lemma lambda_dvd_or (z : EisensteinInteger R) : lambda ∣ z ∨ lambda ∣ z - 1 ∨ lambda ∣ z + 1 := by
  obtain ⟨q, r, hqr, hr0, hr3⟩ := exists_ediv hL (z.re + z.im) 3 (by norm_num)
  have hr : r = 0 ∨ r = 1 ∨ r = 2 := by
    by_contra! hne
    have h₁ := DiscretelyOrdered.one_le_of_pos r (hr0.lt_of_ne hne.1.symm)
    have h₂ := DiscretelyOrdered.one_le_of_pos (r - 1) (sub_pos.2 (h₁.lt_of_ne hne.2.1.symm))
    have h₃ : 2 < r := (show (2 : R) ≤ r by linarith).lt_of_ne hne.2.2.symm
    linarith [DiscretelyOrdered.one_le_of_pos (r - 2) (sub_pos.2 h₃)]
  rcases hr with rfl | rfl | rfl
  · exact Or.inl (lambda_dvd_of_re_add_im (k := q) (by linear_combination hqr))
  · exact Or.inr (Or.inl (lambda_dvd_of_re_add_im (k := q) (by simp; linear_combination hqr)))
  · exact Or.inr (Or.inr (lambda_dvd_of_re_add_im (k := q + 1) (by simp; linear_combination hqr)))

lemma exists_unit_mod (hz : ¬lambda ∣ z) :
    ∃ e : EisensteinInteger R, (e = 1 ∨ e = -1) ∧ lambda ∣ z - e := by
  rcases lambda_dvd_or hL z with h | h | h
  · exact absurd h hz
  · use 1
    exact ⟨Or.inl rfl, h⟩
  · use -1
    exact ⟨Or.inr rfl, by rwa [sub_neg_eq_add]⟩

lemma prime_lambda : Prime (lambda : EisensteinInteger R) := by
  refine ⟨lambda_ne_zero, fun hu => not_lambda_dvd_one hu.dvd, ?_⟩
  intro p q hpq
  by_contra hcon
  push Not at hcon
  obtain ⟨e, he, hpe⟩ := exists_unit_mod hL hcon.1
  obtain ⟨f, hf, hqf⟩ := exists_unit_mod hL hcon.2
  have hef : lambda ∣ e * f := by
    convert dvd_sub hpq ((hpe.mul_right q).add (hqf.mul_left e)) using 1
    ring
  apply absurd hef
  rcases he with rfl | rfl <;> rcases hf with rfl | rfl <;> simp [dvd_neg, not_lambda_dvd_one]

lemma lambda_pow_four_dvd_cube_sub_one (h : lambda ∣ z - 1) : lambda ^ 4 ∣ z ^ 3 - 1 := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨s, hs⟩ : lambda ∣ t ^ 3 - ω ^ 2 * t - ω ^ 2 * lambda * t ^ 2 := by
    have h3 : lambda ∣ (t - 1) * t * (t + 1) := by
      rcases lambda_dvd_or hL t with h | h | h
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h _) _
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _
      · exact dvd_mul_of_dvd_right h _
    convert dvd_add h3 (dvd_mul_right lambda (-(ω + 1) * t - ω ^ 2 * t ^ 2)) using 1
    simp only [lambda]; ring
  use s
  linear_combination (z ^ 2 + z * (1 + lambda * t) + (1 + lambda * t) ^ 2) * ht
    + (lambda * t + lambda ^ 2 * t ^ 2) * three_eq (R := R) + lambda ^ 3 * hs

lemma exists_cube_mod (hz : ¬lambda ∣ z) :
    ∃ e : EisensteinInteger R, (e = 1 ∨ e = -1) ∧ lambda ^ 4 ∣ z ^ 3 - e := by
  rcases lambda_dvd_or hL z with h | h | h
  · exact absurd h hz
  · use 1
    exact ⟨Or.inl rfl, lambda_pow_four_dvd_cube_sub_one hL h⟩
  · use -1
    have := lambda_pow_four_dvd_cube_sub_one hL (z := -z) (by convert dvd_neg.2 h using 1; ring)
    exact ⟨Or.inr rfl, by convert dvd_neg.2 this using 1; ring⟩

lemma case_one (ha : ¬lambda ∣ a) (hb : ¬lambda ∣ b) (hc : ¬lambda ∣ c) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  intro h
  obtain ⟨e₁, he₁, h₁⟩ := exists_cube_mod hL ha
  obtain ⟨e₂, he₂, h₂⟩ := exists_cube_mod hL hb
  obtain ⟨e₃, he₃, h₃⟩ := exists_cube_mod hL hc
  have hd : lambda ^ 4 ∣ e₁ + e₂ - e₃ := by
    rw [show e₁ + e₂ - e₃ = (c ^ 3 - e₃) - (a ^ 3 - e₁) - (b ^ 3 - e₂) by linear_combination h]
    exact dvd_sub (dvd_sub h₃ h₁) h₂
  rcases he₁ with rfl | rfl <;> rcases he₂ with rfl | rfl <;> rcases he₃ with rfl | rfl <;>
    norm_num at hd <;>
    first
    | exact not_lambda_pow_four_dvd_one hd
    | exact not_lambda_pow_four_dvd_three hd

lemma exists_normalize {a b c u : EisensteinInteger R} (ha : ¬lambda ∣ a) (hb : ¬lambda ∣ b)
    (hc : lambda ∣ c) (h : a ^ 3 + b ^ 3 = u * c ^ 3) :
    lambda ^ 2 ∣ a + b ∨ lambda ^ 2 ∣ a + ω * b ∨ lambda ^ 2 ∣ a + ω ^ 2 * b := by
  have hp := prime_lambda hL
  have e₁ : a + ω * b = (a + b) + lambda * b := by simp only [lambda]; ring
  have e₂ : a + ω ^ 2 * b = (a + b) + lambda * ((ω + 1) * b) := by simp only [lambda]; ring
  have h1 : lambda ∣ a ^ 3 + b ^ 3 :=
    (dvd_pow_self lambda three_ne_zero).trans (h ▸ (pow_dvd_pow_of_dvd hc 3).mul_left u)
  have hab : lambda ∣ a + b := hp.dvd_of_dvd_pow (n := 3) <| by
    rw [show (a + b) ^ 3 = a ^ 3 + b ^ 3 + lambda * (lambda * -ω ^ 2 * (a * b * (a + b))) by
      linear_combination (a * b * (a + b)) * three_eq (R := R)]
    exact dvd_add h1 (dvd_mul_right _ _)
  have h4 : lambda ^ 4 ∣ a ^ 3 + b ^ 3 := by
    obtain ⟨f₁, hf₁, k₁⟩ := exists_cube_mod hL ha
    obtain ⟨f₂, hf₂, k₂⟩ := exists_cube_mod hL hb
    have hs : lambda ^ 4 ∣ a ^ 3 + b ^ 3 - (f₁ + f₂) := by
      convert dvd_add k₁ k₂ using 1
      ring
    have hs1 : lambda ∣ f₁ + f₂ := by
      convert dvd_sub h1 ((dvd_pow_self lambda four_ne_zero).trans hs) using 1
      ring
    rcases hf₁ with rfl | rfl <;> rcases hf₂ with rfl | rfl <;> norm_num at hs hs1 <;>
      first | exact absurd hs1 not_lambda_dvd_two | exact hs
  obtain ⟨q, hq⟩ := hab
  rw [sum_cubes_eq, e₁, e₂, hq, pow_succ,
    show lambda * q * (lambda * q + lambda * b) * (lambda * q + lambda * ((ω + 1) * b)) =
      lambda ^ 3 * (q * (q + b) * (q + (ω + 1) * b)) by ring,
    mul_dvd_mul_iff_left (pow_ne_zero 3 lambda_ne_zero)] at h4
  rw [e₁, e₂, hq, ← mul_add, ← mul_add, sq]
  simp only [mul_dvd_mul_iff_left (lambda_ne_zero (R := R))]
  rcases hp.dvd_or_dvd h4 with h' | h'
  · exact (hp.dvd_or_dvd h').imp_right Or.inl
  · exact .inr (.inr h')

end EisensteinInteger
