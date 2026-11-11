module

public import Foundation.FirstOrder.Arithmetic.EA.Basic
public import AlphaCentauri.Schemata.Pigeonhole
public import AlphaCentauri.Schemata.WeakPigeonhole
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Factorial
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Prime

/-!
# The infinitude of primes

Euclid's argument needs a bound on the next prime: $x!$ over $\mathsf{E}\mathsf{A} =
\mathsf{I}\Delta_0 + \mathrm{Exp}$, from which $\mathsf{I}\Sigma_1$ inherits it; over
$\mathsf{I}\Delta_0$ no term bounds it. With $\Omega_1$ adjoined the sentence is a theorem of
Paris, Wilkie and Woods: if every prime is at most $a$, the $a$ consecutive numbers
$a^{20} + i$, $i < a$, have no prime factor above $a$, and their factorizations give a
$\Delta_0$ injection of $18a\|a\|$ into $16a\|a\|$, against the weak pigeonhole principle
with ratio $9/8$. Over $\mathsf{I}\Delta_0$ alone it is an open problem.

- [HP98, Theorem I.1.58(2), Remark I.1.59(3)]
- [PWW88, Problem 1, Theorem 11, Corollary 8]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

/-- There are arbitrarily large primes. -/
def infinitudeOfPrimes : ArithmeticSentence := “∀ x, ∃ p, x < p ∧ !isPrime p”

noncomputable section

variable {V : Type*} [ORingStructure V]

@[simp] lemma models_infinitudeOfPrimes_iff [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] :
    V↓[ℒₒᵣ] ⊧ infinitudeOfPrimes ↔ ∀ x : V, ∃ p, x < p ∧ IsPrime p := by
  simp [models_iff, infinitudeOfPrimes]

/-- - [HP98, Theorem I.1.58(2)] -/
lemma ElementaryArithmetic.exists_prime_gt [V↓[ℒₒᵣ] ⊧* 𝗘𝗔] (x : V) : ∃ p, x < p ∧ IsPrime p := by
  obtain ⟨p, hp, hpn⟩ := exists_isPrime_dvd (n := factorial x + 1) (by simp)
  refine ⟨p, ?_, hp⟩
  by_contra! hle
  exact absurd (le_of_dvd one_pos (dvd_of_dvd_add (dvd_factorial (zero_lt_one.trans hp.1) hle) hpn))
    (not_le.mpr hp.1)

/-- - [HP98, Remark I.1.59(3)] -/
theorem provable_infinitudeOfPrimes_ElementaryArithmetic : 𝗘𝗔 ⊢ infinitudeOfPrimes :=
  complete 𝗘𝗔 infinitudeOfPrimes fun (_ : Type) _ _ ↦
    models_infinitudeOfPrimes_iff.mpr ElementaryArithmetic.exists_prime_gt

/-- - [HP98, Theorem I.1.58(2)] -/
theorem provable_infinitudeOfPrimes_ISigma1 : 𝗜𝚺₁ ⊢ infinitudeOfPrimes :=
  Entailment.WeakerThan.pbl provable_infinitudeOfPrimes_ElementaryArithmetic

namespace InfinitudeOfPrimes

noncomputable section

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀]

variable (a A l : V)

/-- `t` is the first index below `a` with `P ∣ A + t`. -/
def IsFirst (P t : V) : Prop := t < a ∧ P ∣ A + t ∧ ∀ s < t, ¬P ∣ A + s

/-- The images `z` of the position `x` in the block of `A + i`. -/
def Image (i x z : V) : Prop :=
  ∃ T < A + i, IsSegment (A + i) x T ∧ ∃ t ≤ i, IsFirst a A (T + 1) t ∧
    ((∃ D < a, i = t + D ∧ 0 < D ∧
        z = 2 * ‖divisorUpTo D T‖ + (x + 1 - ‖divisorUpTo (A + i) T‖) + 2 * ‖a‖ * (2 * D)) ∨
      (t = i ∧ ∃ D < a, 0 < D ∧ i + D < a ∧ T + 1 ∣ A + (i + D) ∧
        z = 2 * ‖divisorUpTo D T‖ + (x + 1 - ‖divisorUpTo (A + i) T‖) +
          2 * ‖a‖ * (1 + 2 * D)) ∨
      (t = i ∧ (∀ s < a, i < s → ¬T + 1 ∣ A + s) ∧
        ∃ p ≤ T + 1, IsPrimePower p (T + 1) ∧ z = x + l * ((p - 1) / 2) + 4 * a * ‖a‖))

/-- The relation sending `x + l * i`, for `x < l` and `i < a`, to the images of `x` in the block
of `A + i`. -/
def Code (X z : V) : Prop := ∃ i < a, ∃ x < l, X = x + l * i ∧ Image a A l i x z

variable {a A l}

lemma definable_isFirst : 𝚺ᴬ₀.DefinableRel (IsFirst a A) := by
  unfold IsFirst
  definability

lemma definable_image : 𝚺ᴬ₀.DefinableRel₃ (Image a A l) := by
  have := definable_isFirst (a := a) (A := A)
  have := definable_isSegment (V := V)
  unfold Image
  definability

lemma definable_code : 𝚺ᴬ₀.DefinableRel (Code a A l) := by
  have := definable_image (a := a) (A := A) (l := l)
  unfold Code
  definability

lemma IsFirst.unique {P t t' : V} (h : IsFirst a A P t) (h' : IsFirst a A P t') : t = t' := by
  rcases lt_trichotomy t t' with hlt | heq | hgt
  · exact absurd h.2.1 (h'.2.2 t hlt)
  · exact heq
  · exact absurd h'.2.1 (h.2.2 t' hgt)


variable {i x z D p o T : V}

lemma two_mul_length_add_lt_of_dvd (hD : 0 < D) (hDa : D < a)
    (hP : IsPrimePower p (T + 1)) (hdvd : T + 1 ∣ D) (ho : o < ‖p‖) :
    2 * ‖divisorUpTo D T‖ + o < 2 * ‖a‖ :=
  (two_mul_length_add_lt hD hP hdvd ho).trans_le <| mul_le_mul_left <|
    (length_monotone (divisorUpTo_le D (T + 1))).trans (length_monotone hDa.le)

lemma add_mul_lt_four_mul_mul_length {W D f : V} (hW : W < 2 * ‖a‖) (hD : D < a) (hf : f ≤ 1) :
    W + 2 * ‖a‖ * (f + 2 * D) < 4 * a * ‖a‖ := by
  have hDa : 1 + f + 2 * D ≤ 2 * a := calc
    1 + f + 2 * D ≤ 1 + 1 + 2 * D := (add_le_add_iff_right _).mpr ((add_le_add_iff_left 1).mpr hf)
    _ = 2 * (D + 1) := by grind
    _ ≤ 2 * a := mul_le_mul_left (succ_le_iff_lt.mpr hD)
  calc W + 2 * ‖a‖ * (f + 2 * D) < 2 * ‖a‖ + 2 * ‖a‖ * (f + 2 * D) :=
        (add_lt_add_iff_right _).mpr hW
    _ = 2 * ‖a‖ * (1 + f + 2 * D) := by grind
    _ ≤ 2 * ‖a‖ * (2 * a) := mul_le_mul_left hDa
    _ = 4 * a * ‖a‖ := by grind

lemma exists_image (hA : 0 < A) (hl : l < ‖A‖) (hprime : ∀ p, IsPrime p → p ≤ a) (hi : i < a)
    (hx : x < l) : ∃ z < l * ((a - 1) / 2 + 1) + 4 * a * ‖a‖, Image a A l i x z := by
  have hN : 0 < A + i := lt_of_lt_of_le hA le_self_add
  have hxN : x + 1 < ‖A + i‖ :=
    (succ_le_iff_lt.mpr hx).trans_lt <| hl.trans_le (length_monotone le_self_add)
  obtain ⟨T, hT⟩ := exists_length_divisorUpTo_le_lt hN hxN
  obtain ⟨p, hP, hdvd, ho⟩ := IsSegment.exists_isPrimePower hN hT
  have hTN : T < A + i := (lt_add_one T).trans_le (le_of_dvd hN hdvd)
  obtain ⟨t, htP, htmin⟩ :=
    ISigma0.least_number (P := fun t ↦ T + 1 ∣ A + t) (by definability) hdvd
  have hti : t ≤ i := by
    by_contra! h
    exact htmin i h hdvd
  have hfirst : IsFirst a A (T + 1) t := ⟨hti.trans_lt hi, htP, htmin⟩
  have hbound : 4 * a * ‖a‖ ≤ l * ((a - 1) / 2 + 1) + 4 * a * ‖a‖ := le_add_self
  rcases hti.lt_or_eq with hlt | rfl
  · obtain ⟨D, rfl⟩ := le_iff_exists_add.mp hlt.le
    have hD : 0 < D := (lt_add_iff_pos_right t).mp hlt
    have hDa : D < a := le_add_self.trans_lt hi
    have hdvdD : T + 1 ∣ D := dvd_of_dvd_add htP (by rwa [← add_assoc] at hdvd)
    use 2 * ‖divisorUpTo D T‖ + (x + 1 - ‖divisorUpTo (A + (t + D)) T‖) + 2 * ‖a‖ * (2 * D)
    constructor
    · apply lt_of_lt_of_le _ hbound
      simpa using add_mul_lt_four_mul_mul_length
        (two_mul_length_add_lt_of_dvd hD hDa hP hdvdD ho) hDa zero_le_one
    · use T, hTN, hT, t, hlt.le, hfirst
      left
      use D
  · by_cases hnext : ∃ s < a, t < s ∧ T + 1 ∣ A + s
    · obtain ⟨s, hs, hts, hsP⟩ := hnext
      obtain ⟨D, rfl⟩ := le_iff_exists_add.mp hts.le
      have hD : 0 < D := (lt_add_iff_pos_right t).mp hts
      have hDa : D < a := le_add_self.trans_lt hs
      have hdvdD : T + 1 ∣ D := dvd_of_dvd_add htP (by rwa [← add_assoc] at hsP)
      use 2 * ‖divisorUpTo D T‖ + (x + 1 - ‖divisorUpTo (A + t) T‖) + 2 * ‖a‖ * (1 + 2 * D)
      constructor
      · exact (add_mul_lt_four_mul_mul_length
          (two_mul_length_add_lt_of_dvd hD hDa hP hdvdD ho) hDa le_rfl).trans_le hbound
      · use T, hTN, hT, t, le_rfl, hfirst
        right
        left
        exact ⟨rfl, D, hDa, hD, hs, hsP, rfl⟩
    · push Not at hnext
      use x + l * ((p - 1) / 2) + 4 * a * ‖a‖
      constructor
      · apply (add_lt_add_iff_right _).mpr
        calc x + l * ((p - 1) / 2) < l + l * ((p - 1) / 2) := (add_lt_add_iff_right _).mpr hx
          _ = l * ((p - 1) / 2 + 1) := by grind
          _ ≤ l * ((a - 1) / 2 + 1) := mul_le_mul_left <|
            (add_le_add_iff_right 1).mpr (div_monotone (tsub_le_tsub_right (hprime p hP.1) 1) 2)
      · use T, hTN, hT, t, le_rfl, hfirst
        right
        right
        exact ⟨rfl, hnext, p, le_of_dvd (by simp) hP.dvd, hP, rfl⟩

lemma Image.cases (hA : 0 < A) (hi : i < a) (h : Image a A l i x z) :
    (∃ T t D f p, IsSegment (A + i) x T ∧ IsFirst a A (T + 1) t ∧ IsPrimePower p (T + 1) ∧
      T + 1 ∣ D ∧ 0 < D ∧ D < a ∧ f ≤ 1 ∧ (f = 0 → i = t + D) ∧ (f = 1 → i = t) ∧
      x + 1 - ‖divisorUpTo (A + i) T‖ < ‖p‖ ∧
      z = 2 * ‖divisorUpTo D T‖ + (x + 1 - ‖divisorUpTo (A + i) T‖) + 2 * ‖a‖ * (f + 2 * D)) ∨
    (∃ T p, IsPrimePower p (T + 1) ∧ T + 1 ∣ A + i ∧ (∀ s < a, s ≠ i → ¬T + 1 ∣ A + s) ∧
      z = x + l * ((p - 1) / 2) + 4 * a * ‖a‖) := by
  obtain ⟨T, -, hT, t, -, hfirst, h⟩ := h
  have hN : 0 < A + i := lt_of_lt_of_le hA le_self_add
  obtain ⟨p, hP, hdvd, ho⟩ := hT.exists_isPrimePower hN
  rcases h with ⟨D, hDa, rfl, hD, rfl⟩ | ⟨rfl, D, hDa, hD, -, hdvd', rfl⟩ |
    ⟨rfl, hnext, p', -, hP', rfl⟩
  · left
    use T, t, D, 0, p
    exact ⟨hT, hfirst, hP, dvd_of_dvd_add hfirst.2.1 (by rwa [← add_assoc] at hdvd), hD, hDa,
      zero_le_one, fun _ ↦ rfl, fun h ↦ absurd h zero_ne_one, ho, by simp⟩
  · left
    use T, t, D, 1, p
    exact ⟨hT, hfirst, hP, dvd_of_dvd_add hdvd (by rwa [← add_assoc] at hdvd'), hD, hDa, le_rfl,
      fun h ↦ absurd h one_ne_zero, fun _ ↦ rfl, ho, rfl⟩
  · right
    use T, p'
    refine ⟨hP', hdvd, ?_, rfl⟩
    intro s hs hst
    rcases lt_or_gt_of_ne hst with hlt | hgt
    · exact hfirst.2.2 s hlt
    · exact hnext s hs hgt

lemma image_injective (hA : 0 < A) {i' x' : V} (hi : i < a) (hi' : i' < a) (hx : x < l)
    (hx' : x' < l) (h : Image a A l i x z) (h' : Image a A l i' x' z) : i = i' ∧ x = x' := by
  rcases h.cases hA hi with ⟨T, t, D, f, p, hT, hfirst, hP, hdvd, hD, hDa, hf, hf0, hf1, ho, rfl⟩ |
      ⟨T, p, hP, hdvd, hlone, rfl⟩ <;>
    rcases h'.cases hA hi' with
      ⟨T', t', D', f', p', hT', hfirst', hP', hdvd', hD', hDa', hf', hf0', hf1', ho', heq⟩ |
      ⟨T', p', hP', hdvd', hlone', heq⟩
  · have hW := two_mul_length_add_lt_of_dvd hD hDa hP hdvd ho
    have hW' := two_mul_length_add_lt_of_dvd hD' hDa' hP' hdvd' ho'
    obtain ⟨hWeq, hfD⟩ := (add_mul_eq_add_mul_iff hW hW').mp heq
    obtain ⟨rfl, rfl⟩ :=
      (add_mul_eq_add_mul_iff (lt_two_iff_le_one.mpr hf) (lt_two_iff_le_one.mpr hf')).mp hfD
    obtain ⟨rfl, hoeq⟩ := eq_of_two_mul_length_add_eq hD hP hdvd ho hP' hdvd' ho' hWeq
    obtain rfl := hfirst.unique hfirst'
    have hii : i = i' := by
      rcases le_one_iff_eq_zero_or_one.mp hf with rfl | rfl
      · rw [hf0 rfl, hf0' rfl]
      · rw [hf1 rfl, hf1' rfl]
    subst hii
    constructor
    · rfl
    · exact add_right_cancel <| (tsub_left_inj hT.1 hT'.1).mp hoeq
  · have := add_mul_lt_four_mul_mul_length
      (two_mul_length_add_lt_of_dvd hD hDa hP hdvd ho) hDa hf
    rw [heq] at this
    exact absurd this (not_lt.mpr le_add_self)
  · have := add_mul_lt_four_mul_mul_length
      (two_mul_length_add_lt_of_dvd hD' hDa' hP' hdvd' ho') hDa' hf'
    rw [← heq] at this
    exact absurd this (not_lt.mpr le_add_self)
  · obtain ⟨rfl, hk⟩ := (add_mul_eq_add_mul_iff hx hx').mp (add_right_cancel heq)
    obtain rfl := hP.1.eq_of_sub_one_div_two_eq hP'.1 hk
    constructor
    · by_contra hne
      rcases hP.dvd_or_dvd hP' with h | h
      · exact hlone i' hi' (Ne.symm hne) (h.trans hdvd')
      · exact hlone' i hi hne (h.trans hdvd)
    · rfl


end

end InfinitudeOfPrimes

/-- $\mathsf{I}\Delta_0$ proves the infinitude of primes. An open problem.
- [PWW88, Problem 1] -/
def ProvableInfinitudeOfPrimesISigma0 : Prop := 𝗜𝚺₀ ⊢ infinitudeOfPrimes

open InfinitudeOfPrimes in
/-- - [PWW88, Theorem 11, Corollary 8] -/
lemma exists_prime_gt [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ ∪ 𝝮₁] (x : V) : ∃ p, x < p ∧ IsPrime p := by
  by_contra! hx
  have hlen2 : ∀ (k : ℕ) {y : V}, 0 < y → ‖(2 : V) ^ k * y‖ = ‖y‖ + k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro y hy
      rw [show (2 : V) ^ (k + 1) * y = 2 * (2 ^ k * y) by grind,
        length_two_mul_of_pos (mul_pos (pow_pos two_pos k) hy), ih hy]
      push_cast
      grind
  set a : V := 2 ^ 9 * (x + 1)
  have hx1 : (0 : V) < x + 1 := by simp
  have hLa : 10 ≤ ‖a‖ := by
    rw [hlen2 9 hx1, Nat.cast_ofNat]
    calc (10 : V) = 1 + 9 := by grind
      _ ≤ ‖x + 1‖ + 9 := (add_le_add_iff_right _).mpr (pos_iff_one_le.mp (length_pos_iff.mpr hx1))
  have ha : 10 ≤ a := hLa.trans (length_le a)
  have ha0 : 0 < a := mul_pos (pow_pos two_pos 9) hx1
  have hprime : ∀ p, IsPrime p → p ≤ a := by
    intro p hp
    have hpx : p ≤ x := not_lt.mp fun h ↦ hx p h hp
    exact hpx.trans <| le_self_add.trans <| le_mul_of_one_le_left (Arithmetic.zero_le _) <|
      one_le_pow₀ one_le_two
  set L := ‖a‖
  set A : V := a ^ 20
  set l : V := 18 * L
  have hA : 0 < A := pow_pos ha0 20
  have hpow : ∀ k : ℕ, (k + 1 : V) * L ≤ ‖a ^ (k + 1)‖ + k := by
    intro k
    induction k with
    | zero => simp [L]
    | succ k ih =>
      calc ((k + 1 : ℕ) + 1 : V) * L = (k + 1) * L + L := by push_cast; grind
        _ ≤ ‖a ^ (k + 1)‖ + k + L := (add_le_add_iff_right _).mpr ih
        _ = ‖a ^ (k + 1)‖ + ‖a‖ + k := by grind
        _ ≤ ‖a ^ (k + 1) * a‖ + 1 + k :=
          (add_le_add_iff_right _).mpr (length_add_length_le (pow_pos ha0 _) ha0)
        _ = ‖a ^ (k + 1 + 1)‖ + ((k + 1 : ℕ) : V) := by rw [← pow_succ]; push_cast; grind
  have hl : l < ‖A‖ := by
    have h20 := hpow 19
    have : l + 20 ≤ ‖A‖ + 19 := calc
      l + 20 ≤ 18 * L + 2 * L := (add_le_add_iff_left _).mpr <| calc
        (20 : V) = 2 * 10 := by grind
        _ ≤ 2 * L := mul_le_mul_left hLa
      _ = ((19 : ℕ) + 1 : V) * L := by push_cast; grind
      _ ≤ ‖A‖ + ((19 : ℕ) : V) := h20
      _ = ‖A‖ + 19 := by simp
    exact succ_le_iff_lt.mp <| (add_le_add_iff_right 19).mp <| by
      rwa [show l + 1 + 19 = l + 20 by grind]
  set m : V := 2 * a * L
  have hl0 : 0 < l := mul_pos (by exact_mod_cast Nat.succ_pos 17) (length_pos_iff.mpr ha0)
  have hR : 𝚺ᴬ₀.DefinableRel fun X z ↦ Code a A l X z ∧ z < 8 * m := by
    have := definable_code (a := a) (A := A) (l := l)
    definability
  have hbound : l * ((a - 1) / 2 + 1) + 4 * a * L ≤ 8 * m := by
    have h2 : 2 * ((a - 1) / 2) ≤ a - 1 := mul_div_le _ _
    have h3 : a - 1 + 2 = a + 1 := by
      rw [show (2 : V) = 1 + 1 by grind, ← add_assoc, tsub_add_cancel_of_le (pos_iff_one_le.mp ha0)]
    calc l * ((a - 1) / 2 + 1) + 4 * a * L = 9 * L * (2 * ((a - 1) / 2) + 2) + 4 * a * L := by
          grind
      _ ≤ 9 * L * (a - 1 + 2) + 4 * a * L :=
        (add_le_add_iff_right _).mpr (mul_le_mul_left ((add_le_add_iff_right 2).mpr h2))
      _ = 9 * L * a + 9 * L + 4 * a * L := by rw [h3]; grind
      _ ≤ 9 * L * a + 3 * L * a + 4 * a * L :=
        (add_le_add_iff_right _).mpr ((add_le_add_iff_left _).mpr
          (by
            have h := mul_le_mul_left (a := 3 * L)
              ((show (3 : V) ≤ 10 by exact_mod_cast (show 3 ≤ 10 by decide)).trans ha)
            rwa [show 3 * L * 3 = 9 * L by grind] at h))
      _ = 8 * m := by grind
  have total : ∀ X < ((8 : ℕ) + 1 : V) * m, ∃ z < ((8 : ℕ) : V) * m,
      Code a A l X z ∧ z < 8 * m := by
    intro X hX
    have hXl : X < a * l := by
      rw [show ((8 : ℕ) + 1 : V) * m = a * l by push_cast; grind] at hX
      exact hX
    obtain ⟨z, hz, himage⟩ :=
      exists_image hA hl hprime (div_lt_of_lt_mul hXl) (mod_lt X hl0)
    have hz' : z < 8 * m := hz.trans_le hbound
    use z
    constructor
    · simpa using hz'
    · exact ⟨⟨X / l, div_lt_of_lt_mul hXl, X % l, mod_lt X hl0, by rw [add_comm, div_add_mod],
        himage⟩, hz'⟩
  obtain ⟨X, -, X', -, z, -, hne, ⟨⟨i, hi, y, hy, rfl, h⟩, -⟩, ⟨⟨i', hi', y', hy', rfl, h'⟩, -⟩⟩ :=
    weakPigeonhole_succ_mul 8 hR (by simp [m, ha0, L]) total
  obtain ⟨rfl, rfl⟩ := image_injective hA hi hi' hy hy' h h'
  exact hne rfl

/-- - [PWW88, Corollary 8] -/
theorem provable_infinitudeOfPrimes_ISigma0_union_Omega1 : 𝗜𝚺₀ ∪ 𝝮₁ ⊢ infinitudeOfPrimes :=
  have : 𝗘𝗤 ℒₒᵣ ⪯ 𝗜𝚺₀ ∪ 𝝮₁ :=
    Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗜𝚺₀) inferInstance
  complete (𝗜𝚺₀ ∪ 𝝮₁) infinitudeOfPrimes fun (M : Type) _ _ ↦ by
    have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := mod_paMinus_of_ISigma (s := 0)
    exact models_infinitudeOfPrimes_iff.mpr exists_prime_gt

end

end FFL.FirstOrder.Arithmetic
