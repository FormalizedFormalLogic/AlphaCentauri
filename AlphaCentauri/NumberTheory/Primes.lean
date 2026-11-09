module

public import Foundation.FirstOrder.Arithmetic.EA.Basic
public import AlphaCentauri.ToFoundation.Factorial
public import AlphaCentauri.ToFoundation.Prime
public import AlphaCentauri.Schemata.WeakPigeonhole

/-!
# The infinitude of primes and Bertrand's postulate

Euclid's argument needs a bound on the next prime: $x!$ over $\mathsf{E}\mathsf{A} =
\mathsf{I}\Delta_0 + \mathrm{Exp}$, from which $\mathsf{I}\Sigma_1$ inherits it; over
$\mathsf{I}\Delta_0$ no term bounds it, and with $\Omega_1$ adjoined the sentence is instead a
theorem of Paris, Wilkie and Woods, obtained from a weak $\Delta_0$ pigeonhole principle, while
over $\mathsf{I}\Delta_0$ alone it is an open problem. $\mathsf{I}\Delta_0 + \Omega_1$ and
$\mathsf{I}\Delta_0$ each have the sentence as an axiom of its own, so that neither carries the
debt of the other.

Bertrand's postulate is a $\Pi_1$ sentence, and is likewise an axiom of its own over
$\mathsf{I}\Delta_0 + \Omega_1$, where it is a theorem, and over $\mathsf{I}\Delta_0$, where it is
open.

- [HP98, Theorem I.1.58(2), Remark I.1.59(3)]
- [PWW88, Problem 1, Corollary 8]
- [HP98, §V.5(f)]
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

end

noncomputable section

variable {V : Type*} [ORingStructure V]

/-- - [HP98, Theorem I.1.58(2)] -/
lemma ElementaryArithmetic.exists_prime_gt [V↓[ℒₒᵣ] ⊧* 𝗘𝗔] (x : V) : ∃ p, x < p ∧ IsPrime p := by
  obtain ⟨p, hp, hpn⟩ := exists_isPrime_dvd (n := factorial x + 1) (by simp)
  refine ⟨p, ?_, hp⟩
  by_contra hle
  push Not at hle
  obtain ⟨c, hc⟩ := dvd_factorial (zero_lt_one.trans hp.1) hle
  obtain ⟨e, he⟩ := hpn
  have heq : p * c + 1 = p * e := by rw [← hc, ← he]
  rcases le_or_gt e c with hle' | hlt'
  · have h1 : p * e ≤ p * c := mul_le_mul_of_nonneg_left hle' (Arithmetic.zero_le p)
    rw [← heq] at h1
    exact lt_irrefl _ (lt_of_le_of_lt h1 (lt_add_one (p * c)))
  · have h1 : p * (c + 1) ≤ p * e :=
      mul_le_mul_of_nonneg_left (lt_iff_succ_le.mp hlt') (Arithmetic.zero_le p)
    rw [mul_add, mul_one, ← heq] at h1
    exact absurd ((add_le_add_iff_left (p * c)).mp h1) (not_le.mpr hp.1)

end

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

lemma eq_of_sub_one_div_two_eq {p p' : V} (hp : IsPrime p) (hp' : IsPrime p')
    (h : (p - 1) / 2 = (p' - 1) / 2) : p = p' := by
  have key : ∀ {q : V}, IsPrime q → q = 2 ∨ q - 1 = 2 * ((q - 1) / 2) := by
    intro q hq
    by_cases h2 : 2 ∣ q
    · left
      rcases hq.2 2 (le_of_dvd (pos_of_gt hq.1) h2) h2 with h | h
      · simp at h
      · exact h.symm
    · right
      have hmod : q % 2 = 1 := by
        rcases mod_two q with h | h
        · exact absurd (mod_eq_zero_iff_dvd.mp h) h2
        · exact h
      have hq' : q - 1 = 2 * (q / 2) := by
        conv_lhs => rw [← div_add_mod q 2, hmod]
        simp
      rw [hq']
      simp
  have hle : ∀ {q : V}, IsPrime q → 1 ≤ q := fun hq ↦ hq.1.le
  have htwo : ∀ {q : V}, IsPrime q → (q - 1) / 2 = 0 → q = 2 := by
    intro q hq h0
    rcases key hq with h | h
    · exact h
    · rw [h0, mul_zero] at h
      have : q = 1 := by
        rw [← tsub_add_cancel_of_le (hle hq), h, zero_add]
      exact absurd hq.1 (by simp [this])
  have hzero : ((2 : V) - 1) / 2 = 0 := by
    rw [show (2 : V) - 1 = 1 from tsub_eq_of_eq_add one_add_one_eq_two.symm]
    exact div_eq_zero_of_lt _ one_lt_two
  rcases key hp with rfl | hp2 <;> rcases key hp' with rfl | hp2'
  · rfl
  · exact (htwo hp' (h.symm.trans hzero)).symm
  · exact htwo hp (h.trans hzero)
  · rw [← tsub_add_cancel_of_le (hle hp), ← tsub_add_cancel_of_le (hle hp'), hp2, hp2', h]

variable (a A l : V)

/-- `t` is the first index below `a` with `P ∣ A + t`. -/
def IsFirst (P t : V) : Prop := t < a ∧ P ∣ A + t ∧ ∀ s < t, ¬P ∣ A + s

/-- The position `x + 1` falls between the lengths of the largest divisors of `y` whose
prime-power divisors are at most `T` and at most `T + 1`. -/
def IsSegment (y x T : V) : Prop :=
  ‖divisorUpTo y T‖ ≤ x + 1 ∧ x + 1 < ‖divisorUpTo y (T + 1)‖

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

lemma definable_isSegment : 𝚺ᴬ₀.DefinableRel₃ (IsSegment : V → V → V → Prop) := by
  unfold IsSegment
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

section segment

variable {y x T D p o : V}

lemma IsSegment.exists_isPrimePower (hy : 0 < y) (h : IsSegment y x T) :
    ∃ p, IsPrimePower p (T + 1) ∧ T + 1 ∣ y ∧ x + 1 - ‖divisorUpTo y T‖ < ‖p‖ := by
  have hlt : divisorUpTo y T < divisorUpTo y (T + 1) := by
    by_contra! hle
    exact absurd (h.1.trans_lt h.2) (not_lt.mpr (length_monotone hle))
  obtain ⟨p, hP, hdvd, hle⟩ := exists_isPrimePower_of_divisorUpTo_lt hy hlt
  use p
  constructor
  · exact hP
  constructor
  · exact hdvd
  · apply (tsub_lt_iff_left h.1).mpr
    rw [add_comm (‖divisorUpTo y T‖)]
    exact h.2.trans_le <| (length_monotone hle).trans (length_mul_le _ _)

lemma two_mul_length_add_lt (hD : 0 < D) (hP : IsPrimePower p (T + 1)) (hdvd : T + 1 ∣ D)
    (ho : o < ‖p‖) : 2 * ‖divisorUpTo D T‖ + o < 2 * ‖divisorUpTo D (T + 1)‖ := by
  have h1 : ‖p‖ + ‖divisorUpTo D T‖ ≤ ‖divisorUpTo D (T + 1)‖ + 1 :=
    (length_add_length_le (pos_of_gt hP.1.1) (divisorUpTo_pos hD)).trans <|
      (add_le_add_iff_right 1).mpr (length_monotone (mul_divisorUpTo_le hD hP hdvd))
  have h2 : 2 ≤ ‖p‖ := by
    have h : ‖(2 : V)‖ = 2 := by
      simpa [one_add_one_eq_two] using length_two_mul_of_pos (show (0 : V) < 1 from zero_lt_one)
    rw [← h]
    exact length_monotone (by simpa [one_add_one_eq_two] using succ_le_iff_lt.mpr hP.1.1)
  have : 2 * ‖divisorUpTo D T‖ + o + 2 < 2 * ‖divisorUpTo D (T + 1)‖ + 2 := calc
    2 * ‖divisorUpTo D T‖ + o + 2 < 2 * ‖divisorUpTo D T‖ + ‖p‖ + ‖p‖ := by
      rw [add_assoc, add_assoc]
      exact (add_lt_add_iff_left _).mpr (add_lt_add_of_lt_of_le ho h2)
    _ = 2 * (‖p‖ + ‖divisorUpTo D T‖) := by grind
    _ ≤ 2 * (‖divisorUpTo D (T + 1)‖ + 1) := mul_le_mul_left h1
    _ = 2 * ‖divisorUpTo D (T + 1)‖ + 2 := by grind
  exact lt_of_add_lt_add_right this

lemma eq_of_two_mul_length_add_eq {T' p' o' : V} (hD : 0 < D) (hP : IsPrimePower p (T + 1))
    (hdvd : T + 1 ∣ D) (ho : o < ‖p‖) (hP' : IsPrimePower p' (T' + 1)) (hdvd' : T' + 1 ∣ D)
    (ho' : o' < ‖p'‖) (h : 2 * ‖divisorUpTo D T‖ + o = 2 * ‖divisorUpTo D T'‖ + o') :
    T = T' ∧ o = o' := by
  have key : ∀ {T T' p o o' : V}, IsPrimePower p (T + 1) → T + 1 ∣ D → o < ‖p‖ → T < T' →
      2 * ‖divisorUpTo D T‖ + o ≠ 2 * ‖divisorUpTo D T'‖ + o' := by
    intro T T' p o o' hP hdvd ho hlt heq
    have hlen : ‖divisorUpTo D (T + 1)‖ ≤ ‖divisorUpTo D T'‖ :=
      length_monotone (divisorUpTo_monotone (succ_le_iff_lt.mpr hlt))
    have := two_mul_length_add_lt hD hP hdvd ho
    rw [heq] at this
    exact absurd this <| not_lt.mpr <| (mul_le_mul_left hlen).trans le_self_add
  have hT : T = T' := by
    rcases lt_trichotomy T T' with hlt | heq | hgt
    · exact absurd h (key hP hdvd ho hlt)
    · exact heq
    · exact absurd h.symm (key hP' hdvd' ho' hgt)
  subst hT
  exact ⟨rfl, add_left_cancel h⟩

end segment

end

end InfinitudeOfPrimes

/-- - [PWW88, Corollary 8] -/
axiom provable_infinitudeOfPrimes_ISigma0_union_Omega1 : 𝗜𝚺₀ ∪ 𝝮₁ ⊢ infinitudeOfPrimes

/-- - [PWW88, Problem 1] -/
axiom provable_infinitudeOfPrimes_ISigma0 : 𝗜𝚺₀ ⊢ infinitudeOfPrimes

noncomputable section

variable {V : Type*} [ORingStructure V]

/-- - [PWW88, Corollary 8] -/
lemma exists_prime_gt [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ ∪ 𝝮₁] (x : V) : ∃ p, x < p ∧ IsPrime p :=
  models_infinitudeOfPrimes_iff.mp
    (consequence_iff.mp
      (Theory.Proof.sound provable_infinitudeOfPrimes_ISigma0_union_Omega1) V inferInstance) x

end

/-- Between $n$ and $2n$ there is a prime, for every $n \ge 1$. -/
def bertrandPostulate : ArithmeticSentence :=
  “∀ n, 1 ≤ n → ∃ p, n < p ∧ p ≤ 2 * n ∧ !isPrime p”

/-- - [HP98, §V.5(f), p. 392]
- [PWW88] -/
axiom provable_bertrandPostulate_ISigma0_union_Omega1 : 𝗜𝚺₀ ∪ 𝝮₁ ⊢ bertrandPostulate

/-- An open problem.
- [HP98, §V.5(f), p. 393] -/
axiom provable_bertrandPostulate_ISigma0 : 𝗜𝚺₀ ⊢ bertrandPostulate

end FFL.FirstOrder.Arithmetic
