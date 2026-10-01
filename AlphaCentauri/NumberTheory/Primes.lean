module

public import AlphaCentauri.Schemata.EA
public import AlphaCentauri.ToFoundation.Factorial
public import AlphaCentauri.ToFoundation.Prime

/-!
# The infinitude of primes

Euclid's argument needs a bound on the next prime: $x!$ over $\mathsf{E}\mathsf{A} =
\mathsf{I}\Delta_0 + \mathrm{Exp}$, from which $\mathsf{I}\Sigma_1$ inherits it; over
$\mathsf{I}\Delta_0$ no term bounds it, and with $\Omega_1$ adjoined the sentence is instead a
theorem of Paris, Wilkie and Woods, obtained from a weak $\Delta_0$ pigeonhole principle, while
over $\mathsf{I}\Delta_0$ alone it is an open problem. $\mathsf{I}\Delta_0 + \Omega_1$ and
$\mathsf{I}\Delta_0$ each have the sentence as an axiom of its own, so that neither carries the
debt of the other.

- [HP98, Theorem I.1.58(2), Remark I.1.59(3)]
- [PWW88, Problem 1, Corollary 8]
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

end FFL.FirstOrder.Arithmetic
