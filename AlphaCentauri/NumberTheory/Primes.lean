module

public import Foundation.FirstOrder.Arithmetic.Omega1.Basic

/-!
# The infinitude of primes

Euclid's argument needs $\mathrm{lcm}(1, \dots, x)$, so it runs in $\mathsf{I}\Sigma_1$ but not in
$\mathsf{I}\Delta_0$, where no term bounds the next prime. Over $\mathsf{I}\Delta_0 + \Omega_1$ the
sentence is a theorem of Paris, Wilkie and Woods, obtained from a weak $\Delta_0$ pigeonhole
principle; over $\mathsf{I}\Delta_0$ it is an open problem. Both are declared as axioms here.

- [HP98, Theorem I.1.58(2)]
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
