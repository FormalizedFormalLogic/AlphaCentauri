module

public import AlphaCentauri.Schemata.EA

/-!
# The infinitude of primes

Euclid's argument needs $\mathrm{lcm}(1, \dots, x)$, so it runs in
$\mathsf{I}\Delta_0 + \mathrm{Exp}$ but not in $\mathsf{I}\Delta_0$, where no term bounds the
next prime. Over $\mathsf{I}\Delta_0 + \Omega_1$ the sentence is a theorem of Paris, Wilkie and
Woods, obtained from a weak $\Delta_0$ pigeonhole principle; over $\mathsf{I}\Delta_0$ it is an
open problem. Each of the three is its own axiom here, so that none of them carries the debt of
another; the $\mathsf{I}\Sigma_1$ case is a weakening of the first.

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

/-- - [HP98, Remark I.1.59(3)] -/
axiom provable_infinitudeOfPrimes_ElementaryArithmetic : 𝗘𝗔 ⊢ infinitudeOfPrimes

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
