module

public import Foundation.FirstOrder.Arithmetic.Induction.Basic

/-!
# Completions of restricted complexity
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

/-- $\mathsf{I}\Delta_0$ has a consistent complete extension axiomatized by $\Sigma_n$ sentences
for some $n$. This is an open problem.

- [ELV25, Question 1.2] -/
axiom exists_complete_extension_ISigma0_of_restricted_complexity :
    ∃ (n : ℕ) (U : ArithmeticTheory), (∀ σ ∈ U, ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚺 n σ) ∧
      𝗜𝚺₀ ⪯ U ∧ Entailment.Consistent U ∧ Entailment.Complete U

end FFL.FirstOrder.Arithmetic
