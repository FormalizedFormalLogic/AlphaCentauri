module

public import AlphaCentauri.Axiomatizability.Basic
public import AlphaCentauri.ToFoundation.FirstOrder.Theory
public import Foundation.FirstOrder.Arithmetic.Induction.Equiv
public import Foundation.FirstOrder.Arithmetic.Omega1.Basic
public import Foundation.FirstOrder.Arithmetic.Induction.Basic
public import Foundation.FirstOrder.Arithmetic.Schemata

/-!
# Complete extensions of $\mathsf{I}\Delta_0$ by $\Sigma_n$ sentences

It is open whether $\mathsf{I}\Delta_0$ has a consistent complete extension axiomatized by
$\Sigma_n$ sentences for some $n$.

- [ELV25, Question 1.2]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder

namespace Arithmetic

/-- $\mathsf{I}\Delta_0$ has a consistent complete extension axiomatized by $\Sigma_n$ sentences
for some $n$. An open problem.
- [ELV25, Question 1.2] -/
def ExistsCompleteExtensionISigma0OfRestrictedComplexity : Prop :=
  ∃ (n : ℕ) (U : ArithmeticTheory), (∀ σ ∈ U, ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚺 n σ) ∧
    𝗜𝚺₀ ⪯ U ∧ Entailment.Consistent U ∧ Entailment.Complete U

end Arithmetic

end FFL.FirstOrder
