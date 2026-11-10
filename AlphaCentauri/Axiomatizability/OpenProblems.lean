module

public import AlphaCentauri.Axiomatizability.Basic
public import Foundation.FirstOrder.Arithmetic.Induction.Equiv
public import Foundation.FirstOrder.Arithmetic.Omega1.Basic
public import Foundation.FirstOrder.Arithmetic.Induction.Basic

/-!
# Open problems on finite axiomatizability and completions

Whether $\mathsf{B}\Sigma_1$, $\mathsf{I}\Delta_0$, or $\mathsf{I}\Delta_0 + \Omega_1$ is finitely
axiomatizable is open; $\mathsf{B}\Sigma_{n + 1}$ is finitely axiomatizable for $n \ge 1$, and
$\mathsf{I}\Delta_0$ and $\mathsf{I}\Delta_0 + \Omega_1$ are not if the polynomial hierarchy does
not collapse. It is also open whether $\mathsf{I}\Delta_0$ has a consistent complete extension
axiomatized by $\Sigma_n$ sentences for some $n$.

- [HP98, Corollary V.4.39]
- [Kay91, Exercise 10.4]
- [ELV25, Question 1.2]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

/-- $\mathsf{B}\Sigma_1$ is finitely axiomatizable. An open problem.
- [Kay91, Exercise 10.4] -/
def BSigma1FiniteAxiomatizable : Prop := FiniteAxiomatizable (𝗕𝚺 1)

/-- $\mathsf{I}\Delta_0$ is finitely axiomatizable. An open problem.
- [HP98, Corollary V.4.39]
- [Kay91, Exercise 10.4] -/
def ISigma0FiniteAxiomatizable : Prop := FiniteAxiomatizable 𝗜𝚺₀

/-- $\mathsf{I}\Delta_0 + \Omega_1$ is finitely axiomatizable. An open problem.
- [HP98, Corollary V.4.39]
- [Kay91, Exercise 10.4] -/
def ISigma0UnionOmega1FiniteAxiomatizable : Prop := FiniteAxiomatizable (𝗜𝚺₀ ∪ 𝝮₁)

/-- $\mathsf{I}\Delta_0$ has a consistent complete extension axiomatized by $\Sigma_n$ sentences
for some $n$. An open problem.
- [ELV25, Question 1.2] -/
def ExistsCompleteExtensionISigma0OfRestrictedComplexity : Prop :=
  ∃ (n : ℕ) (U : ArithmeticTheory), (∀ σ ∈ U, ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚺 n σ) ∧
    𝗜𝚺₀ ⪯ U ∧ Entailment.Consistent U ∧ Entailment.Complete U

end FFL.FirstOrder.Arithmetic
