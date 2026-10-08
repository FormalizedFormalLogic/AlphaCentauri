module

public import Foundation.FirstOrder.Arithmetic.Omega1.Basic
public import AlphaCentauri.ToFoundation.Theory

/-!
# Conservativity of $\Omega_1$

Whether adjoining $\Omega_1$ to $\mathsf{I}\Delta_0$ adds any new $\Pi_1$ theorems is an open
problem.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

/-- $\mathsf{I}\Delta_0 + \Omega_1$ is $\Pi_1$-conservative over $\mathsf{I}\Delta_0$. This is an
open problem.
- [HP98, §V.1(a), p. 274]
- [HP98, §V.5(g), p. 395] -/
axiom ISigma0_union_Omega1_weakerThanOn_Pi1_ISigma0 :
    𝗜𝚺₀ ∪ 𝝮₁ ⪯[fun σ ↦ ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 1 σ] 𝗜𝚺₀

end FFL.FirstOrder.Arithmetic
