module

public import AlphaCentauri.Axiomatizability.Basic
public import Foundation.FirstOrder.Arithmetic.Omega1.Basic

/-!
# Finite axiomatizability of $\mathsf{I}\Delta_0$

Whether $\mathsf{I}\Delta_0$, or $\mathsf{I}\Delta_0 + \Omega_1$, is finitely axiomatizable is an
open problem; neither is if the polynomial hierarchy does not collapse.

- [HP98, Corollary V.4.39]
- [Kay91, Exercise 10.4]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

/-- $\mathsf{I}\Delta_0$ is finitely axiomatizable. An open problem.
- [HP98, Corollary V.4.39]
- [Kay91, Exercise 10.4] -/
def ISigma0FiniteAxiomatizable : Prop := FiniteAxiomatizable 𝗜𝚺₀

/-- $\mathsf{I}\Delta_0 + \Omega_1$ is finitely axiomatizable. An open problem.
- [HP98, Corollary V.4.39]
- [Kay91, Exercise 10.4] -/
def ISigma0UnionOmega1FiniteAxiomatizable : Prop := FiniteAxiomatizable (𝗜𝚺₀ ∪ 𝝮₁)

end FFL.FirstOrder.Arithmetic
