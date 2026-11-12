module

public import AlphaCentauri.Axiomatizability.Basic
public import AlphaCentauri.ToFoundation.FirstOrder.Theory
public import Foundation.FirstOrder.Arithmetic.Induction.Equiv
public import Foundation.FirstOrder.Arithmetic.Omega1.Basic
public import Foundation.FirstOrder.Arithmetic.Induction.Basic
public import Foundation.FirstOrder.Arithmetic.Schemata
import AlphaCentauri.OpenProblem

/-!
# Finite axiomatizability of the open cases

Whether $\mathsf{B}\Sigma_1$, $\mathsf{I}\Delta_0$, or $\mathsf{I}\Delta_0 + \Omega_1$ is finitely
axiomatizable is open. $\mathsf{B}\Sigma_{n + 1}$ is finitely axiomatizable for $n \ge 1$, and
$\mathsf{I}\Delta_0$ and $\mathsf{I}\Delta_0 + \Omega_1$ are not if the polynomial hierarchy does
not collapse.

- [HP98, Corollary V.4.39]
- [Kay91, Exercise 10.4]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder

namespace Arithmetic

/-- $\mathsf{B}\Sigma_1$ is finitely axiomatizable.
- [Kay91, Exercise 10.4] -/
open_problem BSigma1_finiteAxiomatizable := FiniteAxiomatizable (𝗕𝚺 1)

/-- $\mathsf{I}\Delta_0$ is finitely axiomatizable.
- [HP98, Corollary V.4.39]
- [Kay91, Exercise 10.4] -/
open_problem ISigma0_finiteAxiomatizable := FiniteAxiomatizable 𝗜𝚺₀

/-- $\mathsf{I}\Delta_0 + \Omega_1$ is finitely axiomatizable.
- [HP98, Corollary V.4.39]
- [Kay91, Exercise 10.4] -/
open_problem ISigma0_union_Omega1_finiteAxiomatizable := FiniteAxiomatizable (𝗜𝚺₀ ∪ 𝝮₁)

end Arithmetic

end FFL.FirstOrder
