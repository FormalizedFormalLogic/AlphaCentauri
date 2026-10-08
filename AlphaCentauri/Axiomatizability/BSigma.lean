module

public import AlphaCentauri.Axiomatizability.Basic
public import Foundation.FirstOrder.Arithmetic.Induction.Equiv

/-!
# Finite axiomatizability of `𝗕𝚺 1`

$\mathsf{B}\Sigma_{n + 1}$ is finitely axiomatizable for $n \ge 1$; whether $\mathsf{B}\Sigma_1$
is finitely axiomatizable is open.

- [Kay91, Exercise 10.4]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

/-- The finite axiomatizability of $\mathsf{B}\Sigma_1$, an open problem. -/
axiom BSigma1.finiteAxiomatizable : FiniteAxiomatizable (𝗕𝚺 1)

end FFL.FirstOrder.Arithmetic
