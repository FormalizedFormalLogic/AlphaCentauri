module

public import AlphaCentauri.Axiomatizability.Basic
public import Foundation.FirstOrder.Arithmetic.Omega1.Basic

/-!
# Finite axiomatizability of `𝗜𝚺₀`

Whether `𝗜𝚺₀`, or `𝗜𝚺₀` together with `𝝮₁`, is finitely axiomatizable is an open problem; neither is
if the polynomial hierarchy does not collapse.

- [HP98, Corollary V.4.39]
- [Kay91, Exercise 10.4]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

/-- An open problem: `𝗜𝚺₀` is finitely axiomatizable. -/
axiom ISigma0.finiteAxiomatizable : FiniteAxiomatizable 𝗜𝚺₀

/-- An open problem: `𝗜𝚺₀ ∪ 𝝮₁` is finitely axiomatizable. -/
axiom ISigma0_union_Omega1.finiteAxiomatizable : FiniteAxiomatizable (𝗜𝚺₀ ∪ 𝝮₁)


end FFL.FirstOrder.Arithmetic
