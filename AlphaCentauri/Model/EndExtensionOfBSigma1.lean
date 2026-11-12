module

public import AlphaCentauri.Model.EndExtension
public import Foundation.FirstOrder.Arithmetic.Collection.Basic
public import AlphaCentauri.Model.Absolute
import AlphaCentauri.OpenProblem

/-! # End extensions of models of $\mathsf{B}\Sigma_1$

A model of $\mathsf{I}\Delta_0$ with a proper end extension to a model of $\mathsf{I}\Delta_0$
satisfies $\mathsf{B}\Sigma_1$, and a countable model of $\mathsf{B}\Sigma_1 + \mathrm{Exp}$ has
such an extension. Whether the hypothesis $\mathrm{Exp}$ can be dropped is open.

- [Kay91, Chapter 16, p. 269]
- [WP89]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic


/-- Every countable model of $\mathsf{B}\Sigma_1$ has a proper end extension to a model of
$\mathsf{I}\Delta_0$.
- [Kay91, Chapter 16, p. 269]
- [WP89] -/
open_problem exists_proper_endExtension_ISigma0_of_BSigma1 :=
  ∀ (M : Type) [Countable M] [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗕𝚺1],
    ∃ (N : Type) (_ : M ⊂ₑ N), N↓[ℒₒᵣ] ⊧* 𝗜𝚺₀


end FFL.FirstOrder.Arithmetic
