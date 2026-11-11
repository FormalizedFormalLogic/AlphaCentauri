module

public import AlphaCentauri.Model.Absolute
public import AlphaCentauri.Model.Cut
public import AlphaCentauri.Schemata.ParameterFreeInduction
public import AlphaCentauri.Model.EndExtension
public import AlphaCentauri.ProvablyTotal.Basic
public import AlphaCentauri.ProvablyTotal.Parikh
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Completeness
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.ConstantExtension
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Reflection
public import AlphaCentauri.ToFoundation.Logic.Compact
public import Foundation.FirstOrder.Tarski.Ultraproduct
public import AlphaCentauri.ToMathlib.SetTheory.Ordinal.Notation.Grzegorczyk

/-!
# Growth of provably total functions

An $\mathsf{I}\Sigma_0$-provably total function with a $\Delta_0$ graph is bounded by a closed
term, hence grows at most as fast as a term. The provably total functions of
$\mathsf{I}\Pi_{n+1}^-$ and of $\mathsf{I}\Sigma_n + \mathsf{I}\Pi_{n+1}^-$ are described in terms
of the extended Grzegorczyk hierarchy `ONote.extendedGrzegorczyk`.

- [HP98, Theorem V.1.4]
- [Bus98A, Theorem 1.2.7.1]
- [Bek99, Theorem 8]
- [Bek99, Theorem 9]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open _root_.FFL.Entailment Semiformula
open Semantics (modelsSet_iff)

variable {k : ℕ}

/-- An `𝗜𝚺₀`-provably total function with a $\Delta_0$ graph is bounded by a term, hence grows at
most polynomially.
- [HP98, Theorem V.1.4]
- [Bus98A, Theorem 1.2.7.1] -/
theorem exists_term_bound_of_provablyTotal {f φ}
  (hφ : ℬ[<, ℒₒᵣ].Closure φ.val) (h : 𝗜𝚺₀.ProvablyTotalVia f φ) :
  ∃ t : ClosedSemiterm ℒₒᵣ k, ∀ v, f v ≤ Semiterm.valb v t := by
  obtain ⟨t, ht⟩ := parikh φ.val hφ h.total;
  have h₁ : ∀ v : Fin k → ℕ, ∃ y < Semiterm.valb v t, φ.val.Evalb (y :> v) := by
    simpa [models_iff, eval_allClosure] using models_of_provable (M := ℕ) inferInstance ht
  use t;
  intro v;
  obtain ⟨y, hy, hy'⟩ := h₁ v;
  exact le_of_lt (h.graph_iff.mp hy' ▸ hy)

/-- The provably total functions of $\mathsf{I}\Pi_{n+1}^-$, for `n ≥ 1`, are the extended
Grzegorczyk class at `ω_n := ω_n(1)`.
- [Bek99, Theorem 8] -/
axiom provablyTotalFunctions_IParameterFree_Pi (n k : ℕ) (hn : 1 ≤ n) :
    (𝗜ᶠ 𝚷 (n + 1)).provablyTotalFunctions k = ONote.extendedGrzegorczyk (ONote.omegaTower n 1) k

/-- The provably total functions of $\mathsf{I}\Sigma_n + \mathsf{I}\Pi_{n+1}^-$, for `n ≥ 1`, are
the extended Grzegorczyk class at `ω_{n+1}(2)`.
- [Bek99, Theorem 9] -/
axiom provablyTotalFunctions_ISigma_union_IParameterFree_Pi (n k : ℕ) (hn : 1 ≤ n) :
    (𝗜𝚺 n ∪ 𝗜ᶠ 𝚷 (n + 1)).provablyTotalFunctions k =
      ONote.extendedGrzegorczyk (ONote.omegaTower (n + 1) 2) k

end FFL.FirstOrder.Arithmetic
