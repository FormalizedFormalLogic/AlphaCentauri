module

public import AlphaCentauri.ProvablyTotal.Basic
public import AlphaCentauri.Schemata.ParameterFreeInduction
public import AlphaCentauri.ToMathlib.ONote.Grzegorczyk

/-!
# Provably total functions and the fast-growing hierarchy

The provably total functions of $\mathsf{I}\Pi_{n+1}^-$ and of
$\mathsf{I}\Sigma_n + \mathsf{I}\Pi_{n+1}^-$, in terms of the extended Grzegorczyk hierarchy
`ONote.extendedGrzegorczyk`.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

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
