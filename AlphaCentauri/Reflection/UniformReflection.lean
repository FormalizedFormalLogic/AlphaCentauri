module

public import Foundation.FirstOrder.Incompleteness.Reflection.Uniform

@[expose] public section
/-!
# Uniform reflection over the strict hierarchy

The uniform reflection schemas for $\Sigma_n$ and $\Pi_{n + 1}$ formulas are equivalent over `T`.

- [AB05, §4.2]
-/

namespace FFL.FirstOrder.Arithmetic

variable {T : ArithmeticTheory} [T.Δ₁]

/-- `RFN` for $\Sigma_n$ and `RFN` for $\Pi_{n + 1}$ are equivalent over `T`, for `n ≥ 1`.
- [AB05, Lemma 22(ii)] -/
axiom uniformReflectionOn_Sigma_equiv_Pi_succ {n : ℕ} (hn : 1 ≤ n) :
    T ∪ 𝗥𝗙𝗡[StrictHierarchy 𝚺 n] T ≊ T ∪ 𝗥𝗙𝗡[StrictHierarchy 𝚷 (n + 1)] T

end FFL.FirstOrder.Arithmetic
