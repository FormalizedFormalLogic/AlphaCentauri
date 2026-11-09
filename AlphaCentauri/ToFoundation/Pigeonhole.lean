module

public import Foundation.FirstOrder.Arithmetic.Exponential.Bit

/-!
# The pigeonhole principle in models of $\mathsf{I}\Sigma_m$

In a model of $\mathsf{I}\Sigma_m$, $m \ge 1$, no $\Sigma_m$-definable relation is an injection of
$a + 1$ into $a$.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] {m : ℕ}

/-- A $\Sigma_m$-definable relation giving every `x < a + 1` some value below `a` gives two of
them a common value.
- [HP98, Theorem I.1.41] -/
axiom pigeonhole [Fact (1 ≤ m)] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺m] {R : V → V → Prop} (hR : 𝚺ᴬ_[m].DefinableRel R) (a : V)
    (total : ∀ x < a + 1, ∃ y < a, R x y) :
    ∃ x < a + 1, ∃ x' < a + 1, ∃ y < a, x ≠ x' ∧ R x y ∧ R x' y

end FFL.FirstOrder.Arithmetic
