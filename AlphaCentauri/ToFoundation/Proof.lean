module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.Basic

/-!
# Elementary facts about internal derivation codes

The end-sequent of a derivation code.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The end-sequent of a proof code is bounded by the code itself. -/
lemma fstIdx_le (d : V) : fstIdx d ≤ d :=
  le_trans (pi₁_le_self (d - 1)) (by simp)

end FFL.FirstOrder.Arithmetic.Bootstrapping
