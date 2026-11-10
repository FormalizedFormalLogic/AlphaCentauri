module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax

/-!
# Gaps in Foundation's `Syntax/Proof/Basic`

The shift of free variables is monotone on coded formula sets, and the weakening and shift rules
are definable at every level.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

lemma setShift_subset_setShift {s t : V} (h : s ⊆ t) : setShift L s ⊆ setShift L t := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_setShift_iff.mp hx
  exact shift_mem_setShift (h hy)

instance wkRule.definable (ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]) :
    ℌ-Function₂ (wkRule : V → V → V) :=
  .of_zero wkRule.defined.to_definable

instance shiftRule.definable (ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]) :
    ℌ-Function₂ (shiftRule : V → V → V) :=
  .of_zero shiftRule.defined.to_definable

end FFL.FirstOrder.Arithmetic.Bootstrapping
