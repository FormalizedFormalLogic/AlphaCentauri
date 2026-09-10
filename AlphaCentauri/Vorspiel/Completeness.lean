module

public import Foundation.FirstOrder.Arithmetic.Basic.Model
public import Foundation.FirstOrder.Completeness

/-! # Counter-models for unprovable arithmetic sentences

The converse of `FFL.FirstOrder.Arithmetic.complete`: an arithmetic sentence a theory does not
prove fails in some model of that theory.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

/-- A sentence unprovable in `T` fails in some model of `T`. -/
lemma exists_countermodel_of_unprovable {T : ArithmeticTheory} [𝗘𝗤 ℒₒᵣ ⪯ T]
    {σ : ArithmeticSentence} (h : ¬T ⊢ σ) :
    ∃ (M : Type) (_ : ORingStructure M) (_ : M↓[ℒₒᵣ] ⊧* T), ¬M↓[ℒₒᵣ] ⊧ σ := by
  by_contra! hc
  exact h (complete T σ fun M _ _ ↦ hc M ‹_› ‹_›)

end FFL.FirstOrder.Arithmetic
