module

public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinus.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.IndexedSetModel

/-!
# Soundness and completeness of $\mathbf{IL}^-(\mathbf{J2}^+, \mathbf{J5})$
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

section Consistency

open Veltman.Model Logic

variable {α : Type*}

instance : Entailment.Consistent (ILMinusJ2PlusJ5 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILMinusJ2PlusJ5.sound (M := pointModel fun _ ↦ False) h 0

end Consistency

section Completeness

namespace Logic

open Entailment Formula MaximalConsistentSet Veltman Veltman.Model

variable {α : Type} {A : Formula α}

/-- - [KO21, Theorem 5.4] -/
theorem ILMinusJ2PlusJ5.complete
    (h : ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ2] → [M.IsJ5] → M ⊧ A) :
    ILMinusJ2PlusJ5 ⊢ A := by
  classical
  by_contra hA;
  have : Entailment.Consistent (ILMinusJ2PlusJ5 : Logic α) := .of_unprovable hA;
  exact ofAxiomsMinus.not_models_countermodel hA <|
    h (countermodel ILMinusJ2PlusJ5 (ilMinusAdequateClosure {A}))

/-- - [KO21, Theorem 5.4] -/
theorem ILMinusJ2PlusJ5.iff_valid_finite :
    ILMinusJ2PlusJ5 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ2] → [M.IsJ5] → M ⊧ A := by
  constructor;
  · intro h _ _ _ M;
    intros;
    exact ILMinusJ2PlusJ5.sound h;
  · exact ILMinusJ2PlusJ5.complete;

end Logic

end Completeness


end FFL.InterpretabilityLogic

end
