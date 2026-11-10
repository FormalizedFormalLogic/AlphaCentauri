module

public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinus.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.LabelledSetModel

/-!
# Soundness and completeness of $\mathbf{IL}^-$
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

section Soundness

namespace Logic

open Veltman Veltman.Model Veltman.Model.World

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {A : Formula α}

theorem ILMinus.sound [M.IsILMinus] : 𝐈𝐋⁻ ⊢ A → M ⊧ A := ofAxiomsMinus.sound (by simp)

end Logic

end Soundness

section Consistency

open Veltman.Model Logic

variable {α : Type*}

instance : Entailment.Consistent (𝐈𝐋⁻ : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILMinus.sound (M := pointModel fun _ ↦ False) h 0

end Consistency

section Completeness

namespace Logic

open Entailment Formula MaximalConsistentSet Veltman Veltman.Model
open LabelledSet.Condition ofAxiomsMinus

variable {α : Type} {A : Formula α}

/-- - [KO21, Theorem 5.1] -/
theorem ILMinus.complete
    (h : ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α), [M.IsILMinus] → M ⊧ A) :
    𝐈𝐋⁻ ⊢ A := by
  classical
  exact provable_of_models_labelledModel .ILMinus (h _)

/-- - [KO21, Theorem 5.1] -/
theorem ILMinus.iff_valid_finite :
    𝐈𝐋⁻ ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → M ⊧ A := by
  constructor;
  · intro h _ _ _ M;
    intros;
    exact ILMinus.sound h;
  · exact ILMinus.complete;

end Logic

end Completeness


end FFL.InterpretabilityLogic

end
