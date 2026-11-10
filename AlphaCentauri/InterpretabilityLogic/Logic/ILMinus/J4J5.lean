module

public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinus.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.ILMinus
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.ILMinusModel

/-!
# Soundness and completeness of $\mathbf{IL}^-(\mathbf{J4}, \mathbf{J5})$
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

section SoundnessVerbrugge

namespace Logic

open Verbrugge Verbrugge.Model Verbrugge.Model.World

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {A : Formula α}

theorem ILMinusJ4J5.sound_verbrugge [M.IsILMinus] [M.IsJ4] [M.IsJ5] :
    ILMinusJ4J5 ⊢ A → M ⊧ A :=
  ofAxiomsMinus.sound_verbrugge <| by
    rintro _ (⟨A, B, rfl⟩ | ⟨A, rfl⟩) x;
    · exact forces_axiomJ4;
    · exact forces_axiomJ5;

end Logic

end SoundnessVerbrugge

section CompletenessVerbrugge

namespace Logic

open Entailment Formula MaximalConsistentSet Verbrugge Verbrugge.Model

variable {α : Type} {A : Formula α}

/-- - [KO21, Theorem 7.1] -/
theorem ILMinusJ4J5.complete_verbrugge
    (h : ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Verbrugge.Model κ α),
      [M.IsILMinus] → [M.IsJ4] → [M.IsJ5] → M ⊧ A) :
    ILMinusJ4J5 ⊢ A := by
  classical
  by_contra hA;
  obtain ⟨Γ, hΓ⟩ := exists_neg_consistent (Φ := ilMinusAdequateClosure {A}) hA;
  have : Nonempty (LabelledSet ILMinusJ4J5 (ilMinusAdequateClosure {A})) := ⟨⟨Γ, ⊥, .bot⟩⟩;
  exact MaximalConsistentSet.not_mem_of_provable_neg hΓ (Context.by_axm rfl) <|
    (LabelledSet.truthlemma_condJ4J5 (x := ⟨Γ, ⊥, .bot⟩)
      (ilMinusAdequateClosure.subset (by simp))).mp <|
        h (LabelledSet.model LabelledSet.condJ4J5) ⟨Γ, ⊥, .bot⟩

/-- - [KO21, Theorem 7.1] -/
theorem ILMinusJ4J5.iff_valid_finite_verbrugge :
    ILMinusJ4J5 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Verbrugge.Model κ α),
      [M.IsILMinus] → [M.IsJ4] → [M.IsJ5] → M ⊧ A := by
  constructor;
  · intro h _ _ _ M;
    intros;
    exact ILMinusJ4J5.sound_verbrugge h;
  · exact ILMinusJ4J5.complete_verbrugge;

end Logic

end CompletenessVerbrugge


end FFL.InterpretabilityLogic

end
