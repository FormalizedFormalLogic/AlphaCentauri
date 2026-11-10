module

public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinus.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.ILMinus
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.ILMinusModel

/-!
# Soundness and completeness of $\mathbf{IL}^-(\mathbf{J2})$
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

section Soundness

namespace Logic

open Veltman Veltman.Model Veltman.Model.World

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {A : Formula α}

theorem ILMinusJ2.sound [M.IsILMinus] [M.IsJ2] : ILMinusJ2 ⊢ A → M ⊧ A :=
  ofAxiomsMinus.sound <| by
    rintro _ ⟨A, B, C, rfl⟩ x;
    exact forces_axiomJ2

end Logic

end Soundness

section SoundnessVerbrugge

namespace Logic

open Verbrugge Verbrugge.Model Verbrugge.Model.World

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {A : Formula α}

theorem ILMinusJ2.sound_verbrugge [M.IsILMinus] [M.IsJ2] : ILMinusJ2 ⊢ A → M ⊧ A :=
  ofAxiomsMinus.sound_verbrugge <| by
    rintro _ ⟨A, B, C, rfl⟩ x;
    exact forces_axiomJ2

end Logic

end SoundnessVerbrugge

section Consistency

open Veltman.Model Logic

variable {α : Type*}

instance : Entailment.Consistent (ILMinusJ2 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILMinusJ2.sound (M := pointModel fun _ ↦ False) h 0

end Consistency

section CompletenessVerbrugge

namespace Logic

open Entailment Formula MaximalConsistentSet Verbrugge Verbrugge.Model

variable {α : Type} {A : Formula α}

/-- - [KO21, Theorem 7.1] -/
theorem ILMinusJ2.complete_verbrugge
    (h : ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Verbrugge.Model κ α),
      [M.IsILMinus] → [M.IsJ2] → M ⊧ A) :
    ILMinusJ2 ⊢ A := by
  classical
  by_contra hA;
  obtain ⟨Γ, hΓ⟩ := exists_neg_consistent (Φ := ilMinusAdequateClosure {A}) hA;
  have : Nonempty (LabelledSet ILMinusJ2 (ilMinusAdequateClosure {A})) := ⟨⟨Γ, ⊥, .bot⟩⟩;
  exact MaximalConsistentSet.not_mem_of_provable_neg hΓ (Context.by_axm rfl) <|
    (LabelledSet.truthlemma_condJ2 (x := ⟨Γ, ⊥, .bot⟩)
      (ilMinusAdequateClosure.subset (by simp))).mp <|
        h (LabelledSet.model LabelledSet.condJ2) ⟨Γ, ⊥, .bot⟩

/-- - [KO21, Theorem 7.1] -/
theorem ILMinusJ2.iff_valid_finite_verbrugge :
    ILMinusJ2 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Verbrugge.Model κ α),
      [M.IsILMinus] → [M.IsJ2] → M ⊧ A := by
  constructor;
  · intro h _ _ _ M;
    intros;
    exact ILMinusJ2.sound_verbrugge h;
  · exact ILMinusJ2.complete_verbrugge;

end Logic

end CompletenessVerbrugge


end FFL.InterpretabilityLogic

end
