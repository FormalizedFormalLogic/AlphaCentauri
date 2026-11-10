module

public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinus.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.ILMinus
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.ILMinusModel
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinusJ2J4PlusJ5.Basic

/-!
# Soundness and completeness of $\mathbf{IL}^-(\mathbf{J2}, \mathbf{J4}^+)$
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

section SoundnessVerbrugge

namespace Logic

open Verbrugge Verbrugge.Model Verbrugge.Model.World

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {A : Formula α}

theorem ILMinusJ2J4Plus.sound_verbrugge [M.IsILMinus] [M.IsJ2] [M.IsJ4Plus] :
    ILMinusJ2J4Plus ⊢ A → M ⊧ A :=
  ofAxiomsMinus.sound_verbrugge <| by
    rintro _ (⟨A, B, C, rfl⟩ | ⟨A, B, C, rfl⟩) x;
    · exact forces_axiomJ2;
    · exact forces_axiomJ4Plus;

end Logic

end SoundnessVerbrugge

section CompletenessVerbrugge

namespace Logic

open Entailment Formula MaximalConsistentSet Verbrugge Verbrugge.Model

variable {α : Type} {A : Formula α}

/-- - [KO21, Theorem 7.1] -/
theorem ILMinusJ2J4Plus.iff_valid_finite_verbrugge :
    ILMinusJ2J4Plus ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Verbrugge.Model κ α),
      [M.IsILMinus] → [M.IsJ2] → [M.IsJ4Plus] → M ⊧ A := by
  constructor;
  · intro h _ _ _ M;
    intros;
    exact ILMinusJ2J4Plus.sound_verbrugge h;
  · intro h;
    classical
    by_contra hA;
    obtain ⟨Γ, hΓ⟩ := exists_neg_consistent (Φ := ilMinusAdequateClosure {A}) hA;
    have : Nonempty (LabelledSet ILMinusJ2J4Plus (ilMinusAdequateClosure {A})) := ⟨⟨Γ, ⊥, .bot⟩⟩;
    exact MaximalConsistentSet.not_mem_of_provable_neg hΓ (Context.by_axm rfl) <|
      (LabelledSet.truthlemma_condJ2J4Plus (x := ⟨Γ, ⊥, .bot⟩)
        (ilMinusAdequateClosure.subset (by simp))).mp <|
          h (LabelledSet.model LabelledSet.condJ2J4Plus) ⟨Γ, ⊥, .bot⟩

end Logic

end CompletenessVerbrugge



section IncompletenessVerbrugge

namespace Logic

open Entailment

/-- - [KO21, Corollary 6.2] -/
theorem ILMinusJ2J4Plus.incomplete : ∃ A : Formula ℕ,
    (∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ ℕ), [M.IsILMinus] → [M.IsJ2] → M ⊧ A) ∧
      ILMinusJ2J4Plus ⊬ A := by
  use Axioms.J2Plus (#0) (#1) (#2);
  constructor;
  · intro κ _ M _ _;
    exact valid_J2Plus M;
  · exact unprovable_J2Plus;

end Logic

end IncompletenessVerbrugge



end FFL.InterpretabilityLogic

