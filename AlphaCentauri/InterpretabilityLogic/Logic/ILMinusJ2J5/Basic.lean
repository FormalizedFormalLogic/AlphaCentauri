module

public import AlphaCentauri.InterpretabilityLogic.Logic.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.ILMinus
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.ILMinusModel
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinusJ2J4PlusJ5.Basic

/-!
# Soundness and completeness of $\mathbf{IL}^-(\mathbf{J2}, \mathbf{J5})$
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

namespace Logic

open Entailment Formula

variable {α : Type*}

/-- $\mathbf{IL}^-(\mathbf{J2}, \mathbf{J5})$.

- [KO21, §6]
-/
abbrev ILMinusJ2J5 : Logic α := ofAxiomsMinus ({Axioms.J2 A B C | (A) (B) (C)} ∪ {Axioms.J5 A | A})

end Logic

section SoundnessVerbrugge

namespace Logic

open Verbrugge Verbrugge.Model Verbrugge.Model.World

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {A : Formula α}

theorem ILMinusJ2J5.sound_verbrugge [M.IsILMinus] [M.IsJ2] [M.IsJ5] :
    ILMinusJ2J5 ⊢ A → M ⊧ A :=
  ofAxiomsMinus.sound_verbrugge <| by
    rintro _ (⟨A, B, C, rfl⟩ | ⟨A, rfl⟩) x;
    · exact forces_axiomJ2;
    · exact forces_axiomJ5;

end Logic

end SoundnessVerbrugge

section CompletenessVerbrugge

namespace Logic

open Entailment Formula MaximalConsistentSet Verbrugge Verbrugge.Model

variable {α : Type} {A : Formula α}

/-- - [KO21, Theorem 7.4] -/
theorem ILMinusJ2J5.iff_valid_finite_verbrugge :
    ILMinusJ2J5 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Verbrugge.Model κ α),
      [M.IsILMinus] → [M.IsJ2] → [M.IsJ5] → M ⊧ A := by
  constructor;
  · intro h _ _ _ M;
    intros;
    exact ILMinusJ2J5.sound_verbrugge h;
  · intro h;
    classical
    by_contra hA;
    obtain ⟨Γ, hΓ⟩ := exists_neg_consistent (Φ := ilMinusAdequateClosure {A}) hA;
    have : Nonempty (Veltman.IndexedSet ILMinusJ2J5 (ilMinusAdequateClosure {A})) :=
      ⟨⟨Γ, [], by simp, by simp⟩⟩;
    exact MaximalConsistentSet.not_mem_of_provable_neg hΓ (Context.by_axm rfl) <|
      (IndexedModel.truthlemma_condJ2J5 (x := ⟨Γ, [], by simp, by simp⟩)
        (ilMinusAdequateClosure.subset (by simp))).mp <|
          h (IndexedModel.model IndexedModel.condJ2J5) ⟨Γ, [], by simp, by simp⟩

end Logic

end CompletenessVerbrugge



section IncompletenessVerbrugge

namespace Logic

open Entailment

/-- - [KO21, Corollary 6.2] -/
theorem ILMinusJ2J5.incomplete : ∃ A : Formula ℕ,
    (∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ ℕ),
      [M.IsILMinus] → [M.IsJ2] → [M.IsJ5] → M ⊧ A) ∧ ILMinusJ2J5 ⊬ A := by
  use Axioms.J2Plus (#0) (#1) (#2);
  constructor;
  · intro κ _ M _ _ _;
    exact valid_J2Plus M;
  · exact unprovable_J2Plus;

end Logic

end IncompletenessVerbrugge



end FFL.InterpretabilityLogic

