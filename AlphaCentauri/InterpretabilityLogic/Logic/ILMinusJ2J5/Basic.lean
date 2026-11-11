module

public import AlphaCentauri.InterpretabilityLogic.Logic.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.ILMinus
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.ILMinusModel
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.Counterexamples
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinusJ2PlusJ5.Basic

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

namespace Verbrugge.Model

variable {κ α : Type*} [Nonempty κ] (M : Model κ α)

class IsILMinusJ2J5 : Prop extends M.IsILMinus, M.IsJ2, M.IsJ5

instance (priority := low) [M.IsILMinus] [M.IsJ2] [M.IsJ5] : M.IsILMinusJ2J5 := {}

end Verbrugge.Model

namespace Logic

/-! ## Completeness for Verbrugge models -/


open Entailment Formula MaximalConsistentSet Verbrugge Verbrugge.Model Verbrugge.Model.World

variable {α : Type} {A : Formula α}

/-- - [KO21, Theorem 7.4] -/
theorem ILMinusJ2J5.semantics_TFAE : [
    ILMinusJ2J5 ⊢ A,
    ∀ {κ : Type} [Nonempty κ] (M : Verbrugge.Model κ α),
      [M.IsILMinusJ2J5] → M ⊧ A,
    ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Verbrugge.Model κ α),
      [M.IsILMinusJ2J5] → M ⊧ A
  ].TFAE := by
  tfae_have 1 → 2 := by
    intro h _ _ M _;
    apply ofAxiomsMinus.sound_verbrugge _ h;
    rintro _ (⟨A, B, C, rfl⟩ | ⟨A, rfl⟩) x;
    · exact forces_axiomJ2;
    · exact forces_axiomJ5;
  tfae_have 2 → 3 := by
    intro h _ _ _ M _;
    exact h M;
  tfae_have 3 → 1 := by
    intro h;
    classical
    by_contra hA;
    obtain ⟨Γ, hΓ⟩ := exists_neg_consistent (Φ := ilMinusAdequateClosure {A}) hA;
    have : Nonempty (Veltman.IndexedSet ILMinusJ2J5 (ilMinusAdequateClosure {A})) :=
      ⟨⟨Γ, [], by simp, by simp⟩⟩;
    exact MaximalConsistentSet.not_mem_of_provable_neg hΓ (Context.by_axm rfl) <|
      (IndexedModel.truthlemma_condJ2J5 (x := ⟨Γ, [], by simp, by simp⟩)
        (ilMinusAdequateClosure.subset (by simp))).mp <|
          h (IndexedModel.model IndexedModel.condJ2J5) ⟨Γ, [], by simp, by simp⟩;
  tfae_finish;

theorem ILMinusJ2J5.iff_valid_verbrugge :
    ILMinusJ2J5 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] (M : Verbrugge.Model κ α),
      [M.IsILMinusJ2J5] → M ⊧ A :=
  ILMinusJ2J5.semantics_TFAE.out 1 2

theorem ILMinusJ2J5.sound_verbrugge {κ : Type} [Nonempty κ] {M : Verbrugge.Model κ α}
    [M.IsILMinusJ2J5] (h : ILMinusJ2J5 ⊢ A) : M ⊧ A :=
  ILMinusJ2J5.iff_valid_verbrugge.mp h M

/-- - [KO21, Theorem 7.4] -/
theorem ILMinusJ2J5.iff_valid_finite_verbrugge :
    ILMinusJ2J5 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Verbrugge.Model κ α),
      [M.IsILMinusJ2J5] → M ⊧ A :=
  ILMinusJ2J5.semantics_TFAE.out 1 3


/-! ## Incompleteness for Verbrugge models -/


open Entailment Verbrugge Veltman.Model.World

/-- - [KO21, Corollary 6.2] -/
theorem ILMinusJ2J5.incomplete : ∃ A : Formula ℕ,
    (∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ ℕ), [M.IsILMinusJ2PlusJ5] → M ⊧ A) ∧
      ILMinusJ2J5 ⊬ A := by
  use Axioms.J2Plus (#0) (#1) (#2);
  constructor;
  · intro κ _ M _ _;
    exact forces_axiomJ2Plus;
  · intro h;
    exact counterJ2Plus.not_models_J2Plus (ILMinusJ2J5.sound_verbrugge (M := counterJ2Plus) h);

end Logic


end FFL.InterpretabilityLogic

