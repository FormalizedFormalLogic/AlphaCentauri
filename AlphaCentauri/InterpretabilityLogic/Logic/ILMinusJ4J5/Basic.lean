module

public import AlphaCentauri.InterpretabilityLogic.Logic.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.ILMinus
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.ILMinusModel
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.Counterexamples
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinusJ4PlusJ5.Basic

/-!
# Soundness and completeness of $\mathbf{IL}^-(\mathbf{J4}, \mathbf{J5})$
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula

variable {α : Type*}

/-- $\mathbf{IL}^-(\mathbf{J4}, \mathbf{J5})$.

- [KO21, §6]
-/
abbrev Logic.ILMinusJ4J5 : Logic α := ofAxiomsMinus ({Axioms.J4 A B | (A) (B)} ∪ {Axioms.J5 A | A})

namespace Verbrugge.Model

variable {κ α : Type*} [Nonempty κ] (M : Model κ α)

class IsILMinusJ4J5 : Prop extends M.IsILMinus, M.IsJ4, M.IsJ5

instance (priority := low) [M.IsILMinus] [M.IsJ4] [M.IsJ5] : M.IsILMinusJ4J5 := {}

end Verbrugge.Model

namespace Logic

/-! ## Completeness for Verbrugge models -/


open Entailment Formula MaximalConsistentSet Verbrugge Verbrugge.Model Verbrugge.Model.World

variable {α : Type} {A : Formula α}

/-- - [KO21, Theorem 7.1] -/
theorem ILMinusJ4J5.semantics_TFAE : [
    ILMinusJ4J5 ⊢ A,
    ∀ {κ : Type} [Nonempty κ] (M : Verbrugge.Model κ α),
      [M.IsILMinusJ4J5] → M ⊧ A,
    ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Verbrugge.Model κ α),
      [M.IsILMinusJ4J5] → M ⊧ A
  ].TFAE := by
  tfae_have 1 → 2 := by
    intro h _ _ M _;
    apply ofAxiomsMinus.sound_verbrugge _ h;
    rintro _ (⟨A, B, rfl⟩ | ⟨A, rfl⟩) x;
    · exact forces_axiomJ4;
    · exact forces_axiomJ5;
  tfae_have 2 → 3 := by
    intro h _ _ _ M _;
    exact h M;
  tfae_have 3 → 1 := by
    intro h;
    classical
    by_contra hA;
    obtain ⟨Γ, hΓ⟩ := exists_neg_consistent (Φ := ilMinusAdequateClosure {A}) hA;
    have : Nonempty (LabelledSet ILMinusJ4J5 (ilMinusAdequateClosure {A})) := ⟨⟨Γ, ⊥, .bot⟩⟩;
    exact MaximalConsistentSet.not_mem_of_provable_neg hΓ (Context.by_axm rfl) <|
      (LabelledSet.truthlemma_condJ4J5 (x := ⟨Γ, ⊥, .bot⟩)
        (ilMinusAdequateClosure.subset (by simp))).mp <|
          h (LabelledSet.model LabelledSet.condJ4J5) ⟨Γ, ⊥, .bot⟩;
  tfae_finish;

theorem ILMinusJ4J5.iff_valid_verbrugge :
    ILMinusJ4J5 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] (M : Verbrugge.Model κ α),
      [M.IsILMinusJ4J5] → M ⊧ A :=
  ILMinusJ4J5.semantics_TFAE.out 1 2

theorem ILMinusJ4J5.sound_verbrugge {κ : Type} [Nonempty κ] {M : Verbrugge.Model κ α}
    [M.IsILMinusJ4J5] (h : ILMinusJ4J5 ⊢ A) : M ⊧ A :=
  ILMinusJ4J5.iff_valid_verbrugge.mp h M

/-- - [KO21, Theorem 7.1] -/
theorem ILMinusJ4J5.iff_valid_finite_verbrugge :
    ILMinusJ4J5 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Verbrugge.Model κ α),
      [M.IsILMinusJ4J5] → M ⊧ A :=
  ILMinusJ4J5.semantics_TFAE.out 1 3


/-! ## Incompleteness for Verbrugge models -/


open Entailment Verbrugge Veltman.Model.World

/-- - [KO21, Corollary 6.4] -/
theorem ILMinusJ4J5.incomplete : ∃ A : Formula ℕ,
    (∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ ℕ), [M.IsILMinusJ4PlusJ5] → M ⊧ A) ∧
      ILMinusJ4J5 ⊬ A := by
  use Axioms.J4Plus (#1) (#2) (#0);
  constructor;
  · intro κ _ M _ _;
    exact forces_axiomJ4Plus;
  · intro h;
    exact counterJ4Plus.not_models_J4Plus (ILMinusJ4J5.sound_verbrugge (M := counterJ4Plus) h);

end Logic


end FFL.InterpretabilityLogic

