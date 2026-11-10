module

public import AlphaCentauri.InterpretabilityLogic.Logic.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.ILMinus
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.ILMinusModel
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinusJ2J4PlusJ5.Basic

/-!
# Soundness and completeness of $\mathbf{IL}^-(\mathbf{J2}, \mathbf{J4}^+)$
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

namespace Logic

open Entailment Formula

variable {α : Type*}

/-- $\mathbf{IL}^-(\mathbf{J2}, \mathbf{J4}^+)$.

- [KO21, §6]
-/
abbrev ILMinusJ2J4Plus : Logic α :=
  ofAxiomsMinus ({Axioms.J2 A B C | (A) (B) (C)} ∪ {Axioms.J4Plus A B C | (A) (B) (C)})

/-! ## Completeness for Verbrugge models -/


open Entailment Formula MaximalConsistentSet Verbrugge Verbrugge.Model Verbrugge.Model.World

variable {α : Type} {A : Formula α}

/-- - [KO21, Theorem 7.1] -/
theorem ILMinusJ2J4Plus.semantics_TFAE : [
    ILMinusJ2J4Plus ⊢ A,
    ∀ {κ : Type} [Nonempty κ] (M : Verbrugge.Model κ α),
      [M.IsILMinus] → [M.IsJ2] → [M.IsJ4Plus] → M ⊧ A,
    ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Verbrugge.Model κ α),
      [M.IsILMinus] → [M.IsJ2] → [M.IsJ4Plus] → M ⊧ A
  ].TFAE := by
  tfae_have 1 → 2 := by
    intro h _ _ M _ _ _;
    apply ofAxiomsMinus.sound_verbrugge _ h;
    rintro _ (⟨A, B, C, rfl⟩ | ⟨A, B, C, rfl⟩) x;
    · exact forces_axiomJ2;
    · exact forces_axiomJ4Plus;
  tfae_have 2 → 3 := by
    intro h _ _ _ M _ _ _;
    exact h M;
  tfae_have 3 → 1 := by
    intro h;
    classical
    by_contra hA;
    obtain ⟨Γ, hΓ⟩ := exists_neg_consistent (Φ := ilMinusAdequateClosure {A}) hA;
    have : Nonempty (LabelledSet ILMinusJ2J4Plus (ilMinusAdequateClosure {A})) := ⟨⟨Γ, ⊥, .bot⟩⟩;
    exact MaximalConsistentSet.not_mem_of_provable_neg hΓ (Context.by_axm rfl) <|
      (LabelledSet.truthlemma_condJ2J4Plus (x := ⟨Γ, ⊥, .bot⟩)
        (ilMinusAdequateClosure.subset (by simp))).mp <|
          h (LabelledSet.model LabelledSet.condJ2J4Plus) ⟨Γ, ⊥, .bot⟩;
  tfae_finish;

theorem ILMinusJ2J4Plus.iff_valid_verbrugge :
    ILMinusJ2J4Plus ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] (M : Verbrugge.Model κ α),
      [M.IsILMinus] → [M.IsJ2] → [M.IsJ4Plus] → M ⊧ A :=
  ILMinusJ2J4Plus.semantics_TFAE.out 1 2

theorem ILMinusJ2J4Plus.sound_verbrugge {κ : Type} [Nonempty κ] {M : Verbrugge.Model κ α}
    [M.IsILMinus] [M.IsJ2] [M.IsJ4Plus] (h : ILMinusJ2J4Plus ⊢ A) : M ⊧ A :=
  ILMinusJ2J4Plus.iff_valid_verbrugge.mp h M

/-- - [KO21, Theorem 7.1] -/
theorem ILMinusJ2J4Plus.iff_valid_finite_verbrugge :
    ILMinusJ2J4Plus ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Verbrugge.Model κ α),
      [M.IsILMinus] → [M.IsJ2] → [M.IsJ4Plus] → M ⊧ A :=
  ILMinusJ2J4Plus.semantics_TFAE.out 1 3


/-! ## Incompleteness for Verbrugge models -/


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


end FFL.InterpretabilityLogic

