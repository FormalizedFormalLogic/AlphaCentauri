module

public import AlphaCentauri.InterpretabilityLogic.Logic.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.ILMinus
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.ILMinusModel
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.Counterexamples
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinusJ1J4Plus.Basic

/-!
# Soundness and completeness of $\mathbf{IL}^-(\mathbf{J1}, \mathbf{J4})$
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

namespace Logic

open Entailment Formula

variable {α : Type*}

/-- $\mathbf{IL}^-(\mathbf{J1}, \mathbf{J4})$.

- [KO21, §6]
-/
abbrev ILMinusJ1J4 : Logic α :=
  ofAxiomsMinus ({Axioms.J1 A B | (A) (B)} ∪ {Axioms.J4 A B | (A) (B)})

end Logic

namespace Verbrugge.Model

variable {κ α : Type*} [Nonempty κ] (M : Model κ α)

class IsILMinusJ1J4 : Prop extends M.IsILMinus, M.IsJ1, M.IsJ4

instance (priority := low) [M.IsILMinus] [M.IsJ1] [M.IsJ4] : M.IsILMinusJ1J4 := {}

end Verbrugge.Model

namespace Logic

/-! ## Completeness for Verbrugge models -/


open Entailment Formula MaximalConsistentSet Verbrugge Verbrugge.Model Verbrugge.Model.World

variable {α : Type} {A : Formula α}

/-- - [KO21, Theorem 7.1] -/
theorem ILMinusJ1J4.semantics_TFAE : [
    ILMinusJ1J4 ⊢ A,
    ∀ {κ : Type} [Nonempty κ] (M : Verbrugge.Model κ α),
      [M.IsILMinusJ1J4] → M ⊧ A,
    ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Verbrugge.Model κ α),
      [M.IsILMinusJ1J4] → M ⊧ A
  ].TFAE := by
  tfae_have 1 → 2 := by
    intro h _ _ M _;
    apply ofAxiomsMinus.sound_verbrugge _ h;
    rintro _ (⟨A, B, rfl⟩ | ⟨A, B, rfl⟩) x;
    · exact forces_axiomJ1;
    · exact forces_axiomJ4;
  tfae_have 2 → 3 := by
    intro h _ _ _ M _;
    exact h M;
  tfae_have 3 → 1 := by
    intro h;
    classical
    by_contra hA;
    obtain ⟨Γ, hΓ⟩ := exists_neg_consistent (Φ := ilMinusAdequateClosure {A}) hA;
    have : Nonempty (LabelledSet ILMinusJ1J4 (ilMinusAdequateClosure {A})) := ⟨⟨Γ, ⊥, .bot⟩⟩;
    exact MaximalConsistentSet.not_mem_of_provable_neg hΓ (Context.by_axm rfl) <|
      (LabelledSet.truthlemma_condJ4 (x := ⟨Γ, ⊥, .bot⟩)
        (ilMinusAdequateClosure.subset (by simp))).mp <|
          h (LabelledSet.model LabelledSet.condJ4) ⟨Γ, ⊥, .bot⟩;
  tfae_finish;

theorem ILMinusJ1J4.iff_valid_verbrugge :
    ILMinusJ1J4 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] (M : Verbrugge.Model κ α),
      [M.IsILMinusJ1J4] → M ⊧ A :=
  ILMinusJ1J4.semantics_TFAE.out 1 2

theorem ILMinusJ1J4.sound_verbrugge {κ : Type} [Nonempty κ] {M : Verbrugge.Model κ α}
    [M.IsILMinusJ1J4] (h : ILMinusJ1J4 ⊢ A) : M ⊧ A :=
  ILMinusJ1J4.iff_valid_verbrugge.mp h M

/-- - [KO21, Theorem 7.1] -/
theorem ILMinusJ1J4.iff_valid_finite_verbrugge :
    ILMinusJ1J4 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Verbrugge.Model κ α),
      [M.IsILMinusJ1J4] → M ⊧ A :=
  ILMinusJ1J4.semantics_TFAE.out 1 3


/-! ## Incompleteness for Verbrugge models -/


open Entailment Verbrugge Veltman.Model.World

/-- - [KO21, Corollary 6.4] -/
theorem ILMinusJ1J4.incomplete : ∃ A : Formula ℕ,
    (∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ ℕ), [M.IsILMinusJ1J4Plus] → M ⊧ A) ∧
      ILMinusJ1J4 ⊬ A := by
  use Axioms.J4Plus (#1) (#2) (#0);
  constructor;
  · intro κ _ M _ _;
    exact forces_axiomJ4Plus;
  · intro h;
    exact counterJ4Plus.not_models_J4Plus (ILMinusJ1J4.sound_verbrugge (M := counterJ4Plus) h);

end Logic


end FFL.InterpretabilityLogic

