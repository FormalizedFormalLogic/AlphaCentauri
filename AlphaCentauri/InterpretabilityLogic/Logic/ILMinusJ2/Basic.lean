module

public import AlphaCentauri.InterpretabilityLogic.Logic.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.ILMinus
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.ILMinusModel
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.Counterexamples
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinusJ2Plus.Basic

/-!
# Soundness and completeness of $\mathbf{IL}^-(\mathbf{J2})$
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula

variable {α : Type*}

/-- $\mathbf{IL}^-(\mathbf{J2})$.

- [KO21, §3.3]
-/
abbrev Logic.ILMinusJ2 : Logic α := ofAxiomsMinus {Axioms.J2 A B C | (A) (B) (C)}

namespace Verbrugge.Model

variable {κ α : Type*} [Nonempty κ] (M : Model κ α)

class IsILMinusJ2 : Prop extends M.IsILMinus, M.IsJ2

instance (priority := low) [M.IsILMinus] [M.IsJ2] : M.IsILMinusJ2 := {}

end Verbrugge.Model

namespace Logic

/-! ## Soundness -/


open Veltman Veltman.Model.World in
theorem ILMinusJ2.sound {κ : Type*} [Nonempty κ] {M : Veltman.Model κ α} {A : Formula α}
    [M.IsILMinusJ2Plus] : ILMinusJ2 ⊢ A → M ⊧ A :=
  ofAxiomsMinus.sound <| by
    rintro _ ⟨A, B, C, rfl⟩ x;
    exact forces_axiomJ2

open Veltman.Model in
instance : Entailment.Consistent (ILMinusJ2 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILMinusJ2.sound (M := pointModel fun _ ↦ False) h 0

/-! ## Completeness for Verbrugge models -/

open Entailment Formula MaximalConsistentSet Verbrugge Verbrugge.Model Verbrugge.Model.World

variable {α : Type} {A : Formula α}

/-- - [KO21, Theorem 7.1] -/
theorem ILMinusJ2.semantics_TFAE : [
    ILMinusJ2 ⊢ A,
    ∀ {κ : Type} [Nonempty κ] (M : Verbrugge.Model κ α),
      [M.IsILMinusJ2] → M ⊧ A,
    ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Verbrugge.Model κ α),
      [M.IsILMinusJ2] → M ⊧ A
  ].TFAE := by
  tfae_have 1 → 2 := by
    intro h _ _ M _;
    apply ofAxiomsMinus.sound_verbrugge _ h;
    rintro _ ⟨A, B, C, rfl⟩ x;
    exact forces_axiomJ2;
  tfae_have 2 → 3 := by
    intro h _ _ _ M _;
    exact h M;
  tfae_have 3 → 1 := by
    intro h;
    classical
    by_contra hA;
    obtain ⟨Γ, hΓ⟩ := exists_neg_consistent (Φ := ilMinusAdequateClosure {A}) hA;
    have : Nonempty (LabelledSet ILMinusJ2 (ilMinusAdequateClosure {A})) := ⟨⟨Γ, ⊥, .bot⟩⟩;
    exact MaximalConsistentSet.not_mem_of_provable_neg hΓ (Context.by_axm rfl) <|
      (LabelledSet.truthlemma_condJ2 (x := ⟨Γ, ⊥, .bot⟩)
        (ilMinusAdequateClosure.subset (by simp))).mp <|
          h (LabelledSet.model LabelledSet.condJ2) ⟨Γ, ⊥, .bot⟩;
  tfae_finish;

theorem ILMinusJ2.iff_valid_verbrugge :
    ILMinusJ2 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] (M : Verbrugge.Model κ α),
      [M.IsILMinusJ2] → M ⊧ A :=
  ILMinusJ2.semantics_TFAE.out 1 2

theorem ILMinusJ2.sound_verbrugge {κ : Type} [Nonempty κ] {M : Verbrugge.Model κ α}
    [M.IsILMinusJ2] (h : ILMinusJ2 ⊢ A) : M ⊧ A :=
  ILMinusJ2.iff_valid_verbrugge.mp h M

/-- - [KO21, Theorem 7.1] -/
theorem ILMinusJ2.iff_valid_finite_verbrugge :
    ILMinusJ2 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Verbrugge.Model κ α),
      [M.IsILMinusJ2] → M ⊧ A :=
  ILMinusJ2.semantics_TFAE.out 1 3


/-! ## Incompleteness for Verbrugge models -/


open Entailment Verbrugge Veltman.Model.World

/-- - [KO21, Corollary 6.2] -/
theorem ILMinusJ2.incomplete : ∃ A : Formula ℕ,
    (∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ ℕ), [M.IsILMinusJ2Plus] → M ⊧ A) ∧
      ILMinusJ2 ⊬ A := by
  use Axioms.J2Plus (#0) (#1) (#2);
  constructor;
  · intro κ _ M _ _;
    exact forces_axiomJ2Plus;
  · intro h;
    exact counterJ2Plus.not_models_J2Plus (ILMinusJ2.sound_verbrugge (M := counterJ2Plus) h);

end Logic


end FFL.InterpretabilityLogic

