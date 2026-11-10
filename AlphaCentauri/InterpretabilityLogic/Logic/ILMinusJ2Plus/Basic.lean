module

public import AlphaCentauri.InterpretabilityLogic.Logic.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.LabelledSetModel

/-!
# Soundness and completeness of $\mathbf{IL}^-(\mathbf{J2}^+)$
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

namespace Logic

open Entailment Formula

variable {α : Type*}

/-- $\mathbf{IL}^-(\mathbf{J2}^+)$.

- [KO21, §3.3]
-/
abbrev ILMinusJ2Plus : Logic α := ofAxiomsMinus {Axioms.J2Plus A B C | (A) (B) (C)}


/-! ## Completeness -/


open Entailment Formula MaximalConsistentSet Veltman Veltman.Model Veltman.Model.World
open LabelledSet.Condition ofAxiomsMinus

variable {α : Type} {A : Formula α}

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ2Plus.semantics_TFAE : [
    ILMinusJ2Plus ⊢ A,
    ∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ2] → M ⊧ A,
    ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ2] → M ⊧ A
  ].TFAE := by
  tfae_have 1 → 2 := by
    intro h _ _ M _ _;
    apply ofAxiomsMinus.sound _ h;
    rintro _ ⟨A, B, C, rfl⟩ x;
    exact forces_axiomJ2Plus;
  tfae_have 2 → 3 := by
    intro h _ _ _ M _ _;
    exact h M;
  tfae_have 3 → 1 := by
    intro h;
    classical
    exact provable_of_models_labelledModel .J2Plus (h _);
  tfae_finish;

theorem ILMinusJ2Plus.iff_valid :
    ILMinusJ2Plus ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ2] → M ⊧ A :=
  ILMinusJ2Plus.semantics_TFAE.out 1 2

theorem ILMinusJ2Plus.sound {κ : Type} [Nonempty κ] {M : Veltman.Model κ α}
    [M.IsILMinus] [M.IsJ2] (h : ILMinusJ2Plus ⊢ A) : M ⊧ A :=
  ILMinusJ2Plus.iff_valid.mp h M

instance : Entailment.Consistent (ILMinusJ2Plus : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILMinusJ2Plus.sound (M := pointModel fun _ ↦ False) h 0

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ2Plus.iff_valid_finite :
    ILMinusJ2Plus ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ2] → M ⊧ A :=
  ILMinusJ2Plus.semantics_TFAE.out 1 3


/-! ## Equivalent axiomatizations -/


open Entailment ofAxiomsMinus

variable {α : Type*}

/-- - [KO21, Proposition 3.11] -/
theorem ILMinusJ2Plus.eq_ofAxiomsMinus_J2Plus' :
    (ILMinusJ2Plus : Logic α) = ofAxiomsMinus {Axioms.J2Plus' A B C | (A) (B) (C)} := by
  apply Set.Subset.antisymm;
  · apply subset_of_provable;
    rintro _ ⟨A, B, C, rfl⟩;
    have h₁ : ofAxiomsMinus {Axioms.J2Plus' A B C | (A) (B) (C)} ⊢
        B ▷ C 🡒 ((B ⋎ C) ⋏ ∼C) ▷ C := rhd_anti_left (by cl_prover);
    have h₂ : ofAxiomsMinus {Axioms.J2Plus' A B C | (A) (B) (C)} ⊢
        A ▷ (B ⋎ C) ⋏ ((B ⋎ C) ⋏ ∼C) ▷ C 🡒 A ▷ C := axm (by simp);
    cl_prover [h₁, h₂];
  · apply subset_of_provable;
    rintro _ ⟨A, B, C, rfl⟩;
    have h₁ : ILMinusJ2Plus ⊢ A ▷ B 🡒 A ▷ (B ⋏ ∼C ⋎ C) := rhd_mono_right (by cl_prover);
    have h₂ : ILMinusJ2Plus ⊢ A ▷ (B ⋏ ∼C ⋎ C) ⋏ (B ⋏ ∼C) ▷ C 🡒 A ▷ C :=
      HasAxiomJ2Plus.J2Plus _ _ _;
    cl_prover [h₁, h₂];

end Logic

end FFL.InterpretabilityLogic

