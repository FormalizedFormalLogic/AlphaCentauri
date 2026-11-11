module

public import AlphaCentauri.InterpretabilityLogic.Logic.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinus.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.Counterexamples
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.LabelledSetModel

/-!
# Soundness and completeness of $\mathbf{IL}^-(\mathbf{J4}^+)$
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

namespace Logic

open Entailment Formula

variable {α : Type*}

/-- $\mathbf{IL}^-(\mathbf{J4}^+)$.

- [KO21, §3.2]
-/
abbrev ILMinusJ4Plus : Logic α := ofAxiomsMinus {Axioms.J4Plus A B C | (A) (B) (C)}

end Logic

namespace Veltman.Model

variable {κ α : Type*} [Nonempty κ] (M : Model κ α)

class IsILMinusJ4Plus : Prop extends M.IsILMinus, M.IsJ4

instance (priority := low) [M.IsILMinus] [M.IsJ4] : M.IsILMinusJ4Plus := {}

end Veltman.Model

namespace Logic

/-! ## Completeness -/


open Entailment Formula MaximalConsistentSet Veltman Veltman.Model Veltman.Model.World
open LabelledSet.Condition ofAxiomsMinus

variable {α : Type} {A : Formula α}

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ4Plus.semantics_TFAE : [
    ILMinusJ4Plus ⊢ A,
    ∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ α),
      [M.IsILMinusJ4Plus] → M ⊧ A,
    ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinusJ4Plus] → M ⊧ A
  ].TFAE := by
  tfae_have 1 → 2 := by
    intro h _ _ M _;
    apply ofAxiomsMinus.sound _ h;
    rintro _ ⟨A, B, C, rfl⟩ x;
    exact forces_axiomJ4Plus;
  tfae_have 2 → 3 := by
    intro h _ _ _ M _;
    exact h M;
  tfae_have 3 → 1 := by
    intro h;
    classical
    exact provable_of_models_labelledModel .J4Plus (h _);
  tfae_finish;

theorem ILMinusJ4Plus.iff_valid :
    ILMinusJ4Plus ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ α),
      [M.IsILMinusJ4Plus] → M ⊧ A :=
  ILMinusJ4Plus.semantics_TFAE.out 1 2

theorem ILMinusJ4Plus.sound {κ : Type} [Nonempty κ] {M : Veltman.Model κ α}
    [M.IsILMinusJ4Plus] (h : ILMinusJ4Plus ⊢ A) : M ⊧ A :=
  ILMinusJ4Plus.iff_valid.mp h M

instance : Entailment.Consistent (ILMinusJ4Plus : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILMinusJ4Plus.sound (M := pointModel fun _ ↦ False) h 0

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ4Plus.iff_valid_finite :
    ILMinusJ4Plus ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinusJ4Plus] → M ⊧ A :=
  ILMinusJ4Plus.semantics_TFAE.out 1 3


/-! ## Equivalent axiomatizations -/


open Entailment ofAxiomsMinus

variable {α : Type*}

section J4Plus

private lemma J4Plus'_subset :
    (ofAxiomsMinus {Axioms.J4Plus' A B C | (A) (B) (C)} : Logic α) ⊆ ILMinusJ4Plus := by
  apply subset_of_provable;
  rintro _ ⟨A, B, C, rfl⟩;
  have h₁ : ILMinusJ4Plus ⊢ □A 🡒 □((A 🡒 B) 🡒 B) := box_mono (by cl_prover);
  have h₂ : ILMinusJ4Plus ⊢ □((A 🡒 B) 🡒 B) 🡒 C ▷ (A 🡒 B) 🡒 C ▷ B := HasAxiomJ4Plus.J4Plus _ _ _;
  cl_prover [h₁, h₂];

private lemma J4Plus''_subset :
    (ofAxiomsMinus {Axioms.J4Plus'' A B C | (A) (B) (C)} : Logic α) ⊆
      ofAxiomsMinus {Axioms.J4Plus' A B C | (A) (B) (C)} := by
  apply subset_of_provable;
  rintro _ ⟨A, B, C, rfl⟩;
  have h₁ : ofAxiomsMinus {Axioms.J4Plus' A B C | (A) (B) (C)} ⊢
      C ▷ B 🡒 C ▷ (A 🡒 A ⋏ B) := rhd_mono_right (by cl_prover);
  have h₂ : ofAxiomsMinus {Axioms.J4Plus' A B C | (A) (B) (C)} ⊢
      □A 🡒 C ▷ (A 🡒 A ⋏ B) 🡒 C ▷ (A ⋏ B) := axm (by simp);
  cl_prover [h₁, h₂];

private lemma J4Plus_subset :
    (ILMinusJ4Plus : Logic α) ⊆ ofAxiomsMinus {Axioms.J4Plus'' A B C | (A) (B) (C)} := by
  apply subset_of_provable;
  rintro _ ⟨A, B, C, rfl⟩;
  have h₁ : ofAxiomsMinus {Axioms.J4Plus'' A B C | (A) (B) (C)} ⊢
      □(A 🡒 B) 🡒 C ▷ A 🡒 C ▷ ((A 🡒 B) ⋏ A) := axm (by simp);
  have h₂ : ofAxiomsMinus {Axioms.J4Plus'' A B C | (A) (B) (C)} ⊢
      C ▷ ((A 🡒 B) ⋏ A) 🡒 C ▷ B := rhd_mono_right (by cl_prover);
  cl_prover [h₁, h₂];

/-- - [KO21, Proposition 3.6] -/
theorem ILMinusJ4Plus.eq_ofAxiomsMinus_J4Plus' :
    (ILMinusJ4Plus : Logic α) = ofAxiomsMinus {Axioms.J4Plus' A B C | (A) (B) (C)} :=
  Set.Subset.antisymm (J4Plus_subset.trans J4Plus''_subset) J4Plus'_subset

/-- - [KO21, Proposition 3.6] -/
theorem ILMinusJ4Plus.eq_ofAxiomsMinus_J4Plus'' :
    (ILMinusJ4Plus : Logic α) = ofAxiomsMinus {Axioms.J4Plus'' A B C | (A) (B) (C)} :=
  Set.Subset.antisymm J4Plus_subset (J4Plus''_subset.trans J4Plus'_subset)

end J4Plus

/-! ## Relations -/


open Entailment Veltman

variable {α : Type}

instance : (𝐈𝐋⁻ : Logic α) ⪱ ILMinusJ4Plus :=
  .of_unprovable_provable (φ := Axioms.J4Plus (◇⊤) ⊥ ⊤)
    (fun h ↦ counterJ4.not_models_J4Plus (ILMinus.sound (M := counterJ4 α) h))
    (HasAxiomJ4Plus.J4Plus _ _ _)

end Logic

end FFL.InterpretabilityLogic

