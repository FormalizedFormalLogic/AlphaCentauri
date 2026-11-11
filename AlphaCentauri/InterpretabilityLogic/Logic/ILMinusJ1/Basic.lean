module

public import AlphaCentauri.InterpretabilityLogic.Logic.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinus.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinusJ2PlusJ5.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.LabelledSetModel

/-!
# Soundness and completeness of $\mathbf{IL}^-(\mathbf{J1})$
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

namespace Logic

open Entailment Formula

variable {α : Type*}

/-- $\mathbf{IL}^-(\mathbf{J1})$.

- [KO21, §3.1]
-/
abbrev ILMinusJ1 : Logic α := ofAxiomsMinus {Axioms.J1 A B | (A) (B)}

end Logic

namespace Veltman.Model

variable {κ α : Type*} [Nonempty κ] (M : Model κ α)

class IsILMinusJ1 : Prop extends M.IsILMinus, M.IsJ1

instance (priority := low) [M.IsILMinus] [M.IsJ1] : M.IsILMinusJ1 := {}

end Veltman.Model

namespace Logic

/-! ## Completeness -/


open Entailment Formula MaximalConsistentSet Veltman Veltman.Model Veltman.Model.World
open LabelledSet.Condition ofAxiomsMinus

variable {α : Type} {A : Formula α}

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ1.semantics_TFAE : [
    ILMinusJ1 ⊢ A,
    ∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ α),
      [M.IsILMinusJ1] → M ⊧ A,
    ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinusJ1] → M ⊧ A
  ].TFAE := by
  tfae_have 1 → 2 := by
    intro h _ _ M _;
    apply ofAxiomsMinus.sound _ h;
    rintro _ ⟨A, B, rfl⟩ x;
    exact forces_axiomJ1;
  tfae_have 2 → 3 := by
    intro h _ _ _ M _;
    exact h M;
  tfae_have 3 → 1 := by
    intro h;
    classical
    exact provable_of_models_labelledModel .ILMinus (h _);
  tfae_finish;

theorem ILMinusJ1.iff_valid :
    ILMinusJ1 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ α),
      [M.IsILMinusJ1] → M ⊧ A :=
  ILMinusJ1.semantics_TFAE.out 1 2

theorem ILMinusJ1.sound {κ : Type} [Nonempty κ] {M : Veltman.Model κ α}
    [M.IsILMinusJ1] (h : ILMinusJ1 ⊢ A) : M ⊧ A :=
  ILMinusJ1.iff_valid.mp h M

instance : Entailment.Consistent (ILMinusJ1 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILMinusJ1.sound (M := pointModel fun _ ↦ False) h 0

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ1.iff_valid_finite :
    ILMinusJ1 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinusJ1] → M ⊧ A :=
  ILMinusJ1.semantics_TFAE.out 1 3


/-! ## Equivalent axiomatizations -/


open Entailment ofAxiomsMinus

variable {α : Type*}

/-- - [KO21, Proposition 3.1] -/
theorem ILMinusJ1.eq_ofAxiomsMinus_J1' :
    (ILMinusJ1 : Logic α) = ofAxiomsMinus {Axioms.J1' A | A} := by
  apply Set.Subset.antisymm;
  · apply subset_of_provable;
    rintro _ ⟨A, B, rfl⟩;
    have h₁ : ofAxiomsMinus {Axioms.J1' A | A} ⊢ □(A 🡒 B) 🡒 B ▷ B 🡒 A ▷ B :=
      rhd_anti_left_of_box;
    have h₂ : ofAxiomsMinus {Axioms.J1' A | A} ⊢ B ▷ B := axm (by simp);
    cl_prover [h₁, h₂];
  · apply subset_of_provable;
    rintro _ ⟨A, rfl⟩;
    exact axiomJ1';

/-! ## Relations -/


open Entailment

variable {α : Type}

instance : (𝐈𝐋⁻ : Logic α) ⪱ ILMinusJ1 :=
  .of_unprovable_provable unprovable_J1 (HasAxiomJ1.J1 _ _)

end Logic

end FFL.InterpretabilityLogic

