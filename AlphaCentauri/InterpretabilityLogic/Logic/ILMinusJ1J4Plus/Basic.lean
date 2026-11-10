module

public import AlphaCentauri.InterpretabilityLogic.Logic.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinusJ2PlusJ5.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinusJ1J5.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinusJ4Plus.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinusJ1.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.LabelledSetModel

/-!
# Soundness and completeness of $\mathbf{IL}^-(\mathbf{J1}, \mathbf{J4}^+)$
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

namespace Logic

open Entailment Formula

variable {α : Type*}

/-- $\mathbf{IL}^-(\mathbf{J1}, \mathbf{J4}^+)$.

- [KO21, §3]
-/
abbrev ILMinusJ1J4Plus : Logic α :=
  ofAxiomsMinus ({Axioms.J1 A B | (A) (B)} ∪ {Axioms.J4Plus A B C | (A) (B) (C)})


/-! ## Completeness -/


open Entailment Formula MaximalConsistentSet Veltman Veltman.Model Veltman.Model.World
open LabelledSet.Condition ofAxiomsMinus

variable {α : Type} {A : Formula α}

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ1J4Plus.semantics_TFAE : [
    ILMinusJ1J4Plus ⊢ A,
    ∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ1] → [M.IsJ4] → M ⊧ A,
    ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ1] → [M.IsJ4] → M ⊧ A
  ].TFAE := by
  tfae_have 1 → 2 := by
    intro h _ _ M _ _ _;
    apply ofAxiomsMinus.sound _ h;
    rintro _ (⟨A, B, rfl⟩ | ⟨A, B, C, rfl⟩) x;
    · exact forces_axiomJ1;
    · exact forces_axiomJ4Plus;
  tfae_have 2 → 3 := by
    intro h _ _ _ M _ _ _;
    exact h M;
  tfae_have 3 → 1 := by
    intro h;
    classical
    exact provable_of_models_labelledModel .J4Plus (h _);
  tfae_finish;

theorem ILMinusJ1J4Plus.iff_valid :
    ILMinusJ1J4Plus ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ1] → [M.IsJ4] → M ⊧ A :=
  ILMinusJ1J4Plus.semantics_TFAE.out 1 2

theorem ILMinusJ1J4Plus.sound {κ : Type} [Nonempty κ] {M : Veltman.Model κ α}
    [M.IsILMinus] [M.IsJ1] [M.IsJ4] (h : ILMinusJ1J4Plus ⊢ A) : M ⊧ A :=
  ILMinusJ1J4Plus.iff_valid.mp h M

instance : Entailment.Consistent (ILMinusJ1J4Plus : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILMinusJ1J4Plus.sound (M := pointModel fun _ ↦ False) h 0

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ1J4Plus.iff_valid_finite :
    ILMinusJ1J4Plus ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ1] → [M.IsJ4] → M ⊧ A :=
  ILMinusJ1J4Plus.semantics_TFAE.out 1 3


/-! ## Relations -/


open Entailment

variable {α : Type}

instance : (ILMinusJ1 : Logic α) ⪱ ILMinusJ1J4Plus :=
  .of_unprovable_provable ILMinusJ1J5.unprovable_J4Plus (HasAxiomJ4Plus.J4Plus _ _ _)

instance : (ILMinusJ4Plus : Logic α) ⪱ ILMinusJ1J4Plus :=
  .of_unprovable_provable unprovable_J1 (HasAxiomJ1.J1 _ _)

end Logic

end FFL.InterpretabilityLogic

