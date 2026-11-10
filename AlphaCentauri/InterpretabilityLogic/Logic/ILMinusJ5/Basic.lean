module

public import AlphaCentauri.InterpretabilityLogic.Logic.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinus.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.CL.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.LabelledSetModel

/-!
# Soundness and completeness of $\mathbf{IL}^-(\mathbf{J5})$
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

namespace Logic

open Entailment Formula

variable {α : Type*}

/-- $\mathbf{IL}^-(\mathbf{J5})$.

- [KO21, §3.4]
-/
abbrev ILMinusJ5 : Logic α := ofAxiomsMinus {Axioms.J5 A | A}

end Logic


section Completeness

namespace Logic

open Entailment Formula MaximalConsistentSet Veltman Veltman.Model Veltman.Model.World
open LabelledSet.Condition ofAxiomsMinus

variable {α : Type} {A : Formula α}

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ5.semantics_TFAE : [
    ILMinusJ5 ⊢ A,
    ∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ5] → M ⊧ A,
    ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ5] → M ⊧ A
  ].TFAE := by
  tfae_have 1 → 2 := by
    intro h _ _ M _ _;
    apply ofAxiomsMinus.sound _ h;
    rintro _ ⟨A, rfl⟩ x;
    exact forces_axiomJ5;
  tfae_have 2 → 3 := by
    intro h _ _ _ M _ _;
    exact h M;
  tfae_have 3 → 1 := by
    intro h;
    classical
    exact provable_of_models_labelledModel .J5 (h _);
  tfae_finish;

theorem ILMinusJ5.iff_valid :
    ILMinusJ5 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ5] → M ⊧ A :=
  ILMinusJ5.semantics_TFAE.out 1 2

theorem ILMinusJ5.sound {κ : Type} [Nonempty κ] {M : Veltman.Model κ α}
    [M.IsILMinus] [M.IsJ5] (h : ILMinusJ5 ⊢ A) : M ⊧ A :=
  ILMinusJ5.iff_valid.mp h M

instance : Entailment.Consistent (ILMinusJ5 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILMinusJ5.sound (M := pointModel fun _ ↦ False) h 0

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ5.iff_valid_finite :
    ILMinusJ5 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ5] → M ⊧ A :=
  ILMinusJ5.semantics_TFAE.out 1 3

end Logic

end Completeness



section Relations

namespace Logic

open Entailment

variable {α : Type}

instance : (𝐈𝐋⁻ : Logic α) ⪱ ILMinusJ5 :=
  .of_unprovable_provable unprovable_J5 (HasAxiomJ5.J5 _)

end Logic

end Relations

end FFL.InterpretabilityLogic

