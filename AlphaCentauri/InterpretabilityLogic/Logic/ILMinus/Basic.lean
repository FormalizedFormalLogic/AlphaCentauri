module

public import AlphaCentauri.InterpretabilityLogic.Logic.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.LabelledSetModel

/-!
# The logic $\mathbf{IL}^-$

Soundness of $\mathbf{IL}^-$ for Veltman models and its completeness for finite ones.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

namespace Logic

open Entailment Formula

variable {α : Type*}

/-- - [KO21, Definition 2.1] -/
abbrev ILMinus : Logic α := ofAxiomsMinus ∅

notation "𝐈𝐋⁻" => Logic.ILMinus

end Logic


section Semantics

namespace Logic

open Entailment Formula MaximalConsistentSet Veltman Veltman.Model Veltman.Model.World
open LabelledSet.Condition ofAxiomsMinus

variable {α : Type} {A : Formula α}

/-- - [KO21, Theorem 5.1] -/
theorem ILMinus.semantics_TFAE : [
    𝐈𝐋⁻ ⊢ A,
    ∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ α), [M.IsILMinus] → M ⊧ A,
    ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α), [M.IsILMinus] → M ⊧ A
  ].TFAE := by
  tfae_have 1 → 2 := by
    intro h _ _ M _;
    exact ofAxiomsMinus.sound (by simp) h;
  tfae_have 2 → 3 := by
    intro h _ _ _ M _;
    exact h M;
  tfae_have 3 → 1 := by
    intro h;
    classical
    exact provable_of_models_labelledModel .ILMinus (h _);
  tfae_finish;

theorem ILMinus.iff_valid :
    𝐈𝐋⁻ ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ α), [M.IsILMinus] → M ⊧ A :=
  ILMinus.semantics_TFAE.out 1 2

theorem ILMinus.sound {κ : Type} [Nonempty κ] {M : Veltman.Model κ α} [M.IsILMinus]
    (h : 𝐈𝐋⁻ ⊢ A) : M ⊧ A :=
  ILMinus.iff_valid.mp h M

instance : Entailment.Consistent (𝐈𝐋⁻ : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILMinus.sound (M := pointModel fun _ ↦ False) h 0

/-- - [KO21, Theorem 5.1] -/
theorem ILMinus.iff_valid_finite :
    𝐈𝐋⁻ ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → M ⊧ A :=
  ILMinus.semantics_TFAE.out 1 3

end Logic

end Semantics


end FFL.InterpretabilityLogic

end
