module

public import AlphaCentauri.InterpretabilityLogic.Logic.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.LabelledSetModel

/-!
# Soundness and completeness of $\mathbf{CL}$
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula

variable {α : Type*}

/-- - [KO21, Proposition 3.21] -/
abbrev Logic.CL : Logic α := Logic.ofCLAxioms ∅

notation "𝐂𝐋" => Logic.CL

namespace Logic

/-! ## Completeness -/

open Entailment Formula MaximalConsistentSet Veltman Veltman.Model Veltman.Model.World
open LabelledSet.Condition

variable {α : Type} {A : Formula α}

/-- - [KO21, Theorem 5.1] -/
theorem CL.semantics_TFAE : [
    𝐂𝐋 ⊢ A,
    ∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ α),
      [M.IsCL] → M ⊧ A,
    ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsCL] → M ⊧ A
  ].TFAE := by
  tfae_have 1 → 2 := by
    intro h _ _ M _;
    exact ofCLAxioms.sound (by simp) h;
  tfae_have 2 → 3 := by
    intro h _ _ _ M _;
    exact h M;
  tfae_have 3 → 1 := by
    intro h;
    classical
    exact ofCLAxioms.provable_of_models_labelledModel .J2Plus (h _);
  tfae_finish;

theorem CL.iff_valid :
    𝐂𝐋 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ α),
      [M.IsCL] → M ⊧ A :=
  CL.semantics_TFAE.out 1 2

theorem CL.sound {κ : Type} [Nonempty κ] {M : Veltman.Model κ α}
    [M.IsCL] (h : 𝐂𝐋 ⊢ A) : M ⊧ A :=
  CL.iff_valid.mp h M

instance : Entailment.Consistent (𝐂𝐋 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ CL.sound (M := pointModel fun _ ↦ False) h 0

/-- - [KO21, Theorem 5.1] -/
theorem CL.iff_valid_finite :
    𝐂𝐋 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsCL] → M ⊧ A :=
  CL.semantics_TFAE.out 1 3

end Logic

end FFL.InterpretabilityLogic

