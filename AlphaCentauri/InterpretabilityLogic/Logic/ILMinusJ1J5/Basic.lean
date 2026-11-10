module

public import AlphaCentauri.InterpretabilityLogic.Logic.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinusJ2PlusJ5.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinusJ5.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinusJ1.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.CL.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.LabelledSetModel

/-!
# Soundness and completeness of $\mathbf{IL}^-(\mathbf{J1}, \mathbf{J5})$
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

namespace Logic

open Entailment Formula

variable {α : Type*}

/-- $\mathbf{IL}^-(\mathbf{J1}, \mathbf{J5})$.

- [KO21, §3]
-/
abbrev ILMinusJ1J5 : Logic α := ofAxiomsMinus ({Axioms.J1 A B | (A) (B)} ∪ {Axioms.J5 A | A})


/-! ## Completeness -/


open Entailment Formula MaximalConsistentSet Veltman Veltman.Model Veltman.Model.World
open LabelledSet.Condition ofAxiomsMinus

variable {α : Type} {A : Formula α}

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ1J5.semantics_TFAE : [
    ILMinusJ1J5 ⊢ A,
    ∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ1] → [M.IsJ5] → M ⊧ A,
    ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ1] → [M.IsJ5] → M ⊧ A
  ].TFAE := by
  tfae_have 1 → 2 := by
    intro h _ _ M _ _ _;
    apply ofAxiomsMinus.sound _ h;
    rintro _ (⟨A, B, rfl⟩ | ⟨A, rfl⟩) x;
    · exact forces_axiomJ1;
    · exact forces_axiomJ5;
  tfae_have 2 → 3 := by
    intro h _ _ _ M _ _ _;
    exact h M;
  tfae_have 3 → 1 := by
    intro h;
    classical
    exact provable_of_models_labelledModel .J5 (h _);
  tfae_finish;

theorem ILMinusJ1J5.iff_valid :
    ILMinusJ1J5 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ1] → [M.IsJ5] → M ⊧ A :=
  ILMinusJ1J5.semantics_TFAE.out 1 2

theorem ILMinusJ1J5.sound {κ : Type} [Nonempty κ] {M : Veltman.Model κ α}
    [M.IsILMinus] [M.IsJ1] [M.IsJ5] (h : ILMinusJ1J5 ⊢ A) : M ⊧ A :=
  ILMinusJ1J5.iff_valid.mp h M

instance : Entailment.Consistent (ILMinusJ1J5 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILMinusJ1J5.sound (M := pointModel fun _ ↦ False) h 0

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ1J5.iff_valid_finite :
    ILMinusJ1J5 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ1] → [M.IsJ5] → M ⊧ A :=
  ILMinusJ1J5.semantics_TFAE.out 1 3


/-! ## Incompleteness for Veltman models -/


open Veltman Veltman.Model Veltman.Model.World Entailment ofAxiomsMinus

variable {α : Type} {L : Logic α}

private abbrev counterJ4 (α : Type*) : Model (Fin 3) α :=
  ⟨(· < ·), fun w x _ ↦ w < x, fun _ _ ↦ False⟩

private instance : (counterJ4 α).IsILMinus where
  trans := by omega
  cwf := Finite.converseWellFounded_of_trans_of_irrefl
  rel_of_s_left := by tauto

private instance : (counterJ4 α).IsJ1 := ⟨by tauto⟩

private instance : (counterJ4 α).IsJ5 := ⟨by tauto⟩

lemma ILMinusJ1J5.unprovable_J4Plus [L ⪯ ILMinusJ1J5] : L ⊬ Axioms.J4Plus (◇⊤) ⊥ ⊤ := by
  intro h;
  replace h := WeakerThan.pbl (𝓣 := ILMinusJ1J5) h;
  have h₁ : (1 : Fin 3) ⊩[counterJ4 α] □(◇⊤ 🡒 ⊥) := by
    intro y Rxy hy;
    obtain ⟨z, Ryz, -⟩ := forces_dia.mp hy;
    omega;
  have h₂ : (1 : Fin 3) ⊩[counterJ4 α] ⊤ ▷ ◇⊤ := by
    intro y Rxy _
    exact ⟨0, Rxy, forces_dia.mpr ⟨1, by omega, forces_top⟩⟩
  obtain ⟨z, -, hz⟩ := ILMinusJ1J5.sound (M := counterJ4 α) h 1 h₁ h₂ 2 (by omega) forces_top;
  exact hz;


/-! ## Relations -/


open Entailment

variable {α : Type}

instance : (ILMinusJ1 : Logic α) ⪱ ILMinusJ1J5 :=
  .of_unprovable_provable unprovable_J5 (HasAxiomJ5.J5 _)

instance : (ILMinusJ5 : Logic α) ⪱ ILMinusJ1J5 :=
  .of_unprovable_provable unprovable_J1 (HasAxiomJ1.J1 _ _)

end Logic

end FFL.InterpretabilityLogic

