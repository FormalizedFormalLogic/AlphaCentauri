module

public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinus.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.LabelledSetModel

/-!
# Soundness and completeness of $\mathbf{IL}^-(\mathbf{J1}, \mathbf{J5})$
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

section SoundnessVeltman

namespace Logic

open Veltman Veltman.Model Veltman.Model.World

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {A : Formula α}

theorem ILMinusJ1J5.sound [M.IsILMinus] [M.IsJ1] [M.IsJ5] : ILMinusJ1J5 ⊢ A → M ⊧ A :=
  ofAxiomsMinus.sound <| by
    rintro _ (⟨A, B, rfl⟩ | ⟨A, rfl⟩) x;
    · exact forces_axiomJ1;
    · exact forces_axiomJ5;

end Logic

end SoundnessVeltman

section Consistency

open Veltman.Model Logic

variable {α : Type*}

instance : Entailment.Consistent (ILMinusJ1J5 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILMinusJ1J5.sound (M := pointModel fun _ ↦ False) h 0

end Consistency

section Completeness

namespace Logic

open Entailment Formula MaximalConsistentSet Veltman Veltman.Model
open LabelledSet.Condition ofAxiomsMinus

variable {α : Type} {A : Formula α}

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ1J5.iff_valid_finite :
    ILMinusJ1J5 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ1] → [M.IsJ5] → M ⊧ A := by
  constructor;
  · intro h _ _ _ M;
    intros;
    exact ILMinusJ1J5.sound h;
  · intro h;
    classical
    exact provable_of_models_labelledModel .J5 (h _)

end Logic

end Completeness



section IncompletenessVeltman

namespace Logic

open Veltman Veltman.Model Veltman.Model.World Entailment ofAxiomsMinus

variable {α : Type*} {L : Logic α}

private abbrev counterJ4 (α : Type*) : Model (Fin 3) α :=
  ⟨(· < ·), fun w x _ ↦ w < x, fun _ _ ↦ False⟩

private instance : (counterJ4 α).IsILMinus where
  trans := by omega
  cwf := Finite.converseWellFounded_of_trans_of_irrefl
  rel_of_s_left := by tauto

private instance : (counterJ4 α).IsJ1 := ⟨by tauto⟩

private instance : (counterJ4 α).IsJ5 := ⟨by tauto⟩

private lemma unprovable_J4Plus [L ⪯ ILMinusJ1J5] : L ⊬ Axioms.J4Plus (◇⊤) ⊥ ⊤ := by
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


end Logic

end IncompletenessVeltman















section Relations

namespace Logic

open Entailment Logic Logic.ofAxiomsMinus

variable {α : Type*}

instance : (ILMinusJ1 : Logic α) ⪱ ILMinusJ1J4Plus :=
  .of_unprovable_provable unprovable_J4Plus (axm (by simp))

instance : (ILMinusJ1J5 : Logic α) ⪱ ILMinusJ1J4PlusJ5 :=
  .of_unprovable_provable unprovable_J4Plus (axm (by simp))

instance : (𝐈𝐋⁻ : Logic α) ⪱ ILMinusJ4Plus := .of_unprovable_provable unprovable_J4Plus (by simp)

instance : (ILMinusJ5 : Logic α) ⪱ ILMinusJ4PlusJ5 :=
  .of_unprovable_provable unprovable_J4Plus (axm (by simp))

end Logic

end Relations

end FFL.InterpretabilityLogic

