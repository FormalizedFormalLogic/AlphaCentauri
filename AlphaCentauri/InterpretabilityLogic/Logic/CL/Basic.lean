module

public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinus.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.LabelledSetModel
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinusJ1J4PlusJ5.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinusJ2PlusJ5.Basic

/-!
# Soundness and completeness of $\mathbf{CL}$
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

section SoundnessVeltman

namespace Logic

open Veltman Veltman.Model Veltman.Model.World

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {A : Formula α}

theorem CL.sound [M.IsILMinus] [M.IsJ1] [M.IsJ2] : 𝐂𝐋 ⊢ A → M ⊧ A :=
  ofAxiomsMinus.sound <| by
    rintro _ (⟨A, B, rfl⟩ | ⟨A, B, C, rfl⟩) x;
    · exact forces_axiomJ1;
    · exact forces_axiomJ2;

end Logic

end SoundnessVeltman

section Consistency

open Veltman.Model Logic

variable {α : Type*}

instance : Entailment.Consistent (𝐂𝐋 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ CL.sound (M := pointModel fun _ ↦ False) h 0

end Consistency

section Completeness

namespace Logic

open Entailment Formula MaximalConsistentSet Veltman Veltman.Model
open LabelledSet.Condition ofAxiomsMinus

variable {α : Type} {A : Formula α}

/-- - [KO21, Theorem 5.1] -/
theorem CL.iff_valid_finite :
    𝐂𝐋 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ1] → [M.IsJ2] → M ⊧ A := by
  constructor;
  · intro h _ _ _ M;
    intros;
    exact CL.sound h;
  · intro h;
    classical
    exact provable_of_models_labelledModel .J2Plus (h _)

end Logic

end Completeness



section IncompletenessVeltman

namespace Logic

open Veltman Veltman.Model Veltman.Model.World Entailment ofAxiomsMinus

variable {α : Type*} {L : Logic α}

private abbrev counterJ5 (α : Type*) : Model (Fin 3) α :=
  ⟨(· < ·), fun w x y ↦ w < x ∧ x = y, fun _ _ ↦ False⟩

private instance : (counterJ5 α).IsILMinus where
  trans := by omega
  cwf := Finite.converseWellFounded_of_trans_of_irrefl
  rel_of_s_left := by tauto

private instance : (counterJ5 α).IsJ1 := ⟨by tauto⟩

private instance : (counterJ5 α).IsJ2 where
  rel_of_s_right := by omega
  s_trans := by omega

lemma unprovable_J5 [L ⪯ 𝐂𝐋] : L ⊬ Axioms.J5 (□⊥) := by
  intro h;
  replace h := WeakerThan.pbl (𝓣 := 𝐂𝐋) h;
  have h₁ : (1 : Fin 3) ⊩[counterJ5 α] ◇□⊥ :=
    forces_dia.mpr ⟨2, by omega, fun y hy ↦ by omega⟩
  obtain ⟨z, ⟨-, rfl⟩, hz⟩ := CL.sound (M := counterJ5 α) h 0 1 (by omega) h₁;
  exact hz 2 (by omega);


end Logic

end IncompletenessVeltman








section Relations

namespace Logic

open Entailment Logic Logic.ofAxiomsMinus

variable {α : Type*}

instance : (ILMinusJ1J4Plus : Logic α) ⪱ ILMinusJ1J4PlusJ5 :=
  .of_unprovable_provable unprovable_J5 (axm (by simp))

instance : (ILMinusJ1 : Logic α) ⪱ ILMinusJ1J5 :=
  .of_unprovable_provable unprovable_J5 (axm (by simp))

instance : (ILMinusJ2Plus : Logic α) ⪱ ILMinusJ2PlusJ5 :=
  .of_unprovable_provable unprovable_J5 (axm (by simp))

instance : (ILMinusJ4Plus : Logic α) ⪱ ILMinusJ4PlusJ5 :=
  .of_unprovable_provable unprovable_J5 (axm (by simp))

instance : (𝐈𝐋⁻ : Logic α) ⪱ ILMinusJ5 := .of_unprovable_provable unprovable_J5 (by simp)

end Logic

end Relations

end FFL.InterpretabilityLogic

