module

public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinus.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.LabelledSetModel

/-!
# Soundness and completeness of $\mathbf{IL}^-(\mathbf{J1}, \mathbf{J4}^+, \mathbf{J5})$
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

section SoundnessVeltman

namespace Logic

open Veltman Veltman.Model Veltman.Model.World

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {A : Formula α}

theorem ILMinusJ1J4PlusJ5.sound [M.IsILMinus] [M.IsJ1] [M.IsJ4] [M.IsJ5] :
    ILMinusJ1J4PlusJ5 ⊢ A → M ⊧ A :=
  ofAxiomsMinus.sound <| by
    rintro _ ((⟨A, B, rfl⟩ | ⟨A, B, C, rfl⟩) | ⟨A, rfl⟩) x;
    · exact forces_axiomJ1;
    · exact forces_axiomJ4Plus;
    · exact forces_axiomJ5;

end Logic

end SoundnessVeltman

section Consistency

open Veltman.Model Logic

variable {α : Type*}

instance : Entailment.Consistent (ILMinusJ1J4PlusJ5 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILMinusJ1J4PlusJ5.sound (M := pointModel fun _ ↦ False) h 0

end Consistency

section Completeness

namespace Logic

open Entailment Formula MaximalConsistentSet Veltman Veltman.Model
open LabelledSet.Condition ofAxiomsMinus

variable {α : Type} {A : Formula α}

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ1J4PlusJ5.iff_valid_finite :
    ILMinusJ1J4PlusJ5 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ1] → [M.IsJ4] → [M.IsJ5] → M ⊧ A := by
  constructor;
  · intro h _ _ _ M;
    intros;
    exact ILMinusJ1J4PlusJ5.sound h;
  · intro h;
    classical
    exact provable_of_models_labelledModel .J4PlusJ5 (h _)

end Logic

end Completeness



section IncompletenessVeltman

namespace Logic

open Veltman Veltman.Model Veltman.Model.World Entailment ofAxiomsMinus

variable {α : Type*} {L : Logic α}

private abbrev counterJ2 (α : Type*) : Model (Fin 4) α :=
  ⟨(· < ·), fun w x y ↦ w < x ∧ w < y ∧ (x ≤ y ∨ w = 0 ∧ (x = 3 ∧ y = 2 ∨ x = 2 ∧ y = 1)),
    fun _ _ ↦ False⟩

private instance : (counterJ2 α).IsILMinus where
  trans := by omega
  cwf := Finite.converseWellFounded_of_trans_of_irrefl
  rel_of_s_left := by tauto

private instance : (counterJ2 α).IsJ1 := ⟨by omega⟩

private instance : (counterJ2 α).IsJ4 := ⟨by omega⟩

private instance : (counterJ2 α).IsJ5 := ⟨by omega⟩

lemma unprovable_J2 [L ⪯ ILMinusJ1J4PlusJ5] : L ⊬ Axioms.J2 (□⊥) (◇⊤ ⋏ □□⊥) (◇◇⊤) := by
  intro h;
  replace h := WeakerThan.pbl (𝓣 := ILMinusJ1J4PlusJ5) h;
  have h₁ : (0 : Fin 4) ⊩[counterJ2 α] □⊥ ▷ (◇⊤ ⋏ □□⊥) ⋏ (◇⊤ ⋏ □□⊥) ▷ ◇◇⊤ := by
    refine forces_and.mpr ⟨?_, ?_⟩
    · intro y _ hy
      have : ¬y < 3 := hy 3
      refine ⟨2, by omega, forces_and.mpr ⟨forces_dia.mpr ⟨3, by omega, forces_top⟩, ?_⟩⟩
      intro z hz u hu
      omega
    · intro y _ hy
      obtain ⟨hy₁, hy₂⟩ := forces_and.mp hy
      obtain ⟨z, hz, -⟩ := forces_dia.mp hy₁
      have : ¬y < 2 := by
        intro h
        exact hy₂ 2 h 3 (by omega)
      exact ⟨1, by omega, forces_dia.mpr ⟨2, by omega, forces_dia.mpr ⟨3, by omega, forces_top⟩⟩⟩
  have h₂ : (3 : Fin 4) ⊩[counterJ2 α] □⊥ := by
    intro y hy;
    omega;
  obtain ⟨z, hz, hz'⟩ := ILMinusJ1J4PlusJ5.sound (M := counterJ2 α) h 0 h₁ 3 (by omega) h₂;
  obtain ⟨u, hu, hu'⟩ := forces_dia.mp hz';
  obtain ⟨v, hv, -⟩ := forces_dia.mp hu';
  omega;


end Logic

end IncompletenessVeltman











section Relations

namespace Logic

open Entailment Logic Logic.ofAxiomsMinus

variable {α : Type*}

instance : (ILMinusJ4Plus : Logic α) ⪱ ILMinusJ2Plus :=
  .of_unprovable_provable unprovable_J2 (by simp)

instance : (ILMinusJ4PlusJ5 : Logic α) ⪱ ILMinusJ2PlusJ5 :=
  .of_unprovable_provable unprovable_J2 (WeakerThan.pbl (𝓢 := ILMinusJ2Plus) (by simp))

instance : (ILMinusJ1J4Plus : Logic α) ⪱ 𝐂𝐋 := .of_unprovable_provable unprovable_J2 (by simp)

end Logic

end Relations

end FFL.InterpretabilityLogic

