module

public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinus.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.IndexedSetModel

/-!
# Soundness and completeness of $\mathbf{IL}^-(\mathbf{J2}^+, \mathbf{J5})$
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

section SoundnessVeltman

namespace Logic

open Veltman Veltman.Model Veltman.Model.World

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {A : Formula α}

theorem ILMinusJ2PlusJ5.sound [M.IsILMinus] [M.IsJ2] [M.IsJ5] : ILMinusJ2PlusJ5 ⊢ A → M ⊧ A :=
  ofAxiomsMinus.sound <| by
    rintro _ (⟨A, B, C, rfl⟩ | ⟨A, rfl⟩) x;
    · exact forces_axiomJ2Plus;
    · exact forces_axiomJ5;

end Logic

end SoundnessVeltman

section Consistency

open Veltman.Model Logic

variable {α : Type*}

instance : Entailment.Consistent (ILMinusJ2PlusJ5 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILMinusJ2PlusJ5.sound (M := pointModel fun _ ↦ False) h 0

end Consistency

section Completeness

namespace Logic

open Entailment Formula MaximalConsistentSet Veltman Veltman.Model

variable {α : Type} {A : Formula α}

/-- - [KO21, Theorem 5.4] -/
theorem ILMinusJ2PlusJ5.iff_valid_finite :
    ILMinusJ2PlusJ5 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ2] → [M.IsJ5] → M ⊧ A := by
  constructor;
  · intro h _ _ _ M;
    intros;
    exact ILMinusJ2PlusJ5.sound h;
  · intro h;
    classical
    by_contra hA;
    have : Entailment.Consistent (ILMinusJ2PlusJ5 : Logic α) := .of_unprovable hA;
    exact ofAxiomsMinus.not_models_countermodel hA <|
      h (countermodel ILMinusJ2PlusJ5 (ilMinusAdequateClosure {A}))

end Logic

end Completeness



section IncompletenessVeltman

namespace Logic

open Veltman Veltman.Model Veltman.Model.World Entailment ofAxiomsMinus

variable {α : Type*} {L : Logic α}

private abbrev counterJ1 (α : Type*) : Model (Fin 2) α :=
  ⟨(· < ·), fun _ _ _ ↦ False, fun _ _ ↦ False⟩

private instance : (counterJ1 α).IsILMinus where
  trans := by omega
  cwf := Finite.converseWellFounded_of_trans_of_irrefl
  rel_of_s_left := by tauto

private instance : (counterJ1 α).IsJ2 where
  rel_of_s_right := by tauto
  s_trans := by tauto

private instance : (counterJ1 α).IsJ5 := ⟨by omega⟩

lemma unprovable_J1 [L ⪯ ILMinusJ2PlusJ5] : L ⊬ Axioms.J1 ⊤ ⊤ := by
  intro h;
  replace h := WeakerThan.pbl (𝓣 := ILMinusJ2PlusJ5) h;
  obtain ⟨z, h, -⟩ :=
    ILMinusJ2PlusJ5.sound (M := counterJ1 α) h 0 (fun _ _ ↦ id) 1 (by omega) forces_top;
  exact h;


end Logic

end IncompletenessVeltman



















section Relations

namespace Logic

open Entailment Logic Logic.ofAxiomsMinus

variable {α : Type*}

instance : (𝐈𝐋⁻ : Logic α) ⪱ ILMinusJ1 := .of_unprovable_provable unprovable_J1 (by simp)

instance : (ILMinusJ4Plus : Logic α) ⪱ ILMinusJ1J4Plus :=
  .of_unprovable_provable unprovable_J1 (axm (by simp))

instance : (ILMinusJ4PlusJ5 : Logic α) ⪱ ILMinusJ1J4PlusJ5 :=
  .of_unprovable_provable unprovable_J1 (axm (by simp))

instance : (ILMinusJ5 : Logic α) ⪱ ILMinusJ1J5 :=
  .of_unprovable_provable unprovable_J1 (axm (by simp))

instance : (ILMinusJ2Plus : Logic α) ⪱ 𝐂𝐋 := .of_unprovable_provable unprovable_J1 (by simp)

end Logic

end Relations

end FFL.InterpretabilityLogic

