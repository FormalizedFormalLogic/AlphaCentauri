module

public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic

/-!
# Countermodels separating the extensions of $\mathbf{IL}^-$

Finite Veltman models satisfying all the frame conditions among $\mathbf{J1}$, $\mathbf{J2}$,
$\mathbf{J4}$, $\mathbf{J5}$ but one of them, together with an instance of the corresponding
principle that fails in them.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula

namespace Veltman

open Model Model.World

variable {α : Type}

/-- A model satisfying $\mathbf{J2}$ and $\mathbf{J5}$ but not $\mathbf{J1}$. -/
abbrev counterJ1 (α : Type*) : Model (Fin 2) α :=
  ⟨(· < ·), fun _ _ _ ↦ False, fun _ _ ↦ False⟩

instance : (counterJ1 α).IsILMinus where
  trans := by omega
  cwf := Finite.converseWellFounded_of_trans_of_irrefl
  rel_of_s_left := by tauto

instance : (counterJ1 α).IsJ2 where
  rel_of_s_right := by tauto
  s_trans := by tauto

instance : (counterJ1 α).IsJ5 := ⟨by omega⟩

lemma counterJ1.not_models_J1 : ¬counterJ1 α ⊧ Axioms.J1 ⊤ ⊤ := by
  intro h
  obtain ⟨z, h, -⟩ := h 0 (fun _ _ ↦ id) 1 (by omega) forces_top
  exact h

/-- A model satisfying $\mathbf{J1}$ and $\mathbf{J5}$ but not $\mathbf{J4}^+$. -/
abbrev counterJ4 (α : Type*) : Model (Fin 3) α :=
  ⟨(· < ·), fun w x _ ↦ w < x, fun _ _ ↦ False⟩

instance : (counterJ4 α).IsILMinus where
  trans := by omega
  cwf := Finite.converseWellFounded_of_trans_of_irrefl
  rel_of_s_left := by tauto

instance : (counterJ4 α).IsJ1 := ⟨by tauto⟩

instance : (counterJ4 α).IsJ5 := ⟨by tauto⟩

lemma counterJ4.not_models_J4Plus : ¬counterJ4 α ⊧ Axioms.J4Plus (◇⊤) ⊥ ⊤ := by
  intro h
  have h₁ : (1 : Fin 3) ⊩[counterJ4 α] □(◇⊤ 🡒 ⊥) := by
    intro y Rxy hy
    obtain ⟨z, Ryz, -⟩ := forces_dia.mp hy
    omega
  have h₂ : (1 : Fin 3) ⊩[counterJ4 α] ⊤ ▷ ◇⊤ := by
    intro y Rxy _
    exact ⟨0, Rxy, forces_dia.mpr ⟨1, by omega, forces_top⟩⟩
  obtain ⟨z, -, hz⟩ := h 1 h₁ h₂ 2 (by omega) forces_top
  exact hz

/-- A model satisfying $\mathbf{J1}$, $\mathbf{J4}$ and $\mathbf{J5}$ but not $\mathbf{J2}$. -/
abbrev counterJ2 (α : Type*) : Model (Fin 4) α :=
  ⟨(· < ·), fun w x y ↦ w < x ∧ w < y ∧ (x ≤ y ∨ w = 0 ∧ (x = 3 ∧ y = 2 ∨ x = 2 ∧ y = 1)),
    fun _ _ ↦ False⟩

instance : (counterJ2 α).IsILMinus where
  trans := by omega
  cwf := Finite.converseWellFounded_of_trans_of_irrefl
  rel_of_s_left := by tauto

instance : (counterJ2 α).IsJ1 := ⟨by omega⟩

instance : (counterJ2 α).IsJ4 := ⟨by omega⟩

instance : (counterJ2 α).IsJ5 := ⟨by omega⟩

lemma counterJ2.not_models_J2 : ¬counterJ2 α ⊧ Axioms.J2 (□⊥) (◇⊤ ⋏ □□⊥) (◇◇⊤) := by
  intro h
  have h₁ : (0 : Fin 4) ⊩[counterJ2 α] □⊥ ▷ (◇⊤ ⋏ □□⊥) ⋏ (◇⊤ ⋏ □□⊥) ▷ ◇◇⊤ := by
    refine forces_and.mpr ⟨?_, ?_⟩
    · intro y _ hy
      have : ¬y < 3 := hy 3
      refine ⟨2, by omega,
        forces_and.mpr ⟨forces_dia.mpr ⟨3, by omega, forces_top⟩, ?_⟩⟩
      intro z hz u hu
      omega
    · intro y _ hy
      obtain ⟨hy₁, hy₂⟩ := forces_and.mp hy
      obtain ⟨z, hz, -⟩ := forces_dia.mp hy₁
      have : ¬y < 2 := by
        intro h
        exact hy₂ 2 h 3 (by omega)
      exact ⟨1, by omega,
        forces_dia.mpr ⟨2, by omega, forces_dia.mpr ⟨3, by omega, forces_top⟩⟩⟩
  have h₂ : (3 : Fin 4) ⊩[counterJ2 α] □⊥ := by
    intro y hy
    omega
  obtain ⟨z, hz, hz'⟩ := h 0 h₁ 3 (by omega) h₂
  obtain ⟨u, hu, hu'⟩ := forces_dia.mp hz'
  obtain ⟨v, hv, -⟩ := forces_dia.mp hu'
  omega

/-- A model satisfying $\mathbf{J1}$ and $\mathbf{J2}$ but not $\mathbf{J5}$. -/
abbrev counterJ5 (α : Type*) : Model (Fin 3) α :=
  ⟨(· < ·), fun w x y ↦ w < x ∧ x = y, fun _ _ ↦ False⟩

instance : (counterJ5 α).IsILMinus where
  trans := by omega
  cwf := Finite.converseWellFounded_of_trans_of_irrefl
  rel_of_s_left := by tauto

instance : (counterJ5 α).IsJ1 := ⟨by tauto⟩

instance : (counterJ5 α).IsJ2 where
  rel_of_s_right := by omega
  s_trans := by omega

lemma counterJ5.not_models_J5 : ¬counterJ5 α ⊧ Axioms.J5 (□⊥) := by
  intro h
  have h₁ : (1 : Fin 3) ⊩[counterJ5 α] ◇□⊥ :=
    forces_dia.mpr ⟨2, by omega, fun y hy ↦ by omega⟩
  obtain ⟨z, ⟨-, rfl⟩, hz⟩ := h 0 1 (by omega) h₁
  exact hz 2 (by omega)

end Veltman

end FFL.InterpretabilityLogic

end
