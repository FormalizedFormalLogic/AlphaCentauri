module

public import AlphaCentauri.InterpretabilityLogic.Logic.IL.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.FrameConditions
public import AlphaCentauri.InterpretabilityLogic.Veltman.StepByStepModel

/-!
# The logic $\mathbf{ILM}_0$

The extension of $\mathbf{IL}$ by the principle $\mathsf{M}_0$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula

variable {α : Type*}

/-- - [Vis97] -/
abbrev Logic.ILM₀ : Logic α := Logic.ofILAxioms {Axioms.M₀ A B C | (A) (B) (C)}

notation "𝐈𝐋𝐌₀" => Logic.ILM₀

namespace Veltman.Model

variable {κ α : Type*} [Nonempty κ] (M : Model κ α)

class IsILMZero : Prop extends M.IsIL, M.HasM₀

instance (v : α → Prop) : (pointModel v).IsILMZero := {}

instance (priority := low) [M.IsIL] [M.HasM₀] : M.IsILMZero := {}

end Veltman.Model

namespace Logic

open ofILAxioms Veltman Veltman.Model Veltman.Model.World

variable {A B C : Formula α} {κ : Type*} [Nonempty κ] {M : Model κ α}

@[simp] lemma ILM₀.axiomM₀ : 𝐈𝐋𝐌₀ ⊢ Axioms.M₀ A B C := axm ⟨A, B, C, rfl⟩

theorem ILM₀.sound [M.IsILMZero] (h : 𝐈𝐋𝐌₀ ⊢ A) : M ⊧ A :=
  ofILAxioms.sound (by rintro _ ⟨A, B, C, rfl⟩ x; exact forces_axiomM₀) h

instance : Consistent (𝐈𝐋𝐌₀ : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILM₀.sound (M := pointModel fun _ ↦ False) h 0

open Veltman Veltman.StepByStep MaximalConsistentTheory

/-- - [GJ08, Theorem 6.1] -/
theorem ILM₀.iff_valid :
    𝐈𝐋𝐌₀ ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ α),
      [M.IsILMZero] → M ⊧ A := by
  constructor;
  · intro h _ _ M;
    intros;
    exact ILM₀.sound h;
  · intro h;
    classical
    by_contra hA;
    obtain ⟨Γ₀, hΓ₀⟩ := exists_not_forces (ε := fun _ ↦ ∅) axiomM₀
      (fun h hAB hA ↦ by simpa using h.exists_of_rhd_mem hAB hA) hA;
    have := model_isIL (Γ₀ := Γ₀) (ε := fun _ ↦ ∅)
      (enumJob_mem (bot_mem_jobFormulas (A := A)));
    exact hΓ₀ (h _ 0)

instance : (𝐈𝐋 : Logic ℕ) ⪱ 𝐈𝐋𝐌₀ :=
  .of_unprovable_provable (φ := Axioms.M₀ (#0) (#1) (#2)) (fun h ↦ by
    have H := ofILAxioms.sound (M := countermodelM₀) (𝔸 := ∅) (by simp) h 0;
    have h₁ : (0 : countermodelM₀.World) ⊩[countermodelM₀] #0 ▷ #1 := by
      intro v _ hv;
      obtain rfl : v = 2 := hv;
      exact ⟨3, by decide, rfl⟩;
    have h₂ : (1 : countermodelM₀.World) ⊩[countermodelM₀] ◇(#0) ⋏ □(#2) :=
      forces_and.mpr ⟨forces_dia.mpr ⟨2, by decide, rfl⟩, fun y hy ↦
        (by decide : ∀ y, countermodelM₀.Rel 1 y → y = 2) y hy⟩;
    obtain ⟨t, _, ht⟩ := H h₁ 1 (by decide) h₂;
    obtain ⟨htz, ht⟩ := forces_and.mp ht;
    obtain rfl : t = 3 := htz;
    exact (show (4 : Fin 5) ≠ 2 by decide) (ht 4 (by decide))) ILM₀.axiomM₀

end Logic

end FFL.InterpretabilityLogic

