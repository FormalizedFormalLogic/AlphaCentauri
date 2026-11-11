module

public import AlphaCentauri.InterpretabilityLogic.Logic.ILMZeroW.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILW.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.FrameConditions
public import AlphaCentauri.InterpretabilityLogic.Veltman.StepByStepModel

/-!
# The logic $\mathbf{ILW}^*$

The extension of $\mathbf{IL}$ by the principle $\mathsf{W}^*$, which coincides with
$\mathbf{ILM}_0\mathbf{W}$. It proves exactly the formulas valid in the Veltman models satisfying
the frame conditions of $\mathsf{W}$ and $\mathsf{M}_0$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula

variable {α : Type*}

/-- - [Vis97] -/
abbrev Logic.ILWStar : Logic α := Logic.ofAxioms {Axioms.Wstar A B C | (A) (B) (C)}

notation "𝐈𝐋𝐖*" => Logic.ILWStar

namespace Veltman.Model

variable {κ α : Type*} [Nonempty κ] (M : Model κ α)

class IsILWStar : Prop extends M.IsILMZeroW

instance (v : α → Prop) : (pointModel v).IsILWStar := {}

instance (priority := low) [M.IsIL] [M.HasM₀] [M.HasW] : M.IsILWStar := {}

end Veltman.Model

namespace Logic

open ofAxioms Veltman Veltman.Model Veltman.Model.World

variable {A B C : Formula α} {κ : Type*} [Nonempty κ] {M : Model κ α}

@[simp] lemma ILWStar.axiomWstar : 𝐈𝐋𝐖* ⊢ Axioms.Wstar A B C := axm ⟨A, B, C, rfl⟩

lemma ILWStar.axiomW : 𝐈𝐋𝐖* ⊢ Axioms.W A B := by
  have h₁ : (𝐈𝐋𝐖* : Logic α) ⊢ □⊤ := nec verum;
  have h₂ : 𝐈𝐋𝐖* ⊢ A ▷ B 🡒 A ▷ (B ⋏ □⊤) := rhd_mono_right (by cl_prover [h₁]);
  have h₃ : 𝐈𝐋𝐖* ⊢ (B ⋏ □⊤) ▷ (B ⋏ □⊤ ⋏ □(∼A)) 🡒 (B ⋏ □⊤) ▷ (B ⋏ □(∼A)) :=
    rhd_mono_right (by cl_prover);
  have h₄ : 𝐈𝐋𝐖* ⊢ Axioms.J2 A (B ⋏ □⊤) (B ⋏ □(∼A)) := axiomJ2;
  cl_prover [axiomWstar (A := A) (B := B) (C := ⊤), h₂, h₃, h₄];

lemma ILWStar.axiomM₀ : 𝐈𝐋𝐖* ⊢ Axioms.M₀ A B C := by
  have h₁ : 𝐈𝐋𝐖* ⊢ A ▷ B 🡒 A ▷ (B ⋎ ◇A) := rhd_mono_right or₁;
  have h₂ : 𝐈𝐋𝐖* ⊢ (B ⋎ ∼□(∼A)) ⋏ □C ⋏ □(∼A) 🡒 B ⋏ □C := by cl_prover;
  have h₃ : 𝐈𝐋𝐖* ⊢ ((B ⋎ ◇A) ⋏ □C) ▷ ((B ⋎ ◇A) ⋏ □C ⋏ □(∼A)) 🡒 ((B ⋎ ◇A) ⋏ □C) ▷ (B ⋏ □C) :=
    rhd_mono_right h₂;
  have h₄ : 𝐈𝐋𝐖* ⊢ ((B ⋎ ◇A) ⋏ □C) ▷ (B ⋏ □C) 🡒 (◇A ⋏ □C) ▷ (B ⋏ □C) :=
    rhd_anti_left (by cl_prover);
  cl_prover [axiomWstar (A := A) (B := B ⋎ ◇A) (C := C), h₁, h₃, h₄];

instance : (𝐈𝐋𝐖 : Logic α) ⪯ 𝐈𝐋𝐖* :=
  weakerThan_iff.mpr <| subset_of_provable <| by rintro _ ⟨A, B, rfl⟩; exact ILWStar.axiomW

instance : (𝐈𝐋𝐖* : Logic α) ≊ 𝐈𝐋𝐌₀𝐖 := equiv_iff.mpr <| subset_antisymm
  (subset_of_provable <| by rintro _ ⟨A, B, C, rfl⟩; exact ILM₀W.axiomWstar)
  (subset_of_provable <| by
    rintro _ (⟨A, B, C, rfl⟩ | ⟨A, B, rfl⟩)
    · exact ILWStar.axiomM₀
    · exact ILWStar.axiomW)

theorem ILWStar.sound [M.IsILWStar] (h : 𝐈𝐋𝐖* ⊢ A) : M ⊧ A :=
  ILM₀W.sound <| (equiv_iff.mp inferInstance : (𝐈𝐋𝐖* : Logic α) = 𝐈𝐋𝐌₀𝐖).subset h

instance : Consistent (𝐈𝐋𝐖* : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILWStar.sound (M := pointModel fun _ ↦ False) h 0

open Veltman Veltman.StepByStep MaximalConsistentTheory

/-- - [GJ08, Theorem 7.1] -/
theorem ILWStar.iff_valid :
    𝐈𝐋𝐖* ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ α),
      [M.IsILWStar] → M ⊧ A := by
  constructor;
  · intro h _ _ M;
    intros;
    exact ILWStar.sound h;
  · intro h;
    classical
    by_contra hA;
    obtain ⟨Γ₀, hΓ₀⟩ := exists_not_forces (ε := fun A ↦ {□(∼A)}) axiomM₀
      (fun h hAB hA ↦ h.exists_of_rhd_mem_of_axiomW axiomW hAB hA) hA;
    have hτ := enumJob_mem (bot_mem_jobFormulas (A := A));
    have := model_isIL (Γ₀ := Γ₀) (ε := fun A ↦ {□(∼A)}) hτ;
    have := model_hasW (Γ₀ := Γ₀) (ε := fun A ↦ {□(∼A)}) hτ fun _ ↦ Set.mem_singleton _;
    exact hΓ₀ (h _ 0)

end Logic

end FFL.InterpretabilityLogic

