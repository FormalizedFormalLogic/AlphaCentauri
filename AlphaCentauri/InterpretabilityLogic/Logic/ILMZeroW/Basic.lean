module

public import AlphaCentauri.InterpretabilityLogic.Logic.ILMZero.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.FrameConditions

/-!
# The logic $\mathbf{ILM}_0\mathbf{W}$

The extension of $\mathbf{ILM}_0$ by the principle $\mathsf{W}$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula

variable {α : Type*}

abbrev Logic.ILM₀W : Logic α :=
  Logic.ofAxioms ({Axioms.M₀ A B C | (A) (B) (C)} ∪ {Axioms.W A B | (A) (B)})

notation "𝐈𝐋𝐌₀𝐖" => Logic.ILM₀W

namespace Logic

open ofAxioms

variable {A B C : Formula α}

@[simp] lemma ILM₀W.axiomM₀ : 𝐈𝐋𝐌₀𝐖 ⊢ Axioms.M₀ A B C := axm <| .inl ⟨A, B, C, rfl⟩

@[simp] lemma ILM₀W.axiomW : 𝐈𝐋𝐌₀𝐖 ⊢ Axioms.W A B := axm <| .inr ⟨A, B, rfl⟩

lemma ILM₀W.axiomWstar : 𝐈𝐋𝐌₀𝐖 ⊢ Axioms.Wstar A B C := by
  have h₁ : 𝐈𝐋𝐌₀𝐖 ⊢ B ⋏ □C 🡒 B ⋏ □C ⋏ ∼□(∼A) ⋎ B ⋏ □C ⋏ □(∼A) := by cl_prover;
  have h₂ : 𝐈𝐋𝐌₀𝐖 ⊢ (B ⋏ □C) ▷ (B ⋏ □C ⋏ ◇A ⋎ B ⋏ □C ⋏ □(∼A)) := rhd_of_provable h₁;
  have h₃ : 𝐈𝐋𝐌₀𝐖 ⊢ (◇A ⋏ □C) ▷ ((B ⋏ □(∼A)) ⋏ □C) 🡒 (B ⋏ □C ⋏ ◇A) ▷ ((B ⋏ □(∼A)) ⋏ □C) :=
    rhd_anti_left (by cl_prover);
  have h₄ : 𝐈𝐋𝐌₀𝐖 ⊢
      (B ⋏ □C ⋏ ◇A) ▷ ((B ⋏ □(∼A)) ⋏ □C) 🡒 (B ⋏ □C ⋏ ◇A) ▷ (B ⋏ □C ⋏ □(∼A)) :=
    rhd_mono_right (by cl_prover);
  have h₅ : 𝐈𝐋𝐌₀𝐖 ⊢ Axioms.J3 (B ⋏ □C ⋏ ◇A) (B ⋏ □C ⋏ □(∼A)) (B ⋏ □C ⋏ □(∼A)) := axiomJ3;
  have h₆ : 𝐈𝐋𝐌₀𝐖 ⊢
      Axioms.J2 (B ⋏ □C) (B ⋏ □C ⋏ ◇A ⋎ B ⋏ □C ⋏ □(∼A)) (B ⋏ □C ⋏ □(∼A)) := axiomJ2;
  have h₇ : 𝐈𝐋𝐌₀𝐖 ⊢ (B ⋏ □C ⋏ □(∼A)) ▷ (B ⋏ □C ⋏ □(∼A)) := rhd_refl;
  cl_prover [axiomW (A := A) (B := B), axiomM₀ (A := A) (B := B ⋏ □(∼A)) (C := C), h₂, h₃, h₄,
    h₅, h₆, h₇];

instance : (𝐈𝐋𝐌₀ : Logic α) ⪯ 𝐈𝐋𝐌₀𝐖 := weakerThan_iff.mpr <| subset_of_subset Set.subset_union_left

end Logic

namespace Logic

open Veltman Veltman.Model Veltman.Model.World

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {A : Formula α}

theorem ILM₀W.sound [M.IsIL] [M.HasM₀] [M.HasW] (h : 𝐈𝐋𝐌₀𝐖 ⊢ A) : M ⊧ A := by
  apply ofAxioms.sound _ h;
  rintro _ (⟨A, B, C, rfl⟩ | ⟨A, B, rfl⟩) x;
  · exact forces_axiomM₀;
  · exact forces_axiomW;

instance : Consistent (𝐈𝐋𝐌₀𝐖 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILM₀W.sound (M := pointModel fun _ ↦ False) h 0

end Logic

namespace Logic

open Veltman Veltman.Model Veltman.Model.World

instance : (𝐈𝐋𝐌₀ : Logic ℕ) ⪱ 𝐈𝐋𝐌₀𝐖 :=
  .of_unprovable_provable (φ := Axioms.W (#0) (#1)) (fun h ↦ by
    have H := ILM₀.sound (M := countermodelW) h 0;
    have h₁ : (0 : countermodelW.World) ⊩[countermodelW] #0 ▷ #1 := by
      intro u _ hu;
      exact ⟨1, Or.inl ⟨rfl, hu, by decide⟩, rfl⟩;
    obtain ⟨z, _, hz⟩ := H h₁ 1 (by decide) (show (1 : Fin 3) ≠ 0 by decide);
    obtain ⟨hz₁, hz₂⟩ := forces_and.mp hz;
    obtain rfl : z = 1 := hz₁;
    exact hz₂ 2 (by decide) (show (2 : Fin 3) ≠ 0 by decide)) ILM₀W.axiomW

end Logic

end FFL.InterpretabilityLogic

