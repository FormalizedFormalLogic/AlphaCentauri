module

public import AlphaCentauri.InterpretabilityLogic.Logic.ILRW.Basic

/-!
# The logic $\mathbf{ILR}^*$

The extension of $\mathbf{IL}$ by the principle $\mathsf{R}^*$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula

variable {α : Type*}

/-- - [GJ11] -/
abbrev Logic.ILRStar : Logic α := Logic.ofAxioms {Axioms.Rstar A B C | (A) (B) (C)}

notation "𝐈𝐋𝐑*" => Logic.ILRStar

namespace Veltman.Model

variable {κ α : Type*} [Nonempty κ] (M : Model κ α)

class IsILRStar : Prop extends M.IsILRW

instance (v : α → Prop) : (pointModel v).IsILRStar := {}

instance (priority := low) [M.IsIL] [M.HasR] [M.HasW] : M.IsILRStar := {}

end Veltman.Model

namespace Logic

open ofAxioms Veltman Veltman.Model Veltman.Model.World

variable {A B C : Formula α} {κ : Type*} [Nonempty κ] {M : Model κ α}

@[simp] lemma ILRStar.axiomRstar : 𝐈𝐋𝐑* ⊢ Axioms.Rstar A B C := axm ⟨A, B, C, rfl⟩

lemma ILRStar.axiomR : 𝐈𝐋𝐑* ⊢ Axioms.R A B C := by
  have h : 𝐈𝐋𝐑* ⊢ ∼(A ▷ ∼C) ▷ (B ⋏ □C ⋏ □(∼A)) 🡒 ∼(A ▷ ∼C) ▷ (B ⋏ □C) :=
    rhd_mono_right (by cl_prover);
  cl_prover [axiomRstar (A := A) (B := B) (C := C), h];

/-- - [GJ11] -/
lemma ILRStar.axiomW : 𝐈𝐋𝐑* ⊢ Axioms.W A B := by
  have h₁ : 𝐈𝐋𝐑* ⊢ A ▷ ∼⊤ 🡒 ∼□(∼A) 🡒 ∼□(∼∼⊤) := axiomJ4;
  have h₂ : (𝐈𝐋𝐑* : Logic α) ⊢ ∼∼⊤ := by cl_prover;
  have h₃ : (𝐈𝐋𝐑* : Logic α) ⊢ □(∼∼⊤) := nec h₂;
  have h₄ : 𝐈𝐋𝐑* ⊢ ∼□(∼A) 🡒 ∼(A ▷ ∼⊤) := by cl_prover [h₁, h₃];
  have h₅ : 𝐈𝐋𝐑* ⊢ ◇A ▷ ∼(A ▷ ∼⊤) := rhd_of_provable h₄;
  have h₆ : 𝐈𝐋𝐑* ⊢ ∼(A ▷ ∼⊤) ▷ (B ⋏ □⊤ ⋏ □(∼A)) 🡒 ∼(A ▷ ∼⊤) ▷ (B ⋏ □(∼A)) :=
    rhd_mono_right (by cl_prover);
  have h₇ : 𝐈𝐋𝐑* ⊢ Axioms.J2 (◇A) (∼(A ▷ ∼⊤)) (B ⋏ □(∼A)) := axiomJ2;
  have h₈ : 𝐈𝐋𝐑* ⊢ Axioms.J3 (B ⋏ □(∼A)) (◇A) (B ⋏ □(∼A)) := axiomJ3;
  have h₉ : 𝐈𝐋𝐑* ⊢ B 🡒 B ⋏ □(∼A) ⋎ ∼□(∼A) := by cl_prover;
  have h₁₀ : 𝐈𝐋𝐑* ⊢ A ▷ B 🡒 A ▷ (B ⋏ □(∼A) ⋎ ◇A) := rhd_mono_right h₉;
  have h₁₁ : 𝐈𝐋𝐑* ⊢ Axioms.J2 A (B ⋏ □(∼A) ⋎ ◇A) (B ⋏ □(∼A)) := axiomJ2;
  have h₁₂ : 𝐈𝐋𝐑* ⊢ (B ⋏ □(∼A)) ▷ (B ⋏ □(∼A)) := rhd_refl;
  cl_prover [axiomRstar (A := A) (B := B) (C := ⊤), h₅, h₆, h₇, h₈, h₁₀, h₁₁, h₁₂];

instance : (𝐈𝐋𝐑𝐖 : Logic α) ≊ 𝐈𝐋𝐑* := equiv_iff.mpr <| subset_antisymm
  (subset_of_provable <| by
    rintro _ (⟨A, B, C, rfl⟩ | ⟨A, B, rfl⟩)
    · exact ILRStar.axiomR
    · exact ILRStar.axiomW)
  (subset_of_provable <| by rintro _ ⟨A, B, C, rfl⟩; exact ILRW.axiomRstar)

theorem ILRStar.sound [M.IsILRStar] (h : 𝐈𝐋𝐑* ⊢ A) : M ⊧ A :=
  ILRW.sound <| (equiv_iff.mp inferInstance : (𝐈𝐋𝐑𝐖 : Logic α) = 𝐈𝐋𝐑*).symm.subset h

instance : Consistent (𝐈𝐋𝐑* : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILRStar.sound (M := pointModel fun _ ↦ False) h 0

end Logic

end FFL.InterpretabilityLogic

