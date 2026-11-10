module

public import AlphaCentauri.InterpretabilityLogic.Logic.ILMZero.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.FrameConditions

/-!
# The logic $\mathbf{ILR}$

The extension of $\mathbf{IL}$ by the principle $\mathsf{R}$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula

variable {α : Type*}

/-- - [GJ11] -/
abbrev Logic.ILR : Logic α := Logic.ofAxioms {Axioms.R A B C | (A) (B) (C)}

notation "𝐈𝐋𝐑" => Logic.ILR

namespace Logic

open ofAxioms

variable {A B C : Formula α}

@[simp] lemma ILR.axiomR : 𝐈𝐋𝐑 ⊢ Axioms.R A B C := axm ⟨A, B, C, rfl⟩

lemma ILR.axiomM₀ : 𝐈𝐋𝐑 ⊢ Axioms.M₀ A B C := by
  have h₁ : 𝐈𝐋𝐑 ⊢ A ▷ ∼C 🡒 ∼□(∼A) 🡒 ∼□(∼∼C) := axiomJ4;
  have h₂ : 𝐈𝐋𝐑 ⊢ □C 🡒 □(∼∼C) := box_mono dni;
  have h₃ : 𝐈𝐋𝐑 ⊢ ∼□(∼A) ⋏ □C 🡒 ∼(A ▷ ∼C) := by cl_prover [h₁, h₂];
  have h₄ : 𝐈𝐋𝐑 ⊢ (◇A ⋏ □C) ▷ ∼(A ▷ ∼C) := rhd_of_provable h₃;
  have h₅ : 𝐈𝐋𝐑 ⊢ Axioms.J2 (◇A ⋏ □C) (∼(A ▷ ∼C)) (B ⋏ □C) := axiomJ2;
  cl_prover [axiomR (A := A) (B := B) (C := C), h₄, h₅];

/-- - [GJ11] -/
lemma ILR.axiomP₀ : 𝐈𝐋𝐑 ⊢ Axioms.P₀ A B := by
  have h₁ : 𝐈𝐋𝐑 ⊢ ∼□(∼B) ⋏ □(∼B) 🡒 ⊥ := by cl_prover;
  have h₂ : 𝐈𝐋𝐑 ⊢ ∼(A ▷ ∼∼B) ▷ (◇B ⋏ □(∼B)) 🡒 ∼(A ▷ ∼∼B) ▷ ⊥ := rhd_mono_right h₁;
  have h₃ : 𝐈𝐋𝐑 ⊢ ∼(A ▷ ∼∼B) ▷ ⊥ 🡒 □(∼∼(A ▷ ∼∼B)) := rhd_bot;
  have h₄ : 𝐈𝐋𝐑 ⊢ A ▷ ∼∼B 🡒 A ▷ B := rhd_mono_right Entailment.dne;
  have h₅ : 𝐈𝐋𝐑 ⊢ ∼∼(A ▷ ∼∼B) 🡒 A ▷ B := by cl_prover [h₄];
  cl_prover [axiomR (A := A) (B := ◇B) (C := ∼B), h₂, h₃, box_mono h₅];

instance : (𝐈𝐋𝐌₀ : Logic α) ⪯ 𝐈𝐋𝐑 :=
  weakerThan_iff.mpr <| subset_of_provable <| by rintro _ ⟨A, B, C, rfl⟩; exact ILR.axiomM₀

end Logic

namespace Logic

open Veltman Veltman.Model Veltman.Model.World

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {A : Formula α}

theorem ILR.sound [M.IsIL] [M.HasR] (h : 𝐈𝐋𝐑 ⊢ A) : M ⊧ A :=
  ofAxioms.sound (by rintro _ ⟨A, B, C, rfl⟩ x; exact forces_axiomR) h

instance : Consistent (𝐈𝐋𝐑 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILR.sound (M := pointModel fun _ ↦ False) h 0

end Logic

/-- $\mathbf{ILR}$ is complete with respect to Veltman frames. An open problem.
- [MV20, §2.5] -/
def ILRVeltmanCompletenessProblem : Prop :=
  ∀ A : Formula ℕ,
    (∀ (κ : Type) [Nonempty κ] (M : Veltman.Model κ ℕ) [M.IsIL] [M.HasR], M ⊧ A) → 𝐈𝐋𝐑 ⊢ A

end FFL.InterpretabilityLogic

