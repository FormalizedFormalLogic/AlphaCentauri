module

public import AlphaCentauri.InterpretabilityLogic.Logic.ILMZero.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILPZero.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.FrameConditions
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.MaximalConsistentTheoryModel

/-!
# The logic $\mathbf{ILR}$

The extension of $\mathbf{IL}$ by the principle $\mathsf{R}$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula

variable {α : Type*}

/-- - [GJ11] -/
abbrev Logic.ILR : Logic α := Logic.ofILAxioms {Axioms.R A B C | (A) (B) (C)}

notation "𝐈𝐋𝐑" => Logic.ILR

namespace Veltman.Model

variable {κ α : Type*} [Nonempty κ] (M : Model κ α)

class IsILR : Prop extends M.IsIL, M.HasR

instance (v : α → Prop) : (pointModel v).IsILR := {}

instance (priority := low) [M.IsIL] [M.HasR] : M.IsILR := {}

end Veltman.Model

namespace Verbrugge.Model

variable {κ α : Type*} [Nonempty κ] (M : Model κ α)

class IsILR : Prop extends M.IsIL, M.HasR

instance (priority := low) [M.IsIL] [M.HasR] : M.IsILR := {}

end Verbrugge.Model

namespace Logic

open ofILAxioms Veltman Veltman.Model Veltman.Model.World

variable {A B C : Formula α} {κ : Type*} [Nonempty κ] {M : Model κ α}

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

instance : (𝐈𝐋𝐏₀ : Logic α) ⪯ 𝐈𝐋𝐑 :=
  weakerThan_iff.mpr <| subset_of_provable <| by rintro _ ⟨A, B, rfl⟩; exact ILR.axiomP₀

instance : (𝐈𝐋𝐌₀ : Logic α) ⪯ 𝐈𝐋𝐑 :=
  weakerThan_iff.mpr <| subset_of_provable <| by rintro _ ⟨A, B, C, rfl⟩; exact ILR.axiomM₀

theorem ILR.sound [M.IsILR] (h : 𝐈𝐋𝐑 ⊢ A) : M ⊧ A :=
  ofILAxioms.sound (by rintro _ ⟨A, B, C, rfl⟩ x; exact forces_axiomR) h

instance : Consistent (𝐈𝐋𝐑 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILR.sound (M := pointModel fun _ ↦ False) h 0

/-- - [MV20, Theorem 25] -/
theorem ILR.complete_verbrugge {α : Type} {A : Formula α}
    (h : ∀ {κ : Type} [Nonempty κ] (M : Verbrugge.Model κ α), [M.IsILR] → M ⊧ A) :
    𝐈𝐋𝐑 ⊢ A := by
  classical
  by_contra hA;
  have := ofILAxioms.nonempty_countermodelWorld hA;
  have := Verbrugge.countermodel.hasR (A₀ := A) fun {_ _ _} ↦ ILR.axiomR;
  exact ofILAxioms.not_models_verbrugge_countermodel hA (h _)

end Logic

/-- $\mathbf{ILR}$ is complete with respect to Veltman frames. An open problem.
- [MV20, §2.5] -/
def ILRVeltmanCompletenessProblem : Prop :=
  ∀ A : Formula ℕ,
    (∀ (κ : Type) [Nonempty κ] (M : Veltman.Model κ ℕ) [M.IsILR], M ⊧ A) → 𝐈𝐋𝐑 ⊢ A

end FFL.InterpretabilityLogic

