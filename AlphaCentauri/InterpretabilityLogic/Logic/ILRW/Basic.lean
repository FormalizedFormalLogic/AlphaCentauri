module

public import AlphaCentauri.InterpretabilityLogic.Logic.ILMZeroW.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILR.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.FrameConditions
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.Basic
import AlphaCentauri.OpenProblem

/-!
# The logic $\mathbf{ILRW}$

The extension of $\mathbf{IL}$ by the principles $\mathsf{R}$ and $\mathsf{W}$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula

variable {α : Type*}

abbrev Logic.ILRW : Logic α :=
  Logic.ofILAxioms ({Axioms.R A B C | (A) (B) (C)} ∪ {Axioms.W A B | (A) (B)})

notation "𝐈𝐋𝐑𝐖" => Logic.ILRW

namespace Veltman.Model

variable {κ α : Type*} [Nonempty κ] (M : Model κ α)

class IsILRW : Prop extends M.IsIL, M.HasR, M.HasW

instance (v : α → Prop) : (pointModel v).IsILRW := {}

instance (priority := low) [M.IsIL] [M.HasR] [M.HasW] : M.IsILRW := {}

end Veltman.Model

namespace Verbrugge.Model

variable {κ α : Type*} [Nonempty κ] (M : Model κ α)

class IsILRW : Prop extends M.IsIL, M.HasR, M.HasW

instance (priority := low) [M.IsIL] [M.HasR] [M.HasW] : M.IsILRW := {}

end Verbrugge.Model

namespace Logic

open ofILAxioms Veltman Veltman.Model Veltman.Model.World

variable {A B C : Formula α} {κ : Type*} [Nonempty κ] {M : Model κ α}

@[simp] lemma ILRW.axiomR : 𝐈𝐋𝐑𝐖 ⊢ Axioms.R A B C := axm <| .inl ⟨A, B, C, rfl⟩

@[simp] lemma ILRW.axiomW : 𝐈𝐋𝐑𝐖 ⊢ Axioms.W A B := axm <| .inr ⟨A, B, rfl⟩

lemma ILRW.axiomRstar : 𝐈𝐋𝐑𝐖 ⊢ Axioms.Rstar A B C := by
  have h : 𝐈𝐋𝐑𝐖 ⊢
      ∼(A ▷ ∼C) ▷ ((B ⋏ □(∼A)) ⋏ □C) 🡒 ∼(A ▷ ∼C) ▷ (B ⋏ □C ⋏ □(∼A)) :=
    rhd_mono_right (by cl_prover);
  cl_prover [axiomW (A := A) (B := B), axiomR (A := A) (B := B ⋏ □(∼A)) (C := C), h];

instance : (𝐈𝐋𝐑 : Logic α) ⪯ 𝐈𝐋𝐑𝐖 := weakerThan_iff.mpr <| subset_of_subset Set.subset_union_left

instance : (𝐈𝐋𝐌₀𝐖 : Logic α) ⪯ 𝐈𝐋𝐑𝐖 := weakerThan_iff.mpr <| subset_of_provable <| by
  rintro _ (⟨A, B, C, rfl⟩ | ⟨A, B, rfl⟩)
  · exact subset_of_subset Set.subset_union_left ILR.axiomM₀
  · exact ILRW.axiomW

theorem ILRW.sound [M.IsILRW] (h : 𝐈𝐋𝐑𝐖 ⊢ A) : M ⊧ A := by
  apply ofILAxioms.sound _ h;
  rintro _ (⟨A, B, C, rfl⟩ | ⟨A, B, rfl⟩) x;
  · exact forces_axiomR;
  · exact forces_axiomW;

instance : Consistent (𝐈𝐋𝐑𝐖 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILRW.sound (M := pointModel fun _ ↦ False) h 0

private abbrev countermodelRW : Model (Fin 3) ℕ where
  Rel' := (· < ·)
  S' w x y := w = 0 ∧ x ≠ 0 ∧ y ≠ 0 ∨ w = 1 ∧ x = 2 ∧ y = 2
  Val' u a := match a with | 1 => u = 1 | _ => u ≠ 0

private instance : IsTrans _ countermodelRW.Rel := ⟨by decide⟩
private instance : Std.Irrefl countermodelRW.Rel := ⟨by decide⟩

private instance : countermodelRW.IsIL where
  rel_of_s_left := by decide
  rel_of_s_right := by decide
  s_refl := by decide
  s_trans := by decide
  s_of_rel := by decide

private instance : countermodelRW.HasR := ⟨by decide⟩

private abbrev countermodelR : Model (Fin 5) ℕ where
  Rel' x y := x = 0 ∧ 0 < y ∨ x = 1 ∧ (y = 2 ∨ y = 4) ∨ x = 3 ∧ y = 4
  S' w x y :=
    w = 0 ∧ 1 ≤ x ∧ x ≤ y ∨ w = 1 ∧ (x = 2 ∧ y = 2 ∨ x = 4 ∧ y = 4) ∨ w = 3 ∧ x = 4 ∧ y = 4
  Val' t a := match a with | 0 => t = 2 | 1 => t = 3 | _ => t = 2

private instance : IsTrans _ countermodelR.Rel := ⟨by decide⟩
private instance : Std.Irrefl countermodelR.Rel := ⟨by decide⟩

private instance : countermodelR.IsIL where
  rel_of_s_left := by decide
  rel_of_s_right := by decide
  s_refl := by decide
  s_trans := by decide
  s_of_rel := by decide

private instance : countermodelR.HasM₀ := ⟨by decide⟩
private instance : countermodelR.HasW := HasW.of_finite (by decide)

instance : (𝐈𝐋𝐑 : Logic ℕ) ⪱ 𝐈𝐋𝐑𝐖 :=
  .of_unprovable_provable (φ := Axioms.W (#0) (#1)) (fun h ↦ by
    have H := ILR.sound (M := countermodelRW) h 0;
    have h₁ : (0 : countermodelRW.World) ⊩[countermodelRW] #0 ▷ #1 := by
      intro u _ hu;
      exact ⟨1, Or.inl ⟨rfl, hu, by decide⟩, rfl⟩;
    obtain ⟨z, _, hz⟩ := H h₁ 1 (by decide) (show (1 : Fin 3) ≠ 0 by decide);
    obtain ⟨hz₁, hz₂⟩ := forces_and.mp hz;
    obtain rfl : z = 1 := hz₁;
    exact hz₂ 2 (by decide) (show (2 : Fin 3) ≠ 0 by decide)) ILRW.axiomW

instance : (𝐈𝐋𝐌₀𝐖 : Logic ℕ) ⪱ 𝐈𝐋𝐑𝐖 :=
  .of_unprovable_provable (φ := Axioms.R (#0) (#1) (#2)) (fun h ↦ by
    have H := ILM₀W.sound (M := countermodelR) h 0;
    have h₁ : (0 : countermodelR.World) ⊩[countermodelR] #0 ▷ #1 := by
      intro v _ hv;
      obtain rfl : v = 2 := hv;
      exact ⟨3, by decide, rfl⟩;
    have h₂ : (1 : countermodelR.World) ⊩[countermodelR] ∼(#0 ▷ ∼(#2)) := by
      apply not_forces_rhd.mpr;
      refine ⟨2, by decide, rfl, ?_⟩;
      intro z hz hz';
      exact hz' ((by decide : ∀ z, countermodelR.S 1 2 z → z = 2) z hz);
    obtain ⟨t, _, ht⟩ := H h₁ 1 (by decide) h₂;
    obtain ⟨htz, ht⟩ := forces_and.mp ht;
    obtain rfl : t = 3 := htz;
    exact (show (4 : Fin 5) ≠ 2 by decide) (ht 4 (by decide))) ILRW.axiomR

end Logic

/-- Is $\mathbf{ILRW}$ complete with respect to Veltman semantics?
- [JMMV20, §6.5] -/
open_problem Logic.ILRW.complete_veltman :=
  ∀ A : Formula ℕ,
    (∀ (κ : Type) [Nonempty κ] (M : Veltman.Model κ ℕ) [M.IsILRW], M ⊧ A) →
      𝐈𝐋𝐑𝐖 ⊢ A

/-- Is $\mathbf{ILRW}$ complete with respect to Verbrugge semantics?
- [JMMV20, §6.5] -/
open_problem Logic.ILRW.complete_verbrugge :=
  ∀ A : Formula ℕ,
    (∀ (κ : Type) [Nonempty κ] (M : Verbrugge.Model κ ℕ) [M.IsILRW], M ⊧ A) →
      𝐈𝐋𝐑𝐖 ⊢ A

end FFL.InterpretabilityLogic

