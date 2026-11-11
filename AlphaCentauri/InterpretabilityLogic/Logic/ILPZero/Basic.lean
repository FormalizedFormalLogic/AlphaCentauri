module

public import AlphaCentauri.InterpretabilityLogic.Logic.IL.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.FrameConditions
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.MaximalConsistentTheoryModel

/-!
# The logic $\mathbf{ILP}_0$

The extension of $\mathbf{IL}$ by the principle $\mathsf{P}_0$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula

variable {α : Type*}

/-- - [GJ08] -/
abbrev Logic.ILP₀ : Logic α := Logic.ofAxioms {Axioms.P₀ A B | (A) (B)}

notation "𝐈𝐋𝐏₀" => Logic.ILP₀

namespace Verbrugge.Model

variable {κ α : Type*} [Nonempty κ] (M : Model κ α)

class IsILPZero : Prop extends M.IsIL, M.HasP₀

instance (priority := low) [M.IsIL] [M.HasP₀] : M.IsILPZero := {}

end Verbrugge.Model

namespace Logic

open ofAxioms Veltman Veltman.Model Veltman.Model.World

variable {A B C : Formula α} {κ : Type*} [Nonempty κ] {M : Model κ α}

@[simp] lemma ILP₀.axiomP₀ : 𝐈𝐋𝐏₀ ⊢ Axioms.P₀ A B := axm ⟨A, B, rfl⟩

theorem ILP₀.sound [M.IsIL] [M.HasR] (h : 𝐈𝐋𝐏₀ ⊢ A) : M ⊧ A :=
  ofAxioms.sound (by rintro _ ⟨A, B, rfl⟩ x; exact forces_axiomP₀) h

instance : Consistent (𝐈𝐋𝐏₀ : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILP₀.sound (M := pointModel fun _ ↦ False) h 0

private abbrev countermodelPZeroM₀ : Model (Fin 5) ℕ where
  Rel' x y := x = 0 ∧ 0 < y ∨ x = 1 ∧ y = 2 ∨ x = 3 ∧ y = 4
  S' w x y := w = 0 ∧ 1 ≤ x ∧ x ≤ y ∨ w = 1 ∧ x = 2 ∧ y = 2 ∨ w = 3 ∧ x = 4 ∧ y = 4
  Val' t a := match a with | 0 => t = 2 | 1 => t = 3 | 2 => t = 2 | _ => t = 4

private instance : IsTrans _ countermodelPZeroM₀.Rel := ⟨by decide⟩
private instance : Std.Irrefl countermodelPZeroM₀.Rel := ⟨by decide⟩

private instance : countermodelPZeroM₀.IsIL where
  rel_of_s_left := by decide
  rel_of_s_right := by decide
  s_refl := by decide
  s_trans := by decide
  s_of_rel := by decide

instance : (𝐈𝐋 : Logic ℕ) ⪱ 𝐈𝐋𝐏₀ :=
  .of_unprovable_provable (φ := Axioms.P₀ (#0) (#3)) (fun h ↦ by
    have H := ofAxioms.sound (M := countermodelPZeroM₀) (𝔸 := ∅) (by simp) h 0;
    have h₁ : (0 : countermodelPZeroM₀.World) ⊩[countermodelPZeroM₀] #0 ▷ ◇(#3) := by
      intro v _ hv;
      obtain rfl : v = 2 := hv;
      exact ⟨3, by decide, forces_dia.mpr ⟨4, by decide, rfl⟩⟩;
    obtain ⟨t, hSt, ht⟩ := H h₁ 1 (by decide) 2 (by decide) rfl;
    obtain rfl : t = 4 := ht;
    exact absurd hSt (by decide)) ILP₀.axiomP₀

/-- - [MV20, Theorem 23] -/
theorem ILP₀.complete_verbrugge {α : Type} {A : Formula α}
    (h : ∀ {κ : Type} [Nonempty κ] (M : Verbrugge.Model κ α), [M.IsILPZero] → M ⊧ A) :
    𝐈𝐋𝐏₀ ⊢ A := by
  classical
  by_contra hA;
  have := ofAxioms.nonempty_countermodelWorld hA;
  have := Verbrugge.countermodel.hasP₀ (A₀ := A) fun {_ _} ↦ ILP₀.axiomP₀;
  exact ofAxioms.not_models_verbrugge_countermodel hA (h _)

end Logic

end FFL.InterpretabilityLogic

