module

public import AlphaCentauri.InterpretabilityLogic.Veltman.FrameConditions
public import AlphaCentauri.InterpretabilityLogic.Logic.ILKW2.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILM.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMZeroW.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILP.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILR.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILW.Basic

/-!
# Veltman semantics of the remaining extensions of $\mathbf{IL}$

Soundness, consistency, and strict inclusions of the extensions of $\mathbf{IL}$ by the principles
$\mathsf{F}$, $\mathsf{M}$, $\mathsf{P}$, $\mathsf{R}$, and $\mathsf{W}$ and their variants.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment

/-! ### Soundness and consistency -/

namespace Logic

open Veltman Veltman.Model Veltman.Model.World

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {A : Formula α}

theorem ILM.sound [M.IsIL] [M.HasM] (h : 𝐈𝐋𝐌 ⊢ A) : M ⊧ A :=
  ofAxioms.sound (by rintro _ ⟨A, B, C, rfl⟩ x; exact forces_axiomM) h

theorem ILP.sound [M.IsIL] [M.HasP] (h : 𝐈𝐋𝐏 ⊢ A) : M ⊧ A :=
  ofAxioms.sound (by rintro _ ⟨A, B, rfl⟩ x; exact forces_axiomP) h

theorem ILKW2.sound [M.IsIL] [M.HasW] (h : 𝐈𝐋𝐊𝐖𝟐 ⊢ A) : M ⊧ A :=
  ILW.sound <| weakerThan_iff.mp inferInstance h

theorem ILKW1Zero.sound [M.IsIL] [M.HasW] (h : 𝐈𝐋𝐊𝐖𝟏⁰ ⊢ A) : M ⊧ A :=
  ILKW2.sound <| (equiv_iff.mp inferInstance : (𝐈𝐋𝐊𝐖𝟏⁰ : Logic α) = 𝐈𝐋𝐊𝐖𝟐).subset h

theorem ILF.sound [M.IsIL] [M.HasW] (h : 𝐈𝐋𝐅 ⊢ A) : M ⊧ A :=
  ILKW2.sound <| weakerThan_iff.mp inferInstance h

theorem ILR.sound [M.IsIL] [M.HasR] (h : 𝐈𝐋𝐑 ⊢ A) : M ⊧ A :=
  ofAxioms.sound (by rintro _ ⟨A, B, C, rfl⟩ x; exact forces_axiomR) h

theorem ILP₀.sound [M.IsIL] [M.HasR] (h : 𝐈𝐋𝐏₀ ⊢ A) : M ⊧ A :=
  ILR.sound <| weakerThan_iff.mp inferInstance h

theorem ILRW.sound [M.IsIL] [M.HasR] [M.HasW] (h : 𝐈𝐋𝐑𝐖 ⊢ A) : M ⊧ A := by
  apply ofAxioms.sound _ h;
  rintro _ (⟨A, B, C, rfl⟩ | ⟨A, B, rfl⟩) x;
  · exact forces_axiomR;
  · exact forces_axiomW;

theorem ILRStar.sound [M.IsIL] [M.HasR] [M.HasW] (h : 𝐈𝐋𝐑* ⊢ A) : M ⊧ A :=
  ILRW.sound <| (equiv_iff.mp inferInstance : (𝐈𝐋𝐑𝐖 : Logic α) = 𝐈𝐋𝐑*).symm.subset h

instance : Consistent (𝐈𝐋𝐌 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILM.sound (M := pointModel fun _ ↦ False) h 0
instance : Consistent (𝐈𝐋𝐏 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILP.sound (M := pointModel fun _ ↦ False) h 0
instance : Consistent (𝐈𝐋𝐏₀ : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILP₀.sound (M := pointModel fun _ ↦ False) h 0
instance : Consistent (𝐈𝐋𝐅 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILF.sound (M := pointModel fun _ ↦ False) h 0
instance : Consistent (𝐈𝐋𝐊𝐖𝟏⁰ : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILKW1Zero.sound (M := pointModel fun _ ↦ False) h 0
instance : Consistent (𝐈𝐋𝐊𝐖𝟐 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILKW2.sound (M := pointModel fun _ ↦ False) h 0
instance : Consistent (𝐈𝐋𝐑 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILR.sound (M := pointModel fun _ ↦ False) h 0
instance : Consistent (𝐈𝐋𝐑𝐖 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILRW.sound (M := pointModel fun _ ↦ False) h 0
instance : Consistent (𝐈𝐋𝐑* : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILRStar.sound (M := pointModel fun _ ↦ False) h 0

end Logic

/-! ### Strict inclusions -/

namespace Logic

open Veltman Veltman.Model Veltman.Model.World

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

private abbrev countermodelM : Model (Fin 4) ℕ where
  Rel' x y := x = 0 ∧ 0 < y ∨ x = 2 ∧ y = 3
  S' w x y := w = 0 ∧ 1 ≤ x ∧ x ≤ y ∨ w = 2 ∧ x = 3 ∧ y = 3
  Val' t a := match a with | 0 => t = 1 | 1 => t = 2 | _ => False

private instance : IsTrans _ countermodelM.Rel := ⟨by decide⟩
private instance : Std.Irrefl countermodelM.Rel := ⟨by decide⟩

private instance : countermodelM.IsIL where
  rel_of_s_left := by decide
  rel_of_s_right := by decide
  s_refl := by decide
  s_trans := by decide
  s_of_rel := by decide

private instance : countermodelM.HasR := ⟨by decide⟩
private instance : countermodelM.HasW := HasW.of_finite (by decide)

private abbrev countermodelP : Model (Fin 4) ℕ where
  Rel' x y := x = 0 ∧ 0 < y ∨ x = 1 ∧ y = 2
  S' w x y := w = 0 ∧ 1 ≤ x ∧ x ≤ y ∨ w = 1 ∧ x = 2 ∧ y = 2
  Val' t a := match a with | 0 => t = 2 | _ => t = 3

private instance : IsTrans _ countermodelP.Rel := ⟨by decide⟩
private instance : Std.Irrefl countermodelP.Rel := ⟨by decide⟩

private instance : countermodelP.IsIL where
  rel_of_s_left := by decide
  rel_of_s_right := by decide
  s_refl := by decide
  s_trans := by decide
  s_of_rel := by decide

private instance : countermodelP.HasR := ⟨by decide⟩
private instance : countermodelP.HasW := HasW.of_finite (by decide)

instance : (𝐈𝐋 : Logic ℕ) ⪱ 𝐈𝐋𝐅 :=
  .of_unprovable_provable (φ := Axioms.F (#0)) (fun h ↦ by
    have H := ofAxioms.sound (M := countermodelW) (𝔸 := ∅) (by simp) h 0;
    have h₁ : (0 : countermodelW.World) ⊩[countermodelW] #0 ▷ ◇(#0) := by
      intro u _ hu;
      exact ⟨1, Or.inl ⟨rfl, hu, by decide⟩,
        forces_dia.mpr ⟨2, by decide, show (2 : Fin 3) ≠ 0 by decide⟩⟩;
    exact H h₁ 1 (by decide) (show (1 : Fin 3) ≠ 0 by decide)) ILF.axiomF

instance : (𝐈𝐋𝐑 : Logic ℕ) ⪱ 𝐈𝐋𝐑𝐖 :=
  .of_unprovable_provable (φ := Axioms.W (#0) (#1)) (fun h ↦ by
    have H := ILR.sound (M := countermodelW) h 0;
    have h₁ : (0 : countermodelW.World) ⊩[countermodelW] #0 ▷ #1 := by
      intro u _ hu;
      exact ⟨1, Or.inl ⟨rfl, hu, by decide⟩, rfl⟩;
    obtain ⟨z, _, hz⟩ := H h₁ 1 (by decide) (show (1 : Fin 3) ≠ 0 by decide);
    obtain ⟨hz₁, hz₂⟩ := forces_and.mp hz;
    obtain rfl : z = 1 := hz₁;
    exact hz₂ 2 (by decide) (show (2 : Fin 3) ≠ 0 by decide)) ILRW.axiomW

instance : (𝐈𝐋 : Logic ℕ) ⪱ 𝐈𝐋𝐏₀ :=
  .of_unprovable_provable (φ := Axioms.P₀ (#0) (#3)) (fun h ↦ by
    have H := ofAxioms.sound (M := countermodelM₀) (𝔸 := ∅) (by simp) h 0;
    have h₁ : (0 : countermodelM₀.World) ⊩[countermodelM₀] #0 ▷ ◇(#3) := by
      intro v _ hv;
      obtain rfl : v = 2 := hv;
      exact ⟨3, by decide, forces_dia.mpr ⟨4, by decide, rfl⟩⟩;
    obtain ⟨t, hSt, ht⟩ := H h₁ 1 (by decide) 2 (by decide) rfl;
    obtain rfl : t = 4 := ht;
    exact absurd hSt (by decide)) ILP₀.axiomP₀

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

instance : (𝐈𝐋𝐑𝐖 : Logic ℕ) ⪱ 𝐈𝐋𝐌 :=
  .of_unprovable_provable (φ := Axioms.M (#0) (#1) (#2)) (fun h ↦ by
    have H := ILRW.sound (M := countermodelM) h 0;
    have h₁ : (0 : countermodelM.World) ⊩[countermodelM] #0 ▷ #1 := by
      intro v _ hv;
      obtain rfl : v = 1 := hv;
      exact ⟨2, by decide, rfl⟩;
    obtain ⟨t, _, ht⟩ := H h₁ 1 (by decide) (forces_and.mpr ⟨rfl, fun y hy ↦
      ((by decide : ∀ y, ¬countermodelM.Rel 1 y) y hy).elim⟩);
    obtain ⟨htz, ht⟩ := forces_and.mp ht;
    obtain rfl : t = 2 := htz;
    exact ht 3 (by decide)) ILM.axiomM

instance : (𝐈𝐋𝐑𝐖 : Logic ℕ) ⪱ 𝐈𝐋𝐏 :=
  .of_unprovable_provable (φ := Axioms.P (#0) (#1)) (fun h ↦ by
    have H := ILRW.sound (M := countermodelP) h 0;
    have h₁ : (0 : countermodelP.World) ⊩[countermodelP] #0 ▷ #1 := by
      intro v _ hv;
      obtain rfl : v = 2 := hv;
      exact ⟨3, by decide, rfl⟩;
    obtain ⟨t, hSt, ht⟩ := H h₁ 1 (by decide) 2 (by decide) rfl;
    obtain rfl : t = 3 := ht;
    exact absurd hSt (by decide)) ILP.axiomP

end Logic

end FFL.InterpretabilityLogic

end
