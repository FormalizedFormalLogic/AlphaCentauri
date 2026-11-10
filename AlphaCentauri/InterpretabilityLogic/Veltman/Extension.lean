module

public import AlphaCentauri.InterpretabilityLogic.Logic
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic

/-!
# Veltman semantics of the extensions of $\mathbf{IL}$

Frame conditions for the principles beyond $\mathbf{IL}$, the validity of the principles under
them, soundness and consistency of the extensions, and strict inclusions among the extensions.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment

namespace Veltman

namespace Model

variable {κ α : Type*} [Nonempty κ] (M : Model κ α)

/-- - [Vis90, §6.4.1] -/
class HasM : Prop where
  rel_of_s_rel {w x y z : M.World} : x ≺[w] y → y ≺ z → x ≺ z

class HasM₀ : Prop where
  rel_of_rel_rel_s_rel {w x y z u : M.World} : w ≺ x → x ≺ y → y ≺[w] z → z ≺ u → x ≺ u

/-- - [Vis90, §6.3] -/
class HasP : Prop where
  s_of_rel_rel_s {w x y z : M.World} : w ≺ x → x ≺ y → y ≺[w] z → y ≺[x] z

class HasR : Prop where
  s_of_rel_rel_s_rel {w x y z u : M.World} : w ≺ x → x ≺ y → y ≺[w] z → z ≺ u → y ≺[x] u

/-- For every world `w`, the composition of `≺` and `≺[w]` is conversely well-founded.

- [Vis90, §6.2]
-/
class HasW : Prop where
  cwf_rel_comp_s (w : M.World) : ConverseWellFounded (Relation.Comp M.Rel (M.S w))

export HasM (rel_of_s_rel)
export HasM₀ (rel_of_rel_rel_s_rel)
export HasP (s_of_rel_rel_s)
export HasR (s_of_rel_rel_s_rel)
export HasW (cwf_rel_comp_s)

variable {M}
lemma HasW.of_finite [Finite M.World] [M.IsIL] (h : ∀ {w x y : M.World}, x ≺ y → ¬y ≺[w] x) :
    M.HasW where
  cwf_rel_comp_s w :=
    have : IsTrans _ (Relation.Comp M.Rel (M.S w)) := ⟨by
      rintro x y z ⟨u, Rxu, Suy⟩ ⟨v, Ryv, Svz⟩
      exact ⟨u, Rxu, s_trans Suy <| s_trans (s_of_rel (rel_of_s_right Suy) Ryv) Svz⟩⟩
    have : Std.Irrefl (Relation.Comp M.Rel (M.S w)) := ⟨by
      rintro x ⟨u, Rxu, Sux⟩
      exact h Rxu Sux⟩
    Finite.converseWellFounded_of_trans_of_irrefl

variable (v : α → Prop)

instance : (pointModel v).HasM := ⟨by tauto⟩
instance : (pointModel v).HasM₀ := ⟨by tauto⟩
instance : (pointModel v).HasP := ⟨by tauto⟩
instance : (pointModel v).HasR := ⟨by tauto⟩
instance : (pointModel v).HasW := HasW.of_finite (by tauto)

end Model

namespace Model.World

open Model

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {x : M.World} {A B C : Formula α}

lemma forces_axiomM [M.HasM] : x ⊩ Axioms.M A B C := by grind [rel_of_s_rel]

lemma forces_axiomM₀ [M.IsIL] [M.HasM₀] : x ⊩ Axioms.M₀ A B C := by
  intro h y Rxy hy
  obtain ⟨hA, hC⟩ := forces_and.mp hy
  obtain ⟨z, Ryz, hz⟩ := forces_dia.mp hA
  obtain ⟨u, Sxzu, hu⟩ := h z (IsTrans.trans _ _ _ Rxy Ryz) hz
  exact ⟨u, s_trans (s_of_rel Rxy Ryz) Sxzu,
    forces_and.mpr ⟨hu, fun v Ruv ↦ hC v (rel_of_rel_rel_s_rel Rxy Ryz Sxzu Ruv)⟩⟩

lemma forces_axiomP [M.IsIL] [M.HasP] : x ⊩ Axioms.P A B := by
  have := IsTrans.trans (r := M.Rel)
  grind [s_of_rel_rel_s]

lemma forces_axiomR [M.IsIL] [M.HasR] : x ⊩ Axioms.R A B C := by
  intro h y Rxy hy
  obtain ⟨z, Ryz, hz, hC⟩ := not_forces_rhd.mp hy
  obtain ⟨u, Sxzu, hu⟩ := h z (IsTrans.trans _ _ _ Rxy Ryz) hz
  exact ⟨u, s_trans (s_of_rel Rxy Ryz) Sxzu,
    forces_and.mpr ⟨hu, fun v Ruv ↦ not_not.mp <| hC v (s_of_rel_rel_s_rel Rxy Ryz Sxzu Ruv)⟩⟩

lemma forces_axiomW [M.IsIL] [M.HasW] : x ⊩ Axioms.W A B := by
  intro h y Rxy hy
  obtain ⟨z, Sxyz, hz⟩ := h y Rxy hy
  obtain ⟨t, ⟨Sxyt, ht⟩, tmax⟩ := ConverseWellFounded.iff_has_max.mp (cwf_rel_comp_s x)
    {z | y ≺[x] z ∧ z ⊩ B} ⟨z, Sxyz, hz⟩
  refine ⟨t, Sxyt, forces_and.mpr ⟨ht, ?_⟩⟩
  intro u Rtu hu
  have Rxt : x ≺ t := rel_of_s_right Sxyt
  obtain ⟨v, Sxuv, hv⟩ := h u (IsTrans.trans _ _ _ Rxt Rtu) hu
  exact tmax v ⟨s_trans Sxyt <| s_trans (s_of_rel Rxt Rtu) Sxuv, hv⟩ ⟨u, Rtu, Sxuv⟩

end Model.World

end Veltman

/-! ### Soundness and consistency -/

namespace Logic

open Veltman Veltman.Model Veltman.Model.World

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {A : Formula α}

theorem ILM₀.sound [M.IsIL] [M.HasM₀] (h : 𝐈𝐋𝐌₀ ⊢ A) : M ⊧ A :=
  ofAxioms.sound (by rintro _ ⟨A, B, C, rfl⟩ x; exact forces_axiomM₀) h

theorem ILM.sound [M.IsIL] [M.HasM] (h : 𝐈𝐋𝐌 ⊢ A) : M ⊧ A :=
  ofAxioms.sound (by rintro _ ⟨A, B, C, rfl⟩ x; exact forces_axiomM) h

theorem ILP.sound [M.IsIL] [M.HasP] (h : 𝐈𝐋𝐏 ⊢ A) : M ⊧ A :=
  ofAxioms.sound (by rintro _ ⟨A, B, rfl⟩ x; exact forces_axiomP) h

theorem ILW.sound [M.IsIL] [M.HasW] (h : 𝐈𝐋𝐖 ⊢ A) : M ⊧ A :=
  ofAxioms.sound (by rintro _ ⟨A, B, rfl⟩ x; exact forces_axiomW) h

theorem ILM₀W.sound [M.IsIL] [M.HasM₀] [M.HasW] (h : 𝐈𝐋𝐌₀𝐖 ⊢ A) : M ⊧ A := by
  apply ofAxioms.sound _ h;
  rintro _ (⟨A, B, C, rfl⟩ | ⟨A, B, rfl⟩) x;
  · exact forces_axiomM₀;
  · exact forces_axiomW;

theorem ILWStar.sound [M.IsIL] [M.HasM₀] [M.HasW] (h : 𝐈𝐋𝐖* ⊢ A) : M ⊧ A :=
  ILM₀W.sound <| (equiv_iff.mp inferInstance : (𝐈𝐋𝐖* : Logic α) = 𝐈𝐋𝐌₀𝐖).subset h

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

instance : Consistent (𝐈𝐋𝐌₀ : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILM₀.sound (M := pointModel fun _ ↦ False) h 0
instance : Consistent (𝐈𝐋𝐌 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILM.sound (M := pointModel fun _ ↦ False) h 0
instance : Consistent (𝐈𝐋𝐏 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILP.sound (M := pointModel fun _ ↦ False) h 0
instance : Consistent (𝐈𝐋𝐏₀ : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILP₀.sound (M := pointModel fun _ ↦ False) h 0
instance : Consistent (𝐈𝐋𝐖 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILW.sound (M := pointModel fun _ ↦ False) h 0
instance : Consistent (𝐈𝐋𝐖* : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILWStar.sound (M := pointModel fun _ ↦ False) h 0
instance : Consistent (𝐈𝐋𝐌₀𝐖 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILM₀W.sound (M := pointModel fun _ ↦ False) h 0
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

private abbrev countermodelW : Model (Fin 3) ℕ where
  Rel' := (· < ·)
  S' w x y := w = 0 ∧ x ≠ 0 ∧ y ≠ 0 ∨ w = 1 ∧ x = 2 ∧ y = 2
  Val' u a := match a with | 1 => u = 1 | _ => u ≠ 0

private instance : IsTrans _ countermodelW.Rel := ⟨by decide⟩
private instance : Std.Irrefl countermodelW.Rel := ⟨by decide⟩

private instance : countermodelW.IsIL where
  rel_of_s_left := by decide
  rel_of_s_right := by decide
  s_refl := by decide
  s_trans := by decide
  s_of_rel := by decide

private instance : countermodelW.HasM₀ := ⟨by decide⟩
private instance : countermodelW.HasR := ⟨by decide⟩

private abbrev countermodelM₀ : Model (Fin 5) ℕ where
  Rel' x y := x = 0 ∧ 0 < y ∨ x = 1 ∧ y = 2 ∨ x = 3 ∧ y = 4
  S' w x y := w = 0 ∧ 1 ≤ x ∧ x ≤ y ∨ w = 1 ∧ x = 2 ∧ y = 2 ∨ w = 3 ∧ x = 4 ∧ y = 4
  Val' t a := match a with | 0 => t = 2 | 1 => t = 3 | 2 => t = 2 | _ => t = 4

private instance : IsTrans _ countermodelM₀.Rel := ⟨by decide⟩
private instance : Std.Irrefl countermodelM₀.Rel := ⟨by decide⟩

private instance : countermodelM₀.IsIL where
  rel_of_s_left := by decide
  rel_of_s_right := by decide
  s_refl := by decide
  s_trans := by decide
  s_of_rel := by decide

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

instance : (𝐈𝐋 : Logic ℕ) ⪱ 𝐈𝐋𝐌₀ :=
  .of_unprovable_provable (φ := Axioms.M₀ (#0) (#1) (#2)) (fun h ↦ by
    have H := ofAxioms.sound (M := countermodelM₀) (𝔸 := ∅) (by simp) h 0;
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
