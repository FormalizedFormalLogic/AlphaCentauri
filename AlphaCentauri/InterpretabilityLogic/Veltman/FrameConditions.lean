module

public import AlphaCentauri.InterpretabilityLogic.Logic.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic

/-!
# Frame conditions of the extensions of $\mathbf{IL}$

Frame conditions for the principles beyond $\mathbf{IL}$, the validity of the principles under
them, and the countermodels separating the extensions.
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

lemma forces_axiomP₀ [M.IsIL] [M.HasR] : x ⊩ Axioms.P₀ A B := by
  intro h y Rxy z Ryz hz
  obtain ⟨v, Sxzv, hv⟩ := h z (IsTrans.trans _ _ _ Rxy Ryz) hz
  obtain ⟨u, Rvu, hu⟩ := forces_dia.mp hv
  exact ⟨u, s_of_rel_rel_s_rel Rxy Ryz Sxzv Rvu, hu⟩

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

lemma forces_axiomKW2 [M.IsIL] [M.HasW] : x ⊩ Axioms.KW2 A B := by
  intro h y Rxy hy
  by_contra! hn
  have hA : ∀ z, y ≺[x] z → z ⊩ B → z ⊩ A := fun z Syz hz ↦ by
    by_contra hz'
    exact hn z Syz (forces_and.mpr ⟨hz, hz'⟩)
  obtain ⟨s, Sys, hs⟩ := forces_axiomW (x := x) (A := A) (B := ◇B) h y Rxy (hA y (s_refl Rxy) hy)
  obtain ⟨hsB, hsA⟩ := forces_and.mp hs
  obtain ⟨u, Rsu, hu⟩ := forces_dia.mp hsB
  exact hn u (s_trans Sys (s_of_rel (rel_of_s_right Sys) Rsu))
    (forces_and.mpr ⟨hu, hsA u Rsu⟩)

lemma forces_axiomF [M.IsIL] [M.HasW] : x ⊩ Axioms.F A := by
  intro h y Rxy hy
  obtain ⟨z, Syz, hz⟩ := h y Rxy hy
  obtain ⟨t, ⟨Rxt, ht⟩, tmax⟩ := ConverseWellFounded.iff_has_max.mp (cwf_rel_comp_s x)
    {t | x ≺ t ∧ t ⊩ ◇A} ⟨z, rel_of_s_right Syz, hz⟩
  obtain ⟨u, Rtu, hu⟩ := forces_dia.mp ht
  obtain ⟨v, Suv, hv⟩ := h u (IsTrans.trans _ _ _ Rxt Rtu) hu
  exact tmax v ⟨rel_of_s_right Suv, hv⟩ ⟨u, Rtu, Suv⟩

end Model.World

end Veltman

/-! ### Countermodels to the strict inclusions -/

namespace Logic

open Veltman Veltman.Model Veltman.Model.World

abbrev countermodelW : Model (Fin 3) ℕ where
  Rel' := (· < ·)
  S' w x y := w = 0 ∧ x ≠ 0 ∧ y ≠ 0 ∨ w = 1 ∧ x = 2 ∧ y = 2
  Val' u a := match a with | 1 => u = 1 | _ => u ≠ 0

instance : IsTrans _ countermodelW.Rel := ⟨by decide⟩
instance : Std.Irrefl countermodelW.Rel := ⟨by decide⟩

instance : countermodelW.IsIL where
  rel_of_s_left := by decide
  rel_of_s_right := by decide
  s_refl := by decide
  s_trans := by decide
  s_of_rel := by decide

instance : countermodelW.HasM₀ := ⟨by decide⟩
instance : countermodelW.HasR := ⟨by decide⟩

abbrev countermodelM₀ : Model (Fin 5) ℕ where
  Rel' x y := x = 0 ∧ 0 < y ∨ x = 1 ∧ y = 2 ∨ x = 3 ∧ y = 4
  S' w x y := w = 0 ∧ 1 ≤ x ∧ x ≤ y ∨ w = 1 ∧ x = 2 ∧ y = 2 ∨ w = 3 ∧ x = 4 ∧ y = 4
  Val' t a := match a with | 0 => t = 2 | 1 => t = 3 | 2 => t = 2 | _ => t = 4

instance : IsTrans _ countermodelM₀.Rel := ⟨by decide⟩
instance : Std.Irrefl countermodelM₀.Rel := ⟨by decide⟩

instance : countermodelM₀.IsIL where
  rel_of_s_left := by decide
  rel_of_s_right := by decide
  s_refl := by decide
  s_trans := by decide
  s_of_rel := by decide

end Logic

end FFL.InterpretabilityLogic

end
