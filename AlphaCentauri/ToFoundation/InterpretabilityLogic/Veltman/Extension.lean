module

public import AlphaCentauri.ToFoundation.InterpretabilityLogic.Extension
public import AlphaCentauri.ToFoundation.InterpretabilityLogic.Veltman.Basic

/-!
# Veltman semantics of the extensions of $\mathbf{IL}$

Frame conditions for the principles beyond $\mathbf{IL}$, the validity of the principles under
them and the converses, soundness and consistency of the extensions, and strict inclusions among
the extensions.
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

variable {M} {V : M.World → α → Prop}

instance [M.HasM] : (M.overwrite V).HasM := ⟨rel_of_s_rel (M := M)⟩
instance [M.HasM₀] : (M.overwrite V).HasM₀ := ⟨rel_of_rel_rel_s_rel (M := M)⟩
instance [M.HasP] : (M.overwrite V).HasP := ⟨s_of_rel_rel_s (M := M)⟩
instance [M.HasR] : (M.overwrite V).HasR := ⟨s_of_rel_rel_s_rel (M := M)⟩
instance [M.HasW] : (M.overwrite V).HasW := ⟨cwf_rel_comp_s (M := M)⟩

lemma HasW.of_finite [Finite M.World] [M.IsIL] (h : ∀ {w x y : M.World}, x ≺ y → ¬y ≺[w] x) :
    M.HasW where
  cwf_rel_comp_s w :=
    have : IsTrans _ (Relation.Comp M.Rel (M.S w)) := ⟨by
      rintro x y z ⟨u, Rxu, Suy⟩ ⟨v, Ryv, Svz⟩;
      use u;
      and_intros;
      · exact Rxu;
      · exact s_trans Suy <| s_trans (s_of_rel (rel_of_s_right Suy) Ryv) Svz⟩;
    have : Std.Irrefl (Relation.Comp M.Rel (M.S w)) := ⟨by
      rintro x ⟨u, Rxu, Sux⟩;
      exact h Rxu Sux⟩;
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
  intro h y Rxy hy;
  obtain ⟨hA, hC⟩ := forces_and.mp hy;
  obtain ⟨z, Ryz, hz⟩ := forces_dia.mp hA;
  obtain ⟨u, Sxzu, hu⟩ := h z (IsTrans.trans _ _ _ Rxy Ryz) hz;
  use u;
  and_intros;
  · exact s_trans (s_of_rel Rxy Ryz) Sxzu;
  · exact forces_and.mpr ⟨hu, fun v Ruv ↦ hC v (rel_of_rel_rel_s_rel Rxy Ryz Sxzu Ruv)⟩;

lemma forces_axiomP [M.IsIL] [M.HasP] : x ⊩ Axioms.P A B := by
  have := IsTrans.trans (r := M.Rel);
  grind [s_of_rel_rel_s]

lemma forces_axiomR [M.IsIL] [M.HasR] : x ⊩ Axioms.R A B C := by
  intro h y Rxy hy;
  obtain ⟨z, Ryz, hz, hC⟩ := not_forces_rhd.mp hy;
  obtain ⟨u, Sxzu, hu⟩ := h z (IsTrans.trans _ _ _ Rxy Ryz) hz;
  use u;
  and_intros;
  · exact s_trans (s_of_rel Rxy Ryz) Sxzu;
  · exact forces_and.mpr ⟨hu, fun v Ruv ↦ not_not.mp <| hC v (s_of_rel_rel_s_rel Rxy Ryz Sxzu Ruv)⟩;

lemma forces_axiomW [M.IsIL] [M.HasW] : x ⊩ Axioms.W A B := by
  intro h y Rxy hy;
  obtain ⟨z, Sxyz, hz⟩ := h y Rxy hy;
  obtain ⟨t, ⟨Sxyt, ht⟩, tmax⟩ := ConverseWellFounded.iff_has_max.mp (cwf_rel_comp_s x)
    {z | y ≺[x] z ∧ z ⊩ B} ⟨z, Sxyz, hz⟩;
  use t;
  and_intros;
  · exact Sxyt;
  · apply forces_and.mpr;
    and_intros;
    · exact ht;
    · intro u Rtu hu;
      have Rxt : x ≺ t := rel_of_s_right Sxyt;
      obtain ⟨v, Sxuv, hv⟩ := h u (IsTrans.trans _ _ _ Rxt Rtu) hu;
      exact tmax v ⟨s_trans Sxyt <| s_trans (s_of_rel Rxt Rtu) Sxuv, hv⟩ ⟨u, Rtu, Sxuv⟩;

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

/-! ### Correspondence -/

namespace Veltman.Model

open World

variable {κ : Type*} [Nonempty κ] {M : Model κ ℕ}

lemma HasM.of_valid_axiomM [M.IsIL] (h : ∀ V, M.overwrite V ⊧ Axioms.M (#0) (#1) (#2)) :
    M.HasM where
  rel_of_s_rel {w x y z} Sxy Ryz := by
    let V : M.World → ℕ → Prop := fun u a ↦ match a with | 0 => u = x | 1 => u = y | _ => x ≺ u;
    have h₁ : w ⊩[M.overwrite V] #0 ▷ #1 := by
      intro v _ hv;
      use y;
      and_intros;
      · exact (show v = x from hv) ▸ Sxy;
      · rfl;
    obtain ⟨t, -, ht⟩ := h V w h₁ x (rel_of_s_left Sxy) (forces_and.mpr ⟨rfl, fun _ ↦ id⟩);
    obtain ⟨hty, ht⟩ := forces_and.mp ht;
    exact ht z <| (show t = y from hty) ▸ Ryz;

lemma HasM₀.of_valid_axiomM₀ (h : ∀ V, M.overwrite V ⊧ Axioms.M₀ (#0) (#1) (#2)) :
    M.HasM₀ where
  rel_of_rel_rel_s_rel {w x y z u} Rwx Rxy Swyz Rzu := by
    let V : M.World → ℕ → Prop := fun t a ↦ match a with | 0 => t = y | 1 => t = z | _ => x ≺ t;
    have h₁ : w ⊩[M.overwrite V] #0 ▷ #1 := by
      intro v _ hv;
      use z;
      and_intros;
      · exact (show v = y from hv) ▸ Swyz;
      · rfl;
    have h₂ : x ⊩[M.overwrite V] ◇(#0) ⋏ □(#2) :=
      forces_and.mpr ⟨forces_dia.mpr ⟨y, Rxy, rfl⟩, fun _ ↦ id⟩;
    obtain ⟨t, -, ht⟩ := h V w h₁ x Rwx h₂;
    obtain ⟨htz, ht⟩ := forces_and.mp ht;
    exact ht u <| (show t = z from htz) ▸ Rzu;

lemma HasP.of_valid_axiomP (h : ∀ V, M.overwrite V ⊧ Axioms.P (#0) (#1)) : M.HasP where
  s_of_rel_rel_s {w x y z} Rwx Rxy Swyz := by
    let V : M.World → ℕ → Prop := fun t a ↦ match a with | 0 => t = y | _ => t = z;
    have h₁ : w ⊩[M.overwrite V] #0 ▷ #1 := by
      intro v _ hv;
      use z;
      and_intros;
      · exact (show v = y from hv) ▸ Swyz;
      · rfl;
    obtain ⟨t, Sxyt, ht⟩ := h V w h₁ x Rwx y Rxy rfl;
    exact (show t = _ from ht) ▸ Sxyt;

lemma HasR.of_valid_axiomR [M.IsIL] (h : ∀ V, M.overwrite V ⊧ Axioms.R (#0) (#1) (#2)) :
    M.HasR where
  s_of_rel_rel_s_rel {w x y z u} Rwx Rxy Swyz Rzu := by
    let V : M.World → ℕ → Prop := fun t a ↦ match a with | 0 => t = y | 1 => t = z | _ => y ≺[x] t;
    have h₁ : w ⊩[M.overwrite V] #0 ▷ #1 := by
      intro v _ hv;
      use z;
      and_intros;
      · exact (show v = y from hv) ▸ Swyz;
      · rfl;
    have h₂ : x ⊩[M.overwrite V] ∼(#0 ▷ ∼(#2)) := by
      apply not_forces_rhd.mpr;
      use y;
      and_intros;
      · exact Rxy;
      · rfl;
      · exact fun _ Sxyt ht ↦ ht Sxyt;
    obtain ⟨t, -, ht⟩ := h V w h₁ x Rwx h₂;
    obtain ⟨htz, ht⟩ := forces_and.mp ht;
    exact ht u <| (show t = z from htz) ▸ Rzu;

lemma HasR.of_valid_axiomP₀ [M.IsIL] (h : ∀ V, M.overwrite V ⊧ Axioms.P₀ (#0) (#1)) :
    M.HasR where
  s_of_rel_rel_s_rel {w x y z u} Rwx Rxy Swyz Rzu := by
    let V : M.World → ℕ → Prop := fun t a ↦ match a with | 0 => t = y | _ => t = u;
    have h₁ : w ⊩[M.overwrite V] #0 ▷ ◇(#1) := by
      intro v _ hv;
      use z;
      and_intros;
      · exact (show v = y from hv) ▸ Swyz;
      · exact forces_dia.mpr ⟨u, Rzu, rfl⟩;
    obtain ⟨t, Sxyt, ht⟩ := h V w h₁ x Rwx y Rxy rfl;
    exact (show t = _ from ht) ▸ Sxyt;

lemma HasW.of_valid_axiomF [M.IsIL] (h : ∀ V, M.overwrite V ⊧ Axioms.F (#0)) : M.HasW where
  cwf_rel_comp_s w := by
    apply ConverseWellFounded.iff_has_max.mpr;
    intro X hX;
    by_contra! hmax;
    let V : M.World → ℕ → Prop := fun u _ ↦ ∃ x ∈ X, u ≺[w] x;
    have h₁ : w ⊩[M.overwrite V] #0 ▷ ◇(#0) := by
      rintro u - ⟨x, hx, Sux⟩;
      obtain ⟨x', hx', v, Rxv, Svx'⟩ := hmax x hx;
      use x;
      and_intros;
      · exact Sux;
      · exact forces_dia.mpr ⟨v, Rxv, x', hx', Svx'⟩;
    obtain ⟨m, hm⟩ := hX;
    obtain ⟨x, hx, u, -, Sux⟩ := hmax m hm;
    exact h V w h₁ u (rel_of_s_left Sux) ⟨x, hx, Sux⟩;

lemma HasW.of_valid_axiomW [M.IsIL] (h : ∀ V, M.overwrite V ⊧ Axioms.W (#0) (#1)) : M.HasW where
  cwf_rel_comp_s w := by
    apply ConverseWellFounded.iff_has_max.mpr;
    intro X hX;
    by_contra! hmax;
    let V : M.World → ℕ → Prop := fun u a ↦ match a with | 0 => ∃ x ∈ X, u ≺[w] x | _ => u ∈ X;
    have h₁ : w ⊩[M.overwrite V] #0 ▷ #1 := by
      rintro u - ⟨x, hx, Sux⟩;
      use x;
      and_intros;
      · exact Sux;
      · exact hx;
    obtain ⟨m, hm⟩ := hX;
    obtain ⟨x, hx, u, -, Sux⟩ := hmax m hm;
    obtain ⟨z, -, hz⟩ := h V w h₁ u (rel_of_s_left Sux) ⟨x, hx, Sux⟩;
    obtain ⟨hzX, hz⟩ := forces_and.mp hz;
    obtain ⟨x', hx', v, Rzv, Svx'⟩ := hmax z hzX;
    exact hz v Rzv ⟨x', hx', Svx'⟩;

theorem HasM.iff_valid_axiomM [M.IsIL] :
    M.HasM ↔ ∀ V, M.overwrite V ⊧ Axioms.M (#0) (#1) (#2) :=
  ⟨fun _ _ _ ↦ forces_axiomM, of_valid_axiomM⟩

theorem HasM₀.iff_valid_axiomM₀ [M.IsIL] :
    M.HasM₀ ↔ ∀ V, M.overwrite V ⊧ Axioms.M₀ (#0) (#1) (#2) :=
  ⟨fun _ _ _ ↦ forces_axiomM₀, of_valid_axiomM₀⟩

theorem HasP.iff_valid_axiomP [M.IsIL] : M.HasP ↔ ∀ V, M.overwrite V ⊧ Axioms.P (#0) (#1) :=
  ⟨fun _ _ _ ↦ forces_axiomP, of_valid_axiomP⟩

theorem HasR.TFAE [M.IsIL] : [
    M.HasR,
    ∀ V, M.overwrite V ⊧ Axioms.R (#0) (#1) (#2),
    ∀ V, M.overwrite V ⊧ Axioms.P₀ (#0) (#1)
  ].TFAE := by
  tfae_have 1 → 2 := fun _ _ _ ↦ forces_axiomR;
  tfae_have 2 → 1 := of_valid_axiomR;
  tfae_have 1 → 3 := fun _ _ ↦ Logic.ILP₀.sound (by simp);
  tfae_have 3 → 1 := of_valid_axiomP₀;
  tfae_finish;

/-- - [Vis90, §6.2.1] -/
theorem HasW.TFAE [M.IsIL] : [
    M.HasW,
    ∀ V, M.overwrite V ⊧ Axioms.W (#0) (#1),
    ∀ V, M.overwrite V ⊧ Axioms.F (#0)
  ].TFAE := by
  tfae_have 1 → 2 := fun _ _ _ ↦ forces_axiomW;
  tfae_have 2 → 1 := of_valid_axiomW;
  tfae_have 1 → 3 := fun _ _ ↦ Logic.ILF.sound (by simp);
  tfae_have 3 → 1 := of_valid_axiomF;
  tfae_finish;

end Veltman.Model

/-! ### Strict inclusions -/

namespace Logic

open Veltman Veltman.Model

private abbrev countermodelW : Model (Fin 3) ℕ :=
  ⟨(· < ·), fun w x y ↦ w = 0 ∧ x ≠ 0 ∧ y ≠ 0 ∨ w = 1 ∧ x = 2 ∧ y = 2, fun _ _ ↦ False⟩

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

private lemma countermodelW.not_hasW : ¬countermodelW.HasW := fun _ ↦ by
  obtain ⟨_, rfl, h⟩ :=
    ConverseWellFounded.iff_has_max.mp (cwf_rel_comp_s (M := countermodelW) 0) {1} ⟨1, rfl⟩;
  exact h 1 rfl ⟨2, by decide, by decide⟩

private abbrev countermodelM₀ : Model (Fin 5) ℕ where
  Rel' x y := x = 0 ∧ 0 < y ∨ x = 1 ∧ y = 2 ∨ x = 3 ∧ y = 4
  S' w x y := w = 0 ∧ 1 ≤ x ∧ x ≤ y ∨ w = 1 ∧ x = 2 ∧ y = 2 ∨ w = 3 ∧ x = 4 ∧ y = 4
  Val' _ _ := False

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
  Val' _ _ := False

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
  Val' _ _ := False

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
  Val' _ _ := False

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
  .of_unprovable_provable (fun h ↦ countermodelW.not_hasW <|
    HasW.of_valid_axiomF fun _ ↦ ofAxioms.sound (by simp) h) ILF.axiomF

instance : (𝐈𝐋𝐌₀ : Logic ℕ) ⪱ 𝐈𝐋𝐌₀𝐖 :=
  .of_unprovable_provable (fun h ↦ countermodelW.not_hasW <|
    HasW.of_valid_axiomW fun _ ↦ ILM₀.sound h) ILM₀W.axiomW

instance : (𝐈𝐋𝐑 : Logic ℕ) ⪱ 𝐈𝐋𝐑𝐖 :=
  .of_unprovable_provable (fun h ↦ countermodelW.not_hasW <|
    HasW.of_valid_axiomW fun _ ↦ ILR.sound h) ILRW.axiomW

instance : (𝐈𝐋 : Logic ℕ) ⪱ 𝐈𝐋𝐌₀ :=
  .of_unprovable_provable (fun h ↦ by
    have := HasM₀.of_valid_axiomM₀ fun _ ↦ ofAxioms.sound (M := countermodelM₀.overwrite _)
      (by simp) h;
    exact absurd (rel_of_rel_rel_s_rel (M := countermodelM₀) (w := 0) (x := 1) (y := 2) (z := 3)
      (u := 4) (by decide) (by decide) (by decide) (by decide)) (by decide)) ILM₀.axiomM₀

instance : (𝐈𝐋 : Logic ℕ) ⪱ 𝐈𝐋𝐏₀ :=
  .of_unprovable_provable (fun h ↦ by
    have := HasR.of_valid_axiomP₀ fun _ ↦ ofAxioms.sound (M := countermodelM₀.overwrite _)
      (by simp) h;
    exact absurd (s_of_rel_rel_s_rel (M := countermodelM₀) (w := 0) (x := 1) (y := 2) (z := 3)
      (u := 4) (by decide) (by decide) (by decide) (by decide)) (by decide)) ILP₀.axiomP₀

instance : (𝐈𝐋𝐌₀𝐖 : Logic ℕ) ⪱ 𝐈𝐋𝐑𝐖 :=
  .of_unprovable_provable (fun h ↦ by
    have := HasR.of_valid_axiomR fun _ ↦ ILM₀W.sound (M := countermodelR.overwrite _) h;
    exact absurd (s_of_rel_rel_s_rel (M := countermodelR) (w := 0) (x := 1) (y := 2) (z := 3)
      (u := 4) (by decide) (by decide) (by decide) (by decide)) (by decide)) ILRW.axiomR

instance : (𝐈𝐋𝐑𝐖 : Logic ℕ) ⪱ 𝐈𝐋𝐌 :=
  .of_unprovable_provable (fun h ↦ by
    have := HasM.of_valid_axiomM fun _ ↦ ILRW.sound (M := countermodelM.overwrite _) h;
    exact absurd (rel_of_s_rel (M := countermodelM) (w := 0) (x := 1) (y := 2) (z := 3)
      (by decide) (by decide)) (by decide)) ILM.axiomM

instance : (𝐈𝐋𝐑𝐖 : Logic ℕ) ⪱ 𝐈𝐋𝐏 :=
  .of_unprovable_provable (fun h ↦ by
    have := HasP.of_valid_axiomP fun _ ↦ ILRW.sound (M := countermodelP.overwrite _) h;
    exact absurd (s_of_rel_rel_s (M := countermodelP) (w := 0) (x := 1) (y := 2) (z := 3)
      (by decide) (by decide) (by decide)) (by decide)) ILP.axiomP

end Logic

end FFL.InterpretabilityLogic

end
