module

public import Foundation.ProvabilityLogic.GL.Basic

/-!
# The LR-closure is finite up to $\mathbf{GL}$-equivalence
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment Formula Kripke Kripke.Model Kripke.Model.World

universe u

variable {α : Type u}

namespace Logic.GL

variable {A B : Formula α}

lemma of_forces
    (h : ∀ {κ : Type u} [Nonempty κ] (M : Model κ α) [M.IsFiniteGL] (x : M.World), x ⊩ A) :
    𝐆𝐋 ⊢ A :=
  iff_valid_finite.mpr fun M _ x ↦ h M x

lemma forces {κ : Type*} [Nonempty κ] {M : Model κ α} [M.IsGL] (h : 𝐆𝐋 ⊢ A) (x : M.World) :
    x ⊩ A :=
  sound M h x

end Logic.GL

namespace Kripke.Model.World

variable [DecidableEq α] {κ : Type*} [Nonempty κ] {M : Model κ α}
  {a : α} {x : M.World} {D E : Formula α}

/-- A formula and its instance substituting `⊥` for `a` agree at a world where `a` fails at the
world and above it. -/
lemma forces_subst_bot_iff [IsTrans _ M.Rel] (h : ∀ y, x = y ∨ x ≺ y → ¬M y a) : x ⊩ D ↔ x ⊩ D⟦a ↦ ⊥⟧ := by
  induction D generalizing x with
  | atom b =>
    by_cases hb : b = a
    · subst hb
      simpa using h x (.inl rfl)
    · simp [hb]
  | falsum => rfl
  | imp D E ihD ihE => exact imp_congr (ihD h) (ihE h)
  | box D ih =>
    refine forall_congr' fun y ↦ imp_congr_right fun Rxy ↦ ih fun z hz ↦ h z (.inr ?_)
    rcases hz with rfl | Ryz
    · exact Rxy
    · exact IsTrans.trans _ _ _ Rxy Ryz

omit [DecidableEq α] in
private lemma forces_box_neg_and_box_of [M.IsGL]
    (hDE : ∀ y : M.World, (∀ z, y = z ∨ y ≺ z → ¬M z a) → (y ⊩ D ↔ y ⊩ E))
    (hx : x ⊩ □(∼(#a ⋏ □D))) : x ⊩ □(∼(#a ⋏ □E)) := by
  intro y Rxy hy
  obtain ⟨hya, hyE⟩ := forces_and.mp hy
  have hn : ∀ z, y ≺ z → ¬M z a := by
    intro z Ryz hz
    obtain ⟨t, ⟨Ryt, ht⟩, tmax⟩ := M.terminalOf {t | y ≺ t ∧ M t a} ⟨z, Ryz, hz⟩
    obtain ⟨u, Rtu, hu⟩ := not_forces_box.mp fun h ↦
      hx t (IsTrans.trans _ _ _ Rxy Ryt) (forces_and.mpr ⟨ht, h⟩)
    apply hu
    apply (hDE u _).mpr (hyE u (IsTrans.trans _ _ _ Ryt Rtu))
    intro v huv hv
    rcases huv with rfl | Ruv
    · exact tmax u ⟨IsTrans.trans _ _ _ Ryt Rtu, hv⟩ Rtu
    · exact tmax v ⟨IsTrans.trans _ _ _ (IsTrans.trans _ _ _ Ryt Rtu) Ruv, hv⟩
        (IsTrans.trans _ _ _ Rtu Ruv)
  apply hx y Rxy (forces_and.mpr ⟨hya, fun z Ryz ↦ (hDE z ?_).mpr (hyE z Ryz)⟩)
  rintro w (rfl | Rzw)
  · exact hn _ Ryz
  · exact hn w (IsTrans.trans _ _ _ Ryz Rzw)

end Kripke.Model.World

namespace Logic.GL

variable [DecidableEq α] {a : α} {D : Formula α}

/-- - [Ign91, Lemma 6.3] -/
lemma box_neg_and_box_iff_subst_bot : 𝐆𝐋 ⊢ □(∼(#a ⋏ □D)) 🡘 □(∼(#a ⋏ □D⟦a ↦ ⊥⟧)) := by
  apply of_forces
  intro κ _ M _ x
  have h (y : M.World) (hy : ∀ z, y = z ∨ y ≺ z → ¬M z a) : y ⊩ D ↔ y ⊩ D⟦a ↦ ⊥⟧ :=
    forces_subst_bot_iff hy
  exact forces_iff.mpr ⟨forces_box_neg_and_box_of h, forces_box_neg_and_box_of fun y hy ↦ (h y hy).symm⟩

end Logic.GL

end FFL.ProvabilityLogic
