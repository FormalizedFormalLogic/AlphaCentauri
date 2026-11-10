module

public import AlphaCentauri.InterpretabilityLogic.Logic.ILKW2.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.Extension

/-!
# The logic $\mathbf{ILKW1}^0$

The extension of $\mathbf{IL}$ by the principle $\mathsf{KW1}^0$, which is equivalent to
$\mathbf{ILKW2}$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula

variable {α : Type*}

/-- - [Sve91] -/
abbrev Logic.ILKW1Zero : Logic α := Logic.ofAxioms {Axioms.KW1Zero A B | (A) (B)}

notation "𝐈𝐋𝐊𝐖𝟏⁰" => Logic.ILKW1Zero

namespace Logic

open ofAxioms

variable {A B C : Formula α}

@[simp] lemma ILKW1Zero.axiomKW1Zero : 𝐈𝐋𝐊𝐖𝟏⁰ ⊢ Axioms.KW1Zero A B := axm ⟨A, B, rfl⟩

lemma ILKW1Zero.axiomKW2 : 𝐈𝐋𝐊𝐖𝟏⁰ ⊢ Axioms.KW2 A B := by
  have h : 𝐈𝐋𝐊𝐖𝟏⁰ ⊢ A ▷ ◇B 🡒 (B ⋏ A) ▷ ◇B := rhd_anti_left and₂;
  cl_prover [h, axiomKW1Zero (A := A) (B := B)];

instance : (𝐈𝐋𝐊𝐖𝟏⁰ : Logic α) ≊ 𝐈𝐋𝐊𝐖𝟐 := equiv_iff.mpr <| subset_antisymm
  (subset_of_provable <| by rintro _ ⟨A, B, rfl⟩; exact ILKW2.axiomKW1Zero)
  (subset_of_provable <| by rintro _ ⟨A, B, rfl⟩; exact ILKW1Zero.axiomKW2)

section

open Veltman Veltman.Model Veltman.Model.World

variable {κ : Type*} [Nonempty κ] {M : Model κ α}

theorem ILKW1Zero.sound [M.IsIL] [M.HasW] (h : 𝐈𝐋𝐊𝐖𝟏⁰ ⊢ A) : M ⊧ A :=
  ILKW2.sound <| (equiv_iff.mp inferInstance : (𝐈𝐋𝐊𝐖𝟏⁰ : Logic α) = 𝐈𝐋𝐊𝐖𝟐).subset h

instance : Consistent (𝐈𝐋𝐊𝐖𝟏⁰ : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILKW1Zero.sound (M := pointModel fun _ ↦ False) h 0

end

end Logic

end FFL.InterpretabilityLogic

end
