module

public import AlphaCentauri.InterpretabilityLogic.Logic.ILW.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.FrameConditions

/-!
# The logic $\mathbf{ILF}$

The extension of $\mathbf{IL}$ by the principle $\mathsf{F}$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula

variable {α : Type*}

/-- - [Sve91] -/
abbrev Logic.ILF : Logic α := Logic.ofAxioms {Axioms.F A | (A)}

notation "𝐈𝐋𝐅" => Logic.ILF

namespace Logic

open ofAxioms

variable {A B C : Formula α}

@[simp] lemma ILF.axiomF : 𝐈𝐋𝐅 ⊢ Axioms.F A := axm ⟨A, rfl⟩

instance : (𝐈𝐋𝐅 : Logic α) ⪯ 𝐈𝐋𝐊𝐖𝟐 :=
  weakerThan_iff.mpr <| subset_of_provable <| by rintro _ ⟨A, rfl⟩; exact ILKW2.axiomF

section

open Veltman Veltman.Model Veltman.Model.World

variable {κ : Type*} [Nonempty κ] {M : Model κ α}

theorem ILF.sound [M.IsIL] [M.HasW] (h : 𝐈𝐋𝐅 ⊢ A) : M ⊧ A :=
  ILKW2.sound <| weakerThan_iff.mp inferInstance h

instance : Consistent (𝐈𝐋𝐅 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILF.sound (M := pointModel fun _ ↦ False) h 0

instance : (𝐈𝐋 : Logic ℕ) ⪱ 𝐈𝐋𝐅 :=
  .of_unprovable_provable (φ := Axioms.F (#0)) (fun h ↦ by
    have H := ofAxioms.sound (M := countermodelW) (𝔸 := ∅) (by simp) h 0;
    have h₁ : (0 : countermodelW.World) ⊩[countermodelW] #0 ▷ ◇(#0) := by
      intro u _ hu;
      exact ⟨1, Or.inl ⟨rfl, hu, by decide⟩,
        forces_dia.mpr ⟨2, by decide, show (2 : Fin 3) ≠ 0 by decide⟩⟩;
    exact H h₁ 1 (by decide) (show (1 : Fin 3) ≠ 0 by decide)) ILF.axiomF

end

end Logic

end FFL.InterpretabilityLogic

end
