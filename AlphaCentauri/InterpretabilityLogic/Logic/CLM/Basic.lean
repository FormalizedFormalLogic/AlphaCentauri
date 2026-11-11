module

public import AlphaCentauri.InterpretabilityLogic.Logic.CL.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILM.Basic

/-!
# The logic $\mathbf{CLM}$

The extension of $\mathbf{CL}$ by the principle $\mathsf{M}$, and its soundness with respect to the
$\mathbf{CL}$-models satisfying the frame condition of $\mathsf{M}$. $\mathbf{CLM}$ lies strictly
between $\mathbf{CL}$ and $\mathbf{ILM}$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula

variable {α : Type*}

/-- - [Ign91, Definition 2.3] -/
abbrev Logic.CLM : Logic α := Logic.ofCLAxioms {Axioms.M A B C | (A) (B) (C)}

notation "𝐂𝐋𝐌" => Logic.CLM

namespace Logic

open ofCLAxioms

variable {A B C : Formula α}

@[simp] lemma CLM.axiomM : 𝐂𝐋𝐌 ⊢ Axioms.M A B C := axm ⟨A, B, C, rfl⟩

instance : (𝐂𝐋 : Logic α) ⪯ 𝐂𝐋𝐌 := weakerThan_iff.mpr <| subset_of_subset (Set.empty_subset _)

instance : (𝐂𝐋𝐌 : Logic α) ⪯ 𝐈𝐋𝐌 := by
  rw [weakerThan_iff, ILM, ofILAxioms.eq_ofCLAxioms];
  exact subset_of_subset Set.subset_union_right;

/-! ## Soundness -/

open Veltman Veltman.Model.World

/-- - [Ign91, Definition 3.3]
- [Ign91, Lemma 3.5]
-/
theorem CLM.sound {κ : Type*} [Nonempty κ] {M : Veltman.Model κ α} [M.IsCL] [M.HasM]
    (h : 𝐂𝐋𝐌 ⊢ A) : M ⊧ A :=
  ofCLAxioms.sound (by rintro _ ⟨A, B, C, rfl⟩ x; exact forces_axiomM) h

end Logic

/-! ## Strict inclusions -/

instance : (Veltman.countermodelJ5 α).HasM := ⟨by omega⟩

namespace Logic

open Veltman

instance : (𝐂𝐋 : Logic ℕ) ⪱ 𝐂𝐋𝐌 :=
  .of_unprovable_provable (φ := Axioms.M (#0) (#1) (#2))
    (fun h ↦ countermodelM.not_models_axiomM (CL.sound h)) CLM.axiomM

instance : (𝐂𝐋𝐌 : Logic ℕ) ⪱ 𝐈𝐋𝐌 :=
  .of_unprovable_provable (φ := Axioms.J5 (□⊥))
    (fun h ↦ countermodelJ5.not_models_axiomJ5 (CLM.sound (M := countermodelJ5 ℕ) h))
    ofILAxioms.axiomJ5

end Logic

end FFL.InterpretabilityLogic
