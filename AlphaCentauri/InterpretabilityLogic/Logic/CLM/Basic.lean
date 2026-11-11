module

public import AlphaCentauri.InterpretabilityLogic.Logic.CL.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILM.Basic
public import AlphaCentauri.ToFoundation.ProvabilityLogic.GL.LRClosure

/-!
# The logic $\mathbf{CLM}$

The extension of $\mathbf{CL}$ by the principle $\mathsf{M}$, and its soundness with respect to the
$\mathbf{CL}$-models satisfying the frame condition of $\mathsf{M}$.
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

/-! ## Modal formulas over formulas -/

namespace Formula

/-- The formula obtained from a modal formula whose atoms are formulas by reading each atom as
itself. -/
def ofModal : ProvabilityLogic.Formula (Formula α) → Formula α
  | .atom A => A
  | .falsum => ⊥
  | .imp A B => ofModal A 🡒 ofModal B
  | .box A => □(ofModal A)

@[simp] lemma ofModal_atom {A : Formula α} : ofModal (.atom A) = A := rfl
@[simp] lemma ofModal_falsum : ofModal (⊥ : ProvabilityLogic.Formula (Formula α)) = ⊥ := rfl
@[simp] lemma ofModal_imp {A B : ProvabilityLogic.Formula (Formula α)} :
    ofModal (A 🡒 B) = ofModal A 🡒 ofModal B := rfl
@[simp] lemma ofModal_box {A : ProvabilityLogic.Formula (Formula α)} :
    ofModal (□A) = □(ofModal A) := rfl

end Formula

namespace Logic

variable {L : Logic α} [L.ExtendsGL] [Entailment.Cl L]

lemma provable_ofModal {A : ProvabilityLogic.Formula (Formula α)} (h : 𝐆𝐋 ⊢ A) :
    L ⊢ Formula.ofModal A := by
  induction h with
  | axm h =>
    rcases h with ⟨B, rfl⟩ | ⟨B, rfl⟩
    · exact axiom4
    · exact ExtendsGL.axiomL
  | mdp _ _ ih₁ ih₂ => exact ih₁ ⨀ ih₂
  | nec _ ih => exact provable_box ih
  | verum => exact verum
  | implyK => exact implyK
  | implyS => exact implyS
  | andElimL => exact and₁
  | andElimR => exact and₂
  | andIntro => exact and₃
  | orIntroL => exact or₁
  | orIntroR => exact or₂
  | orElim => exact or₃
  | dne => exact dne
  | axiomK => exact ExtendsGL.axiomK

end Logic

end FFL.InterpretabilityLogic
