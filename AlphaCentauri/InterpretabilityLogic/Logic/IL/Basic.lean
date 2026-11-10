module

public import AlphaCentauri.InterpretabilityLogic.Logic.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinus.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.IndexedSetModel
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.Basic

/-!
# Interpretability logic $\mathbf{IL}$

$\mathbf{IL}$ is the logic `ofAxioms ∅`, contained in every extension by axioms.
It proves exactly the formulas valid in the finite Veltman models, equivalently in the finite
generalised Veltman models, equivalently in the finite $\mathbf{IL}^-$-models satisfying the frame
conditions of $\mathbf{J1}$, $\mathbf{J2}$ and $\mathbf{J5}$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

section Basic

open Entailment Formula

variable {α : Type*}

/-- - [Vis90, §6.1] -/
abbrev Logic.IL : Logic α := Logic.ofAxioms ∅

notation "𝐈𝐋" => Logic.IL

namespace Logic.ofAxioms

variable {𝔸 : Set (Formula α)}

lemma IL_subset : (𝐈𝐋 : Logic α) ⊆ ofAxioms 𝔸 := subset_of_subset (Set.empty_subset _)

end Logic.ofAxioms

namespace Logic

open ofAxioms

variable {A B C : Formula α}

instance {𝔸 : Set (Formula α)} : (𝐈𝐋 : Logic α) ⪯ ofAxioms 𝔸 := weakerThan_iff.mpr IL_subset

end Logic


end Basic

section Soundness

/-! ### Soundness of $\mathbf{IL}$ -/

namespace Logic.ofAxioms

open Veltman Veltman.Model Veltman.Model.World

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {𝔸 : Set (Formula α)} {A : Formula α}

theorem sound [M.IsIL] (h𝔸 : ∀ A ∈ 𝔸, M ⊧ A) (h : ofAxioms 𝔸 ⊢ A) : M ⊧ A := by
  intro x
  induction h generalizing x with
  | axm hA => exact h𝔸 _ hA x
  | mdp _ _ ih₁ ih₂ => exact ih₁ x (ih₂ x)
  | nec _ ih =>
    intro y _
    exact ih y
  | axiomL => exact forces_axiomL
  | axiomJ1 => exact forces_axiomJ1
  | axiomJ2 => exact forces_axiomJ2
  | axiomJ3 => exact forces_axiomJ3
  | axiomJ4 => exact forces_axiomJ4
  | axiomJ5 => exact forces_axiomJ5
  | _ => grind

end Logic.ofAxioms

instance {α : Type*} : Entailment.Consistent (𝐈𝐋 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦
    Logic.ofAxioms.sound (M := Veltman.Model.pointModel fun _ ↦ False) (by simp) h 0


end Soundness

section Extension

variable {α : Type*}

/-! ### $\mathbf{IL}$ as an extension of $\mathbf{IL}^-$ -/

namespace Logic.ofAxioms

variable {𝔸 : Set (Formula α)} {A : Formula α}

/-- - [KO21, Proposition 3.20.1] -/
lemma axiomJ6 : ofAxioms 𝔸 ⊢ Axioms.J6 A := by
  have h₁ : ofAxioms 𝔸 ⊢ □A 🡒 □(∼A 🡒 ⊥) := box_mono (by cl_prover);
  have h₂ : ofAxioms 𝔸 ⊢ □(∼A 🡒 ⊥) 🡒 ∼A ▷ ⊥ := axiomJ1;
  have h₃ : ofAxioms 𝔸 ⊢ ∼A ▷ ⊥ 🡒 ∼□(∼∼A) 🡒 ∼□(∼⊥) := axiomJ4;
  have h₄ : ofAxioms 𝔸 ⊢ ∼⊥ := by cl_prover;
  have h₄ : ofAxioms 𝔸 ⊢ □(∼⊥) := nec h₄;
  have h₅ : ofAxioms 𝔸 ⊢ □(∼∼A) 🡒 □A := box_mono (by cl_prover);
  cl_prover [h₁, h₂, h₃, h₄, h₅];

/-- The extension of $\mathbf{IL}$ by `𝔸` is $\mathbf{IL}^-(\mathbf{J1}, \mathbf{J2}, \mathbf{J5})$
extended by `𝔸`.

- [KO21, Corollary 3.22]
-/
theorem eq_ofAxiomsMinus :
    ofAxioms 𝔸 = ofAxiomsMinus
      ({Axioms.J1 A B | (A) (B)} ∪ {Axioms.J2 A B C | (A) (B) (C)} ∪ {Axioms.J5 A | A} ∪ 𝔸) := by
  apply Set.Subset.antisymm;
  · intro A h;
    induction h with
    | axm h => exact ofAxiomsMinus.axm (by simp [h]);
    | mdp _ _ ih₁ ih₂ => exact ofAxiomsMinus.mdp ih₁ ih₂;
    | nec _ ih => exact ofAxiomsMinus.nec ih;
    | verum => exact ofAxiomsMinus.verum;
    | implyK => exact ofAxiomsMinus.implyK;
    | implyS => exact ofAxiomsMinus.implyS;
    | andElimL => exact ofAxiomsMinus.andElimL;
    | andElimR => exact ofAxiomsMinus.andElimR;
    | andIntro => exact ofAxiomsMinus.andIntro;
    | orIntroL => exact ofAxiomsMinus.orIntroL;
    | orIntroR => exact ofAxiomsMinus.orIntroR;
    | orElim => exact ofAxiomsMinus.orElim;
    | dne => exact ofAxiomsMinus.dne;
    | axiomK => exact ofAxiomsMinus.axiomK;
    | axiomL => exact ofAxiomsMinus.axiomL;
    | axiomJ1 => exact ofAxiomsMinus.axm (by simp);
    | axiomJ2 => exact ofAxiomsMinus.axm (by simp);
    | axiomJ3 => exact ofAxiomsMinus.axiomJ3;
    | axiomJ4 => exact ofAxiomsMinus.subset_of_subset (by tauto_set) ILMinusJ2.axiomJ4;
    | axiomJ5 => exact ofAxiomsMinus.axm (by simp);
  · intro A h;
    induction h with
    | axm h =>
      rcases h with (((⟨A, B, rfl⟩ | ⟨A, B, C, rfl⟩) | ⟨A, rfl⟩) | h);
      · exact axiomJ1;
      · exact axiomJ2;
      · exact axiomJ5;
      · exact axm h;
    | mdp _ _ ih₁ ih₂ => exact mdp ih₁ ih₂;
    | nec _ ih => exact nec ih;
    | rule1 _ ih => exact rhd_mono_right ih;
    | rule2 _ ih => exact rhd_anti_left ih;
    | verum => exact verum;
    | implyK => exact implyK;
    | implyS => exact implyS;
    | andElimL => exact andElimL;
    | andElimR => exact andElimR;
    | andIntro => exact andIntro;
    | orIntroL => exact orIntroL;
    | orIntroR => exact orIntroR;
    | orElim => exact orElim;
    | dne => exact dne;
    | axiomK => exact axiomK;
    | axiomL => exact axiomL;
    | axiomJ3 => exact axiomJ3;
    | axiomJ6 => exact axiomJ6;

end Logic.ofAxioms

namespace Logic

open ofAxiomsMinus

/-- - [KO21, Corollary 3.22] -/
theorem IL.eq_ofAxiomsMinus :
    (𝐈𝐋 : Logic α) = ofAxiomsMinus
      ({Axioms.J1 A B | (A) (B)} ∪ {Axioms.J2 A B C | (A) (B) (C)} ∪ {Axioms.J5 A | A}) := by
  simpa using ofAxioms.eq_ofAxiomsMinus (𝔸 := (∅ : Set (Formula α)));

instance : (𝐂𝐋 : Logic α) ⪯ 𝐈𝐋 :=
  weakerThan_iff.mpr <| IL.eq_ofAxiomsMinus ▸ subset_of_subset Set.subset_union_left

instance : (ILMinusJ2PlusJ5 : Logic α) ⪯ 𝐈𝐋 :=
  weakerThan_iff.mpr <| IL.eq_ofAxiomsMinus ▸ subset_of_provable (by
    rintro _ (⟨A, B, C, rfl⟩ | ⟨A, rfl⟩);
    · exact subset_of_subset Set.subset_union_left CL.axiomJ2Plus;
    · exact axm (by simp);)

instance : (ILMinusJ1J4PlusJ5 : Logic α) ⪯ 𝐈𝐋 :=
  weakerThan_iff.mpr <| IL.eq_ofAxiomsMinus ▸ subset_of_provable (by
    rintro _ ((⟨A, B, rfl⟩ | ⟨A, B, C, rfl⟩) | ⟨A, rfl⟩);
    · exact axm (by simp);
    · exact subset_of_subset Set.subset_union_left CL.axiomJ4Plus;
    · exact axm (by simp);)

end Logic

section Strict

namespace Logic

open Entailment ofAxiomsMinus

instance : (ILMinusJ2PlusJ5 : Logic α) ⪱ 𝐈𝐋 :=
  .of_unprovable_provable unprovable_J1 ofAxioms.axiomJ1

instance : (𝐂𝐋 : Logic α) ⪱ 𝐈𝐋 := .of_unprovable_provable unprovable_J5 ofAxioms.axiomJ5

instance : (ILMinusJ1J4PlusJ5 : Logic α) ⪱ 𝐈𝐋 :=
  .of_unprovable_provable unprovable_J2 ofAxioms.axiomJ2

end Logic

end Strict

end Extension

section Completeness

namespace Logic

open Entailment Formula MaximalConsistentSet Veltman Veltman.Model Veltman.Model.World

variable {α : Type} {A : Formula α}

/-- - [KO21, Theorem 5.4] -/
theorem IL.complete_ILMinus
    (h : ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ1] → [M.IsJ2] → [M.IsJ5] → M ⊧ A) :
    𝐈𝐋 ⊢ A := by
  classical
  let 𝔸 : Set (Formula α) :=
    {Axioms.J1 A B | (A) (B)} ∪ {Axioms.J2 A B C | (A) (B) (C)} ∪ {Axioms.J5 A | A}
  rw [IL.eq_ofAxiomsMinus];
  by_contra hA;
  have : Entailment.Consistent (ofAxiomsMinus 𝔸) := .of_unprovable hA;
  have : (ILMinusJ1 : Logic α) ⪯ ofAxiomsMinus 𝔸 :=
    weakerThan_iff.mpr <| ofAxiomsMinus.subset_of_subset <|
      Set.subset_union_left.trans Set.subset_union_left;
  have : (ILMinusJ5 : Logic α) ⪯ ofAxiomsMinus 𝔸 :=
    weakerThan_iff.mpr <| ofAxiomsMinus.subset_of_subset Set.subset_union_right;
  have : (ILMinusJ2Plus : Logic α) ⪯ ofAxiomsMinus 𝔸 :=
    weakerThan_iff.mpr <| ofAxiomsMinus.subset_of_provable <| by
      rintro _ ⟨A, B, C, rfl⟩;
      exact ofAxiomsMinus.subset_of_subset Set.subset_union_left CL.axiomJ2Plus;
  exact ofAxiomsMinus.not_models_countermodel hA <| h (countermodel _ (ilMinusAdequateClosure {A}))

/-- - [dJV90, Theorem 4.1] -/
theorem IL.complete
    (h : ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α), [M.IsIL] → M ⊧ A) :
    𝐈𝐋 ⊢ A := by
  apply IL.complete_ILMinus;
  intro κ _ _ M _ _ _ _;
  have : M.IsIL := .of_isILMinus
  exact h M

/-- - [dJV90, Theorem 4.1]
- [JMMV20, Theorem 3.2]
-/
theorem IL.semantics_TFAE : [
    𝐈𝐋 ⊢ A,
    ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α), [M.IsIL] → M ⊧ A,
    ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Verbrugge.Model κ α), [M.IsIL] → M ⊧ A
  ].TFAE := by
  tfae_have 1 → 3 := by
    intro h _ _ _ M _;
    exact ofAxioms.sound_verbrugge (by simp) h;
  tfae_have 3 → 2 := by
    intro h _ _ _ M _ x;
    exact Veltman.Model.forces_toVerbrugge.mp (h M.toVerbrugge x);
  tfae_have 2 → 1 := IL.complete;
  tfae_finish;

/-- - [KO21, Theorem 5.4] -/
theorem IL.iff_valid_finite_ILMinus :
    𝐈𝐋 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ1] → [M.IsJ2] → [M.IsJ5] → M ⊧ A := by
  constructor;
  · intro h _ _ _ M _ _ _ _;
    have : M.IsIL := .of_isILMinus;
    exact ofAxioms.sound (by simp) h;
  · exact IL.complete_ILMinus;

end Logic

end Completeness


end FFL.InterpretabilityLogic

end
