module

public import AlphaCentauri.InterpretabilityLogic.Logic.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.IndexedSetModel
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.CL.Basic

/-!
# Interpretability logic $\mathbf{IL}$

$\mathbf{IL}$ is the logic `ofILAxioms ∅`, contained in every extension by axioms.
It proves exactly the formulas valid in the finite Veltman models, equivalently in the finite
generalised Veltman models, equivalently in the finite models satisfying the frame conditions of
$\mathbf{CL}$ and $\mathbf{J5}$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula

variable {α : Type*}

/-- - [Vis90, §6.1] -/
abbrev Logic.IL : Logic α := Logic.ofILAxioms ∅

notation "𝐈𝐋" => Logic.IL

namespace Logic.ofILAxioms

variable {𝔸 : FormulaSet α}

lemma IL_subset : (𝐈𝐋 : Logic α) ⊆ ofILAxioms 𝔸 := subset_of_subset (Set.empty_subset _)

end Logic.ofILAxioms

namespace Logic

open ofILAxioms

variable {A B C : Formula α}

instance {𝔸 : FormulaSet α} : (𝐈𝐋 : Logic α) ⪯ ofILAxioms 𝔸 := weakerThan_iff.mpr IL_subset

end Logic

/-! ## Soundness -/

namespace Logic.ofILAxioms

open Veltman Veltman.Model Veltman.Model.World

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {𝔸 : FormulaSet α} {A : Formula α}

theorem sound [M.IsIL] (h𝔸 : ∀ A ∈ 𝔸, M ⊧ A) (h : ofILAxioms 𝔸 ⊢ A) : M ⊧ A := by
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

end Logic.ofILAxioms

instance {α : Type*} : Entailment.Consistent (𝐈𝐋 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦
    Logic.ofILAxioms.sound (M := Veltman.Model.pointModel fun _ ↦ False) (by simp) h 0

/-! ## $\mathbf{IL}$ as an extension of $\mathbf{CL}$ -/

namespace Logic.ofILAxioms

variable {𝔸 : FormulaSet α} {A : Formula α}

/-- The extension of $\mathbf{IL}$ by `𝔸` is the extension of $\mathbf{CL}$ by $\mathbf{J5}$ and
`𝔸`.

- [KO21, §3.5]
-/
theorem eq_ofCLAxioms :
    ofILAxioms 𝔸 = ofCLAxioms ({Axioms.J5 A | A} ∪ 𝔸) := by
  apply Set.Subset.antisymm;
  · intro A h;
    induction h with
    | axm h => exact ofCLAxioms.axm (by simp [h]);
    | mdp _ _ ih₁ ih₂ => exact ofCLAxioms.mdp ih₁ ih₂;
    | nec _ ih => exact ofCLAxioms.nec ih;
    | verum => exact ofCLAxioms.verum;
    | implyK => exact ofCLAxioms.implyK;
    | implyS => exact ofCLAxioms.implyS;
    | andElimL => exact ofCLAxioms.andElimL;
    | andElimR => exact ofCLAxioms.andElimR;
    | andIntro => exact ofCLAxioms.andIntro;
    | orIntroL => exact ofCLAxioms.orIntroL;
    | orIntroR => exact ofCLAxioms.orIntroR;
    | orElim => exact ofCLAxioms.orElim;
    | dne => exact ofCLAxioms.dne;
    | axiomK => exact ofCLAxioms.axiomK;
    | axiomL => exact ofCLAxioms.axiomL;
    | axiomJ1 => exact ofCLAxioms.axiomJ1;
    | axiomJ2 => exact ofCLAxioms.axiomJ2;
    | axiomJ3 => exact ofCLAxioms.axiomJ3;
    | axiomJ4 => exact ofCLAxioms.axiomJ4;
    | axiomJ5 => exact ofCLAxioms.axm (by simp);
  · intro A h;
    induction h with
    | axm h =>
      rcases h with ⟨A, rfl⟩ | h;
      · exact axiomJ5;
      · exact axm h;
    | mdp _ _ ih₁ ih₂ => exact mdp ih₁ ih₂;
    | nec _ ih => exact nec ih;
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
    | axiomJ1 => exact axiomJ1;
    | axiomJ2 => exact axiomJ2;
    | axiomJ3 => exact axiomJ3;
    | axiomJ4 => exact axiomJ4;

end Logic.ofILAxioms

namespace Logic

/-- - [KO21, §3.5] -/
theorem IL.eq_ofCLAxioms : (𝐈𝐋 : Logic α) = ofCLAxioms {Axioms.J5 A | A} := by
  simpa using ofILAxioms.eq_ofCLAxioms (𝔸 := (∅ : FormulaSet α));

end Logic

/-! ## Strict -/

namespace Veltman

open Model Model.World

/-- A model satisfying $\mathbf{J1}$ and $\mathbf{J2}$ but not $\mathbf{J5}$. -/
abbrev countermodelJ5 (α : Type*) : Model (Fin 3) α :=
  ⟨(· < ·), fun w x y ↦ w < x ∧ x = y, fun _ _ ↦ False⟩

instance {α : Type*} : (countermodelJ5 α).IsCL where
  trans := by omega
  cwf := Finite.converseWellFounded_of_trans_of_irrefl
  rel_of_s_left := by tauto
  s_refl := by tauto
  rel_of_s_right := by omega
  s_trans := by omega

lemma countermodelJ5.not_models_axiomJ5 {α : Type*} : ¬countermodelJ5 α ⊧ Axioms.J5 (□⊥) := by
  intro h
  have h₁ : (1 : Fin 3) ⊩[countermodelJ5 α] ◇□⊥ :=
    forces_dia.mpr ⟨2, by omega, fun y hy ↦ by omega⟩
  obtain ⟨z, ⟨-, rfl⟩, hz⟩ := h 0 1 (by omega) h₁
  exact hz 2 (by omega)

end Veltman

namespace Logic

open Entailment Veltman

variable {α : Type}

instance : (𝐂𝐋 : Logic α) ⪯ 𝐈𝐋 :=
  weakerThan_iff.mpr <| IL.eq_ofCLAxioms ▸ ofCLAxioms.subset_of_subset (Set.empty_subset _)

instance : (𝐂𝐋 : Logic α) ⪱ 𝐈𝐋 :=
  .of_unprovable_provable (φ := Axioms.J5 (□⊥))
    (fun h ↦ countermodelJ5.not_models_axiomJ5 (CL.sound (M := countermodelJ5 α) h))
    ofILAxioms.axiomJ5

/-! ## Completeness -/

open Formula MaximalConsistentSet Veltman.Model Veltman.Model.World

variable {A : Formula α}

/-- - [dJV90, Theorem 4.1]
- [JMMV20, Theorem 3.2]
- [KO21, Theorem 5.4]
-/
theorem IL.semantics_TFAE : [
    𝐈𝐋 ⊢ A,
    ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α), [M.IsIL] → M ⊧ A,
    ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Verbrugge.Model κ α), [M.IsIL] → M ⊧ A,
    ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsCL] → [M.IsJ5] → M ⊧ A
  ].TFAE := by
  tfae_have 1 → 3 := by
    intro h _ _ _ M _;
    exact ofILAxioms.sound_verbrugge (by simp) h;
  tfae_have 3 → 2 := by
    intro h _ _ _ M _ x;
    exact Veltman.Model.forces_toVerbrugge.mp (h M.toVerbrugge x);
  tfae_have 2 → 4 := by
    intro h κ _ _ M _ _;
    have : M.IsIL := .of_isCL;
    exact h M;
  tfae_have 4 → 1 := by
    intro h;
    classical
    rw [IL.eq_ofCLAxioms];
    by_contra hA;
    have : Entailment.Consistent (ofCLAxioms {Axioms.J5 A | A}) := .of_unprovable hA;
    exact ofCLAxioms.not_models_countermodel hA <|
      h (countermodel _ (clAdequateClosure {A}));
  tfae_finish;

/-- - [KO21, Theorem 5.4] -/
theorem IL.iff_valid_finite_CL :
    𝐈𝐋 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsCL] → [M.IsJ5] → M ⊧ A :=
  IL.semantics_TFAE.out 1 4

end Logic

end FFL.InterpretabilityLogic

