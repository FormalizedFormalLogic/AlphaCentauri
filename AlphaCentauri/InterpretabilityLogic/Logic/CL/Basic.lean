module

public import AlphaCentauri.InterpretabilityLogic.Logic.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinusJ2Plus.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.LabelledSetModel
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinusJ2PlusJ5.Basic

/-!
# Soundness and completeness of $\mathbf{CL}$
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

namespace Logic

open Entailment Formula

variable {α : Type*}

/-- $\mathbf{CL}$, presented as $\mathbf{IL}^-(\mathbf{J1}, \mathbf{J2})$.

- [KO21, Proposition 3.21]
-/
abbrev CL : Logic α :=
  ofAxiomsMinus ({Axioms.J1 A B | (A) (B)} ∪ {Axioms.J2 A B C | (A) (B) (C)})

notation "𝐂𝐋" => Logic.CL

end Logic

section J2Plus

namespace Logic

open ofAxiomsMinus

variable {α : Type*}

/-- - [KO21, Proposition 3.12.2] -/
instance : HasAxiomJ2Plus (𝐂𝐋 : Logic α) where
  J2Plus A B C := by
    have h₁ : 𝐂𝐋 ⊢ B ▷ C ⋏ C ▷ C 🡒 (B ⋎ C) ▷ C := axiomJ3;
    have h₂ : 𝐂𝐋 ⊢ C ▷ C := axiomJ1';
    have h₃ : 𝐂𝐋 ⊢ A ▷ (B ⋎ C) ⋏ (B ⋎ C) ▷ C 🡒 A ▷ C := HasAxiomJ2.J2 _ _ _;
    cl_prover [h₁, h₂, h₃];

end Logic

end J2Plus

section SoundnessVeltman

namespace Logic

open Veltman Veltman.Model Veltman.Model.World

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {A : Formula α}

theorem CL.sound [M.IsILMinus] [M.IsJ1] [M.IsJ2] : 𝐂𝐋 ⊢ A → M ⊧ A :=
  ofAxiomsMinus.sound <| by
    rintro _ (⟨A, B, rfl⟩ | ⟨A, B, C, rfl⟩) x;
    · exact forces_axiomJ1;
    · exact forces_axiomJ2;

end Logic

end SoundnessVeltman

section Consistency

open Veltman.Model Logic

variable {α : Type*}

instance : Entailment.Consistent (𝐂𝐋 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ CL.sound (M := pointModel fun _ ↦ False) h 0

end Consistency

section Completeness

namespace Logic

open Entailment Formula MaximalConsistentSet Veltman Veltman.Model
open LabelledSet.Condition ofAxiomsMinus

variable {α : Type} {A : Formula α}

/-- - [KO21, Theorem 5.1] -/
theorem CL.iff_valid_finite :
    𝐂𝐋 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ1] → [M.IsJ2] → M ⊧ A := by
  constructor;
  · intro h _ _ _ M;
    intros;
    exact CL.sound h;
  · intro h;
    classical
    exact provable_of_models_labelledModel .J2Plus (h _)

end Logic

end Completeness



section IncompletenessVeltman

namespace Logic

open Veltman Veltman.Model Veltman.Model.World Entailment ofAxiomsMinus

variable {α : Type*} {L : Logic α}

private abbrev counterJ5 (α : Type*) : Model (Fin 3) α :=
  ⟨(· < ·), fun w x y ↦ w < x ∧ x = y, fun _ _ ↦ False⟩

private instance : (counterJ5 α).IsILMinus where
  trans := by omega
  cwf := Finite.converseWellFounded_of_trans_of_irrefl
  rel_of_s_left := by tauto

private instance : (counterJ5 α).IsJ1 := ⟨by tauto⟩

private instance : (counterJ5 α).IsJ2 where
  rel_of_s_right := by omega
  s_trans := by omega

lemma unprovable_J5 [L ⪯ 𝐂𝐋] : L ⊬ Axioms.J5 (□⊥) := by
  intro h;
  replace h := WeakerThan.pbl (𝓣 := 𝐂𝐋) h;
  have h₁ : (1 : Fin 3) ⊩[counterJ5 α] ◇□⊥ :=
    forces_dia.mpr ⟨2, by omega, fun y hy ↦ by omega⟩
  obtain ⟨z, ⟨-, rfl⟩, hz⟩ := CL.sound (M := counterJ5 α) h 0 1 (by omega) h₁;
  exact hz 2 (by omega);


end Logic

end IncompletenessVeltman









section Relations

namespace Logic

open Entailment

variable {α : Type*}

instance : (ILMinusJ2Plus : Logic α) ⪱ ILMinusJ2PlusJ5 :=
  .of_unprovable_provable unprovable_J5 (HasAxiomJ5.J5 _)

instance : (ILMinusJ2Plus : Logic α) ⪱ 𝐂𝐋 :=
  .of_unprovable_provable unprovable_J1 (HasAxiomJ1.J1 _ _)

end Logic

end Relations

end FFL.InterpretabilityLogic

