module

public import AlphaCentauri.InterpretabilityLogic.Logic.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinus.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinusJ2PlusJ5.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.LabelledSetModel

/-!
# Soundness and completeness of $\mathbf{IL}^-(\mathbf{J1})$
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

namespace Logic

open Entailment Formula

variable {α : Type*}

/-- $\mathbf{IL}^-(\mathbf{J1})$.

- [KO21, §3.1]
-/
abbrev ILMinusJ1 : Logic α := ofAxiomsMinus {Axioms.J1 A B | (A) (B)}

end Logic

section Soundness

namespace Logic

open Veltman Veltman.Model Veltman.Model.World

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {A : Formula α}

theorem ILMinusJ1.sound [M.IsILMinus] [M.IsJ1] : ILMinusJ1 ⊢ A → M ⊧ A :=
  ofAxiomsMinus.sound <| by
    rintro _ ⟨A, B, rfl⟩ x;
    exact forces_axiomJ1

end Logic

end Soundness

section Consistency

open Veltman.Model Logic

variable {α : Type*}

instance : Entailment.Consistent (ILMinusJ1 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILMinusJ1.sound (M := pointModel fun _ ↦ False) h 0

end Consistency

section Completeness

namespace Logic

open Entailment Formula MaximalConsistentSet Veltman Veltman.Model
open LabelledSet.Condition ofAxiomsMinus

variable {α : Type} {A : Formula α}

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ1.iff_valid_finite :
    ILMinusJ1 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ1] → M ⊧ A := by
  constructor;
  · intro h _ _ _ M;
    intros;
    exact ILMinusJ1.sound h;
  · intro h;
    classical
    exact provable_of_models_labelledModel .ILMinus (h _)

end Logic

end Completeness



section EquivalentAxiomatizations

namespace Logic

open Entailment ofAxiomsMinus

variable {α : Type*}

/-- - [KO21, Proposition 3.1] -/
theorem ILMinusJ1.eq_ofAxiomsMinus_J1' :
    (ILMinusJ1 : Logic α) = ofAxiomsMinus {Axioms.J1' A | A} := by
  apply Set.Subset.antisymm;
  · apply subset_of_provable;
    rintro _ ⟨A, B, rfl⟩;
    have h₁ : ofAxiomsMinus {Axioms.J1' A | A} ⊢ □(A 🡒 B) 🡒 B ▷ B 🡒 A ▷ B :=
      rhd_anti_left_of_box;
    have h₂ : ofAxiomsMinus {Axioms.J1' A | A} ⊢ B ▷ B := axm (by simp);
    cl_prover [h₁, h₂];
  · apply subset_of_provable;
    rintro _ ⟨A, rfl⟩;
    exact axiomJ1';

end Logic

end EquivalentAxiomatizations

section Relations

namespace Logic

open Entailment

variable {α : Type*}

instance : (𝐈𝐋⁻ : Logic α) ⪱ ILMinusJ1 :=
  .of_unprovable_provable unprovable_J1 (HasAxiomJ1.J1 _ _)

end Logic

end Relations

end FFL.InterpretabilityLogic

