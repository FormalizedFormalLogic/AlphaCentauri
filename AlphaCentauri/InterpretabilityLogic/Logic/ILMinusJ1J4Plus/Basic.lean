module

public import AlphaCentauri.InterpretabilityLogic.Logic.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinusJ2PlusJ5.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinusJ1J5.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinusJ4Plus.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinusJ1.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.LabelledSetModel

/-!
# Soundness and completeness of $\mathbf{IL}^-(\mathbf{J1}, \mathbf{J4}^+)$
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

namespace Logic

open Entailment Formula

variable {α : Type*}

/-- $\mathbf{IL}^-(\mathbf{J1}, \mathbf{J4}^+)$.

- [KO21, §3]
-/
abbrev ILMinusJ1J4Plus : Logic α :=
  ofAxiomsMinus ({Axioms.J1 A B | (A) (B)} ∪ {Axioms.J4Plus A B C | (A) (B) (C)})

end Logic

section Soundness

namespace Logic

open Veltman Veltman.Model Veltman.Model.World

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {A : Formula α}

theorem ILMinusJ1J4Plus.sound [M.IsILMinus] [M.IsJ1] [M.IsJ4] : ILMinusJ1J4Plus ⊢ A → M ⊧ A :=
  ofAxiomsMinus.sound <| by
    rintro _ (⟨A, B, rfl⟩ | ⟨A, B, C, rfl⟩) x;
    · exact forces_axiomJ1;
    · exact forces_axiomJ4Plus;

end Logic

end Soundness

section Consistency

open Veltman.Model Logic

variable {α : Type*}

instance : Entailment.Consistent (ILMinusJ1J4Plus : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILMinusJ1J4Plus.sound (M := pointModel fun _ ↦ False) h 0

end Consistency

section Completeness

namespace Logic

open Entailment Formula MaximalConsistentSet Veltman Veltman.Model
open LabelledSet.Condition ofAxiomsMinus

variable {α : Type} {A : Formula α}

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ1J4Plus.iff_valid_finite :
    ILMinusJ1J4Plus ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ1] → [M.IsJ4] → M ⊧ A := by
  constructor;
  · intro h _ _ _ M;
    intros;
    exact ILMinusJ1J4Plus.sound h;
  · intro h;
    classical
    exact provable_of_models_labelledModel .J4Plus (h _)

end Logic

end Completeness



section Relations

namespace Logic

open Entailment

variable {α : Type*}

instance : (ILMinusJ1 : Logic α) ⪱ ILMinusJ1J4Plus :=
  .of_unprovable_provable ILMinusJ1J5.unprovable_J4Plus (HasAxiomJ4Plus.J4Plus _ _ _)

instance : (ILMinusJ4Plus : Logic α) ⪱ ILMinusJ1J4Plus :=
  .of_unprovable_provable unprovable_J1 (HasAxiomJ1.J1 _ _)

end Logic

end Relations

end FFL.InterpretabilityLogic

