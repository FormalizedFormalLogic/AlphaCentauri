module

public import AlphaCentauri.InterpretabilityLogic.Logic.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinusJ1J5.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinusJ5.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.CL.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinusJ4Plus.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.LabelledSetModel

/-!
# Soundness and completeness of $\mathbf{IL}^-(\mathbf{J4}^+, \mathbf{J5})$
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

namespace Logic

open Entailment Formula

variable {α : Type*}

/-- $\mathbf{IL}^-(\mathbf{J4}^+, \mathbf{J5})$.

- [KO21, §3]
-/
abbrev ILMinusJ4PlusJ5 : Logic α :=
  ofAxiomsMinus ({Axioms.J4Plus A B C | (A) (B) (C)} ∪ {Axioms.J5 A | A})

end Logic

section Soundness

namespace Logic

open Veltman Veltman.Model Veltman.Model.World

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {A : Formula α}

theorem ILMinusJ4PlusJ5.sound [M.IsILMinus] [M.IsJ4] [M.IsJ5] : ILMinusJ4PlusJ5 ⊢ A → M ⊧ A :=
  ofAxiomsMinus.sound <| by
    rintro _ (⟨A, B, C, rfl⟩ | ⟨A, rfl⟩) x;
    · exact forces_axiomJ4Plus;
    · exact forces_axiomJ5;

end Logic

end Soundness

section Consistency

open Veltman.Model Logic

variable {α : Type*}

instance : Entailment.Consistent (ILMinusJ4PlusJ5 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILMinusJ4PlusJ5.sound (M := pointModel fun _ ↦ False) h 0

end Consistency

section Completeness

namespace Logic

open Entailment Formula MaximalConsistentSet Veltman Veltman.Model
open LabelledSet.Condition ofAxiomsMinus

variable {α : Type} {A : Formula α}

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ4PlusJ5.iff_valid_finite :
    ILMinusJ4PlusJ5 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ4] → [M.IsJ5] → M ⊧ A := by
  constructor;
  · intro h _ _ _ M;
    intros;
    exact ILMinusJ4PlusJ5.sound h;
  · intro h;
    classical
    exact provable_of_models_labelledModel .J4PlusJ5 (h _)

end Logic

end Completeness



section Relations

namespace Logic

open Entailment

variable {α : Type*}

instance : (ILMinusJ4Plus : Logic α) ⪱ ILMinusJ4PlusJ5 :=
  .of_unprovable_provable unprovable_J5 (HasAxiomJ5.J5 _)

instance : (ILMinusJ5 : Logic α) ⪱ ILMinusJ4PlusJ5 :=
  .of_unprovable_provable ILMinusJ1J5.unprovable_J4Plus (HasAxiomJ4Plus.J4Plus _ _ _)

end Logic

end Relations

end FFL.InterpretabilityLogic

