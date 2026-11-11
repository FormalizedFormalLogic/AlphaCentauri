module

public import AlphaCentauri.InterpretabilityLogic.Logic.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinusJ1J4Plus.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinusJ1J5.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinusJ4PlusJ5.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.Counterexamples
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.LabelledSetModel

/-!
# Soundness and completeness of $\mathbf{IL}^-(\mathbf{J1}, \mathbf{J4}^+, \mathbf{J5})$
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

namespace Logic

open Entailment Formula

variable {α : Type*}

/-- $\mathbf{IL}^-(\mathbf{J1}, \mathbf{J4}^+, \mathbf{J5})$.

- [KO21, §3]
-/
abbrev ILMinusJ1J4PlusJ5 : Logic α :=
  ofAxiomsMinus
    ({Axioms.J1 A B | (A) (B)} ∪ {Axioms.J4Plus A B C | (A) (B) (C)} ∪ {Axioms.J5 A | A})

end Logic

namespace Veltman.Model

variable {κ α : Type*} [Nonempty κ] (M : Model κ α)

class IsILMinusJ1J4PlusJ5 : Prop extends M.IsILMinus, M.IsJ1, M.IsJ4, M.IsJ5

instance (priority := low) [M.IsILMinus] [M.IsJ1] [M.IsJ4] [M.IsJ5] : M.IsILMinusJ1J4PlusJ5 := {}

end Veltman.Model

namespace Logic

/-! ## Completeness -/


open Entailment Formula MaximalConsistentSet Veltman Veltman.Model Veltman.Model.World
open LabelledSet.Condition ofAxiomsMinus

variable {α : Type} {A : Formula α}

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ1J4PlusJ5.semantics_TFAE : [
    ILMinusJ1J4PlusJ5 ⊢ A,
    ∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ α),
      [M.IsILMinusJ1J4PlusJ5] → M ⊧ A,
    ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinusJ1J4PlusJ5] → M ⊧ A
  ].TFAE := by
  tfae_have 1 → 2 := by
    intro h _ _ M _;
    apply ofAxiomsMinus.sound _ h;
    rintro _ ((⟨A, B, rfl⟩ | ⟨A, B, C, rfl⟩) | ⟨A, rfl⟩) x;
    · exact forces_axiomJ1;
    · exact forces_axiomJ4Plus;
    · exact forces_axiomJ5;
  tfae_have 2 → 3 := by
    intro h _ _ _ M _;
    exact h M;
  tfae_have 3 → 1 := by
    intro h;
    classical
    exact provable_of_models_labelledModel .J4PlusJ5 (h _);
  tfae_finish;

theorem ILMinusJ1J4PlusJ5.iff_valid :
    ILMinusJ1J4PlusJ5 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ α),
      [M.IsILMinusJ1J4PlusJ5] → M ⊧ A :=
  ILMinusJ1J4PlusJ5.semantics_TFAE.out 1 2

theorem ILMinusJ1J4PlusJ5.sound {κ : Type} [Nonempty κ] {M : Veltman.Model κ α}
    [M.IsILMinusJ1J4PlusJ5] (h : ILMinusJ1J4PlusJ5 ⊢ A) : M ⊧ A :=
  ILMinusJ1J4PlusJ5.iff_valid.mp h M

instance : Entailment.Consistent (ILMinusJ1J4PlusJ5 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILMinusJ1J4PlusJ5.sound (M := pointModel fun _ ↦ False) h 0

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ1J4PlusJ5.iff_valid_finite :
    ILMinusJ1J4PlusJ5 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinusJ1J4PlusJ5] → M ⊧ A :=
  ILMinusJ1J4PlusJ5.semantics_TFAE.out 1 3


/-! ## Relations -/


open Entailment Veltman

variable {α : Type}

instance : (ILMinusJ1J4Plus : Logic α) ⪱ ILMinusJ1J4PlusJ5 :=
  .of_unprovable_provable (φ := Axioms.J5 (□⊥))
    (fun h ↦ counterJ5.not_models_J5 (ILMinusJ1J4Plus.sound (M := counterJ5 α) h)) (HasAxiomJ5.J5 _)

instance : (ILMinusJ1J5 : Logic α) ⪱ ILMinusJ1J4PlusJ5 :=
  .of_unprovable_provable (φ := Axioms.J4Plus (◇⊤) ⊥ ⊤)
    (fun h ↦ counterJ4.not_models_J4Plus (ILMinusJ1J5.sound (M := counterJ4 α) h))
    (HasAxiomJ4Plus.J4Plus _ _ _)

instance : (ILMinusJ4PlusJ5 : Logic α) ⪱ ILMinusJ1J4PlusJ5 :=
  .of_unprovable_provable (φ := Axioms.J1 ⊤ ⊤)
    (fun h ↦ counterJ1.not_models_J1 (ILMinusJ4PlusJ5.sound (M := counterJ1 α) h))
    (HasAxiomJ1.J1 _ _)

end Logic

end FFL.InterpretabilityLogic

