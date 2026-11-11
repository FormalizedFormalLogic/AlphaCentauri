module

public import AlphaCentauri.InterpretabilityLogic.Logic.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinusJ1.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinusJ5.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.Counterexamples
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.LabelledSetModel

/-!
# Soundness and completeness of $\mathbf{IL}^-(\mathbf{J1}, \mathbf{J5})$
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula

variable {α : Type*}

/-- $\mathbf{IL}^-(\mathbf{J1}, \mathbf{J5})$.

- [KO21, §3]
-/
abbrev Logic.ILMinusJ1J5 : Logic α := ofAxiomsMinus ({Axioms.J1 A B | (A) (B)} ∪ {Axioms.J5 A | A})

namespace Veltman.Model

variable {κ α : Type*} [Nonempty κ] (M : Model κ α)

class IsILMinusJ1J5 : Prop extends M.IsILMinus, M.IsJ1, M.IsJ5

instance (priority := low) [M.IsILMinus] [M.IsJ1] [M.IsJ5] : M.IsILMinusJ1J5 := {}

end Veltman.Model

namespace Logic

/-! ## Completeness -/


open Entailment Formula MaximalConsistentSet Veltman Veltman.Model Veltman.Model.World
open LabelledSet.Condition ofAxiomsMinus

variable {α : Type} {A : Formula α}

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ1J5.semantics_TFAE : [
    ILMinusJ1J5 ⊢ A,
    ∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ α),
      [M.IsILMinusJ1J5] → M ⊧ A,
    ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinusJ1J5] → M ⊧ A
  ].TFAE := by
  tfae_have 1 → 2 := by
    intro h _ _ M _;
    apply ofAxiomsMinus.sound _ h;
    rintro _ (⟨A, B, rfl⟩ | ⟨A, rfl⟩) x;
    · exact forces_axiomJ1;
    · exact forces_axiomJ5;
  tfae_have 2 → 3 := by
    intro h _ _ _ M _;
    exact h M;
  tfae_have 3 → 1 := by
    intro h;
    classical
    exact provable_of_models_labelledModel .J5 (h _);
  tfae_finish;

theorem ILMinusJ1J5.iff_valid :
    ILMinusJ1J5 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ α),
      [M.IsILMinusJ1J5] → M ⊧ A :=
  ILMinusJ1J5.semantics_TFAE.out 1 2

theorem ILMinusJ1J5.sound {κ : Type} [Nonempty κ] {M : Veltman.Model κ α}
    [M.IsILMinusJ1J5] (h : ILMinusJ1J5 ⊢ A) : M ⊧ A :=
  ILMinusJ1J5.iff_valid.mp h M

instance : Entailment.Consistent (ILMinusJ1J5 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILMinusJ1J5.sound (M := pointModel fun _ ↦ False) h 0

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ1J5.iff_valid_finite :
    ILMinusJ1J5 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinusJ1J5] → M ⊧ A :=
  ILMinusJ1J5.semantics_TFAE.out 1 3


/-! ## Relations -/


open Entailment Veltman

variable {α : Type}

instance : (ILMinusJ1 : Logic α) ⪱ ILMinusJ1J5 :=
  .of_unprovable_provable (φ := Axioms.J5 (□⊥))
    (fun h ↦ counterJ5.not_models_J5 (ILMinusJ1.sound (M := counterJ5 α) h)) (HasAxiomJ5.J5 _)

instance : (ILMinusJ5 : Logic α) ⪱ ILMinusJ1J5 :=
  .of_unprovable_provable (φ := Axioms.J1 ⊤ ⊤)
    (fun h ↦ counterJ1.not_models_J1 (ILMinusJ5.sound (M := counterJ1 α) h)) (HasAxiomJ1.J1 _ _)

end Logic

end FFL.InterpretabilityLogic

