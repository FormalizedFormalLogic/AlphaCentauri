module

public import AlphaCentauri.InterpretabilityLogic.Logic.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinusJ2Plus.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinusJ4PlusJ5.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.Counterexamples
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.IndexedSetModel

/-!
# Soundness and completeness of $\mathbf{IL}^-(\mathbf{J2}^+, \mathbf{J5})$
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula

variable {α : Type*}

/-- $\mathbf{IL}^-(\mathbf{J2}^+, \mathbf{J5})$.

- [KO21, §3]
-/
abbrev Logic.ILMinusJ2PlusJ5 : Logic α :=
  ofAxiomsMinus ({Axioms.J2Plus A B C | (A) (B) (C)} ∪ {Axioms.J5 A | A})

namespace Veltman.Model

variable {κ α : Type*} [Nonempty κ] (M : Model κ α)

class IsILMinusJ2PlusJ5 : Prop extends M.IsILMinus, M.IsJ2, M.IsJ5

instance (priority := low) [M.IsILMinus] [M.IsJ2] [M.IsJ5] : M.IsILMinusJ2PlusJ5 := {}

end Veltman.Model

namespace Logic

/-! ## Completeness -/


open Entailment Formula MaximalConsistentSet Veltman Veltman.Model Veltman.Model.World

variable {α : Type} {A : Formula α}

/-- - [KO21, Theorem 5.4] -/
theorem ILMinusJ2PlusJ5.semantics_TFAE : [
    ILMinusJ2PlusJ5 ⊢ A,
    ∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ α),
      [M.IsILMinusJ2PlusJ5] → M ⊧ A,
    ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinusJ2PlusJ5] → M ⊧ A
  ].TFAE := by
  tfae_have 1 → 2 := by
    intro h _ _ M _;
    apply ofAxiomsMinus.sound _ h;
    rintro _ (⟨A, B, C, rfl⟩ | ⟨A, rfl⟩) x;
    · exact forces_axiomJ2Plus;
    · exact forces_axiomJ5;
  tfae_have 2 → 3 := by
    intro h _ _ _ M _;
    exact h M;
  tfae_have 3 → 1 := by
    intro h;
    classical
    by_contra hA;
    have : Entailment.Consistent (ILMinusJ2PlusJ5 : Logic α) := .of_unprovable hA;
    exact ofAxiomsMinus.not_models_countermodel hA <|
      h (countermodel ILMinusJ2PlusJ5 (ilMinusAdequateClosure {A}));
  tfae_finish;

theorem ILMinusJ2PlusJ5.iff_valid :
    ILMinusJ2PlusJ5 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ α),
      [M.IsILMinusJ2PlusJ5] → M ⊧ A :=
  ILMinusJ2PlusJ5.semantics_TFAE.out 1 2

theorem ILMinusJ2PlusJ5.sound {κ : Type} [Nonempty κ] {M : Veltman.Model κ α}
    [M.IsILMinusJ2PlusJ5] (h : ILMinusJ2PlusJ5 ⊢ A) : M ⊧ A :=
  ILMinusJ2PlusJ5.iff_valid.mp h M

instance : Entailment.Consistent (ILMinusJ2PlusJ5 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILMinusJ2PlusJ5.sound (M := pointModel fun _ ↦ False) h 0

/-- - [KO21, Theorem 5.4] -/
theorem ILMinusJ2PlusJ5.iff_valid_finite :
    ILMinusJ2PlusJ5 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinusJ2PlusJ5] → M ⊧ A :=
  ILMinusJ2PlusJ5.semantics_TFAE.out 1 3

/-! ## Relations -/


open Entailment Veltman

variable {α : Type}

instance : (ILMinusJ2Plus : Logic α) ⪱ ILMinusJ2PlusJ5 :=
  .of_unprovable_provable (φ := Axioms.J5 (□⊥))
    (fun h ↦ counterJ5.not_models_J5 (ILMinusJ2Plus.sound (M := counterJ5 α) h)) (HasAxiomJ5.J5 _)

instance : (ILMinusJ4PlusJ5 : Logic α) ⪱ ILMinusJ2PlusJ5 :=
  .of_unprovable_provable (φ := Axioms.J2 (□⊥) (◇⊤ ⋏ □□⊥) (◇◇⊤))
    (fun h ↦ counterJ2.not_models_J2 (ILMinusJ4PlusJ5.sound (M := counterJ2 α) h))
    (HasAxiomJ2.J2 _ _ _)

end Logic


end FFL.InterpretabilityLogic

