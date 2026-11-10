module

public import AlphaCentauri.InterpretabilityLogic.Logic.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.IndexedSetModel

/-!
# Soundness and completeness of $\mathbf{IL}^-(\mathbf{J2}^+, \mathbf{J5})$
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

namespace Logic

open Entailment Formula

variable {α : Type*}

/-- $\mathbf{IL}^-(\mathbf{J2}^+, \mathbf{J5})$.

- [KO21, §3]
-/
abbrev ILMinusJ2PlusJ5 : Logic α :=
  ofAxiomsMinus ({Axioms.J2Plus A B C | (A) (B) (C)} ∪ {Axioms.J5 A | A})


/-! ## Completeness -/


open Entailment Formula MaximalConsistentSet Veltman Veltman.Model Veltman.Model.World

variable {α : Type} {A : Formula α}

/-- - [KO21, Theorem 5.4] -/
theorem ILMinusJ2PlusJ5.semantics_TFAE : [
    ILMinusJ2PlusJ5 ⊢ A,
    ∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ2] → [M.IsJ5] → M ⊧ A,
    ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ2] → [M.IsJ5] → M ⊧ A
  ].TFAE := by
  tfae_have 1 → 2 := by
    intro h _ _ M _ _ _;
    apply ofAxiomsMinus.sound _ h;
    rintro _ (⟨A, B, C, rfl⟩ | ⟨A, rfl⟩) x;
    · exact forces_axiomJ2Plus;
    · exact forces_axiomJ5;
  tfae_have 2 → 3 := by
    intro h _ _ _ M _ _ _;
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
      [M.IsILMinus] → [M.IsJ2] → [M.IsJ5] → M ⊧ A :=
  ILMinusJ2PlusJ5.semantics_TFAE.out 1 2

theorem ILMinusJ2PlusJ5.sound {κ : Type} [Nonempty κ] {M : Veltman.Model κ α}
    [M.IsILMinus] [M.IsJ2] [M.IsJ5] (h : ILMinusJ2PlusJ5 ⊢ A) : M ⊧ A :=
  ILMinusJ2PlusJ5.iff_valid.mp h M

instance : Entailment.Consistent (ILMinusJ2PlusJ5 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILMinusJ2PlusJ5.sound (M := pointModel fun _ ↦ False) h 0

/-- - [KO21, Theorem 5.4] -/
theorem ILMinusJ2PlusJ5.iff_valid_finite :
    ILMinusJ2PlusJ5 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ2] → [M.IsJ5] → M ⊧ A :=
  ILMinusJ2PlusJ5.semantics_TFAE.out 1 3


/-! ## Incompleteness for Veltman models -/


open Veltman Veltman.Model Veltman.Model.World Entailment ofAxiomsMinus

variable {α : Type} {L : Logic α}

private abbrev counterJ1 (α : Type*) : Model (Fin 2) α :=
  ⟨(· < ·), fun _ _ _ ↦ False, fun _ _ ↦ False⟩

private instance : (counterJ1 α).IsILMinus where
  trans := by omega
  cwf := Finite.converseWellFounded_of_trans_of_irrefl
  rel_of_s_left := by tauto

private instance : (counterJ1 α).IsJ2 where
  rel_of_s_right := by tauto
  s_trans := by tauto

private instance : (counterJ1 α).IsJ5 := ⟨by omega⟩

lemma unprovable_J1 [L ⪯ ILMinusJ2PlusJ5] : L ⊬ Axioms.J1 ⊤ ⊤ := by
  intro h;
  replace h := WeakerThan.pbl (𝓣 := ILMinusJ2PlusJ5) h;
  obtain ⟨z, h, -⟩ :=
    ILMinusJ2PlusJ5.sound (M := counterJ1 α) h 0 (fun _ _ ↦ id) 1 (by omega) forces_top;
  exact h;


end Logic


end FFL.InterpretabilityLogic

