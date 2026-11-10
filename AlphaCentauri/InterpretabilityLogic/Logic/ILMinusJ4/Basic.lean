module

public import AlphaCentauri.InterpretabilityLogic.Logic.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.ILMinus
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.ILMinusModel
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinusJ1J4J5.Basic

/-!
# Soundness and completeness of $\mathbf{IL}^-(\mathbf{J4})$
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

namespace Logic

open Entailment Formula

variable {α : Type*}

/-- $\mathbf{IL}^-(\mathbf{J4})$.

- [KO21, §3.2]
-/
abbrev ILMinusJ4 : Logic α := ofAxiomsMinus {Axioms.J4 A B | (A) (B)}

end Logic

section Soundness

namespace Logic

open Veltman Veltman.Model Veltman.Model.World

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {A : Formula α}

theorem ILMinusJ4.sound [M.IsILMinus] [M.IsJ4] : ILMinusJ4 ⊢ A → M ⊧ A :=
  ofAxiomsMinus.sound <| by
    rintro _ ⟨A, B, rfl⟩ x;
    exact forces_axiomJ4

end Logic

end Soundness

section Consistency

open Veltman.Model Logic

variable {α : Type*}

instance : Entailment.Consistent (ILMinusJ4 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILMinusJ4.sound (M := pointModel fun _ ↦ False) h 0

end Consistency

section CompletenessVerbrugge

namespace Logic

open Entailment Formula MaximalConsistentSet Verbrugge Verbrugge.Model Verbrugge.Model.World

variable {α : Type} {A : Formula α}

/-- - [KO21, Theorem 7.1] -/
theorem ILMinusJ4.semantics_TFAE : [
    ILMinusJ4 ⊢ A,
    ∀ {κ : Type} [Nonempty κ] (M : Verbrugge.Model κ α),
      [M.IsILMinus] → [M.IsJ4] → M ⊧ A,
    ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Verbrugge.Model κ α),
      [M.IsILMinus] → [M.IsJ4] → M ⊧ A
  ].TFAE := by
  tfae_have 1 → 2 := by
    intro h _ _ M _ _;
    apply ofAxiomsMinus.sound_verbrugge _ h;
    rintro _ ⟨A, B, rfl⟩ x;
    exact forces_axiomJ4;
  tfae_have 2 → 3 := by
    intro h _ _ _ M _ _;
    exact h M;
  tfae_have 3 → 1 := by
    intro h;
    classical
    by_contra hA;
    obtain ⟨Γ, hΓ⟩ := exists_neg_consistent (Φ := ilMinusAdequateClosure {A}) hA;
    have : Nonempty (LabelledSet ILMinusJ4 (ilMinusAdequateClosure {A})) := ⟨⟨Γ, ⊥, .bot⟩⟩;
    exact MaximalConsistentSet.not_mem_of_provable_neg hΓ (Context.by_axm rfl) <|
      (LabelledSet.truthlemma_condJ4 (x := ⟨Γ, ⊥, .bot⟩)
        (ilMinusAdequateClosure.subset (by simp))).mp <|
          h (LabelledSet.model LabelledSet.condJ4) ⟨Γ, ⊥, .bot⟩;
  tfae_finish;

theorem ILMinusJ4.iff_valid_verbrugge :
    ILMinusJ4 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] (M : Verbrugge.Model κ α),
      [M.IsILMinus] → [M.IsJ4] → M ⊧ A :=
  ILMinusJ4.semantics_TFAE.out 1 2

theorem ILMinusJ4.sound_verbrugge {κ : Type} [Nonempty κ] {M : Verbrugge.Model κ α}
    [M.IsILMinus] [M.IsJ4] (h : ILMinusJ4 ⊢ A) : M ⊧ A :=
  ILMinusJ4.iff_valid_verbrugge.mp h M

/-- - [KO21, Theorem 7.1] -/
theorem ILMinusJ4.iff_valid_finite_verbrugge :
    ILMinusJ4 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Verbrugge.Model κ α),
      [M.IsILMinus] → [M.IsJ4] → M ⊧ A :=
  ILMinusJ4.semantics_TFAE.out 1 3

end Logic

end CompletenessVerbrugge



section IncompletenessVerbrugge

namespace Logic

open Entailment

/-- - [KO21, Corollary 6.4] -/
theorem ILMinusJ4.incomplete : ∃ A : Formula ℕ,
    (∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ ℕ), [M.IsILMinus] → [M.IsJ4] → M ⊧ A) ∧
      ILMinusJ4 ⊬ A := by
  use Axioms.J4Plus (#1) (#2) (#0);
  constructor;
  · intro κ _ M _ _;
    exact valid_J4Plus M;
  · exact unprovable_J4Plus;

end Logic

end IncompletenessVerbrugge


section EquivalentAxiomatizations

namespace Logic

open Entailment ofAxiomsMinus

variable {α : Type*}

/-- - [KO21, Proposition 3.4] -/
theorem ILMinusJ4.eq_ofAxiomsMinus_J4' :
    (ILMinusJ4 : Logic α) = ofAxiomsMinus {Axioms.J4' A B | (A) (B)} := by
  apply Set.Subset.antisymm;
  · apply subset_of_provable;
    rintro _ ⟨A, B, rfl⟩;
    have h₁ : ofAxiomsMinus {Axioms.J4' A B | (A) (B)} ⊢ A ▷ B 🡒 B ▷ ⊥ 🡒 A ▷ ⊥ := axm (by simp);
    have h₂ : ofAxiomsMinus {Axioms.J4' A B | (A) (B)} ⊢ (◇A 🡒 ◇B) 🡘 (B ▷ ⊥ 🡒 A ▷ ⊥) :=
      dia_imp_dia_iff;
    cl_prover [h₁, h₂];
  · apply subset_of_provable;
    rintro _ ⟨A, B, rfl⟩;
    have h₁ : ILMinusJ4 ⊢ A ▷ B 🡒 ◇A 🡒 ◇B := HasAxiomJ4.J4 _ _;
    have h₂ : ILMinusJ4 ⊢ (◇A 🡒 ◇B) 🡘 (B ▷ ⊥ 🡒 A ▷ ⊥) := dia_imp_dia_iff;
    cl_prover [h₁, h₂];

end Logic

end EquivalentAxiomatizations

end FFL.InterpretabilityLogic

