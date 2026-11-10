module

public import AlphaCentauri.InterpretabilityLogic.Logic.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinus.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinusJ1J5.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.LabelledSetModel

/-!
# Soundness and completeness of $\mathbf{IL}^-(\mathbf{J4}^+)$
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

namespace Logic

open Entailment Formula

variable {α : Type*}

/-- $\mathbf{IL}^-(\mathbf{J4}^+)$.

- [KO21, §3.2]
-/
abbrev ILMinusJ4Plus : Logic α := ofAxiomsMinus {Axioms.J4Plus A B C | (A) (B) (C)}

end Logic

section Soundness

namespace Logic

open Veltman Veltman.Model Veltman.Model.World

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {A : Formula α}

theorem ILMinusJ4Plus.sound [M.IsILMinus] [M.IsJ4] : ILMinusJ4Plus ⊢ A → M ⊧ A :=
  ofAxiomsMinus.sound <| by
    rintro _ ⟨A, B, C, rfl⟩ x;
    exact forces_axiomJ4Plus

end Logic

end Soundness

section Consistency

open Veltman.Model Logic

variable {α : Type*}

instance : Entailment.Consistent (ILMinusJ4Plus : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILMinusJ4Plus.sound (M := pointModel fun _ ↦ False) h 0

end Consistency

section Completeness

namespace Logic

open Entailment Formula MaximalConsistentSet Veltman Veltman.Model
open LabelledSet.Condition ofAxiomsMinus

variable {α : Type} {A : Formula α}

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ4Plus.iff_valid_finite :
    ILMinusJ4Plus ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ4] → M ⊧ A := by
  constructor;
  · intro h _ _ _ M;
    intros;
    exact ILMinusJ4Plus.sound h;
  · intro h;
    classical
    exact provable_of_models_labelledModel .J4Plus (h _)

end Logic

end Completeness



section EquivalentAxiomatizations

namespace Logic

open Entailment ofAxiomsMinus

variable {α : Type*}

section J4Plus

private lemma J4Plus'_subset :
    (ofAxiomsMinus {Axioms.J4Plus' A B C | (A) (B) (C)} : Logic α) ⊆ ILMinusJ4Plus := by
  apply subset_of_provable;
  rintro _ ⟨A, B, C, rfl⟩;
  have h₁ : ILMinusJ4Plus ⊢ □A 🡒 □((A 🡒 B) 🡒 B) := box_mono (by cl_prover);
  have h₂ : ILMinusJ4Plus ⊢ □((A 🡒 B) 🡒 B) 🡒 C ▷ (A 🡒 B) 🡒 C ▷ B := HasAxiomJ4Plus.J4Plus _ _ _;
  cl_prover [h₁, h₂];

private lemma J4Plus''_subset :
    (ofAxiomsMinus {Axioms.J4Plus'' A B C | (A) (B) (C)} : Logic α) ⊆
      ofAxiomsMinus {Axioms.J4Plus' A B C | (A) (B) (C)} := by
  apply subset_of_provable;
  rintro _ ⟨A, B, C, rfl⟩;
  have h₁ : ofAxiomsMinus {Axioms.J4Plus' A B C | (A) (B) (C)} ⊢
      C ▷ B 🡒 C ▷ (A 🡒 A ⋏ B) := rhd_mono_right (by cl_prover);
  have h₂ : ofAxiomsMinus {Axioms.J4Plus' A B C | (A) (B) (C)} ⊢
      □A 🡒 C ▷ (A 🡒 A ⋏ B) 🡒 C ▷ (A ⋏ B) := axm (by simp);
  cl_prover [h₁, h₂];

private lemma J4Plus_subset :
    (ILMinusJ4Plus : Logic α) ⊆ ofAxiomsMinus {Axioms.J4Plus'' A B C | (A) (B) (C)} := by
  apply subset_of_provable;
  rintro _ ⟨A, B, C, rfl⟩;
  have h₁ : ofAxiomsMinus {Axioms.J4Plus'' A B C | (A) (B) (C)} ⊢
      □(A 🡒 B) 🡒 C ▷ A 🡒 C ▷ ((A 🡒 B) ⋏ A) := axm (by simp);
  have h₂ : ofAxiomsMinus {Axioms.J4Plus'' A B C | (A) (B) (C)} ⊢
      C ▷ ((A 🡒 B) ⋏ A) 🡒 C ▷ B := rhd_mono_right (by cl_prover);
  cl_prover [h₁, h₂];

/-- - [KO21, Proposition 3.6] -/
theorem ILMinusJ4Plus.eq_ofAxiomsMinus_J4Plus' :
    (ILMinusJ4Plus : Logic α) = ofAxiomsMinus {Axioms.J4Plus' A B C | (A) (B) (C)} :=
  Set.Subset.antisymm (J4Plus_subset.trans J4Plus''_subset) J4Plus'_subset

/-- - [KO21, Proposition 3.6] -/
theorem ILMinusJ4Plus.eq_ofAxiomsMinus_J4Plus'' :
    (ILMinusJ4Plus : Logic α) = ofAxiomsMinus {Axioms.J4Plus'' A B C | (A) (B) (C)} :=
  Set.Subset.antisymm J4Plus_subset (J4Plus''_subset.trans J4Plus'_subset)

end J4Plus

end Logic

end EquivalentAxiomatizations

section Relations

namespace Logic

open Entailment

variable {α : Type*}

instance : (𝐈𝐋⁻ : Logic α) ⪱ ILMinusJ4Plus :=
  .of_unprovable_provable ILMinusJ1J5.unprovable_J4Plus (HasAxiomJ4Plus.J4Plus _ _ _)

end Logic

end Relations

end FFL.InterpretabilityLogic

