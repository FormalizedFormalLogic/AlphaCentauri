module

public import AlphaCentauri.InterpretabilityLogic.Logic.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.LabelledSetModel

/-!
# Soundness and completeness of $\mathbf{IL}^-(\mathbf{J2}^+)$
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

namespace Logic

open Entailment Formula

variable {α : Type*}

/-- $\mathbf{IL}^-(\mathbf{J2}^+)$.

- [KO21, §3.3]
-/
abbrev ILMinusJ2Plus : Logic α := ofAxiomsMinus {Axioms.J2Plus A B C | (A) (B) (C)}

end Logic

section Soundness

namespace Logic

open Veltman Veltman.Model Veltman.Model.World

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {A : Formula α}

theorem ILMinusJ2Plus.sound [M.IsILMinus] [M.IsJ2] : ILMinusJ2Plus ⊢ A → M ⊧ A :=
  ofAxiomsMinus.sound <| by
    rintro _ ⟨A, B, C, rfl⟩ x;
    exact forces_axiomJ2Plus

end Logic

end Soundness

section Consistency

open Veltman.Model Logic

variable {α : Type*}

instance : Entailment.Consistent (ILMinusJ2Plus : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILMinusJ2Plus.sound (M := pointModel fun _ ↦ False) h 0

end Consistency

section Completeness

namespace Logic

open Entailment Formula MaximalConsistentSet Veltman Veltman.Model
open LabelledSet.Condition ofAxiomsMinus

variable {α : Type} {A : Formula α}

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ2Plus.iff_valid_finite :
    ILMinusJ2Plus ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ2] → M ⊧ A := by
  constructor;
  · intro h _ _ _ M;
    intros;
    exact ILMinusJ2Plus.sound h;
  · intro h;
    classical
    exact provable_of_models_labelledModel .J2Plus (h _)

end Logic

end Completeness



section EquivalentAxiomatizations

namespace Logic

open Entailment ofAxiomsMinus

variable {α : Type*}

/-- - [KO21, Proposition 3.11] -/
theorem ILMinusJ2Plus.eq_ofAxiomsMinus_J2Plus' :
    (ILMinusJ2Plus : Logic α) = ofAxiomsMinus {Axioms.J2Plus' A B C | (A) (B) (C)} := by
  apply Set.Subset.antisymm;
  · apply subset_of_provable;
    rintro _ ⟨A, B, C, rfl⟩;
    have h₁ : ofAxiomsMinus {Axioms.J2Plus' A B C | (A) (B) (C)} ⊢
        B ▷ C 🡒 ((B ⋎ C) ⋏ ∼C) ▷ C := rhd_anti_left (by cl_prover);
    have h₂ : ofAxiomsMinus {Axioms.J2Plus' A B C | (A) (B) (C)} ⊢
        A ▷ (B ⋎ C) ⋏ ((B ⋎ C) ⋏ ∼C) ▷ C 🡒 A ▷ C := axm (by simp);
    cl_prover [h₁, h₂];
  · apply subset_of_provable;
    rintro _ ⟨A, B, C, rfl⟩;
    have h₁ : ILMinusJ2Plus ⊢ A ▷ B 🡒 A ▷ (B ⋏ ∼C ⋎ C) := rhd_mono_right (by cl_prover);
    have h₂ : ILMinusJ2Plus ⊢ A ▷ (B ⋏ ∼C ⋎ C) ⋏ (B ⋏ ∼C) ▷ C 🡒 A ▷ C :=
      HasAxiomJ2Plus.J2Plus _ _ _;
    cl_prover [h₁, h₂];

end Logic

end EquivalentAxiomatizations

end FFL.InterpretabilityLogic

