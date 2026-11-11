module

public import AlphaCentauri.InterpretabilityLogic.Logic.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinusJ2Plus.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinusJ1J4Plus.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.Counterexamples
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.LabelledSetModel

/-!
# Soundness and completeness of $\mathbf{CL}$
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

namespace Logic

open Entailment Formula

variable {α : Type*}

/-- $\mathbf{CL}$, presented as $\mathbf{IL}^-(\mathbf{J1}, \mathbf{J2})$.

- [KO21, Proposition 3.21]
-/
abbrev CL : Logic α :=
  ofAxiomsMinus ({Axioms.J1 A B | (A) (B)} ∪ {Axioms.J2 A B C | (A) (B) (C)})

notation "𝐂𝐋" => Logic.CL

end Logic

namespace Veltman.Model

variable {κ α : Type*} [Nonempty κ] (M : Model κ α)

class IsCL : Prop extends M.IsILMinus, M.IsJ1, M.IsJ2

instance (priority := low) [M.IsILMinus] [M.IsJ1] [M.IsJ2] : M.IsCL := {}

end Veltman.Model

namespace Logic

/-! ## The principle $\mathsf{J2}^+$ -/


open ofAxiomsMinus

variable {α : Type*}

/-- - [KO21, Proposition 3.12.2] -/
instance : HasAxiomJ2Plus (𝐂𝐋 : Logic α) where
  J2Plus A B C := by
    have h₁ : 𝐂𝐋 ⊢ B ▷ C ⋏ C ▷ C 🡒 (B ⋎ C) ▷ C := axiomJ3;
    have h₂ : 𝐂𝐋 ⊢ C ▷ C := axiomJ1';
    have h₃ : 𝐂𝐋 ⊢ A ▷ (B ⋎ C) ⋏ (B ⋎ C) ▷ C 🡒 A ▷ C := HasAxiomJ2.J2 _ _ _;
    cl_prover [h₁, h₂, h₃];


/-! ## Completeness -/


open Entailment Formula MaximalConsistentSet Veltman Veltman.Model Veltman.Model.World
open LabelledSet.Condition ofAxiomsMinus

variable {α : Type} {A : Formula α}

/-- - [KO21, Theorem 5.1] -/
theorem CL.semantics_TFAE : [
    𝐂𝐋 ⊢ A,
    ∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ α),
      [M.IsCL] → M ⊧ A,
    ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsCL] → M ⊧ A
  ].TFAE := by
  tfae_have 1 → 2 := by
    intro h _ _ M _;
    apply ofAxiomsMinus.sound _ h;
    rintro _ (⟨A, B, rfl⟩ | ⟨A, B, C, rfl⟩) x;
    · exact forces_axiomJ1;
    · exact forces_axiomJ2;
  tfae_have 2 → 3 := by
    intro h _ _ _ M _;
    exact h M;
  tfae_have 3 → 1 := by
    intro h;
    classical
    exact provable_of_models_labelledModel .J2Plus (h _);
  tfae_finish;

theorem CL.iff_valid :
    𝐂𝐋 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ α),
      [M.IsCL] → M ⊧ A :=
  CL.semantics_TFAE.out 1 2

theorem CL.sound {κ : Type} [Nonempty κ] {M : Veltman.Model κ α}
    [M.IsCL] (h : 𝐂𝐋 ⊢ A) : M ⊧ A :=
  CL.iff_valid.mp h M

instance : Entailment.Consistent (𝐂𝐋 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ CL.sound (M := pointModel fun _ ↦ False) h 0

/-- - [KO21, Theorem 5.1] -/
theorem CL.iff_valid_finite :
    𝐂𝐋 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsCL] → M ⊧ A :=
  CL.semantics_TFAE.out 1 3


/-! ## Relations -/


open Entailment Veltman

variable {α : Type}

instance : (ILMinusJ2Plus : Logic α) ⪱ 𝐂𝐋 :=
  .of_unprovable_provable (φ := Axioms.J1 ⊤ ⊤)
    (fun h ↦ counterJ1.not_models_J1 (ILMinusJ2Plus.sound (M := counterJ1 α) h)) (HasAxiomJ1.J1 _ _)

instance : (ILMinusJ1J4Plus : Logic α) ⪱ 𝐂𝐋 :=
  .of_unprovable_provable (φ := Axioms.J2 (□⊥) (◇⊤ ⋏ □□⊥) (◇◇⊤))
    (fun h ↦ counterJ2.not_models_J2 (ILMinusJ1J4Plus.sound (M := counterJ2 α) h))
    (HasAxiomJ2.J2 _ _ _)

end Logic

end FFL.InterpretabilityLogic

