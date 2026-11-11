module

public import AlphaCentauri.Interpretability.InterpretationExistence
public import AlphaCentauri.InterpretabilityLogic.Logic.Basic
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.ProvabilityFormula
public import Foundation.FirstOrder.Incompleteness.ProvabilityAbstraction.Basic
public import Foundation.ProvabilityLogic.Arithmetic.Interpret
public import Foundation.FirstOrder.Incompleteness.StandardProvability

/-!
# Arithmetical soundness of interpretability logics

An interpretability abstraction over a provability abstraction `𝔅` is a binary operator on
sentences. Interpreting `□` by `𝔅` and `▷` by the operator, the theorems of a logic extending
$\mathbf{CL}$ are provable under every realization once the arithmetical forms of
$\mathbf{J1}$–$\mathbf{J4}$ and of its axioms are.

## References

- [Vis90, §6.1, §6.2.2.1]
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

section

open Entailment FirstOrder FirstOrder.ProvabilityAbstraction

variable {α : Type*} {L : Language} [L.ReferenceableBy L] {T₀ T : Theory L}

/-- A binary operator on sentences, read as interpretability alongside the provability `𝔅`. -/
structure Interpretability (𝔅 : Provability T₀ T) where
  rhd : Sentence L → Sentence L → Sentence L

namespace Interpretability

variable {𝔅 : Provability T₀ T}

instance : CoeFun (Interpretability 𝔅) (fun _ ↦ Sentence L → Sentence L → Sentence L) := ⟨rhd⟩

variable (𝔍 : Interpretability 𝔅)

/-- $T_0$ proves the arithmetical forms of the axioms $\mathbf{J1}$–$\mathbf{J4}$ of
$\mathbf{CL}$. -/
class CL where
  J1 {σ τ : Sentence L} : T₀ ⊢ 𝔅 (σ 🡒 τ) 🡒 𝔍 σ τ
  J2 {σ τ χ : Sentence L} : T₀ ⊢ 𝔍 σ τ ⋏ 𝔍 τ χ 🡒 𝔍 σ χ
  J3 {σ τ χ : Sentence L} : T₀ ⊢ 𝔍 σ χ ⋏ 𝔍 τ χ 🡒 𝔍 (σ ⋎ τ) χ
  J4 {σ τ : Sentence L} : T₀ ⊢ 𝔍 σ τ 🡒 𝔅.dia σ 🡒 𝔅.dia τ
export CL (J1 J2 J3 J4)

/-- $T_0$ proves the arithmetical forms of the axioms $\mathbf{J1}$–$\mathbf{J5}$ of
$\mathbf{IL}$. -/
class IL extends 𝔍.CL where
  J5 {σ : Sentence L} : T₀ ⊢ 𝔍 (𝔅.dia σ) σ
export IL (J5)

/-- $T_0$ proves the arithmetical form of the axiom $\mathbf{M}$. -/
class M where
  axiomM {σ τ χ : Sentence L} : T₀ ⊢ 𝔍 σ τ 🡒 𝔍 (σ ⋏ 𝔅 χ) (τ ⋏ 𝔅 χ)

variable {𝔍} [𝔍.CL] {σ σ' τ τ' χ : Sentence L}

lemma rhd_anti_left (h : T ⊢ σ' 🡒 σ) : T₀ ⊢ 𝔍 σ χ 🡒 𝔍 σ' χ := by
  have h₁ : T₀ ⊢ 𝔍 σ' σ := J1 ⨀ 𝔅.D1 h;
  have h₂ : T₀ ⊢ 𝔍 σ' σ ⋏ 𝔍 σ χ 🡒 𝔍 σ' χ := J2;
  cl_prover [h₁, h₂];

lemma rhd_mono_right (h : T ⊢ τ 🡒 τ') : T₀ ⊢ 𝔍 σ τ 🡒 𝔍 σ τ' := by
  have h₁ : T₀ ⊢ 𝔍 τ τ' := J1 ⨀ 𝔅.D1 h;
  have h₂ : T₀ ⊢ 𝔍 σ τ ⋏ 𝔍 τ τ' 🡒 𝔍 σ τ' := J2;
  cl_prover [h₁, h₂];

end Interpretability

namespace Formula

/-- The arithmetical interpretation of a formula, reading `□` as `𝔅` and `▷` as `𝔍`. -/
@[grind]
def interpret (f : ProvabilityLogic.Realization α L) (𝔅 : Provability T₀ T)
    (𝔍 : Interpretability 𝔅) : Formula α → Sentence L
  | #a    => f.val a
  | ⊥     => ⊥
  | A 🡒 B => A.interpret f 𝔅 𝔍 🡒 B.interpret f 𝔅 𝔍
  | □A    => 𝔅 (A.interpret f 𝔅 𝔍)
  | A ▷ B => 𝔍 (A.interpret f 𝔅 𝔍) (B.interpret f 𝔅 𝔍)

end Formula

open Interpretability Formula

variable [L.DecidableEq] [Diagonalization T₀] [T₀ ⪯ T]
  {𝔅 : Provability T₀ T} [𝔅.HBL] {𝔍 : Interpretability 𝔅} [𝔍.CL]
  {f : ProvabilityLogic.Realization α L} {𝔸 : FormulaSet α} {A : Formula α}

theorem Logic.ofCLAxioms.arithmetical_soundness (h𝔸 : ∀ A ∈ 𝔸, T₀ ⊢ A.interpret f 𝔅 𝔍)
    (h : ofCLAxioms 𝔸 ⊢ A) : T₀ ⊢ A.interpret f 𝔅 𝔍 := by
  induction h with
  | axm hA => exact h𝔸 _ hA;
  | mdp _ _ ih₁ ih₂ => exact ih₁ ⨀ ih₂;
  | nec _ ih => exact 𝔅.D1 <| WeakerThan.pbl ih;
  | axiomK => exact 𝔅.D2;
  | axiomL => exact formalized_löb_theorem;
  | axiomJ1 => exact J1;
  | @axiomJ2 A B C =>
    dsimp only [interpret];
    generalize A.interpret f 𝔅 𝔍 = σ, B.interpret f 𝔅 𝔍 = τ, C.interpret f 𝔅 𝔍 = χ;
    have h : T₀ ⊢ 𝔍 σ τ ⋏ 𝔍 τ χ 🡒 𝔍 σ χ := J2;
    cl_prover [h];
  | @axiomJ3 A B C =>
    dsimp only [interpret];
    generalize A.interpret f 𝔅 𝔍 = σ, B.interpret f 𝔅 𝔍 = τ, C.interpret f 𝔅 𝔍 = χ;
    have h₁ : T₀ ⊢ 𝔍 σ χ ⋏ 𝔍 τ χ 🡒 𝔍 (σ ⋎ τ) χ := J3;
    have h₂ : T₀ ⊢ 𝔍 (σ ⋎ τ) χ 🡒 𝔍 ((σ 🡒 ⊥) 🡒 τ) χ :=
      Interpretability.rhd_anti_left <| by cl_prover;
    cl_prover [h₁, h₂];
  | @axiomJ4 A B =>
    dsimp only [interpret];
    generalize A.interpret f 𝔅 𝔍 = σ, B.interpret f 𝔅 𝔍 = τ;
    have h₁ : T₀ ⊢ 𝔍 σ τ 🡒 𝔅.dia σ 🡒 𝔅.dia τ := J4;
    have h₂ : T₀ ⊢ 𝔅 (∼σ) 🡒 𝔅 (σ 🡒 ⊥) := 𝔅.mono <| by cl_prover;
    have h₃ : T₀ ⊢ 𝔅 (τ 🡒 ⊥) 🡒 𝔅 (∼τ) := 𝔅.mono <| by cl_prover;
    simp only [Provability.dia] at h₁;
    cl_prover [h₁, h₂, h₃];
  | _ => dsimp [interpret]; cl_prover;

end

section

open FirstOrder FirstOrder.Arithmetic FirstOrder.ProvabilityAbstraction

variable (T : ArithmeticTheory) [T.Δ₁]

/-- Formalized relative interpretability over `T`, as an interpretability abstraction over the
standard provability predicate of `T`.

- [Vis90, §5.5]
-/
noncomputable def _root_.FFL.FirstOrder.ArithmeticTheory.interpretabilityAbstraction :
    Interpretability T.standardProvability :=
  ⟨T.interpretability⟩

/-- The interpretability logic of `T`: the formulas provable in `T` under every realization,
reading `□` as provability in `T` and `▷` as formalized relative interpretability over `T`.

- [Vis90, §6.1]
-/
def _root_.FFL.FirstOrder.ArithmeticTheory.interpretabilityLogic {α : Type*} : Logic α :=
  { A | ∀ f : ProvabilityLogic.Realization α ℒₒᵣ,
    T ⊢ A.interpret f T.standardProvability T.interpretabilityAbstraction }

variable [𝗣𝗔 ⪯ T] [Theory.Δ₁.Sentential T]

instance instILInterpretabilityAbstraction : T.interpretabilityAbstraction.IL where
  J1 := ArithmeticTheory.interpretability_of_provable
  J2 := ArithmeticTheory.interpretability_trans
  J3 := ArithmeticTheory.interpretability_or
  J4 := ArithmeticTheory.consistent_of_interpretability
  J5 := ArithmeticTheory.interpretability_consistency _

end

end FFL.InterpretabilityLogic

end
