module

public import AlphaCentauri.Interpretability.Formalized
public import AlphaCentauri.InterpretabilityLogic.Logic.Basic
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.ProvabilityFormula
public import Foundation.FirstOrder.Incompleteness.ProvabilityAbstraction.Basic
public import Foundation.ProvabilityLogic.Arithmetic.Interpret
public import Foundation.FirstOrder.Incompleteness.StandardProvability
public import AlphaCentauri.InterpretabilityLogic.Logic.IL.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILM.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILF.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILPZero.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILW.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILRW.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMZeroW.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILP.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILWStar.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILRStar.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILKWOneZero.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILKW2.Basic

/-!
# Arithmetical soundness of interpretability logics

An interpretability abstraction over a provability abstraction `𝔅` is a binary operator on
sentences. Interpreting `□` by `𝔅` and `▷` by the operator, every theorem of $\mathbf{IL}$ is
provable under every realization once the arithmetical forms of $\mathbf{J1}$–$\mathbf{J5}$ are,
and every theorem of $\mathbf{ILM}$ once the arithmetical form of $\mathbf{M}$ is as well.

For an arithmetical theory $T \supseteq \mathsf{PA}$ with $\Delta_1$ axioms, reading `□` as the
standard provability predicate of $T$ and `▷` as formalized relative interpretability over $T$
satisfies these forms, so every theorem of $\mathbf{IL}$ is provable in $T$ under every
realization.

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

/-- $T_0$ proves the arithmetical forms of the axioms $\mathbf{J1}$–$\mathbf{J5}$ of
$\mathbf{IL}$. -/
class IL where
  J1 {σ τ : Sentence L} : T₀ ⊢ 𝔅 (σ 🡒 τ) 🡒 𝔍 σ τ
  J2 {σ τ χ : Sentence L} : T₀ ⊢ 𝔍 σ τ ⋏ 𝔍 τ χ 🡒 𝔍 σ χ
  J3 {σ τ χ : Sentence L} : T₀ ⊢ 𝔍 σ χ ⋏ 𝔍 τ χ 🡒 𝔍 (σ ⋎ τ) χ
  J4 {σ τ : Sentence L} : T₀ ⊢ 𝔍 σ τ 🡒 𝔅.dia σ 🡒 𝔅.dia τ
  J5 {σ : Sentence L} : T₀ ⊢ 𝔍 (𝔅.dia σ) σ
export IL (J1 J2 J3 J4 J5)

/-- $T_0$ proves the arithmetical form of the axiom $\mathbf{M}$. -/
class M where
  axiomM {σ τ χ : Sentence L} : T₀ ⊢ 𝔍 σ τ 🡒 𝔍 (σ ⋏ 𝔅 χ) (τ ⋏ 𝔅 χ)

variable {𝔍} [𝔍.IL] {σ σ' τ τ' χ : Sentence L}

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
  {𝔅 : Provability T₀ T} [𝔅.HBL] {𝔍 : Interpretability 𝔅} [𝔍.IL]
  {f : ProvabilityLogic.Realization α L} {𝔸 : Set (Formula α)} {A : Formula α}

theorem Logic.ofAxioms.arithmetical_soundness (h𝔸 : ∀ A ∈ 𝔸, T₀ ⊢ A.interpret f 𝔅 𝔍)
    (h : ofAxioms 𝔸 ⊢ A) : T₀ ⊢ A.interpret f 𝔅 𝔍 := by
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
    cl_prover [h₁, h₂, h₃];
  | @axiomJ5 A =>
    dsimp only [interpret];
    generalize A.interpret f 𝔅 𝔍 = σ;
    have h₁ : T₀ ⊢ 𝔅 (∼σ) 🡒 𝔅 (σ 🡒 ⊥) := 𝔅.mono <| by cl_prover;
    have h₂ : T₀ ⊢ 𝔍 (𝔅.dia σ) σ 🡒 𝔍 (𝔅 (σ 🡒 ⊥) 🡒 ⊥) σ :=
      Interpretability.rhd_anti_left <| WeakerThan.pbl (𝓢 := T₀) <| by cl_prover [h₁];
    exact h₂ ⨀ J5;
  | _ => dsimp [interpret]; cl_prover;

theorem Logic.IL.arithmetical_soundness (h : 𝐈𝐋 ⊢ A) : T₀ ⊢ A.interpret f 𝔅 𝔍 :=
  Logic.ofAxioms.arithmetical_soundness (by simp) h

theorem Logic.ILM.arithmetical_soundness [𝔍.M] (h : 𝐈𝐋𝐌 ⊢ A) : T₀ ⊢ A.interpret f 𝔅 𝔍 := by
  apply Logic.ofAxioms.arithmetical_soundness _ h;
  rintro _ ⟨A, B, C, rfl⟩;
  dsimp only [interpret];
  generalize A.interpret f 𝔅 𝔍 = σ, B.interpret f 𝔅 𝔍 = τ, C.interpret f 𝔅 𝔍 = χ;
  have h₁ : T₀ ⊢ 𝔍 σ τ 🡒 𝔍 (σ ⋏ 𝔅 χ) (τ ⋏ 𝔅 χ) := M.axiomM;
  have h₂ : T₀ ⊢ 𝔍 (σ ⋏ 𝔅 χ) (τ ⋏ 𝔅 χ) 🡒 𝔍 ((σ 🡒 𝔅 χ 🡒 ⊥) 🡒 ⊥) (τ ⋏ 𝔅 χ) :=
    Interpretability.rhd_anti_left <| by cl_prover;
  have h₃ : T₀ ⊢ 𝔍 ((σ 🡒 𝔅 χ 🡒 ⊥) 🡒 ⊥) (τ ⋏ 𝔅 χ) 🡒
      𝔍 ((σ 🡒 𝔅 χ 🡒 ⊥) 🡒 ⊥) ((τ 🡒 𝔅 χ 🡒 ⊥) 🡒 ⊥) :=
    Interpretability.rhd_mono_right <| by cl_prover;
  cl_prover [h₁, h₂, h₃];

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

variable [𝗣𝗔 ⪯ T] [Theory.Δ₁.Sentential T]

instance instILInterpretabilityAbstraction : T.interpretabilityAbstraction.IL where
  J1 := ArithmeticTheory.interpretability_of_provable
  J2 := ArithmeticTheory.interpretability_trans
  J3 := ArithmeticTheory.interpretability_or
  J4 := ArithmeticTheory.consistent_of_interpretability
  J5 := ArithmeticTheory.interpretability_consistency _

variable {T} {α : Type*} {f : ProvabilityLogic.Realization α ℒₒᵣ} {A : Formula α}

/-- Arithmetical soundness of $\mathbf{IL}$: every theorem of $\mathbf{IL}$ is provable in $T$
when `□` is read as provability in $T$ and `▷` as formalized relative interpretability over $T$.

- [Vis90, §6.1]
-/
theorem Logic.IL.arithmetical_soundness_interpretability (h : 𝐈𝐋 ⊢ A) :
    T ⊢ A.interpret f T.standardProvability T.interpretabilityAbstraction :=
  have : 𝗜𝚺₁ ⪯ T :=
    Entailment.WeakerThan.trans (inferInstance : 𝗜𝚺₁ ⪯ 𝗣𝗔) (inferInstance : 𝗣𝗔 ⪯ T)
  Entailment.WeakerThan.pbl (Logic.IL.arithmetical_soundness h)

end

end FFL.InterpretabilityLogic

end
