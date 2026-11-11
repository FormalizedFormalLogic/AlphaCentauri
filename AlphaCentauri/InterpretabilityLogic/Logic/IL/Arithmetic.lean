module

public import AlphaCentauri.InterpretabilityLogic.Arithmetic.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.IL.Basic

/-!
# Arithmetical soundness of $\mathbf{IL}$

The arithmetical interpretation of $\mathbf{IL}$ is sound for provability in an arithmetical theory.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment FirstOrder FirstOrder.ProvabilityAbstraction
open Interpretability Formula

variable {α : Type*} {L : Language} [L.ReferenceableBy L] {T₀ T : Theory L}

variable [L.DecidableEq] [Diagonalization T₀] [T₀ ⪯ T]
  {𝔅 : Provability T₀ T} [𝔅.HBL] {𝔍 : Interpretability 𝔅} [𝔍.IL]
  {f : ProvabilityLogic.Realization α L} {𝔸 : FormulaSet α} {A : Formula α}

theorem Logic.ofILAxioms.arithmetical_soundness (h𝔸 : ∀ A ∈ 𝔸, T₀ ⊢ A.interpret f 𝔅 𝔍)
    (h : ofILAxioms 𝔸 ⊢ A) : T₀ ⊢ A.interpret f 𝔅 𝔍 := by
  rw [Logic.ofILAxioms.eq_ofCLAxioms] at h;
  apply Logic.ofCLAxioms.arithmetical_soundness _ h;
  rintro _ (⟨A, rfl⟩ | hA);
  · dsimp only [interpret];
    generalize A.interpret f 𝔅 𝔍 = σ;
    have h₁ : T₀ ⊢ 𝔅 (∼σ) 🡒 𝔅 (σ 🡒 ⊥) := 𝔅.mono <| by cl_prover;
    have h₂ : T₀ ⊢ 𝔍 (𝔅.dia σ) σ 🡒 𝔍 (𝔅 (σ 🡒 ⊥) 🡒 ⊥) σ :=
      Interpretability.rhd_anti_left <| WeakerThan.pbl (𝓢 := T₀) <| by cl_prover [h₁];
    exact h₂ ⨀ J5;
  · exact h𝔸 _ hA;

theorem Logic.IL.arithmetical_soundness (h : 𝐈𝐋 ⊢ A) : T₀ ⊢ A.interpret f 𝔅 𝔍 :=
  Logic.ofILAxioms.arithmetical_soundness (by simp) h

section

open FirstOrder FirstOrder.Arithmetic FirstOrder.ProvabilityAbstraction

variable (T : ArithmeticTheory) [T.Δ₁]

variable [𝗣𝗔 ⪯ T] [Theory.Δ₁.Sentential T]

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
