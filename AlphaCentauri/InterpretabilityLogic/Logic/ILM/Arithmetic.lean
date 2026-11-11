module

public import AlphaCentauri.InterpretabilityLogic.Arithmetic.Conservativity
public import AlphaCentauri.InterpretabilityLogic.Logic.IL.Arithmetic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILM.Basic

/-!
# Arithmetical soundness of $\mathbf{ILM}$

The arithmetical interpretation of $\mathbf{ILM}$ is sound for provability in an arithmetical
theory, and for $\Pi_1$-conservativity over $\mathsf{I}\Sigma_1$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment FirstOrder FirstOrder.ProvabilityAbstraction
open Interpretability Formula

variable {α : Type*} {L : Language} [L.ReferenceableBy L] {T₀ T : Theory L}

variable [L.DecidableEq] [Diagonalization T₀] [T₀ ⪯ T]
  {𝔅 : Provability T₀ T} [𝔅.HBL] {𝔍 : Interpretability 𝔅} [𝔍.IL]
  {f : ProvabilityLogic.Realization α L} {A : Formula α}

theorem Logic.ILM.arithmetical_soundness [𝔍.M] (h : 𝐈𝐋𝐌 ⊢ A) : T₀ ⊢ A.interpret f 𝔅 𝔍 := by
  apply Logic.ofILAxioms.arithmetical_soundness _ h;
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

section

open FirstOrder Arithmetic

variable {α : Type*} {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T]
  {f : ProvabilityLogic.Realization α ℒₒᵣ} {A : Formula α}

/-- - [HM90, Definition 3.1] -/
theorem Logic.ILM.arithmetical_soundness_pi1Conservativity (h : 𝐈𝐋𝐌 ⊢ A) :
    T ⊢ A.interpret f T.standardProvability (T.conservativity 𝚷 1) :=
  Entailment.WeakerThan.pbl <| Logic.ILM.arithmetical_soundness h

end

end FFL.InterpretabilityLogic

end
