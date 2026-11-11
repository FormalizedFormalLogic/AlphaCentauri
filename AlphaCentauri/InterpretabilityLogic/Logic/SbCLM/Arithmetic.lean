module

public import AlphaCentauri.InterpretabilityLogic.Arithmetic.Conservativity
public import AlphaCentauri.InterpretabilityLogic.Logic.SbCLM.Basic

/-!
# Arithmetical soundness of $\mathbf{SbCLM}$

The arithmetical interpretation of $\mathbf{SbCLM}$ is sound for every interpretability abstraction
satisfying $\mathbf{J1}$–$\mathbf{J4}$, $\mathbf{M}$ and $\mathsf{Sb}$, in particular for
$\Pi_n$-conservativity over a theory containing $\mathsf{B}\Sigma_2$ for $n \geq 2$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment FirstOrder FirstOrder.ProvabilityAbstraction
open Interpretability Formula

variable {α : Type*} {L : Language} [L.ReferenceableBy L] {T₀ T : Theory L}
  [L.DecidableEq] [Diagonalization T₀] [T₀ ⪯ T]
  {𝔅 : Provability T₀ T} [𝔅.HBL] {𝔍 : Interpretability 𝔅} [𝔍.CL]
  {f : ProvabilityLogic.Realization α L}

theorem Logic.SbCLM.arithmetical_soundness [𝔍.M] [𝔍.Sb] {A : Formula α} (h : 𝐒𝐛𝐂𝐋𝐌 ⊢ A) :
    T₀ ⊢ A.interpret f 𝔅 𝔍 := by
  apply Logic.ofCLAxioms.arithmetical_soundness _ h;
  rintro _ (⟨A, B, C, rfl⟩ | ⟨A, B, C, D, rfl⟩) <;> dsimp only [interpret];
  · apply rhd_and_of_iff M.axiomM;
    cl_prover;
  · apply rhd_and_of_iff Sb.axiomSb;
    cl_prover;

end FFL.InterpretabilityLogic

namespace FFL.FirstOrder.ArithmeticTheory

open InterpretabilityLogic

variable {α : Type*} {T : ArithmeticTheory} [T.Δ₁] [𝗕𝚺2 ⪯ T] {n : ℕ}

/-- - [Ign91, Theorem A.2] -/
instance instSbCLMConservativityLogicPi :
    (𝐒𝐛𝐂𝐋𝐌 : Logic α) ⪯ T.conservativityLogic 𝚷 (n + 2) := by
  have : 𝗜𝚺₁ ⪯ T := Arithmetic.ISigma_weakerThan_BSigma_succ.trans inferInstance;
  exact Logic.weakerThan_iff.mpr fun _ hA _ ↦
    Entailment.WeakerThan.pbl <| Logic.SbCLM.arithmetical_soundness hA

end FFL.FirstOrder.ArithmeticTheory

end
