module

public import AlphaCentauri.InterpretabilityLogic.Arithmetic.Conservativity
public import AlphaCentauri.InterpretabilityLogic.Logic.CL.Basic

/-!
# Arithmetical soundness of $\mathbf{CL}$

The arithmetical interpretation of $\mathbf{CL}$ is sound for every interpretability abstraction
satisfying $\mathbf{J1}$–$\mathbf{J4}$, in particular for $\Gamma_n$-conservativity over a theory
containing $\mathsf{I}\Sigma_1$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment FirstOrder FirstOrder.ProvabilityAbstraction
open Interpretability Formula

variable {α : Type*} {L : Language} [L.ReferenceableBy L] {T₀ T : Theory L}
  [L.DecidableEq] [Diagonalization T₀] [T₀ ⪯ T]
  {𝔅 : Provability T₀ T} [𝔅.HBL] {𝔍 : Interpretability 𝔅} [𝔍.CL]
  {f : ProvabilityLogic.Realization α L} {A : Formula α}

theorem Logic.CL.arithmetical_soundness (h : 𝐂𝐋 ⊢ A) : T₀ ⊢ A.interpret f 𝔅 𝔍 :=
  Logic.ofCLAxioms.arithmetical_soundness (by simp) h

end FFL.InterpretabilityLogic

namespace FFL.FirstOrder.ArithmeticTheory

open InterpretabilityLogic

variable {α : Type*} {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] {Γ : Polarity} {n : ℕ}

/-- - [Ign91, §1] -/
instance : (𝐂𝐋 : Logic α) ⪯ T.conservativityLogic Γ n :=
  Logic.weakerThan_iff.mpr fun _ hA _ ↦
    Entailment.WeakerThan.pbl <| Logic.CL.arithmetical_soundness hA

end FFL.FirstOrder.ArithmeticTheory

end
