module

public import AlphaCentauri.InterpretabilityLogic.Arithmetic.Conservativity
public import AlphaCentauri.InterpretabilityLogic.Logic.CL.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.IL.Basic

/-!
# Arithmetical soundness of $\mathbf{CL}$

The arithmetical interpretation of $\mathbf{CL}$ is sound for every interpretability abstraction
satisfying $\mathbf{J1}$–$\mathbf{J4}$, in particular for $\Gamma_n$-conservativity over a theory
containing $\mathsf{I}\Sigma_1$. If the theory is moreover $\Sigma_1$-sound, the
$\Sigma_{n + 1}$- and $\Pi_{n + 2}$-conservativity logics do not contain $\mathbf{IL}$.
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

section

variable [T.SoundOnHierarchy 𝚺 1]

/-- - [Ign91, §1] -/
theorem not_IL_weakerThan_conservativityLogic_sigma :
    ¬(𝐈𝐋 : Logic α) ⪯ T.conservativityLogic 𝚺 (n + 1) :=
  Entailment.not_weakerThan_iff.mpr
    ⟨_, Logic.ofILAxioms.axiomJ5, conservativityLogic_sigma_unprovable_axiomJ5⟩

/-- - [Ign91, §1] -/
theorem not_IL_weakerThan_conservativityLogic_pi :
    ¬(𝐈𝐋 : Logic α) ⪯ T.conservativityLogic 𝚷 (n + 2) :=
  Entailment.not_weakerThan_iff.mpr
    ⟨_, Logic.ofILAxioms.axiomJ5, conservativityLogic_pi_unprovable_axiomJ5⟩

end

end FFL.FirstOrder.ArithmeticTheory

end
