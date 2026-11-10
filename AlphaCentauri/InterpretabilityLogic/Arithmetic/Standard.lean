module

public import AlphaCentauri.InterpretabilityLogic.Arithmetic.Basic
public import AlphaCentauri.Interpretability.InterpretationExistence

/-!
# Arithmetical soundness of $\mathbf{IL}$ for formalized interpretability

For an arithmetical theory $T \supseteq \mathsf{PA}$ with $\Delta_1$ axioms, reading `□` as the
standard provability predicate of $T$ and `▷` as formalized relative interpretability over $T$,
every theorem of $\mathbf{IL}$ is provable in $T$ under every realization.

## References

- [Vis90, §6.1, §6.2.2.1]
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open FirstOrder FirstOrder.Arithmetic FirstOrder.ProvabilityAbstraction

variable (T : ArithmeticTheory) [T.Δ₁]

/-- Formalized relative interpretability over `T`, as an interpretability abstraction over the
standard provability predicate of `T`.
- [Vis90, §5.5] -/
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
- [Vis90, §6.1] -/
theorem Logic.IL.arithmetical_soundness_interpretability (h : 𝐈𝐋 ⊢ A) :
    T ⊢ A.interpret f T.standardProvability T.interpretabilityAbstraction :=
  have : 𝗜𝚺₁ ⪯ T :=
    Entailment.WeakerThan.trans (inferInstance : 𝗜𝚺₁ ⪯ 𝗣𝗔) (inferInstance : 𝗣𝗔 ⪯ T)
  Entailment.WeakerThan.pbl (Logic.IL.arithmetical_soundness h)

end FFL.InterpretabilityLogic
