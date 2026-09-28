module

public import Foundation.ProvabilityLogic.Classification.General

@[expose] public section
/-!
# The $\omega$-th stage of the Turing progression by consistency

$T_\omega$ extends `T` by the local reflection principles of `T` for the sentences
$\Box_T^{n}\bot$, which over `T` amounts to adding $\neg\Box_T^{n + 1}\bot$ for every `n`. The
provability logic of `T` relative to $T_\omega$ has trace $\omega$.

- [AB05, §4.1]
-/

namespace FFL

open Entailment FirstOrder FirstOrder.Arithmetic

namespace FirstOrder.ArithmeticTheory

/-- $T_\omega = T + \{\neg\Box_T^{n + 1}\bot\}_n$, the $\omega$-th stage of the Turing progression
of `T` by consistency.
- [AB05, §4.1] -/
abbrev turingOmega (T : ArithmeticTheory) [T.Δ₁] : ArithmeticTheory :=
  T ∪ 𝗥𝗳𝗻[Set.range (T.standardProvability^[·] ⊥)] T

variable {T : ArithmeticTheory} [T.Δ₁]

lemma provable_neg_iterate_turingOmega : ∀ n, T.turingOmega ⊢ ∼T.standardProvability^[n] ⊥
  | 0 => by simp
  | n + 1 => by
    have h : T.turingOmega ⊢ T.standardProvability.refl (T.standardProvability^[n] ⊥) :=
      by_axm <| Set.mem_union_right _ ⟨_, ⟨n, rfl⟩, rfl⟩
    rw [Function.iterate_succ_apply']
    cl_prover [h, provable_neg_iterate_turingOmega n]

end FirstOrder.ArithmeticTheory

namespace ProvabilityLogic

open Formula

variable {α : Type*} {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T]

lemma trace_provabilityLogic_turingOmega_eq_univ :
    (T.provabilityLogicRelativeTo T.turingOmega (α := α)).trace = .univ :=
  Set.eq_univ_of_forall fun n ↦ mem_trace_provabilityLogic_iff.mpr fun _ ↦ by_axm <|
    Set.mem_union_right _
      ⟨_, ⟨n, rfl⟩, by simp [alpha, standardInterpret, interpret, interpret_boxItr]⟩

end ProvabilityLogic

end FFL
