module

public import Foundation.ProvabilityLogic.Classification.General

@[expose] public section
/-!
# Extensions by the standard interpretations of `TBB`
-/

namespace FFL

open Entailment FirstOrder ProvabilityLogic Formula

namespace ProvabilityLogic.Formula

variable {L : Language} [L.ReferenceableBy L] {T₀ T : Theory L}

lemma interpret_TBB (𝔅 : ProvabilityAbstraction.Provability T₀ T) {α : Type*}
    (f : Realization α L) (n : ℕ) :
    (TBB n : Formula α).interpret f 𝔅 = (𝔅^[n + 1] ⊥ 🡒 𝔅^[n] ⊥) := by
  simp [TBB, interpret, Function.iterate_succ_apply']

end ProvabilityLogic.Formula

namespace FirstOrder.ArithmeticTheory

variable {T U : ArithmeticTheory} [T.Δ₁] {N : Set ℕ}

/-- If `N` contains every index below `n`, the extension of `U` by the standard interpretations
of `TBB i` for `i ∈ N` proves that `n` iterations of `T`'s provability predicate do not prove
`⊥`. -/
lemma provable_neg_iterate_addTBB {n : ℕ} (hN : ∀ i < n, i ∈ N) :
    T.addTBB U N ⊢ ∼(T.standardProvability^[n] ⊥) := by
  induction n with
  | zero => simp only [Function.iterate_zero, id]; cl_prover
  | succ n ih =>
    have h : T.addTBB U N ⊢ T.standardProvability^[n + 1] ⊥ 🡒 T.standardProvability^[n] ⊥ :=
      by_axm <| Set.mem_union_right U ⟨n, hN n n.lt_add_one, interpret_TBB _ _ n⟩
    have ih := ih fun i hi ↦ hN i (hi.trans n.lt_add_one)
    cl_prover [h, ih]

end FirstOrder.ArithmeticTheory

end FFL
