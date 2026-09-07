module

public import Foundation.FirstOrder.Basic.Semantics.Semantics

/-!
# Evaluation after exchanging the two leading bound variables

Companion of Foundation's `Semiformula.eval_insert1` and `Semiformula.eval_insert2`.
-/

@[expose] public section

namespace FFL.FirstOrder.Semiformula

variable {L : Language} {ξ : Type*} {M : Type*} [Structure L M] {f : ξ → M}

/-- Evaluating a formula whose two leading bound variables have been exchanged. -/
lemma eval_swap01 {n} (φ : Semiformula L ξ (n + 2)) (u w : M) (e : Fin n → M) :
    Eval (u :> w :> e) f (φ ⇜ (#1 :> #0 :> (#·.succ.succ))) ↔ Eval (w :> u :> e) f φ := by
  simp only [eval_substs, Function.comp_def]
  exact Iff.of_eq (congrArg (fun c ↦ Eval c f φ)
    (Fin.funext_two (by simp) (by simp) fun i ↦ by simp))

end FFL.FirstOrder.Semiformula
