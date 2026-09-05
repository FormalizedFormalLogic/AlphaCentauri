module

public import Foundation.FirstOrder.Basic.Semantics.Semantics

/-!
# Substitution against a rewriting

Commutation and congruence lemmas for substitutions and rewritings.
-/

@[expose] public section

namespace LO.FirstOrder.Rew

variable {L : Language} {ξ : Type*} {n : ℕ}

lemma app_substs (ω : Rew L ξ 0 ξ 0) (φ : Semiformula L ξ 1) (t : Semiterm L ξ 0) :
    ω ▹ (φ/[t]) = (ω.q ▹ φ)/[ω t] := by
  show ω ▹ (Rew.subst ![t] ▹ φ) = Rew.subst ![ω t] ▹ (ω.q ▹ φ)
  have h : ω.comp (Rew.subst ![t]) = (Rew.subst ![ω t]).comp ω.q := by
    ext x
    · cases x using Fin.cases with
      | zero => simp [Rew.comp_app]
      | succ i => exact i.elim0
    · simp [Rew.comp_app]
  rw [← TransitiveRewriting.comp_app, ← TransitiveRewriting.comp_app, h]

lemma subst_comp_subst_q (w : Fin n → Semiterm L ξ 0) (s : Semiterm L ξ 0) :
    (Rew.subst ![s]).comp (Rew.subst w).q = Rew.subst (s :> w) := by
  ext x
  · cases x using Fin.cases with
    | zero => simp [Rew.comp_app]
    | succ i => simp [Rew.comp_app]
  · simp [Rew.comp_app]

lemma subst_q_app (w : Fin n → Semiterm L ξ 0) (s : Semiterm L ξ 0)
    (φ : Semiformula L ξ (n + 1)) : ((Rew.subst w).q ▹ φ)/[s] = Rew.subst (s :> w) ▹ φ := by
  show Rew.subst ![s] ▹ ((Rew.subst w).q ▹ φ) = Rew.subst (s :> w) ▹ φ
  rw [← TransitiveRewriting.comp_app, subst_comp_subst_q]

lemma val_subst_congr {M : Type*} [Structure L M] {ε : ξ → M} {w w' : Fin n → Semiterm L ξ 0}
    (h : ∀ i, Semiterm.val ![] ε (w i) = Semiterm.val ![] ε (w' i)) (t : Semiterm L ξ n) :
    Semiterm.val ![] ε (Rew.subst w t) = Semiterm.val ![] ε (Rew.subst w' t) := by
  simp only [Semiterm.val_substs]
  exact congrArg (Semiterm.val · ε t) (funext fun i => h i)

end LO.FirstOrder.Rew
