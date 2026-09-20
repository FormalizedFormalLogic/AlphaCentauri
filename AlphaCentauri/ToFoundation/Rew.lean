module

public import Foundation.FirstOrder.Tarski.Basic

/-!
# Substitution against a rewriting

Commutation and congruence lemmas for substitutions and rewritings.
-/

@[expose] public section

namespace FFL.FirstOrder.Rew

variable {L : Language} {ξ : Type*} {n : ℕ}

lemma app_substs (ω : Rew L ξ 0 ξ 0) (φ : Semiformula L ξ 1) (t : Semiterm L ξ 0) :
    ω ▹ (φ/[t]) = (ω.q ▹ φ)/[ω t] := by
  change ω ▹ (Rew.subst ![t] ▹ φ) = Rew.subst ![ω t] ▹ (ω.q ▹ φ)
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
  change Rew.subst ![s] ▹ ((Rew.subst w).q ▹ φ) = Rew.subst (s :> w) ▹ φ
  rw [← TransitiveRewriting.comp_app, subst_comp_subst_q]

lemma val_subst_congr {M : Type*} [Tarski.Structure L M] {ε : ξ → M} {w w' : Fin n → Semiterm L ξ 0}
    (h : ∀ i, Semiterm.val ![] ε (w i) = Semiterm.val ![] ε (w' i)) (t : Semiterm L ξ n) :
    Semiterm.val ![] ε (Rew.subst w t) = Semiterm.val ![] ε (Rew.subst w' t) := by
  simp only [Semiterm.val_substs]
  exact congrArg (Semiterm.val · ε t) (funext fun i => h i)

lemma rewrite_subst_shift_eq (f : ℕ → SyntacticTerm L) (t : SyntacticTerm L)
    (φ : Semiformula L ℕ 1) :
    Rew.rewrite (&0 :>ₙ fun x ↦ Rew.shift (f x)) ▹ ((Rewriting.shift φ)/[t]) =
      (Rewriting.shift (Rew.rewrite (Rew.bShift ∘ f) ▹ φ))/[
        Rew.rewrite (&0 :>ₙ fun x ↦ Rew.shift (f x)) t] := by
  simpa [← TransitiveRewriting.comp_app] using Rewriting.smul_ext' <| by
    ext x
    · simp [Rew.comp_app]
    · have e : (Rew.shift : SyntacticRew L 1 1) (Rew.bShift (f x)) =
          Rew.bShift (Rew.shift (f x)) := by
        simpa using Rew.q_comp_bShift_app (ω := (Rew.shift : SyntacticRew L 0 0)) (f x)
      simp [Rew.comp_app, e]

lemma subst_subst_eq {m : ℕ} (v : Fin n → Semiterm L ξ m) (φ : Semiformula L ξ 1)
    (t : Semiterm L ξ n) : Rew.subst v ▹ (φ/[t]) = φ/[Rew.subst v t] := by
  simpa [← TransitiveRewriting.comp_app] using Rewriting.smul_ext' <| by
    ext x
    · cases x using Fin.cases with
      | zero => simp [Rew.comp_app]
      | succ i => exact i.elim0
    · simp [Rew.comp_app]

@[simp] lemma subst_bShift_eq (v : Fin 1 → Semiterm L ξ 1) (t : Semiterm L ξ 0) :
    Rew.subst v (Rew.bShift t) = Rew.bShift t := by
  have e : (Rew.subst v).comp (Rew.bShift : Rew L ξ 0 ξ 1) = Rew.bShift := by
    ext x
    · exact x.elim0
    · simp [Rew.comp_app]
  simpa [Rew.comp_app] using Rew.ext' e t

lemma shift_subst_eq (φ : Semiformula L ℕ 1) (t : SyntacticSemiterm L n) :
    Rew.shift ▹ (φ/[t]) = (Rew.shift ▹ φ)/[Rew.shift t] := by
  simpa [← TransitiveRewriting.comp_app] using Rewriting.smul_ext' <| by
    ext x
    · cases x using Fin.cases with
      | zero => simp [Rew.comp_app]
      | succ i => exact i.elim0
    · simp [Rew.comp_app]

end FFL.FirstOrder.Rew

namespace FFL.FirstOrder.Semiformula

variable {L : Language} {m : ℕ}

/-- Substituting a variable that the formula avoids, and then renaming it to the new bound
variable, is `Rewriting.free`. -/
lemma rewriteMap_subst_eq_free (φ : Semiformula L ℕ 1) (h : ¬φ.FVar? m) :
    (@Rew.rewriteMap L ℕ ℕ 0 fun x ↦ if x = m then 0 else x + 1) ▹ (φ/[&m]) =
      Rewriting.free φ := by
  simp only [← TransitiveRewriting.comp_app]
  exact Semiformula.rew_eq_of_funEqOn (by simp [Rew.comp_app])
    fun x hx ↦ by simp [Rew.comp_app, ne_of_mem_of_not_mem hx h]

/-- Renaming a variable that the formula avoids to the new bound variable shifts the formula. -/
lemma rewriteMap_eq_shift {n} (φ : Semiformula L ℕ n) (h : ¬φ.FVar? m) :
    (@Rew.rewriteMap L ℕ ℕ n fun x ↦ if x = m then 0 else x + 1) ▹ φ = Rewriting.shift φ := by
  have e : (@Rew.rewriteMap L ℕ ℕ n fun x ↦ if x = m then 0 else x + 1) ▹ φ =
      (Rew.shift : SyntacticRew L n n) ▹ φ :=
    Semiformula.rew_eq_of_funEqOn (by simp) (by
      intro x hx
      simp [ne_of_mem_of_not_mem hx h])
  simpa [Rewriting.shift] using e

/-- Renaming a variable that none of the formulas mentions shifts the multiset. -/
lemma map_rewriteMap_eq_shifts (Γ : Multiset (Semiformula L ℕ 0))
    (h : ∀ φ ∈ Γ, ¬φ.FVar? m) :
    Γ.map (fun φ ↦ (@Rew.rewriteMap L ℕ ℕ 0 fun x ↦ if x = m then 0 else x + 1) ▹ φ) = Γ⁺ :=
  Multiset.map_congr rfl fun φ hφ ↦ rewriteMap_eq_shift φ (h φ hφ)

end FFL.FirstOrder.Semiformula
