module

public import AlphaCentauri.Bootstrapping.Proof.CutFreeRewrite

/-!
# Cut elimination for the internal calculus

This module proves that the cut rule is admissible in the cut-free fragment of Foundation's
internal one-sided calculus over the empty theory, and hence that every internal derivation over
the empty theory has a cut-free counterpart with the same end-sequent. Both hold in every model of
`𝗜𝚺⁺2`.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL.FirstOrder.Bounding (HierarchySymbol)

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

open PeanoMinus ISigma0 ISigma1

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

section composition

variable {N u v : V}

/-- If `v` sends the entry of `u` at `x` back to `^&x` for every `x < N`, then substituting by `u`
and then by `v` fixes the terms coded by a number at most `N`. -/
lemma termFvSubst_termFvSubst_eq_self (hu : IsSemitermVec L (len u) 0 u)
    (h : ∀ x < N, x < len u ∧ termFvSubst L v u.[x] = ^&x)
    {n t : V} (ht : IsSemiterm L n t) (htN : t ≤ N) :
    termFvSubst L v (termFvSubst L u t) = t := by
  sorry

/-- If `v` sends the entry of `u` at `x` back to `^&x` for every `x < N`, then substituting by `u`
and then by `v` fixes the formulas coded by a number at most `N`. -/
lemma fvSubst_fvSubst_eq_self (hu : IsSemitermVec L (len u) 0 u)
    (h : ∀ x < N, x < len u ∧ termFvSubst L v u.[x] = ^&x)
    {n p : V} (hp : IsSemiformula L n p) (hpN : p ≤ N) :
    fvSubst L v (fvSubst L u p) = p := by
  sorry

/-- If `v` sends the entry of `u` at `x` back to `^&x` for every `x < N`, then the image under `v`
of the image under `u` of a coded formula set bounded by `N` is the set itself. -/
lemma fvSubstImage_fvSubstImage_eq_self (hu : IsSemitermVec L (len u) 0 u)
    (h : ∀ x < N, x < len u ∧ termFvSubst L v u.[x] = ^&x)
    {s : V} (hs : IsFormulaSet L s) (hsN : s ≤ N) :
    fvSubstImage (L := L) v (fvSubstImage (L := L) u s) = s := by
  sorry

end composition

/-- A formula code whose external-variable shift is an existential quantification is itself one,
and its body shifts to the given one. -/
lemma exists_exs_of_shift_eq_exs {r p : V} (hr : IsUFormula L r) (h : shift L r = ^∃ p) :
    ∃ r₁, IsUFormula L r₁ ∧ r = ^∃ r₁ ∧ shift L r₁ = p := by
  sorry

/-- No formula code is its own negation. -/
private lemma neg_ne_self {p : V} (hp : IsUFormula L p) : neg L p ≠ p := by
  sorry

/-- Adding two codes to a coded set does not depend on their order. -/
private lemma insert_comm (x y s : V) : insert x (insert y s) = insert y (insert x s) :=
  mem_ext fun z ↦ by
    simp only [mem_bitInsert_iff]
    tauto

/-- A member of `insert y s` other than `y` is a member of `s`. -/
private lemma mem_of_mem_insert_of_ne {x y s : V} (h : x ∈ insert y s) (hne : x ≠ y) : x ∈ s := by
  rcases mem_bitInsert_iff.mp h with rfl | h
  · exact absurd rfl hne
  · exact h

/-- Adding a code on both sides preserves a sequent being covered by a formula beside a set. -/
private lemma insert_subset_insert_insert {a p Γ s : V} (h : Γ ⊆ insert p s) :
    insert a Γ ⊆ insert p (insert a s) := by
  sorry

/-- The external-variable shift of coded formula sets is monotone. -/
private lemma setShift_subset_setShift {s t : V} (h : s ⊆ t) : setShift L s ⊆ setShift L t := by
  sorry

namespace CutFreeDerivable

variable {T : Theory L} [T.Δ₁]

/-- Cut-free derivability is closed under weakening. -/
lemma wk {s s' : V} (hs : IsFormulaSet L s) (h : s' ⊆ s) (hd : CutFreeDerivable T s') :
    CutFreeDerivable T s := by
  sorry

/-- Cut-free derivability is closed under the external-variable shift. -/
lemma shift {s : V} (hd : CutFreeDerivable T s) : CutFreeDerivable T (setShift L s) := by
  sorry

/-- Adding a formula beside the first one of a cut-free derivable sequent keeps it cut-free
derivable. -/
private lemma wk_insert {x a s : V} (ha : IsFormula L a) (hd : CutFreeDerivable T (insert x s)) :
    CutFreeDerivable T (insert x (insert a s)) := by
  sorry

end CutFreeDerivable

section

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺2]

/-- A cut on the shift of `p` beside a set `s` covering the shift of a sequent `Δ` containing `p`
reduces to cuts on `p` itself beside sets covering `Δ`. -/
private lemma cut_of_setShift_subset {Δ p s : V} (hΔ : IsFormulaSet L Δ) (hp : p ∈ Δ)
    (hsub : setShift L Δ ⊆ insert (shift L p) s)
    (he : CutFreeDerivable (∅ : Theory L) (insert (neg L (shift L p)) s))
    (ih : ∀ s' e' : V, Δ ⊆ insert p s' →
      CutFreeDerivationOf (∅ : Theory L) e' (insert (neg L p) s') →
      CutFreeDerivable (∅ : Theory L) s') :
    CutFreeDerivable (∅ : Theory L) s := by
  sorry

/-- Cut on a conjunction, given cut on every formula of smaller complexity. -/
private lemma cut_and {c q r s : V}
    (ih : ∀ p s : V, formulaComplexity L p < c → CutFreeDerivable (∅ : Theory L) (insert p s) →
      CutFreeDerivable (∅ : Theory L) (insert (neg L p) s) → CutFreeDerivable (∅ : Theory L) s)
    (hc : formulaComplexity L (q ^⋏ r) ≤ c)
    (h₁ : CutFreeDerivable (∅ : Theory L) (insert (q ^⋏ r) s))
    (h₂ : CutFreeDerivable (∅ : Theory L) (insert (neg L (q ^⋏ r)) s)) :
    CutFreeDerivable (∅ : Theory L) s := by
  sorry

/-- Cut on a formula of complexity zero or on an existential formula of complexity at most `c`,
whose side is covered by the end-sequent of a cut-free derivation code, given cut on every formula
of complexity below `c`. -/
private lemma cut_aux {c : V}
    (ih : ∀ p s : V, formulaComplexity L p < c → CutFreeDerivable (∅ : Theory L) (insert p s) →
      CutFreeDerivable (∅ : Theory L) (insert (neg L p) s) → CutFreeDerivable (∅ : Theory L) s) :
    ∀ d p s e : V, formulaComplexity L p ≤ c →
      (formulaComplexity L p = 0 ∨ ∃ a < p, p = ^∃ a) →
      CutFreeDerivation (∅ : Theory L) d → fstIdx d ⊆ insert p s →
      CutFreeDerivationOf (∅ : Theory L) e (insert (neg L p) s) →
      CutFreeDerivable (∅ : Theory L) s := by
  sorry

/-- Cut on a formula of complexity `c`, for every `c`. -/
private lemma cut_complexity :
    ∀ c p s d₁ d₂ : V, formulaComplexity L p = c →
      CutFreeDerivationOf (∅ : Theory L) d₁ (insert p s) →
      CutFreeDerivationOf (∅ : Theory L) d₂ (insert (neg L p) s) →
      CutFreeDerivable (∅ : Theory L) s := by
  sorry

/-- The cut rule is admissible in the cut-free calculus over the empty theory.
- [Bus98, Lemma 2.4.2.1] -/
theorem CutFreeDerivable.cut {p s : V} (h₁ : CutFreeDerivable (∅ : Theory L) (insert p s))
    (h₂ : CutFreeDerivable (∅ : Theory L) (insert (neg L p) s)) :
    CutFreeDerivable (∅ : Theory L) s := by
  obtain ⟨d₁, hd₁⟩ := h₁
  obtain ⟨d₂, hd₂⟩ := h₂
  exact cut_complexity _ p s d₁ d₂ rfl hd₁ hd₂

/-- Cut elimination: every sequent derivable over the empty theory is cut-free derivable.
- [Bus98, Theorem 2.4.2]
- [AB05, Theorem 152] -/
theorem Derivable.cutFree {s : V} (h : Derivable (∅ : Theory L) s) :
    CutFreeDerivable (∅ : Theory L) s := by
  sorry

end

end FFL.FirstOrder.Arithmetic.Bootstrapping
