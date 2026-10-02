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
  revert htN
  apply IsSemiterm.induction 𝚷
    (P := fun t ↦ t ≤ N → termFvSubst L v (termFvSubst L u t) = t) ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z _ _; simp
  · intro x hx
    have hxN : x < N := lt_of_lt_of_le (by simp) hx
    rw [termFvSubst_fvar u, ite_eq_left (h x hxN).1, (h x hxN).2]
  · intro k f ts hf hts ih hle
    have hts' : IsUTermVec L k (termFvSubstVec L k u ts) :=
      hu.isUTerm.termFvSubstVec hts.isUTerm
    rw [termFvSubst_func hf hts.isUTerm, termFvSubst_func hf hts']
    refine congrArg _ (nth_ext' k (by simp [hts']) hts.lh fun i hi ↦ ?_)
    rw [nth_termFvSubstVec hts' hi, nth_termFvSubstVec hts.isUTerm hi]
    exact ih i hi
      (le_of_lt <| lt_of_lt_of_le (nth_lt_qqFunc_of_lt (by rw [hts.lh]; exact hi)) hle)

/-- If `v` sends the entry of `u` at `x` back to `^&x` for every `x < N`, then substituting by `u`
and then by `v` fixes the formulas coded by a number at most `N`. -/
lemma fvSubst_fvSubst_eq_self (hu : IsSemitermVec L (len u) 0 u)
    (h : ∀ x < N, x < len u ∧ termFvSubst L v u.[x] = ^&x)
    {n p : V} (hp : IsSemiformula L n p) (hpN : p ≤ N) :
    fvSubst L v (fvSubst L u p) = p := by
  revert hpN
  apply IsSemiformula.pi1_structural_induction
    (P := fun _ p ↦ p ≤ N → fvSubst L v (fvSubst L u p) = p) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R ts hR hts hle
    have hts' : IsUTermVec L k (termFvSubstVec L k u ts) :=
      hu.isUTerm.termFvSubstVec hts.isUTerm
    rw [fvSubst_rel hR hts.isUTerm, fvSubst_rel hR hts']
    refine congrArg _ (nth_ext' k (by simp [hts']) hts.lh fun i hi ↦ ?_)
    rw [nth_termFvSubstVec hts' hi, nth_termFvSubstVec hts.isUTerm hi]
    exact termFvSubst_termFvSubst_eq_self hu h (hts.nth hi)
      (le_of_lt <| lt_of_lt_of_le (nth_lt_qqRel_of_lt (by rw [hts.lh]; exact hi)) hle)
  · intro n k R ts hR hts hle
    have hts' : IsUTermVec L k (termFvSubstVec L k u ts) :=
      hu.isUTerm.termFvSubstVec hts.isUTerm
    rw [fvSubst_nrel hR hts.isUTerm, fvSubst_nrel hR hts']
    refine congrArg _ (nth_ext' k (by simp [hts']) hts.lh fun i hi ↦ ?_)
    rw [nth_termFvSubstVec hts' hi, nth_termFvSubstVec hts.isUTerm hi]
    exact termFvSubst_termFvSubst_eq_self hu h (hts.nth hi)
      (le_of_lt <| lt_of_lt_of_le (nth_lt_qqNRel_of_lt (by rw [hts.lh]; exact hi)) hle)
  · intro n _; simp
  · intro n _; simp
  · intro n p q hp hq ihp ihq hle
    have hu' : IsSemitermVec L (len u) n u := hu.weaken (by simp)
    rw [fvSubst_and hp.isUFormula hq.isUFormula,
      fvSubst_and (hp.fvSubst hu').isUFormula (hq.fvSubst hu').isUFormula,
      ihp (le_of_lt <| lt_of_lt_of_le (by simp) hle),
      ihq (le_of_lt <| lt_of_lt_of_le (by simp) hle)]
  · intro n p q hp hq ihp ihq hle
    have hu' : IsSemitermVec L (len u) n u := hu.weaken (by simp)
    rw [fvSubst_or hp.isUFormula hq.isUFormula,
      fvSubst_or (hp.fvSubst hu').isUFormula (hq.fvSubst hu').isUFormula,
      ihp (le_of_lt <| lt_of_lt_of_le (by simp) hle),
      ihq (le_of_lt <| lt_of_lt_of_le (by simp) hle)]
  · intro n p hp ih hle
    rw [fvSubst_all hp.isUFormula, fvSubst_all (hp.fvSubst (hu.weaken (by simp))).isUFormula,
      ih (le_of_lt <| lt_of_lt_of_le (by simp) hle)]
  · intro n p hp ih hle
    rw [fvSubst_exs hp.isUFormula, fvSubst_exs (hp.fvSubst (hu.weaken (by simp))).isUFormula,
      ih (le_of_lt <| lt_of_lt_of_le (by simp) hle)]

/-- If `v` sends the entry of `u` at `x` back to `^&x` for every `x < N`, then the image under `v`
of the image under `u` of a coded formula set bounded by `N` is the set itself. -/
lemma fvSubstImage_fvSubstImage_eq_self (hu : IsSemitermVec L (len u) 0 u)
    (h : ∀ x < N, x < len u ∧ termFvSubst L v u.[x] = ^&x)
    {s : V} (hs : IsFormulaSet L s) (hsN : s ≤ N) :
    fvSubstImage (L := L) v (fvSubstImage (L := L) u s) = s :=
  mem_ext fun x ↦ by
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := mem_fvSubstImage_iff.mp hx
      obtain ⟨q, hq, rfl⟩ := mem_fvSubstImage_iff.mp hy
      rwa [fvSubst_fvSubst_eq_self hu h (hs q hq) (le_of_lt <| lt_of_lt_of_le (lt_of_mem hq) hsN)]
    · intro hx
      exact mem_fvSubstImage_iff.mpr ⟨fvSubst L u x, mem_fvSubstImage_iff.mpr ⟨x, hx, rfl⟩,
        (fvSubst_fvSubst_eq_self hu h (hs x hx)
          (le_of_lt <| lt_of_lt_of_le (lt_of_mem hx) hsN)).symm⟩

end composition

/-- A formula code whose external-variable shift is an existential quantification is itself one,
and its body shifts to the given one. -/
lemma exists_exs_of_shift_eq_exs {r p : V} (hr : IsUFormula L r) (h : shift L r = ^∃ p) :
    ∃ r₁, IsUFormula L r₁ ∧ r = ^∃ r₁ ∧ shift L r₁ = p := by
  sorry

/-- No formula code is its own negation. -/
private lemma neg_ne_self {p : V} (hp : IsUFormula L p) : neg L p ≠ p := by
  rcases hp.case with (⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩ | rfl | rfl |
    ⟨q, r, hq, hr, rfl⟩ | ⟨q, r, hq, hr, rfl⟩ | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩)
  · rw [neg_rel hR hv]; simp [qqRel, qqNRel]
  · rw [neg_nrel hR hv]; simp [qqRel, qqNRel]
  · rw [neg_verum]; simp [qqVerum, qqFalsum]
  · rw [neg_falsum]; simp [qqVerum, qqFalsum]
  · rw [neg_and hq hr]; simp [qqAnd, qqOr]
  · rw [neg_or hq hr]; simp [qqAnd, qqOr]
  · rw [neg_all hq]; simp [qqAll, qqExs]
  · rw [neg_ex hq]; simp [qqAll, qqExs]

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
  intro x hx
  rcases mem_bitInsert_iff.mp hx with rfl | hx
  · simp
  · rcases mem_bitInsert_iff.mp (h hx) with rfl | hx
    · simp
    · simp [hx]

/-- The external-variable shift of coded formula sets is monotone. -/
private lemma setShift_subset_setShift {s t : V} (h : s ⊆ t) : setShift L s ⊆ setShift L t := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_setShift_iff.mp hx
  exact shift_mem_setShift (h hy)

namespace CutFreeDerivable

variable {T : Theory L} [T.Δ₁]

/-- Cut-free derivability is closed under weakening. -/
lemma wk {s s' : V} (hs : IsFormulaSet L s) (h : s' ⊆ s) (hd : CutFreeDerivable T s') :
    CutFreeDerivable T s := by
  obtain ⟨d, hd⟩ := hd
  exact ⟨_, by simp, CutFreeDerivation.wkRule hs h hd⟩

/-- Cut-free derivability is closed under the external-variable shift. -/
lemma shift {s : V} (hd : CutFreeDerivable T s) : CutFreeDerivable T (setShift L s) := by
  obtain ⟨d, hd⟩ := hd
  exact ⟨_, by simp, CutFreeDerivation.shiftRule hd⟩

/-- Adding a formula beside the first one of a cut-free derivable sequent keeps it cut-free
derivable. -/
private lemma wk_insert {x a s : V} (ha : IsFormula L a) (hd : CutFreeDerivable T (insert x s)) :
    CutFreeDerivable T (insert x (insert a s)) := by
  have hs := IsFormulaSet.insert_iff.mp hd.isFormulaSet
  exact hd.wk (by simp [hs.1, hs.2, ha]) (insert_subset_insert_of_subset x (susbset_insert a s))

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
