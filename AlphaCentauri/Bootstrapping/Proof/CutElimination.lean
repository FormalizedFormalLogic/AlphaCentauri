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

/-- Cut on a conjunction, given cut on every formula of smaller complexity. -/
private lemma cut_and {c q r s : V}
    (ih : ∀ p s : V, formulaComplexity L p < c → CutFreeDerivable (∅ : Theory L) (insert p s) →
      CutFreeDerivable (∅ : Theory L) (insert (neg L p) s) → CutFreeDerivable (∅ : Theory L) s)
    (hc : formulaComplexity L (q ^⋏ r) ≤ c)
    (h₁ : CutFreeDerivable (∅ : Theory L) (insert (q ^⋏ r) s))
    (h₂ : CutFreeDerivable (∅ : Theory L) (insert (neg L (q ^⋏ r)) s)) :
    CutFreeDerivable (∅ : Theory L) s := by
  have hqr : IsFormula L q ∧ IsFormula L r := by
    simpa using (IsFormulaSet.insert_iff.mp h₁.isFormulaSet).1
  rw [neg_and hqr.1.isUFormula hqr.2.isUFormula] at h₂
  rw [formulaComplexity_and hqr.1.isUFormula hqr.2.isUFormula] at hc
  obtain ⟨d₁, hd₁⟩ := h₁
  obtain ⟨d₂, hd₂⟩ := h₂
  obtain ⟨eq, heq, -⟩ := CutFreeDerivation.inversion_and (Or.inl rfl) hd₁
  obtain ⟨er, her, -⟩ := CutFreeDerivation.inversion_and (Or.inr rfl) hd₁
  obtain ⟨e, he, -⟩ := CutFreeDerivation.inversion_or hd₂
  have h₃ : CutFreeDerivable (∅ : Theory L) (insert (neg L q) s) :=
    ih r _ (lt_of_lt_of_le (lt_max_succ_right _ _) hc)
      (CutFreeDerivable.wk_insert hqr.1.neg ⟨er, her⟩) (by rw [insert_comm]; exact ⟨e, he⟩)
  exact ih q s (lt_of_lt_of_le (lt_max_succ_left _ _) hc) ⟨eq, heq⟩ h₃

section

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺2]

/-- For every `N` there is a closed term vector `w` such that `w` and `freshVec N` undo each
other on the free variables below `N`. -/
private lemma exists_inverse_freshVec (N : V) : ∃ w : V, IsSemitermVec L (len w) 0 w ∧
    (∀ x < N, x < len (freshVec N : V) ∧ termFvSubst L w (freshVec N : V).[x] = ^&x) ∧
    (∀ x < N, x < len w ∧ termFvSubst L (freshVec N) w.[x] = ^&x) := by
  obtain ⟨ι, hιl, hι⟩ := sigmaOne_skolem_vec (R := fun x y : V ↦ y = ^&x) (by definability)
    (l := N) (fun x _ ↦ ⟨_, rfl⟩)
  have hιc : IsSemitermVec L (len ι) 0 ι := IsSemitermVec.iff.mpr ⟨rfl, fun i hi ↦ by
    rw [hι i (by rwa [hιl] at hi)]
    simp⟩
  refine ⟨^&N ∷ ι, by simp [hιc], ?_, ?_⟩
  · intro x hx
    exact ⟨lt_trans hx (by simp), by simp [nth_freshVec_of_lt hx, hιl, hx, hι x hx]⟩
  · intro x hx
    rcases zero_or_succ x with rfl | ⟨x, rfl⟩
    · simp
    · have hx' : x < N := lt_trans (by simp) hx
      have hx₁ : x < N + 1 := lt_trans hx' (by simp)
      exact ⟨by simp [hιl, hx'], by simp [hι x hx', hx₁, nth_freshVec_of_lt hx']⟩

/-- A cut on the shift of `p` beside a set `s` covering the shift of a sequent `Δ` containing `p`
reduces to cuts on `p` itself beside sets covering `Δ`. -/
private lemma cut_of_setShift_subset {Δ p s : V} (hΔ : IsFormulaSet L Δ) (hp : p ∈ Δ)
    (hsub : setShift L Δ ⊆ insert (shift L p) s)
    (he : CutFreeDerivable (∅ : Theory L) (insert (neg L (shift L p)) s))
    (ih : ∀ s' e' : V, Δ ⊆ insert p s' →
      CutFreeDerivationOf (∅ : Theory L) e' (insert (neg L p) s') →
      CutFreeDerivable (∅ : Theory L) s') :
    CutFreeDerivable (∅ : Theory L) s := by
  have hsF : IsFormulaSet L s := (IsFormulaSet.insert_iff.mp he.isFormulaSet).2
  have hpF : IsFormula L p := hΔ p hp
  obtain ⟨N, hsN, hΔN, hpN⟩ : ∃ N : V, s ≤ N ∧ Δ ≤ N ∧ neg L p ≤ N :=
    ⟨s + Δ + neg L p, by simp [add_assoc], by simp [add_comm s Δ, add_assoc], by simp⟩
  obtain ⟨w, hw, hvw, hwv⟩ := exists_inverse_freshVec (L := L) N
  have hback : ∀ q, IsFormula L q → q ≤ N → fvSubst L w (shift L q) = q := by
    intro q hq hqN
    rw [← fvSubst_eq_shift (by simp) (fun x hx ↦ nth_freshVec_of_lt hx) hq hqN]
    exact fvSubst_fvSubst_eq_self (isSemitermVec_freshVec N) hvw hq hqN
  have h₁ := CutFreeDerivable.rewrite hw he
  rw [fvSubstImage_insert, ← shift_neg hpF, hback _ hpF.neg hpN] at h₁
  have h₂ : Δ ⊆ insert p (fvSubstImage (L := L) w s) := by
    intro x hx
    have hxN : x ≤ N := le_trans (le_of_lt (lt_of_mem hx)) hΔN
    rcases mem_bitInsert_iff.mp (hsub (shift_mem_setShift hx)) with h | h
    · rw [shift_inj (hΔ x hx).isUFormula hpF.isUFormula h]
      simp
    · exact mem_bitInsert_iff.mpr <| Or.inr <|
        mem_fvSubstImage_iff.mpr ⟨_, h, (hback x (hΔ x hx) hxN).symm⟩
  obtain ⟨e, he⟩ := h₁
  have h₃ := CutFreeDerivable.rewrite (isSemitermVec_freshVec N) (ih _ e h₂ he)
  rwa [fvSubstImage_fvSubstImage_eq_self hw hwv hsF hsN] at h₃

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
