module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax

/-!
# Gaps in Foundation's internal syntax

Negation has no fixed point on coded formulas, the shift of free variables is monotone on coded
formula sets, and substitution of closed terms interacts with `qVec`, `fvarVec` and the head of a
vector of closed terms.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

open scoped FFL.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

lemma neg_ne_self {p : V} (hp : IsUFormula L p) : neg L p ≠ p := by
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

lemma setShift_subset_setShift {s t : V} (h : s ⊆ t) : setShift L s ⊆ setShift L t := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_setShift_iff.mp hx
  exact shift_mem_setShift (h hy)

/-- Substituting the bound variables of a closed semiterm is the identity. -/
lemma termSubst_zero {v t : V} (ht : IsSemiterm L 0 t) : termSubst L v t = t := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz
    simp at hz
  · intro x
    simp
  · intro k f ts hf hts ih
    rw [termSubst_func hf hts.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k (by rw [len_termSubstVec hts.isUTerm]) (by simpa using hts.lh)
    intro i hi
    rw [nth_termSubstVec hts.isUTerm hi]
    exact ih i hi

/-- Bound-shifting a closed semiterm is the identity. -/
lemma termBShift_zero {t : V} (ht : IsSemiterm L 0 t) : termBShift L t = t := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz
    simp at hz
  · intro x
    simp
  · intro k f ts hf hts ih
    rw [termBShift_func hf hts.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k (by rw [len_termBShiftVec hts.isUTerm]) (by simpa using hts.lh)
    intro i hi
    rw [nth_termBShiftVec hts.isUTerm hi]
    exact ih i hi

/-- The shift of free variables does not decrease the code of a term. -/
lemma le_termShift {n t : V} (ht : IsSemiterm L n t) : t ≤ termShift L t := by
  apply IsSemiterm.induction 𝚷 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z _
    simp
  · intro x
    rw [termShift_fvar]
    simpa [qqFvar] using pair_le_pair_right 1 (show x ≤ x + 1 by simp)
  · intro k f v hf hv ih
    have hv' : v ≤ termShiftVec L k v := le_of_nth_le_nth (by simp [hv.isUTerm, hv.lh])
      fun i hi ↦ by
        rw [nth_termShiftVec hv.isUTerm (by simpa [hv.lh] using hi)]
        exact ih i (by simpa [hv.lh] using hi)
    rw [termShift_func hf hv.isUTerm]
    simpa [qqFunc] using
      pair_le_pair_right 2 <| pair_le_pair_right k <| pair_le_pair_right f hv'

/-- The shift of free variables does not decrease the code of a formula. -/
lemma le_shift {n p : V} (hp : IsSemiformula L n p) : p ≤ shift L p := by
  apply IsSemiformula.pi1_structural_induction (P := fun _ p ↦ p ≤ shift L p)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R v hR hv
    have hv' : v ≤ termShiftVec L k v := le_of_nth_le_nth (by simp [hv.isUTerm, hv.lh])
      fun i hi ↦ by
        rw [nth_termShiftVec hv.isUTerm (by simpa [hv.lh] using hi)]
        exact le_termShift (hv.nth (by simpa [hv.lh] using hi))
    rw [shift_rel hR hv.isUTerm]
    simpa [qqRel] using
      pair_le_pair_right 0 <| pair_le_pair_right k <| pair_le_pair_right R hv'
  · intro n k R v hR hv
    have hv' : v ≤ termShiftVec L k v := le_of_nth_le_nth (by simp [hv.isUTerm, hv.lh])
      fun i hi ↦ by
        rw [nth_termShiftVec hv.isUTerm (by simpa [hv.lh] using hi)]
        exact le_termShift (hv.nth (by simpa [hv.lh] using hi))
    rw [shift_nrel hR hv.isUTerm]
    simpa [qqNRel] using
      pair_le_pair_right 1 <| pair_le_pair_right k <| pair_le_pair_right R hv'
  · intro n
    simp
  · intro n
    simp
  · intro n p q hp hq ihp ihq
    rw [shift_and hp.isUFormula hq.isUFormula]
    simpa [qqAnd] using pair_le_pair_right 4 <| pair_le_pair ihp ihq
  · intro n p q hp hq ihp ihq
    rw [shift_or hp.isUFormula hq.isUFormula]
    simpa [qqOr] using pair_le_pair_right 5 <| pair_le_pair ihp ihq
  · intro n p hp ih
    rw [shift_all hp.isUFormula]
    simpa [qqAll] using pair_le_pair_right 6 ih
  · intro n p hp ih
    rw [shift_exs hp.isUFormula]
    simpa [qqExs] using pair_le_pair_right 7 ih

lemma isSemitermVec_fvarVec (m n : V) : IsSemitermVec ℒₒᵣ m n (fvarVec m) :=
  IsSemitermVec.iff.mpr ⟨len_fvarVec m, fun i hi ↦ by simp [nth_fvarVec m i hi]⟩

lemma nth_qVec_succ {k w j : V} (hw : IsUTermVec ℒₒᵣ k w) (hj : j < k) :
    (qVec ℒₒᵣ w).[j + 1] = termBShift ℒₒᵣ w.[j] := by
  rw [qVec, ← hw.lh, nth_adjoin_succ, nth_termBShiftVec hw hj]

lemma nth_qVec_qVec_fvarVec {m i : V} (hi : i < m) :
    (qVec ℒₒᵣ (qVec ℒₒᵣ (fvarVec m))).[i + 1 + 1] = ^&i := by
  have h₁ : IsUTermVec ℒₒᵣ m (fvarVec m) := (isSemitermVec_fvarVec m 0).isUTerm
  have h₂ : IsUTermVec ℒₒᵣ (m + 1) (qVec ℒₒᵣ (fvarVec m)) :=
    (isSemitermVec_fvarVec m 0).qVec.isUTerm
  rw [nth_qVec_succ h₂ (by simpa using hi), nth_qVec_succ h₁ hi, nth_fvarVec m i hi]
  simp

lemma subst_subst_qVec_fvarVec {m Z t : V} (hZ : IsSemiformula ℒₒᵣ (m + 1) Z)
    (ht : IsSemiterm ℒₒᵣ 2 t) :
    subst ℒₒᵣ ?[t] (subst ℒₒᵣ (qVec ℒₒᵣ (fvarVec m)) Z) = subst ℒₒᵣ (t ∷ fvarVec m) Z := by
  have h₁ : IsSemitermVec ℒₒᵣ 1 2 (?[t] : V) := by simp [ht]
  have h₂ : IsSemitermVec ℒₒᵣ (m + 1) 1 (qVec ℒₒᵣ (fvarVec m)) := by
    simpa using (isSemitermVec_fvarVec m 0).qVec
  rw [substs_substs hZ h₁ h₂]
  congr 1
  have h₃ : IsUTermVec ℒₒᵣ m (fvarVec m) := (isSemitermVec_fvarVec m 0).isUTerm
  apply nth_ext' (m + 1) (by simp [(h₁.termSubstVec h₂).lh])
    (by simp)
  intro i hi
  rw [nth_termSubstVec h₂.isUTerm hi]
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simp [qVec]
  · have hi : i < m := by simpa using hi
    simp [nth_qVec_succ h₃ hi, nth_fvarVec m i hi]

lemma isSemitermVec_cons_cons {m a b w' : V} (ha : IsSemiterm ℒₒᵣ 0 a)
    (hb : IsSemiterm ℒₒᵣ 0 b) (hw' : IsSemitermVec ℒₒᵣ m 0 w') :
    IsSemitermVec ℒₒᵣ (m + 2) 0 (a ∷ b ∷ w') := by
  rw [← one_add_one_eq_two, ← add_assoc]
  simp [ha, hb, hw']

lemma IsSemitermVec.exists_cons {m w : V} (hw : IsSemitermVec ℒₒᵣ (m + 1) 0 w) :
    ∃ w₀ w', w = w₀ ∷ w' ∧ IsSemiterm ℒₒᵣ 0 w₀ ∧ IsSemitermVec ℒₒᵣ m 0 w' := by
  rcases nil_or_adjoin w with rfl | ⟨w₀, w', rfl⟩
  · simpa using hw.lh
  · exact ⟨w₀, w', rfl, IsSemitermVec.cons_iff.mp hw⟩

lemma substs1_subst_qVec {j w q t : V} (hw : IsSemitermVec L j 0 w)
    (hq : IsSemiformula L (j + 1) q) (ht : IsSemiterm L 0 t) :
    substs1 L t (subst L (qVec L w) q) = subst L (t ∷ w) q := by
  have h₁ : IsSemitermVec L 1 0 (?[t] : V) := by simp [ht]
  have h₂ : IsSemitermVec L (j + 1) 1 (qVec L w) := by simpa using hw.qVec
  rw [substs1, substs_substs hq h₁ h₂]
  congr 1
  apply nth_ext' (j + 1) (by simp [(h₁.termSubstVec h₂).lh]) (by simp [hw.lh])
  intro i hi
  rw [nth_termSubstVec h₂.isUTerm hi]
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simp [qVec]
  · have hi : i < j := by simpa using hi
    rw [qVec, nth_adjoin_succ, hw.lh, nth_termBShiftVec hw.isUTerm hi,
      termBShift_zero (hw.nth hi), termSubst_eq_self (hw.nth hi) (by simp)]
    simp

end FFL.FirstOrder.Arithmetic.Bootstrapping
