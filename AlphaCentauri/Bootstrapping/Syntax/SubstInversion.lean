module

public import AlphaCentauri.Bootstrapping.Syntax.Iteration
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Hierarchy

/-!
# Recovering a formula from a substitution instance

A substitution instance `subst w p` of a coded formula `p` has the same outermost connective as
`p`. A substitution instance of a formula is $\Delta_0$, or prenex of a class, only if the formula
itself is.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## The outermost connective -/

section connective

variable {L : Language} [L.Encodable] [L.LORDefinable] {w p : V}

lemma exists_eq_or_of_subst_eq (hp : IsUFormula L p) {q₁ q₂ : V}
    (h : subst L w p = q₁ ^⋎ q₂) :
    ∃ p₁ p₂, p = p₁ ^⋎ p₂ ∧ subst L w p₁ = q₁ ∧ subst L w p₂ = q₂ := by
  rcases hp.case with (⟨k', R', v', hR, hv, rfl⟩ | ⟨k', R', v', hR, hv, rfl⟩ | rfl | rfl |
    ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, hp₁, rfl⟩ | ⟨p₁, hp₁, rfl⟩)
  case inr.inr.inr.inr.inr.inl =>
    rw [substs_or hp₁ hp₂, qqOr_inj] at h
    exact ⟨p₁, p₂, rfl, h⟩
  all_goals
    simp_all only [substs_rel, substs_nrel, substs_verum, substs_falsum, substs_and,
      substs_all, substs_ex]
    simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs] at h

lemma exists_eq_and_of_subst_eq (hp : IsUFormula L p) {q₁ q₂ : V}
    (h : subst L w p = q₁ ^⋏ q₂) :
    ∃ p₁ p₂, p = p₁ ^⋏ p₂ ∧ subst L w p₁ = q₁ ∧ subst L w p₂ = q₂ := by
  rcases hp.case with (⟨k', R', v', hR, hv, rfl⟩ | ⟨k', R', v', hR, hv, rfl⟩ | rfl | rfl |
    ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, hp₁, rfl⟩ | ⟨p₁, hp₁, rfl⟩)
  case inr.inr.inr.inr.inl =>
    rw [substs_and hp₁ hp₂, qqAnd_inj] at h
    exact ⟨p₁, p₂, rfl, h⟩
  all_goals
    simp_all only [substs_rel, substs_nrel, substs_verum, substs_falsum, substs_or,
      substs_all, substs_ex]
    simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs] at h

lemma exists_eq_all_of_subst_eq (hp : IsUFormula L p) {q : V} (h : subst L w p = ^∀ q) :
    ∃ p₁, p = ^∀ p₁ ∧ subst L (qVec L w) p₁ = q := by
  rcases hp.case with (⟨k', R', v', hR, hv, rfl⟩ | ⟨k', R', v', hR, hv, rfl⟩ | rfl | rfl |
    ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, hp₁, rfl⟩ | ⟨p₁, hp₁, rfl⟩)
  case inr.inr.inr.inr.inr.inr.inl =>
    rw [substs_all hp₁, qqAll_inj] at h
    exact ⟨p₁, rfl, h⟩
  all_goals
    simp_all only [substs_rel, substs_nrel, substs_verum, substs_falsum, substs_and,
      substs_or, substs_ex]
    simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs] at h

lemma exists_eq_exs_of_subst_eq (hp : IsUFormula L p) {q : V} (h : subst L w p = ^∃ q) :
    ∃ p₁, p = ^∃ p₁ ∧ subst L (qVec L w) p₁ = q := by
  rcases hp.case with (⟨k', R', v', hR, hv, rfl⟩ | ⟨k', R', v', hR, hv, rfl⟩ | rfl | rfl |
    ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, hp₁, rfl⟩ | ⟨p₁, hp₁, rfl⟩)
  case inr.inr.inr.inr.inr.inr.inr =>
    rw [substs_ex hp₁, qqExs_inj] at h
    exact ⟨p₁, rfl, h⟩
  all_goals
    simp_all only [substs_rel, substs_nrel, substs_verum, substs_falsum, substs_and,
      substs_or, substs_all]
    simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs] at h

lemma exists_eq_rel_of_subst_eq (hp : IsUFormula L p) {k R v : V}
    (h : subst L w p = ^rel k R v) :
    ∃ v', IsUTermVec L k v' ∧ p = ^rel k R v' ∧ termSubstVec L k w v' = v := by
  rcases hp.case with (⟨k', R', v', hR, hv, rfl⟩ | ⟨k', R', v', hR, hv, rfl⟩ | rfl | rfl |
    ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, hp₁, rfl⟩ | ⟨p₁, hp₁, rfl⟩)
  case inl =>
    rw [substs_rel hR hv, qqRel_inj] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨v', hv, rfl, rfl⟩
  all_goals
    simp_all only [substs_nrel, substs_verum, substs_falsum, substs_and, substs_or,
      substs_all, substs_ex]
    simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs] at h

lemma exists_eq_nrel_of_subst_eq (hp : IsUFormula L p) {k R v : V}
    (h : subst L w p = ^nrel k R v) :
    ∃ v', IsUTermVec L k v' ∧ p = ^nrel k R v' ∧ termSubstVec L k w v' = v := by
  rcases hp.case with (⟨k', R', v', hR, hv, rfl⟩ | ⟨k', R', v', hR, hv, rfl⟩ | rfl | rfl |
    ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, hp₁, rfl⟩ | ⟨p₁, hp₁, rfl⟩)
  case inr.inl =>
    rw [substs_nrel hR hv, qqNRel_inj] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨v', hv, rfl, rfl⟩
  all_goals
    simp_all only [substs_rel, substs_verum, substs_falsum, substs_and, substs_or,
      substs_all, substs_ex]
    simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs] at h

end connective

/-! ## Terms -/

section term

variable {L : Language} [L.Encodable] [L.LORDefinable]

lemma termBShift_ne_bvar_zero {t : V} (ht : IsUTerm L t) : termBShift L t ≠ ^#0 := by
  rcases ht.case with (⟨z, rfl⟩ | ⟨x, rfl⟩ | ⟨k, f, v, hf, hv, rfl⟩)
  · simp
  · rw [termBShift_fvar]
    simp [qqBvar, qqFvar]
  · rw [termBShift_func hf hv]
    simp [qqBvar, qqFunc]

lemma eq_bvar_zero_of_termSubst_qVec_eq {n m w t : V} (hw : IsSemitermVec L n m w)
    (ht : IsSemiterm L (n + 1) t) (h : termSubst L (qVec L w) t = ^#0) : t = ^#0 := by
  rcases ht.case with (⟨z, hz, rfl⟩ | ⟨x, rfl⟩ | ⟨k, f, v, hf, hv, rfl⟩)
  · rcases zero_or_succ z with rfl | ⟨z, rfl⟩
    · rfl
    · have hz : z < len w := by simpa [hw.lh] using hz
      rw [termSubst_bvar, qVec, nth_adjoin_succ, nth_termBShiftVec (hw.lh ▸ hw.isUTerm) hz] at h
      exact absurd h (termBShift_ne_bvar_zero (hw.nth (hw.lh ▸ hz)).isUTerm)
  · rw [termSubst_fvar] at h
    simp [qqFvar, qqBvar] at h
  · rw [termSubst_func hf hv.isUTerm] at h
    simp [qqFunc, qqBvar] at h

/-- If the instance of `t` by `qVec L w` is a term with its bound variables shifted by one, so is
`t`. -/
lemma exists_eq_termBShift_of_termSubst_qVec_eq {n w t u : V} (ht : IsSemiterm L (n + 1) t)
    (hu : IsUTerm L u) (h : termSubst L (qVec L w) t = termBShift L u) :
    ∃ t', IsUTerm L t' ∧ t = termBShift L t' := by
  have hρ : IsSemitermVec L (n + 1) n (^&0 ∷ bvarVec 0 n) :=
    IsSemitermVec.cons_iff.mpr ⟨by simp, IsSemitermVec.bvarVec (by simp)⟩
  suffices ∀ t, IsSemiterm L (n + 1) t → ∀ u, IsUTerm L u →
      termSubst L (qVec L w) t = termBShift L u →
        t = termBShift L (termSubst L (^&0 ∷ bvarVec 0 n) t) from
    ⟨_, (hρ.termSubst ht).isUTerm, this t ht u hu h⟩
  apply IsSemiterm.induction 𝚷 (P := fun t ↦ ∀ u, IsUTerm L u →
    termSubst L (qVec L w) t = termBShift L u →
      t = termBShift L (termSubst L (^&0 ∷ bvarVec 0 n) t)) (by definability)
  · intro z hz u hu h
    rcases zero_or_succ z with rfl | ⟨z, rfl⟩
    · simp only [termSubst_bvar, qVec, nth_adjoin_zero] at h
      exact absurd h.symm (termBShift_ne_bvar_zero hu)
    · have hz : z < n := by simpa using hz
      simp [nth_bvarVec 0 n z hz]
  · intro x u _ _
    simp
  · intro k f v hf hv ih u hu h
    rw [termSubst_func hf hv.isUTerm] at h
    have hρv := hρ.termSubstVec hv
    rcases hu.case with (⟨z, rfl⟩ | ⟨x, rfl⟩ | ⟨k', f', v', hf', hv', rfl⟩)
    · rw [termBShift_bvar] at h
      simp [qqFunc, qqBvar] at h
    · rw [termBShift_fvar] at h
      simp [qqFunc, qqFvar] at h
    rw [termBShift_func hf' hv', qqFunc_inj] at h
    obtain ⟨rfl, rfl, hvv⟩ := h
    rw [termSubst_func hf hv.isUTerm, termBShift_func hf hρv.isUTerm, qqFunc_inj]
    refine ⟨rfl, rfl, nth_ext' k hv.lh (by simp [hρv.isUTerm]) fun i hi ↦ ?_⟩
    rw [nth_termBShiftVec hρv.isUTerm hi, nth_termSubstVec hv.isUTerm hi]
    apply ih i hi v'.[i] (hv'.nth hi)
    simpa [nth_termSubstVec hv.isUTerm hi, nth_termBShiftVec hv' hi] using congrArg (·.[i]) hvv

end term

/-! ## The $\Delta_0$ and prenex classes -/

section hierarchy

lemma IsBounded.of_subst {n m w p : V} (hw : IsSemitermVec ℒₒᵣ n m w)
    (hp : IsSemiformula ℒₒᵣ n p) (h : IsBounded (subst ℒₒᵣ w p)) : IsBounded p := by
  apply IsSemiformula.pi1_structural_induction (P := fun n p ↦ ∀ m w, IsSemitermVec ℒₒᵣ n m w →
    IsBounded (subst ℒₒᵣ w p) → IsBounded p) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp m w hw h
  · definability
  · simp
  · simp
  · simp
  · simp
  · intro n p q hp hq ihp ihq m w hw h
    rw [substs_and hp.isUFormula hq.isUFormula, IsBounded.and_iff] at h
    exact IsBounded.and_iff.mpr ⟨ihp m w hw h.1, ihq m w hw h.2⟩
  · intro n p q hp hq ihp ihq m w hw h
    rw [substs_or hp.isUFormula hq.isUFormula, IsBounded.or_iff] at h
    exact IsBounded.or_iff.mpr ⟨ihp m w hw h.1, ihq m w hw h.2⟩
  · intro n p hp ih m w hw h
    rw [substs_all hp.isUFormula] at h
    obtain ⟨_, q, ⟨u, hu, rfl⟩, hq, he⟩ := IsBounded.of_all h
    have hb := ih (m + 1) (qVec ℒₒᵣ w) hw.qVec (by simp [he, hq, Arithmetic.qqNLT])
    obtain ⟨p₁, p₂, rfl, h₁, -⟩ := exists_eq_or_of_subst_eq hp.isUFormula he
    obtain ⟨hp₁, -⟩ := IsSemiformula.or.mp hp
    obtain ⟨v, hv, rfl, hvv⟩ := exists_eq_nrel_of_subst_eq hp₁.isUFormula h₁
    obtain ⟨a, c, rfl⟩ := eq_doubleton_of_len_eq_two.mp hv.lh.symm
    obtain ⟨ha, hc⟩ : IsSemiterm ℒₒᵣ (n + 1) a ∧ IsSemiterm ℒₒᵣ (n + 1) c := by
      simpa using hp₁
    simp only [termSubstVec_cons₂ ha.isUTerm hc.isUTerm, adjoin_inj] at hvv
    obtain rfl := eq_bvar_zero_of_termSubst_qVec_eq hw ha hvv.1
    obtain ⟨t, ht, rfl⟩ := exists_eq_termBShift_of_termSubst_qVec_eq hc hu hvv.2.1
    exact IsBounded.ball ht (IsBounded.or_iff.mp hb).2
  · intro n p hp ih m w hw h
    rw [substs_ex hp.isUFormula] at h
    obtain ⟨_, q, ⟨u, hu, rfl⟩, hq, he⟩ := IsBounded.of_ex h
    have hb := ih (m + 1) (qVec ℒₒᵣ w) hw.qVec (by simp [he, hq, Arithmetic.qqLT])
    obtain ⟨p₁, p₂, rfl, h₁, -⟩ := exists_eq_and_of_subst_eq hp.isUFormula he
    obtain ⟨hp₁, -⟩ := IsSemiformula.and.mp hp
    obtain ⟨v, hv, rfl, hvv⟩ := exists_eq_rel_of_subst_eq hp₁.isUFormula h₁
    obtain ⟨a, c, rfl⟩ := eq_doubleton_of_len_eq_two.mp hv.lh.symm
    obtain ⟨ha, hc⟩ : IsSemiterm ℒₒᵣ (n + 1) a ∧ IsSemiterm ℒₒᵣ (n + 1) c := by
      simpa using hp₁
    simp only [termSubstVec_cons₂ ha.isUTerm hc.isUTerm, adjoin_inj] at hvv
    obtain rfl := eq_bvar_zero_of_termSubst_qVec_eq hw ha hvv.1
    obtain ⟨t, ht, rfl⟩ := exists_eq_termBShift_of_termSubst_qVec_eq hc hu hvv.2.1
    exact IsBounded.bex ht (IsBounded.and_iff.mp hb).2

lemma IsPrenexHierarchy.of_subst {Γ : Polarity} {s : ℕ} {n m w p : V}
    (hw : IsSemitermVec ℒₒᵣ n m w) (hp : IsSemiformula ℒₒᵣ n p)
    (h : IsPrenexHierarchy Γ s (subst ℒₒᵣ w p)) : IsPrenexHierarchy Γ s p := by
  induction s generalizing Γ n m w p with
  | zero => exact IsBounded.of_subst hw hp h
  | succ s ih =>
    obtain ⟨q, hq, hqs⟩ := h
    cases Γ
    · obtain ⟨p₁, rfl, hp₁⟩ := exists_eq_exs_of_subst_eq hp.isUFormula hq
      exact ⟨p₁, rfl, ih hw.qVec (IsSemiformula.exs.mp hp) (hp₁ ▸ hqs)⟩
    · obtain ⟨p₁, rfl, hp₁⟩ := exists_eq_all_of_subst_eq hp.isUFormula hq
      exact ⟨p₁, rfl, ih hw.qVec (IsSemiformula.all.mp hp) (hp₁ ▸ hqs)⟩

end hierarchy

end FFL.FirstOrder.Arithmetic.Bootstrapping
