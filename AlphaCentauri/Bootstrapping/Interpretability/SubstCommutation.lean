module

public import AlphaCentauri.Bootstrapping.Interpretability.Commutation

/-!
# Commutation of the internal translation with substitution of variables

Along a table satisfying `IsTable`, the internal translation commutes with the substitution of a
vector of variables for the variables of a formula.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section generic

variable {L : Language} [L.Encodable] [L.LORDefinable]

lemma IsSemitermVec.of_var {L' : Language} [L'.Encodable] [L'.LORDefinable] {n m w : V}
    (hw : IsSemitermVec L n m w) (hvar : ∀ i < n, (∃ z, w.[i] = ^#z) ∨ (∃ x, w.[i] = ^&x)) :
    IsSemitermVec L' n m w := by
  refine IsSemitermVec.iff.mpr ⟨hw.lh, fun i hi ↦ ?_⟩
  have h := hw.nth hi
  rcases hvar i hi with ⟨z, hz⟩ | ⟨x, hx⟩
  · rw [hz] at h
    rw [hz]
    exact IsSemiterm.bvar.mpr (IsSemiterm.bvar.mp h)
  · rw [hx]
    exact IsSemiterm.fvar _ _

lemma termSubst_bvarVec_termBShift (k : V) {m t : V} (ht : IsSemiterm L m t) :
    termSubst L (bvarVec k (m + 1)) (termBShift L t) = termSubst L (bvarVec (k + 1) m) t := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz
    rw [termBShift_bvar, termSubst_bvar, termSubst_bvar, nth_bvarVec _ _ _ (by simpa using hz),
      nth_bvarVec _ _ _ hz]
    congr 1
    simp only [add_comm, add_left_comm]
  · intro x; simp
  · intro k' f v hf hv ih
    rw [termBShift_func hf hv.isUTerm, termSubst_func hf hv.termBShiftVec.isUTerm,
      termSubst_func hf hv.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k' (len_termSubstVec hv.termBShiftVec.isUTerm) (len_termSubstVec hv.isUTerm)
    intro i hi
    rw [nth_termSubstVec hv.termBShiftVec.isUTerm hi, nth_termSubstVec hv.isUTerm hi,
      nth_termBShiftVec hv.isUTerm hi, ih i hi]

lemma termBShift_termSubst_bvarVec (k : V) {m t : V} (ht : IsSemiterm L m t) :
    termBShift L (termSubst L (bvarVec k m) t) = termSubst L (bvarVec (k + 1) m) t := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz
    rw [termSubst_bvar, termSubst_bvar, nth_bvarVec _ _ _ hz, nth_bvarVec _ _ _ hz, termBShift_bvar]
    congr 1
    simp only [add_assoc, add_comm, add_left_comm]
  · intro x; simp
  · intro k' f v hf hv ih
    have hs : IsSemitermVec L k' (m + k) (termSubstVec L k' (bvarVec k m) v) :=
      (IsSemitermVec.bvarVec (k := m) (n := m + k) (j := k) (add_comm k m).le).termSubstVec hv
    rw [termSubst_func hf hv.isUTerm, termBShift_func hf hs.isUTerm,
      termSubst_func hf hv.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k' (len_termBShiftVec hs.isUTerm) (len_termSubstVec hv.isUTerm)
    intro i hi
    simp only [nth_termBShiftVec hs.isUTerm hi, nth_termSubstVec hv.isUTerm hi]
    exact ih i hi

lemma termSubst_bvarVec_zero {m t : V} (ht : IsSemiterm L m t) : termSubst L (bvarVec 0 m) t = t :=
  termSubst_eq_self ht fun i hi ↦ by rw [nth_bvarVec _ _ _ hi, zero_add]

lemma nth_qVec_zero (w : V) : (qVec L w).[0] = ^#0 := by simp [qVec]

lemma nth_qVec_succ_semi {m n w i : V} (hw : IsSemitermVec L n m w) (hi : i < n) :
    (qVec L w).[i + 1] = termBShift L w.[i] := by
  have h₁ : IsUTermVec L (len w) w := by rw [hw.lh]; exact hw.isUTerm
  rw [qVec, nth_adjoin_succ, nth_termBShiftVec h₁ (by rw [hw.lh]; exact hi)]

lemma qVec_eq_of_var {L' : Language} [L'.Encodable] [L'.LORDefinable] {n m w : V}
    (hw : IsSemitermVec L n m w) (hvar : ∀ i < n, (∃ z, w.[i] = ^#z) ∨ (∃ x, w.[i] = ^&x)) :
    qVec L w = qVec L' w := by
  have h₁ : IsUTermVec L (len w) w := by rw [hw.lh]; exact hw.isUTerm
  have h₂ : IsUTermVec L' (len w) w := by rw [hw.lh]; exact (hw.of_var (L' := L') hvar).isUTerm
  have h₃ : termBShiftVec L (len w) w = termBShiftVec L' (len w) w := by
    apply nth_ext' (len w) (len_termBShiftVec h₁) (len_termBShiftVec h₂)
    intro i hi
    rw [nth_termBShiftVec h₁ hi, nth_termBShiftVec h₂ hi]
    rcases hvar i (by rw [hw.lh] at hi; exact hi) with ⟨z, hz⟩ | ⟨x, hx⟩
    · rw [hz, termBShift_bvar, termBShift_bvar]
    · rw [hx, termBShift_fvar, termBShift_fvar]
  unfold qVec
  rw [h₃]

lemma hvar_qVec {n m w : V} (hw : IsSemitermVec L n m w)
    (hvar : ∀ i < n, (∃ z, w.[i] = ^#z) ∨ (∃ x, w.[i] = ^&x)) :
    ∀ i < n + 1, (∃ z, (qVec L w).[i] = ^#z) ∨ (∃ x, (qVec L w).[i] = ^&x) := by
  intro i hi
  rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
  · exact Or.inl ⟨0, nth_qVec_zero w⟩
  · have hi' : i < n := by simpa using hi
    rcases hvar i hi' with ⟨z, hz⟩ | ⟨x, hx⟩
    · exact Or.inl ⟨z + 1, by rw [nth_qVec_succ_semi hw hi', hz, termBShift_bvar]⟩
    · exact Or.inr ⟨x, by rw [nth_qVec_succ_semi hw hi', hx, termBShift_fvar]⟩

lemma exists_vec_shift {n m w : V} (hw : IsSemitermVec L n m w) (k : V) :
    ∃ v, IsSemitermVec L (n + k) (m + k) v ∧ (∀ i < k, v.[i] = ^#i) ∧
      ∀ j < n, v.[k + j] = termSubst L (bvarVec k m) w.[j] := by
  have hsub : IsSemitermVec L m (m + k) (bvarVec k m) :=
    IsSemitermVec.bvarVec (j := k) (k := m) (n := m + k) (add_comm k m).le
  have hrest : IsSemitermVec L n (m + k) (termSubstVec L n (bvarVec k m) w) :=
    hsub.termSubstVec hw
  have hl : len (termSubstVec L n (bvarVec k m) w) = n := len_termSubstVec hw.isUTerm
  obtain ⟨v, hvl, hv₁, hv₂⟩ := exists_vec_bvar_append (termSubstVec L n (bvarVec k m) w) k
  refine ⟨v, IsSemitermVec.iff.mpr ⟨by rw [hvl, hl, add_comm], fun i hi ↦ ?_⟩, hv₁, fun j hj ↦ ?_⟩
  · rcases lt_or_ge i k with hik | hik
    · rw [hv₁ i hik]
      exact IsSemiterm.bvar.mpr (lt_of_lt_of_le hik le_add_self)
    · obtain ⟨j, rfl⟩ := exists_add_of_le hik
      have hj' : j < n := by
        rw [add_comm n k] at hi
        exact (add_lt_add_iff_left k).mp hi
      rw [hv₂ j (by rw [hl]; exact hj'), nth_termSubstVec hw.isUTerm hj']
      exact hsub.termSubst (hw.nth hj')
  · rw [hv₂ j (by rw [hl]; exact hj), nth_termSubstVec hw.isUTerm hj]

lemma subst_eq_self_of_le {m k p w : V} (hp : IsSemiformula L m p) (hw : IsUTermVec L k w)
    (hk : m ≤ k) (H : ∀ i < m, w.[i] = ^#i) : subst L w p = p := by
  have h₁ : IsSemitermVec L m m (bvarVec 0 m) := IsSemitermVec.bvarVec (by simp)
  calc subst L w p = subst L (bvarVec 0 m) p := by
        apply subst_congr hp hw h₁.isUTerm hk le_rfl
        intro i hi
        rw [H i hi, nth_bvarVec _ _ _ hi, zero_add]
    _ = p := subst_eq_self hp h₁ fun i hi ↦ by rw [nth_bvarVec _ _ _ hi, zero_add]

lemma subst_imp {n m w p q : V} (hw : IsSemitermVec L n m w) (hp : IsSemiformula L n p)
    (hq : IsSemiformula L n q) : subst L w (imp L p q) = imp L (subst L w p) (subst L w q) := by
  unfold imp
  rw [substs_or hp.isUFormula.neg hq.isUFormula, substs_neg hp hw]

lemma subst_qqConj_exists {w n : V} (ps : V) (hps : ∀ i < len ps, IsSemiformula L n ps.[i]) :
    ∃ qs, len qs = len ps ∧ (∀ i < len ps, qs.[i] = subst L w ps.[i]) ∧
      subst L w (^⋀ ps) = ^⋀ qs := by
  revert hps
  induction ps using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => intro _; exact ⟨0, by simp, by simp, by simp⟩
  case adjoin p ps ih =>
    intro hps
    have h₁ : IsSemiformula L n p := by simpa using hps 0 (by simp)
    have h₂ : ∀ i < len ps, IsSemiformula L n ps.[i] := by
      intro i hi
      simpa using hps (i + 1) (by simpa using hi)
    obtain ⟨qs, hlen, hq, hsh⟩ := ih h₂
    have h₃ : IsUFormula L (^⋀ ps) := (qqConj_semiformula.mpr h₂).isUFormula
    have h₄ : subst L w (^⋀ (p ∷ ps)) = ^⋀ (subst L w p ∷ qs) := by
      rw [qqConj_cons, qqConj_cons, substs_and h₁.isUFormula h₃, hsh]
    have h₅ : ∀ i < len (p ∷ ps), (subst L w p ∷ qs).[i] = subst L w (p ∷ ps).[i] := by
      intro i hi
      rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
      · simp
      · simpa using hq i (by simpa using hi)
    exact ⟨subst L w p ∷ qs, by simp [hlen], h₅, h₄⟩

lemma subst_qqAlls_vec {k n m w v p : V} (hw : IsSemitermVec L n m w) (hp : IsUFormula L p)
    (hv : IsSemitermVec L (n + k) (m + k) v) (h₁ : ∀ i < k, v.[i] = ^#i)
    (h₂ : ∀ j < n, v.[k + j] = termSubst L (bvarVec k m) w.[j]) :
    subst L w (qqAlls p k) = qqAlls (subst L v p) k := by
  induction k using ISigma1.pi1_succ_induction generalizing p v
  · definability
  case zero =>
    have hvw : v = w := nth_ext' n (by simpa using hv.lh) hw.lh fun i hi ↦ by
      simpa [termSubst_bvarVec_zero (hw.nth hi)] using h₂ i hi
    rw [qqAlls_zero, qqAlls_zero, hvw]
  case succ k ih =>
    obtain ⟨v', hv', hv'₁, hv'₂⟩ := exists_vec_shift hw k
    have hqv : qVec L v' = v := by
      have hl : len (qVec L v') = len v := by rw [len_qVec hv'.isUTerm, hv.lh, add_assoc]
      refine nth_ext' (len v) hl rfl ?_
      intro i hi
      rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
      · rw [nth_qVec_zero, h₁ 0 (by simp)]
      · rcases lt_or_ge i k with hik | hik
        · rw [nth_qVec_succ_semi hv' (lt_of_lt_of_le hik le_add_self), hv'₁ i hik, termBShift_bvar,
            h₁ (i + 1) (by simpa using hik)]
        · obtain ⟨j, rfl⟩ := exists_add_of_le hik
          have hj : j < n := by
            have e : n + (k + 1) = k + (n + 1) := by rw [← add_assoc, add_comm n k, add_assoc]
            rw [hv.lh, e, add_assoc k j 1] at hi
            exact (add_lt_add_iff_right 1).mp ((add_lt_add_iff_left k).mp hi)
          have hkj : k + j < n + k := by
            rw [add_comm n k]
            exact (add_lt_add_iff_left k).mpr hj
          rw [nth_qVec_succ_semi hv' hkj, hv'₂ j hj, termBShift_termSubst_bvarVec k (hw.nth hj),
            show k + j + 1 = k + 1 + j by simp only [add_assoc, add_comm, add_left_comm], h₂ j hj]
    rw [qqAlls_succ' p k, qqAlls_succ' (subst L v p) k,
      ih (IsUFormula.all.mpr hp) hv' hv'₁ hv'₂, substs_all hp, hqv]


lemma subst_relocate_qVec {a b c j s v w E : V} (hw : IsSemitermVec L a c w)
    (hE : IsSemiformula L (a + 1) E) (hv : IsSemitermVec L (s + a) b v) (hj : j < s)
    (hvj : v.[j] = ^#j) (hvs : ∀ z < a, v.[s + z] = termSubst L (bvarVec s c) w.[z]) :
    subst L v (relocate L j s E) = relocate L j s (subst L (qVec L w) E) := by
  have hqw : IsSemitermVec L (a + 1) (c + 1) (qVec L w) := hw.qVec
  have hσ : IsSemitermVec L (a + 1) (s + a) (^#j ∷ bvarVec s a) :=
    IsSemitermVec.adjoin (IsSemitermVec.bvarVec le_rfl)
      (IsSemiterm.bvar.mpr (lt_of_lt_of_le hj le_self_add))
  have hτ : IsSemitermVec L (c + 1) (s + c) (^#j ∷ bvarVec s c) :=
    IsSemitermVec.adjoin (IsSemitermVec.bvarVec le_rfl)
      (IsSemiterm.bvar.mpr (lt_of_lt_of_le hj le_self_add))
  rw [relocate_eq_subst hE, relocate_eq_subst (hE.subst hqw), substs_substs hE hv hσ,
    substs_substs hE hτ hqw]
  apply subst_congr hE (hv.termSubstVec hσ).isUTerm (hτ.termSubstVec hqw).isUTerm le_rfl le_rfl
  intro i hi
  rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
  · simp [nth_termSubstVec hσ.isUTerm hi, nth_termSubstVec hqw.isUTerm hi, nth_qVec_zero, hvj]
  · have hi' : i < a := by simpa using hi
    rw [nth_termSubstVec hσ.isUTerm hi, nth_adjoin_succ, nth_bvarVec _ _ _ hi', termSubst_bvar,
      hvs i hi', nth_termSubstVec hqw.isUTerm hi, nth_qVec_succ_semi hw hi',
      substs_cons_bShift (hw.nth hi')]

end generic

section table

variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable]

lemma IsTable.subst_domainAt {tbl i l v : V} (hT : IsTable L₁ L₂ tbl) (hv : IsUTermVec L₁ l v)
    (hk : i + 1 ≤ l) (H : ∀ x < i + 1, v.[x] = ^#x) :
    subst L₁ v (domainAt L₁ tbl i) = domainAt L₁ tbl i :=
  subst_eq_self_of_le (hT.isSemiformula_domainAt (lt_add_one i)) hv hk H

lemma IsTable.subst_funcTail {tbl k f l v : V} (hT : IsTable L₁ L₂ tbl) (hf : L₂.IsFunc k f)
    (hv : IsUTermVec L₁ l v) (hk : k + 1 ≤ l) (H : ∀ x < k + 1, v.[x] = ^#x) :
    subst L₁ v (funcTail L₁ tbl k f) = funcTail L₁ tbl k f :=
  subst_eq_self_of_le (hT.isSemiformula_funcTail hf (lt_add_one k)) hv hk H

lemma IsTable.subst_qqConj_guardVec {tbl n m k s N b w v u u' : V} (hT : IsTable L₁ L₂ tbl)
    (hw : IsSemitermVec L₁ n m w) (hv : IsSemitermVec L₁ (s + n) b v) (hks : k ≤ s) (hkt : k ≤ N)
    (hst : s + n ≤ N) (hvj : ∀ j < k, v.[j] = ^#j)
    (hvs : ∀ z < n, v.[s + z] = termSubst L₁ (bvarVec s m) w.[z])
    (hu : ∀ i < k, IsSemiformula L₁ (n + 1) u.[i])
    (hu' : ∀ i < k, u'.[i] = subst L₁ (qVec L₁ w) u.[i]) :
    subst L₁ v (^⋀ guardVec L₁ tbl s u k) = ^⋀ guardVec L₁ tbl s u' k := by
  obtain ⟨qs, hlen, hq, hsh⟩ := subst_qqConj_exists (L := L₁) (w := v) (guardVec L₁ tbl s u k)
    (fun j hj ↦ hT.isSemiformula_guardVec hkt hst hu (by simpa using hj))
  rw [hsh]
  congr 1
  apply nth_ext' k (by simp [hlen]) (by simp)
  intro i hi
  have hik : i < s := lt_of_lt_of_le hi hks
  have hit : i < N := lt_of_lt_of_le hi hkt
  rw [hq i (by simpa using hi), nth_guardVec tbl s u k i hi, nth_guardVec tbl s u' k i hi, hu' i hi,
    substs_and (hT.isSemiformula_domainAt hit).isUFormula ((hu i hi).relocate hit hst).isUFormula,
    hT.subst_domainAt hv.isUTerm (succ_le_iff_lt.mpr (lt_of_lt_of_le hik le_self_add))
      (fun x hx ↦ hvj x (lt_of_le_of_lt (lt_succ_iff_le.mp hx) hi)),
    subst_relocate_qVec hw (hu i hi) hv hik (hvj i hi) hvs]

lemma varEqual_termSubst {tbl : V} (hT : IsTable L₁ L₂ tbl) {n m w t : V}
    (hw : IsSemitermVec L₂ n m w)
    (hvar : ∀ i < n, (∃ z, w.[i] = ^#z) ∨ (∃ x, w.[i] = ^&x)) (ht : IsSemiterm L₂ n t) :
    varEqual L₁ L₂ tbl (termSubst L₂ w t) = subst L₁ (qVec L₁ w) (varEqual L₁ L₂ tbl t) := by
  have hw₁ : IsSemitermVec L₁ n m w := hw.of_var hvar
  have h₁ : ∀ t, IsSemiterm L₂ n t →
      varEqual L₁ L₂ tbl (termSubst L₂ w t) = subst L₁ (qVec L₁ w) (varEqual L₁ L₂ tbl t) := by
    apply IsSemiterm.sigma1_induction
      (P := fun t ↦
        varEqual L₁ L₂ tbl (termSubst L₂ w t) = subst L₁ (qVec L₁ w) (varEqual L₁ L₂ tbl t))
    · definability
    · intro z hz
      rcases hvar z hz with ⟨y, hy⟩ | ⟨x, hx⟩
      · rw [termSubst_bvar, hy, varEqual_bvar, varEqual_bvar,
          substs_rel isRel_eq_quote (IsUTermVec.pair (show IsUTerm L₁ (^#0 : V) by simp)
            (show IsUTerm L₁ (^#(z + 1) : V) by simp)),
          termSubstVec_cons₂ (show IsUTerm L₁ (^#0 : V) by simp)
            (show IsUTerm L₁ (^#(z + 1) : V) by simp),
          termSubst_bvar, termSubst_bvar, nth_qVec_zero, nth_qVec_succ_semi hw₁ hz, hy,
          termBShift_bvar]
      · rw [termSubst_bvar, hx, varEqual_fvar, varEqual_bvar,
          substs_rel isRel_eq_quote (IsUTermVec.pair (show IsUTerm L₁ (^#0 : V) by simp)
            (show IsUTerm L₁ (^#(z + 1) : V) by simp)),
          termSubstVec_cons₂ (show IsUTerm L₁ (^#0 : V) by simp)
            (show IsUTerm L₁ (^#(z + 1) : V) by simp),
          termSubst_bvar, termSubst_bvar, nth_qVec_zero, nth_qVec_succ_semi hw₁ hz, hx,
          termBShift_fvar]
    · intro x
      rw [termSubst_fvar, varEqual_fvar, substs_rel isRel_eq_quote
          (IsUTermVec.pair (show IsUTerm L₁ (^#0 : V) by simp) (show IsUTerm L₁ (^&x : V) by simp)),
        termSubstVec_cons₂ (show IsUTerm L₁ (^#0 : V) by simp) (show IsUTerm L₁ (^&x : V) by simp),
        termSubst_bvar, nth_qVec_zero, termSubst_fvar]
    · intro k f v hf hv ih
      have h₂ := hT.isSemiformula_funcBody hf hv (fun i hi ↦ IsSemiformula.varEqual hT (hv.nth hi))
      have h₃ := (IsSemiformula.imp.mp h₂).1
      have h₄ := hT.isSemiformula_funcTail hf (show k < n + 1 + k by simp)
      have hvw : IsUTermVec L₂ k (termSubstVec L₂ k w v) :=
        (IsSemitermVec.termSubstVec hw hv).isUTerm
      have h₅ : ∀ i < k, (varEqualVec L₁ L₂ tbl k (termSubstVec L₂ k w v)).[i] =
          subst L₁ (qVec L₁ w) (varEqualVec L₁ L₂ tbl k v).[i] := by
        intro i hi
        rw [nth_varEqualVec hvw hi, nth_termSubstVec hv.isUTerm hi, nth_varEqualVec hv.isUTerm hi]
        exact ih i hi
      obtain ⟨v', hv', h₆, h₇⟩ := exists_vec_shift hw₁.qVec k
      have hk0 : v'.[k] = ^#k := by
        have h₈ := h₇ 0 (by simp)
        rw [nth_qVec_zero, termSubst_bvar, nth_bvarVec _ _ _ (by simp)] at h₈
        simpa using h₈
      have hvs : ∀ z < n, v'.[k + 1 + z] = termSubst L₁ (bvarVec (k + 1) m) w.[z] := by
        intro z hz
        have e : k + 1 + z = k + (z + 1) := by simp only [add_comm, add_left_comm]
        rw [e, h₇ (z + 1) (by simpa using hz), nth_qVec_succ_semi hw₁ hz,
          termSubst_bvarVec_termBShift k (hw₁.nth hz)]
      rw [termSubst_func hf hv.isUTerm, varEqual_func hf hvw, varEqual_func hf hv.isUTerm,
        subst_qqAlls_vec hw₁.qVec h₂.isUFormula hv' h₆ h₇, subst_imp hv' h₃ h₄]
      have hv₁ : IsSemitermVec L₁ (k + 1 + n) (m + 1 + k) v' := by
        rw [add_arity_comm k n]
        exact hv'
      rw [hT.subst_qqConj_guardVec hw₁ hv₁ le_self_add le_add_self (add_arity_comm k n).le h₆ hvs
          (fun i hi ↦ hT.isSemiformula_varEqualVec_nth hv hi) h₅,
        hT.subst_funcTail hf hv'.isUTerm (le_self_add.trans (add_arity_comm k n).le)
          (fun x hx ↦ by
          rcases lt_or_ge x k with hxk | hxk
          · exact h₆ x hxk
          · obtain rfl : x = k := le_antisymm (lt_succ_iff_le.mp hx) hxk
            exact hk0)]
  exact h₁ t ht

lemma subst_translateRel {tbl n m k R v w : V} (hT : IsTable L₁ L₂ tbl)
    (hw : IsSemitermVec L₂ n m w) (hvar : ∀ i < n, (∃ z, w.[i] = ^#z) ∨ (∃ x, w.[i] = ^&x))
    (hR : L₂.IsRel k R) (hv : IsSemitermVec L₂ k n v) :
    subst L₁ w (Bootstrapping.translateRel L₁ L₂ tbl k R v) =
      Bootstrapping.translateRel L₁ L₂ tbl k R (termSubstVec L₂ k w v) := by
  have hw₁ : IsSemitermVec L₁ n m w := hw.of_var hvar
  have h₁ : k ≤ n + k := by simp
  have h₂ : k + n ≤ n + k := (add_comm k n).le
  have h₃ : IsSemiformula L₁ (n + k) (^⋀ guardVec L₁ tbl k (varEqualVec L₁ L₂ tbl k v) k) :=
    IsSemiformula.qqConj_guardVec hT h₁ h₂ (fun i hi ↦ hT.isSemiformula_varEqualVec_nth hv hi)
  have h₄ : IsSemiformula L₁ (n + k) (tableRel tbl k R) := (hT.rel hR).of_le h₁
  have hvw : IsUTermVec L₂ k (termSubstVec L₂ k w v) :=
    (IsSemitermVec.termSubstVec hw hv).isUTerm
  have h₅ : ∀ i < k, (varEqualVec L₁ L₂ tbl k (termSubstVec L₂ k w v)).[i] =
      subst L₁ (qVec L₁ w) (varEqualVec L₁ L₂ tbl k v).[i] := by
    intro i hi
    rw [nth_varEqualVec hvw hi, nth_termSubstVec hv.isUTerm hi, nth_varEqualVec hv.isUTerm hi]
    exact varEqual_termSubst hT hw hvar (hv.nth hi)
  obtain ⟨v', hv', h₆, h₇⟩ := exists_vec_shift hw₁ k
  have hv'' : IsSemitermVec L₁ (k + n) (m + k) v' := by
    rw [add_comm k n]
    exact hv'
  unfold Bootstrapping.translateRel
  rw [subst_qqAlls_vec hw₁ (IsSemiformula.imp.mpr ⟨h₃, h₄⟩).isUFormula hv' h₆ h₇,
    subst_imp hv' h₃ h₄,
    hT.subst_qqConj_guardVec hw₁ hv'' le_rfl h₁ h₂ h₆ h₇
      (fun i hi ↦ hT.isSemiformula_varEqualVec_nth hv hi) h₅,
    subst_eq_self_of_le (hT.rel hR) hv'.isUTerm h₁ h₆]

lemma translate_subst_aux {tbl : V} (hT : IsTable L₁ L₂ tbl) {n p : V} (hp : IsSemiformula L₂ n p) :
    ∀ m w : V, IsSemitermVec L₂ n m w → (∀ i < n, (∃ z, w.[i] = ^#z) ∨ (∃ x, w.[i] = ^&x)) →
      translate L₁ L₂ tbl (subst L₂ w p) = subst L₁ w (translate L₁ L₂ tbl p) := by
  apply IsSemiformula.pi1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R v hR hv m w hw hvar
    rw [substs_rel hR hv.isUTerm, translate_rel hR (IsSemitermVec.termSubstVec hw hv).isUTerm,
      translate_rel hR hv.isUTerm, subst_translateRel hT hw hvar hR hv]
  · intro n k R v hR hv m w hw hvar
    rw [substs_nrel hR hv.isUTerm, translate_nrel hR (IsSemitermVec.termSubstVec hw hv).isUTerm,
      translate_nrel hR hv.isUTerm,
      substs_neg (IsSemiformula.translateRel hT hR hv) (hw.of_var hvar),
      subst_translateRel hT hw hvar hR hv]
  · intro n m w hw hvar
    simp
  · intro n m w hw hvar
    simp
  · intro n p q hp hq ihp ihq m w hw hvar
    rw [substs_and hp.isUFormula hq.isUFormula,
      translate_and (IsSemiformula.subst hp hw).isUFormula (IsSemiformula.subst hq hw).isUFormula,
      ihp m w hw hvar, ihq m w hw hvar, translate_and hp.isUFormula hq.isUFormula,
      substs_and (IsSemiformula.translate hT hp).isUFormula
        (IsSemiformula.translate hT hq).isUFormula]
  · intro n p q hp hq ihp ihq m w hw hvar
    rw [substs_or hp.isUFormula hq.isUFormula,
      translate_or (IsSemiformula.subst hp hw).isUFormula (IsSemiformula.subst hq hw).isUFormula,
      ihp m w hw hvar, ihq m w hw hvar, translate_or hp.isUFormula hq.isUFormula,
      substs_or (IsSemiformula.translate hT hp).isUFormula
        (IsSemiformula.translate hT hq).isUFormula]
  · intro n p hp ih m w hw hvar
    have hw₁ : IsSemitermVec L₁ n m w := hw.of_var hvar
    have hw' : IsSemitermVec L₂ (n + 1) (m + 1) (qVec L₂ w) := hw.qVec
    have hvar' := hvar_qVec hw hvar
    have h₁ : IsSemiformula L₁ (n + 1) (domainAt L₁ tbl 0) :=
      hT.isSemiformula_domainAt (by simp)
    have h₂ : IsSemiformula L₁ (n + 1) (translate L₁ L₂ tbl p) :=
      IsSemiformula.translate hT hp
    have h₃ : subst L₁ (qVec L₁ w) (domainAt L₁ tbl 0) = domainAt L₁ tbl 0 :=
      hT.subst_domainAt hw₁.qVec.isUTerm (by simp) (fun x hx ↦ by
        obtain rfl : x = 0 := by simpa using hx
        exact nth_qVec_zero w)
    rw [substs_all hp.isUFormula, translate_all (IsSemiformula.subst hp hw').isUFormula,
      ih (m + 1) (qVec L₂ w) hw' hvar', qVec_eq_of_var (L' := L₁) hw hvar,
      translate_all hp.isUFormula, substs_all (IsSemiformula.imp.mpr ⟨h₁, h₂⟩).isUFormula,
      subst_imp hw₁.qVec h₁ h₂, h₃]
  · intro n p hp ih m w hw hvar
    have hw₁ : IsSemitermVec L₁ n m w := hw.of_var hvar
    have hw' : IsSemitermVec L₂ (n + 1) (m + 1) (qVec L₂ w) := hw.qVec
    have hvar' := hvar_qVec hw hvar
    have h₁ : IsSemiformula L₁ (n + 1) (domainAt L₁ tbl 0) :=
      hT.isSemiformula_domainAt (by simp)
    have h₂ : IsSemiformula L₁ (n + 1) (translate L₁ L₂ tbl p) :=
      IsSemiformula.translate hT hp
    have h₃ : subst L₁ (qVec L₁ w) (domainAt L₁ tbl 0) = domainAt L₁ tbl 0 :=
      hT.subst_domainAt hw₁.qVec.isUTerm (by simp) (fun x hx ↦ by
        obtain rfl : x = 0 := by simpa using hx
        exact nth_qVec_zero w)
    rw [substs_ex hp.isUFormula, translate_exs (IsSemiformula.subst hp hw').isUFormula,
      ih (m + 1) (qVec L₂ w) hw' hvar', qVec_eq_of_var (L' := L₁) hw hvar,
      translate_exs hp.isUFormula, substs_ex (IsSemiformula.and.mpr ⟨h₁, h₂⟩).isUFormula,
      substs_and h₁.isUFormula h₂.isUFormula, h₃]

lemma translate_subst {tbl : V} (hT : IsTable L₁ L₂ tbl) {n m w p : V} (hw : IsSemitermVec L₂ n m w)
    (hvar : ∀ i < n, (∃ z, w.[i] = ^#z) ∨ (∃ x, w.[i] = ^&x)) (hp : IsSemiformula L₂ n p) :
    translate L₁ L₂ tbl (subst L₂ w p) = subst L₁ w (translate L₁ L₂ tbl p) :=
  translate_subst_aux hT hp m w hw hvar

lemma translate_substs1_fvar {tbl : V} (hT : IsTable L₁ L₂ tbl) {p : V} (x : V)
    (hp : IsSemiformula L₂ 1 p) :
    translate L₁ L₂ tbl (substs1 L₂ (^&x) p) = substs1 L₁ (^&x) (translate L₁ L₂ tbl p) := by
  have hw : IsSemitermVec L₂ 1 0 (?[^&x] : V) := IsSemitermVec.singleton.mpr (IsSemiterm.fvar _ _)
  have hvar : ∀ i < 1, (∃ z, (?[^&x] : V).[i] = ^#z) ∨ (∃ y, (?[^&x] : V).[i] = ^&y) := by
    intro i hi
    obtain rfl : i = 0 := by simpa using hi
    exact Or.inr ⟨x, by simp⟩
  unfold substs1
  exact translate_subst hT hw hvar hp

end table

end FFL.FirstOrder.Arithmetic.Bootstrapping
