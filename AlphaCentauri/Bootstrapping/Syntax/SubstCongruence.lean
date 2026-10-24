module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax

/-!
# Congruence of substitution

Substituting a vector of terms into a coded semiterm or semiformula with `m` bound variables
depends only on the first `m` entries of the vector.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

variable {L : Language} [L.Encodable] [L.LORDefinable]

lemma termSubst_congr {m t w w' : V} (ht : IsSemiterm L m t) (H : ∀ i < m, w.[i] = w'.[i]) :
    termSubst L w t = termSubst L w' t := by
  apply IsSemiterm.induction 𝚺 _ _ _ _ t ht
  · definability
  · intro z hz; simp [H z hz]
  · intro x; simp
  · intro k f v hf hv ih
    rw [termSubst_func hf hv.isUTerm, termSubst_func hf hv.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k (by rw [len_termSubstVec hv.isUTerm]) (by rw [len_termSubstVec hv.isUTerm])
    intro i hi
    rw [nth_termSubstVec hv.isUTerm hi, nth_termSubstVec hv.isUTerm hi, ih i hi]

lemma IsUTermVec.qVec {k w : V} (hw : IsUTermVec L k w) : IsUTermVec L (k + 1) (qVec L w) := by
  obtain rfl := hw.lh
  simpa [Bootstrapping.qVec] using hw.termBShiftVec.adjoin (t := ^#0) (by simp)

private lemma qVec_congr {m k k' w w' : V} (hw : IsUTermVec L k w) (hw' : IsUTermVec L k' w')
    (hk : m ≤ k) (hk' : m ≤ k') (H : ∀ i < m, w.[i] = w'.[i]) :
    ∀ i < m + 1, (qVec L w).[i] = (qVec L w').[i] := by
  obtain rfl := hw.lh
  obtain rfl := hw'.lh
  intro i hi
  rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
  · simp [qVec]
  · have hi : i < m := by simpa using hi
    simp only [qVec, nth_adjoin_succ]
    rw [nth_termBShiftVec hw (lt_of_lt_of_le hi hk), nth_termBShiftVec hw' (lt_of_lt_of_le hi hk'),
      H i hi]

lemma subst_congr {m p : V} (hp : IsSemiformula L m p) {k k' w w' : V}
    (hw : IsUTermVec L k w) (hw' : IsUTermVec L k' w') (hk : m ≤ k) (hk' : m ≤ k')
    (H : ∀ i < m, w.[i] = w'.[i]) : subst L w p = subst L w' p := by
  revert k k' w w'
  apply IsSemiformula.pi1_structural_induction _ _ _ _ _ _ _ _ _ hp
  · definability
  · intro m l R v hR hv k k' w w' _ _ _ _ H
    rw [substs_rel hR hv.isUTerm, substs_rel hR hv.isUTerm]
    simp only [qqRel_inj, true_and]
    apply nth_ext' l (by rw [len_termSubstVec hv.isUTerm]) (by rw [len_termSubstVec hv.isUTerm])
    intro i hi
    rw [nth_termSubstVec hv.isUTerm hi, nth_termSubstVec hv.isUTerm hi,
      termSubst_congr (hv.nth hi) H]
  · intro m l R v hR hv k k' w w' _ _ _ _ H
    rw [substs_nrel hR hv.isUTerm, substs_nrel hR hv.isUTerm]
    simp only [qqNRel_inj, true_and]
    apply nth_ext' l (by rw [len_termSubstVec hv.isUTerm]) (by rw [len_termSubstVec hv.isUTerm])
    intro i hi
    rw [nth_termSubstVec hv.isUTerm hi, nth_termSubstVec hv.isUTerm hi,
      termSubst_congr (hv.nth hi) H]
  · intro m k k' w w' _ _ _ _ _; simp
  · intro m k k' w w' _ _ _ _ _; simp
  · intro m p q hp hq ihp ihq k k' w w' hw hw' hk hk' H
    rw [substs_and hp.isUFormula hq.isUFormula, substs_and hp.isUFormula hq.isUFormula,
      ihp hw hw' hk hk' H, ihq hw hw' hk hk' H]
  · intro m p q hp hq ihp ihq k k' w w' hw hw' hk hk' H
    rw [substs_or hp.isUFormula hq.isUFormula, substs_or hp.isUFormula hq.isUFormula,
      ihp hw hw' hk hk' H, ihq hw hw' hk hk' H]
  · intro m p hp ih k k' w w' hw hw' hk hk' H
    rw [substs_all hp.isUFormula, substs_all hp.isUFormula,
      ih (hw.qVec) (hw'.qVec) (by simpa using hk) (by simpa using hk') (qVec_congr hw hw' hk hk' H)]
  · intro m p hp ih k k' w w' hw hw' hk hk' H
    rw [substs_ex hp.isUFormula, substs_ex hp.isUFormula,
      ih (hw.qVec) (hw'.qVec) (by simpa using hk) (by simpa using hk') (qVec_congr hw hw' hk hk' H)]

end FFL.FirstOrder.Arithmetic.Bootstrapping
