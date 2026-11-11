module

public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Term.Functions

/-!
# Gaps in Foundation's `Syntax/Formula/Functions`

Negation has no fixed point on coded formulas, and the shift of free variables does not decrease
the code of a formula. A substitution instance `subst w p` of a coded formula `p`, and likewise its
shift `shift p`, has the same outermost connective as `p`. Substituting into a coded formula with
`m` bound variables depends only on the first `m` entries of the vector. Structural induction on
one-variable formulas instantiates the quantifier case by a free variable. A coded semiformula fixed
by the shift has no free variables, and the class of such codes is closed under the connectives.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic
namespace Bootstrapping

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

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

/-- The shift of free variables does not decrease the code of a formula. -/
lemma le_shift {n p : V} (hp : IsSemiformula L n p) : p ≤ shift L p := by
  apply IsSemiformula.pi1_structural_induction (P := fun _ p ↦ p ≤ shift L p)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R v hR hv
    rw [shift_rel hR hv.isUTerm]
    simpa [qqRel] using
      pair_le_pair_right 0 <| pair_le_pair_right k <| pair_le_pair_right R (le_termShiftVec hv)
  · intro n k R v hR hv
    rw [shift_nrel hR hv.isUTerm]
    simpa [qqNRel] using
      pair_le_pair_right 1 <| pair_le_pair_right k <| pair_le_pair_right R (le_termShiftVec hv)
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

section connective

variable {w p : V}

attribute [local simp] substs_rel substs_nrel substs_verum substs_falsum substs_and substs_or
  substs_all substs_ex

lemma exists_eq_or_of_subst_eq (hp : IsUFormula L p) {q₁ q₂ : V}
    (h : subst L w p = q₁ ^⋎ q₂) :
    ∃ p₁ p₂, p = p₁ ^⋎ p₂ ∧ subst L w p₁ = q₁ ∧ subst L w p₂ = q₂ := by
  rcases hp.case with (⟨k', R', v', hR, hv, rfl⟩ | ⟨k', R', v', hR, hv, rfl⟩ | rfl | rfl |
    ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, hp₁, rfl⟩ | ⟨p₁, hp₁, rfl⟩) <;>
    simp_all
  all_goals simp_all [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs]

lemma exists_eq_and_of_subst_eq (hp : IsUFormula L p) {q₁ q₂ : V}
    (h : subst L w p = q₁ ^⋏ q₂) :
    ∃ p₁ p₂, p = p₁ ^⋏ p₂ ∧ subst L w p₁ = q₁ ∧ subst L w p₂ = q₂ := by
  rcases hp.case with (⟨k', R', v', hR, hv, rfl⟩ | ⟨k', R', v', hR, hv, rfl⟩ | rfl | rfl |
    ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, hp₁, rfl⟩ | ⟨p₁, hp₁, rfl⟩) <;>
    simp_all
  all_goals simp_all [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs]

lemma exists_eq_all_of_subst_eq (hp : IsUFormula L p) {q : V} (h : subst L w p = ^∀ q) :
    ∃ p₁, p = ^∀ p₁ ∧ subst L (qVec L w) p₁ = q := by
  rcases hp.case with (⟨k', R', v', hR, hv, rfl⟩ | ⟨k', R', v', hR, hv, rfl⟩ | rfl | rfl |
    ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, hp₁, rfl⟩ | ⟨p₁, hp₁, rfl⟩) <;>
    simp_all
  all_goals simp_all [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs]

lemma exists_eq_exs_of_subst_eq (hp : IsUFormula L p) {q : V} (h : subst L w p = ^∃ q) :
    ∃ p₁, p = ^∃ p₁ ∧ subst L (qVec L w) p₁ = q := by
  rcases hp.case with (⟨k', R', v', hR, hv, rfl⟩ | ⟨k', R', v', hR, hv, rfl⟩ | rfl | rfl |
    ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, hp₁, rfl⟩ | ⟨p₁, hp₁, rfl⟩) <;>
    simp_all
  all_goals simp_all [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs]

lemma exists_eq_rel_of_subst_eq (hp : IsUFormula L p) {k R v : V}
    (h : subst L w p = ^rel k R v) :
    ∃ v', IsUTermVec L k v' ∧ p = ^rel k R v' ∧ termSubstVec L k w v' = v := by
  rcases hp.case with (⟨k', R', v', hR, hv, rfl⟩ | ⟨k', R', v', hR, hv, rfl⟩ | rfl | rfl |
    ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, hp₁, rfl⟩ | ⟨p₁, hp₁, rfl⟩)
  case inl =>
    rw [substs_rel hR hv, qqRel_inj] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨v', hv, rfl, rfl⟩
  all_goals simp_all
  all_goals simp_all [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs]

lemma exists_eq_nrel_of_subst_eq (hp : IsUFormula L p) {k R v : V}
    (h : subst L w p = ^nrel k R v) :
    ∃ v', IsUTermVec L k v' ∧ p = ^nrel k R v' ∧ termSubstVec L k w v' = v := by
  rcases hp.case with (⟨k', R', v', hR, hv, rfl⟩ | ⟨k', R', v', hR, hv, rfl⟩ | rfl | rfl |
    ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, hp₁, rfl⟩ | ⟨p₁, hp₁, rfl⟩)
  case inr.inl =>
    rw [substs_nrel hR hv, qqNRel_inj] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨v', hv, rfl, rfl⟩
  all_goals simp_all
  all_goals simp_all [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs]

lemma exists_eq_or_of_shift_eq (hp : IsUFormula L p) {q₁ q₂ : V}
    (h : shift L p = q₁ ^⋎ q₂) :
    ∃ p₁ p₂, p = p₁ ^⋎ p₂ ∧ shift L p₁ = q₁ ∧ shift L p₂ = q₂ := by
  rcases hp.case with (⟨k', R', v', hR, hv, rfl⟩ | ⟨k', R', v', hR, hv, rfl⟩ | rfl | rfl |
    ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, hp₁, rfl⟩ | ⟨p₁, hp₁, rfl⟩) <;>
    simp_all
  all_goals simp_all [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs]

lemma exists_eq_and_of_shift_eq (hp : IsUFormula L p) {q₁ q₂ : V}
    (h : shift L p = q₁ ^⋏ q₂) :
    ∃ p₁ p₂, p = p₁ ^⋏ p₂ ∧ shift L p₁ = q₁ ∧ shift L p₂ = q₂ := by
  rcases hp.case with (⟨k', R', v', hR, hv, rfl⟩ | ⟨k', R', v', hR, hv, rfl⟩ | rfl | rfl |
    ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, hp₁, rfl⟩ | ⟨p₁, hp₁, rfl⟩) <;>
    simp_all
  all_goals simp_all [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs]

lemma exists_eq_all_of_shift_eq (hp : IsUFormula L p) {q : V} (h : shift L p = ^∀ q) :
    ∃ p₁, p = ^∀ p₁ ∧ shift L p₁ = q := by
  rcases hp.case with (⟨k', R', v', hR, hv, rfl⟩ | ⟨k', R', v', hR, hv, rfl⟩ | rfl | rfl |
    ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, hp₁, rfl⟩ | ⟨p₁, hp₁, rfl⟩) <;>
    simp_all
  all_goals simp_all [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs]

lemma exists_eq_exs_of_shift_eq (hp : IsUFormula L p) {q : V} (h : shift L p = ^∃ q) :
    ∃ p₁, p = ^∃ p₁ ∧ shift L p₁ = q := by
  rcases hp.case with (⟨k', R', v', hR, hv, rfl⟩ | ⟨k', R', v', hR, hv, rfl⟩ | rfl | rfl |
    ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, hp₁, rfl⟩ | ⟨p₁, hp₁, rfl⟩) <;>
    simp_all
  all_goals simp_all [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs]

end connective

/-- Structural induction on one-variable formulas whose quantifier case instantiates the inner
bound variable with the free variable `^&(g (^∀ p))`. -/
lemma IsSemiformula.sigma1_induction_fvar {P : V → Prop} (hP : 𝚺ᴬ₁-Predicate P)
    {g : V → V} (hg : 𝚺ᴬ₁-Function₁ g)
    (hrel : ∀ k r v, L.IsRel k r → IsSemitermVec L k 1 v → P (^rel k r v))
    (hnrel : ∀ k r v, L.IsRel k r → IsSemitermVec L k 1 v → P (^nrel k r v))
    (hverum : P ^⊤) (hfalsum : P ^⊥)
    (hand : ∀ p q, IsSemiformula L 1 p → IsSemiformula L 1 q → P p → P q → P (p ^⋏ q))
    (hor : ∀ p q, IsSemiformula L 1 p → IsSemiformula L 1 q → P p → P q → P (p ^⋎ q))
    (hall : ∀ p, IsSemiformula L 2 p →
      P (Bootstrapping.subst L ?[^&(g (^∀ p)), ^#(0 : V)] p) → P (^∀ p))
    (hexs : ∀ p, IsSemiformula L 2 p →
      P (Bootstrapping.subst L ?[^&(g (^∃ p)), ^#(0 : V)] p) → P (^∃ p))
    {p : V} : IsSemiformula L 1 p → P p := by
  have hm : 𝚺ᴬ₁-Function₁[V] formulaComplexity L := inferInstance
  let f : V → V := fun p ↦ max p (Bootstrapping.subst L ?[^&(g p), ^#(0 : V)] (π₂ (p - 1)))
  have hf : 𝚺ᴬ₁-Function₁ f := by unfold f; definability
  apply measured_bounded_sigma1_order_induction hm hf ?_ ?_ p
  · definability
  intro p ih hp
  rcases IsSemiformula.case_iff.mp hp with
    (⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩
      | rfl | rfl
      | ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, p₂, h₁, h₂, rfl⟩
      | ⟨p₁, h₁, rfl⟩ | ⟨p₁, h₁, rfl⟩)
  · exact hrel _ _ _ hR hv
  · exact hnrel _ _ _ hR hv
  · exact hverum
  · exact hfalsum
  · have ih₁ : P p₁ :=
      ih p₁ (by simp only [le_sup_iff, f]; left; exact le_of_lt <| by simp)
          (by simp [h₁.isUFormula, h₂.isUFormula]) h₁
    have ih₂ : P p₂ :=
      ih p₂ (by simp only [le_sup_iff, f]; left; exact le_of_lt <| by simp)
          (by simp [h₁.isUFormula, h₂.isUFormula]) h₂
    exact hand _ _ h₁ h₂ ih₁ ih₂
  · have ih₁ : P p₁ :=
      ih p₁ (by simp only [le_sup_iff, f]; left; exact le_of_lt <| by simp)
          (by simp [h₁.isUFormula, h₂.isUFormula]) h₁
    have ih₂ : P p₂ :=
      ih p₂ (by simp only [le_sup_iff, f]; left; exact le_of_lt <| by simp)
          (by simp [h₁.isUFormula, h₂.isUFormula]) h₂
    exact hor _ _ h₁ h₂ ih₁ ih₂
  · have h₁ : IsSemiformula L 2 p₁ := by simpa [one_add_one_eq_two] using h₁
    have hw : IsSemitermVec L 2 1 (?[^&(g (^∀ p₁)), ^#(0 : V)] : V) :=
      isSemitermVec_fvar_bvar _
    have h₂ : IsSemiformula L 1 (Bootstrapping.subst L ?[^&(g (^∀ p₁)), ^#(0 : V)] p₁) :=
      h₁.subst hw
    have : P (Bootstrapping.subst L ?[^&(g (^∀ p₁)), ^#(0 : V)] p₁) :=
      ih (Bootstrapping.subst L ?[^&(g (^∀ p₁)), ^#(0 : V)] p₁)
        (by simp only [le_sup_iff, f]; right; simp [qqAll])
        (by simp [fomulaComplexity_substs h₁ hw, h₁.isUFormula]) h₂
    exact hall _ h₁ this
  · have h₁ : IsSemiformula L 2 p₁ := by simpa [one_add_one_eq_two] using h₁
    have hw : IsSemitermVec L 2 1 (?[^&(g (^∃ p₁)), ^#(0 : V)] : V) :=
      isSemitermVec_fvar_bvar _
    have h₂ : IsSemiformula L 1 (Bootstrapping.subst L ?[^&(g (^∃ p₁)), ^#(0 : V)] p₁) :=
      h₁.subst hw
    have : P (Bootstrapping.subst L ?[^&(g (^∃ p₁)), ^#(0 : V)] p₁) :=
      ih (Bootstrapping.subst L ?[^&(g (^∃ p₁)), ^#(0 : V)] p₁)
        (by simp only [le_sup_iff, f]; right; simp [qqExs])
        (by simp [fomulaComplexity_substs h₁ hw, h₁.isUFormula]) h₂
    exact hexs _ h₁ this

lemma exists_map_qqConj {n : V} {f : V → V} [𝚺ᴬ₁-Function₁ f]
    (hand : ∀ p q, IsUFormula L p → IsUFormula L q → f (p ^⋏ q) = f p ^⋏ f q) (hverum : f ^⊤ = ^⊤)
    (ps : V) (hps : ∀ i < len ps, IsSemiformula L n ps.[i]) :
    ∃ qs, len qs = len ps ∧ (∀ i < len ps, qs.[i] = f ps.[i]) ∧ f (^⋀ ps) = ^⋀ qs := by
  revert hps
  induction ps using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => intro _; exact ⟨0, by simp [hverum]⟩
  case adjoin p ps ih =>
    intro hps
    have h₁ : IsSemiformula L n p := by simpa using hps 0 (by simp)
    have h₂ : ∀ i < len ps, IsSemiformula L n ps.[i] := by
      intro i hi
      simpa using hps (i + 1) (by simpa using hi)
    obtain ⟨qs, hlen, hq, hsh⟩ := ih h₂
    refine ⟨f p ∷ qs, by simp [hlen], fun i hi ↦ ?_, ?_⟩
    · rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
      · simp
      · simpa using hq i (by simpa using hi)
    · rw [qqConj_cons, qqConj_cons, hand p _ h₁.isUFormula (qqConj_semiformula.mpr h₂).isUFormula,
        hsh]

lemma shift_imp {n p q : V} (hp : IsSemiformula L n p) (hq : IsSemiformula L n q) :
    shift L (imp L p q) = imp L (shift L p) (shift L q) := by
  unfold imp
  rw [shift_or hp.isUFormula.neg hq.isUFormula, shift_neg hp]

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

lemma substs1_subst_fvar_bvar {t u q : V} (ht : IsSemiterm L 0 t) (hq : IsSemiformula L 2 q) :
    substs1 L t (subst L ?[^&u, ^#(0 : V)] q) =
      substs1 L (^&u) (subst L ?[^#(0 : V), t] q) := by
  have h₁ : IsSemitermVec L 2 1 (?[^&u, ^#(0 : V)] : V) := isSemitermVec_fvar_bvar u
  have h₂ : IsSemitermVec L 1 0 (?[t] : V) := by simp [ht]
  have h₃ : IsSemitermVec L 2 1 (?[^#(0 : V), t] : V) := by
    simp [IsSemiterm.of_zero ht]
  have h₄ : IsSemitermVec L 1 1 (?[^&u] : V) := by simp
  have h₅ : termSubstVec L 2 (?[t] : V) (?[^&u, ^#(0 : V)] : V) =
      termSubstVec L 2 (?[^&u] : V) (?[^#(0 : V), t] : V) := by
    simp [termSubstVec_cons₂ (t₁ := ^#(0 : V)) (by simp) ht.isUTerm, termSubst_zero ht]
  unfold substs1
  rw [substs_substs hq h₂ h₁, substs_substs hq h₄ h₃, h₅]

lemma subst_iff {m w p q : V} (hp : IsSemiformula L 1 p) (hq : IsSemiformula L 1 q)
    (hw : IsSemitermVec L 1 m w) :
    subst L w (iff L p q) = iff L (subst L w p) (subst L w q) := by
  have hpq : IsUFormula L (neg L p ^⋎ q) := (IsSemiformula.imp.mpr ⟨hp, hq⟩).isUFormula
  have hqp : IsUFormula L (neg L q ^⋎ p) := (IsSemiformula.imp.mpr ⟨hq, hp⟩).isUFormula
  unfold iff imp
  rw [substs_and hpq hqp, substs_or hp.isUFormula.neg hq.isUFormula,
    substs_or hq.isUFormula.neg hp.isUFormula, substs_neg hp hw, substs_neg hq hw]

lemma substs1_and {t p q : V} (hp : IsSemiformula L 1 p) (hq : IsSemiformula L 1 q) :
    substs1 L t (p ^⋏ q) = substs1 L t p ^⋏ substs1 L t q := by
  unfold substs1
  exact substs_and hp.isUFormula hq.isUFormula

lemma substs1_or {t p q : V} (hp : IsSemiformula L 1 p) (hq : IsSemiformula L 1 q) :
    substs1 L t (p ^⋎ q) = substs1 L t p ^⋎ substs1 L t q := by
  unfold substs1
  exact substs_or hp.isUFormula hq.isUFormula

lemma pi2_qqAll_sub_one (q : V) : π₂ ((^∀ q) - 1) = q := by
  simp [qqAll]

lemma pi2_qqExs_sub_one (q : V) : π₂ ((^∃ q) - 1) = q := by
  simp [qqExs]

lemma shift_substs1_qqFvar {p j : V} (hp : IsSemiformula L 1 p) :
    shift L (substs1 L (^&j) p) = substs1 L (^&(j + 1)) (shift L p) := by
  have hv : IsSemitermVec L 1 (0 : V) ?[^&j] := by simp
  rw [substs1, shift_substs hp hv]
  congr 1
  apply nth_ext' 1 (by simp) (by simp)
  intro i hi
  rcases (show i = 0 by simpa using hi)
  simp

lemma shift_neg_substs1_qqFvar {d j : V} (hd : IsSemiformula L 1 d) (hds : shift L d = d) :
    shift L (neg L (substs1 L (^&j) d)) = neg L (substs1 L (^&(j + 1)) d) := by
  rw [shift_neg (IsSemiformula.substs1 (n := 0) (by simp) hd), shift_substs1_qqFvar hd, hds]

section fvfree

variable (L)

/-- The coded formula `p` is a semiformula with `n` bound variables and no free variables. -/
def _root_.FFL.FirstOrder.Language.IsFVFree (n p : V) : Prop :=
  IsSemiformula L n p ∧ shift L p = p

noncomputable def isFVFree : 𝚺ᴬ₁.Semisentence 2 :=
  .mkSigma “n p. !(isSemiformula L).sigma n p ∧ !(shiftGraph L) p p”

instance _root_.FFL.FirstOrder.Language.IsFVFree.defined :
    𝚺ᴬ₁-Relation (L.IsFVFree (V := V)) via isFVFree L := .mk fun v ↦ by
  simp [isFVFree, Bounding.HierarchySymbol.Semiformula.val_sigma, IsSemiformula.defined.iff,
    shift.defined.iff, Language.IsFVFree, eq_comm]

instance _root_.FFL.FirstOrder.Language.IsFVFree.definable :
    𝚺ᴬ₁-Relation (L.IsFVFree (V := V)) :=
  (Language.IsFVFree.defined (L := L) (V := V)).to_definable

variable {L}

lemma _root_.FFL.FirstOrder.Language.IsFVFree.isSemiformula {n p : V}
    (h : L.IsFVFree n p) : IsSemiformula L n p := h.1

lemma _root_.FFL.FirstOrder.Language.IsFVFree.shift_eq {n p : V}
    (h : L.IsFVFree n p) : shift L p = p := h.2

@[simp] lemma _root_.FFL.FirstOrder.Language.IsFVFree.verum (n : V) :
    L.IsFVFree n ^⊤ := by
  simp [Language.IsFVFree]

@[simp] lemma _root_.FFL.FirstOrder.Language.IsFVFree.falsum (n : V) :
    L.IsFVFree n ^⊥ := by
  simp [Language.IsFVFree]

lemma _root_.FFL.FirstOrder.Language.IsFVFree.and {n p q : V}
    (hp : L.IsFVFree n p) (hq : L.IsFVFree n q) : L.IsFVFree n (p ^⋏ q) := by
  rw [Language.IsFVFree, shift_and hp.isSemiformula.isUFormula hq.isSemiformula.isUFormula,
    hp.shift_eq, hq.shift_eq]
  simp [hp.isSemiformula, hq.isSemiformula]

lemma _root_.FFL.FirstOrder.Language.IsFVFree.or {n p q : V}
    (hp : L.IsFVFree n p) (hq : L.IsFVFree n q) : L.IsFVFree n (p ^⋎ q) := by
  rw [Language.IsFVFree, shift_or hp.isSemiformula.isUFormula hq.isSemiformula.isUFormula,
    hp.shift_eq, hq.shift_eq]
  simp [hp.isSemiformula, hq.isSemiformula]

lemma _root_.FFL.FirstOrder.Language.IsFVFree.all {n p : V}
    (hp : L.IsFVFree (n + 1) p) : L.IsFVFree n (^∀ p) := by
  rw [Language.IsFVFree, shift_all hp.isSemiformula.isUFormula, hp.shift_eq]
  simp [hp.isSemiformula]

lemma _root_.FFL.FirstOrder.Language.IsFVFree.exs {n p : V}
    (hp : L.IsFVFree (n + 1) p) : L.IsFVFree n (^∃ p) := by
  rw [Language.IsFVFree, shift_exs hp.isSemiformula.isUFormula, hp.shift_eq]
  simp [hp.isSemiformula]

@[simp] lemma _root_.FFL.FirstOrder.Language.IsFVFree.neg_iff {n p : V} :
    L.IsFVFree n (neg L p) ↔ L.IsFVFree n p := by
  constructor
  · intro h
    have hp : IsSemiformula L n p := IsSemiformula.neg_iff.mp h.isSemiformula
    have : shift L (neg L p) = neg L p := h.shift_eq
    rw [shift_neg hp, neg_inj_iff hp.shift.isUFormula hp.isUFormula] at this
    exact ⟨hp, this⟩
  · intro h
    exact ⟨by simp [h.isSemiformula], by rw [shift_neg h.isSemiformula, h.shift_eq]⟩

end fvfree

end Bootstrapping
end FFL.FirstOrder.Arithmetic
