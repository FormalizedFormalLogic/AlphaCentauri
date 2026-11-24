module

public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Coding
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Term.Functions
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.FreeVariables

/-!
# Functions on formula codes

Negation has no fixed point on coded formulas, and the shift of free variables does not decrease
the code of a formula. A substitution instance `subst w p` of a coded formula `p`, and likewise its
shift `shift p`, has the same outermost connective as `p`. Substituting into a coded formula with
`m` bound variables depends only on the first `m` entries of the vector. Structural induction on
one-variable formulas instantiates the quantifier case by a free variable. A coded sentence is a
coded semiformula without free variables, and the class of coded sentences with `n` bound variables
is closed under the connectives.

The shift of free variables and the substitution of terms without bound variables pass through a
block `qqAlls p k` of universal quantifiers. `qqExss p k` is a block of `k` existential
quantifiers; instantiating its outermost quantifier by a closed term instantiates the outermost
bound variable.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic
namespace Bootstrapping

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]
variable {d j k m n p q q₁ q₂ r t u v w R Z : V}

/-! ## Connectives, substitution and shift -/

lemma neg_ne_self (hp : IsUFormula L p) : neg L p ≠ p := by
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
lemma le_shift (hp : IsSemiformula L n p) : p ≤ shift L p := by
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

lemma subst_subst_qVec_fvarVec (hZ : IsSemiformula ℒₒᵣ (m + 1) Z) (ht : IsSemiterm ℒₒᵣ 2 t) :
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

lemma substs1_subst_qVec (hw : IsSemitermVec L j 0 w)
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

lemma subst_congr (hp : IsSemiformula L m p) {k' w' : V}
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

attribute [local simp] substs_rel substs_nrel substs_verum substs_falsum substs_and substs_or
  substs_all substs_ex

lemma exists_eq_or_of_subst_eq (hp : IsUFormula L p) (h : subst L w p = q₁ ^⋎ q₂) :
    ∃ p₁ p₂, p = p₁ ^⋎ p₂ ∧ subst L w p₁ = q₁ ∧ subst L w p₂ = q₂ := by
  rcases hp.case with (⟨k', R', v', hR, hv, rfl⟩ | ⟨k', R', v', hR, hv, rfl⟩ | rfl | rfl |
    ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, hp₁, rfl⟩ | ⟨p₁, hp₁, rfl⟩) <;>
    simp_all
  all_goals simp_all [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs]

lemma exists_eq_and_of_subst_eq (hp : IsUFormula L p) (h : subst L w p = q₁ ^⋏ q₂) :
    ∃ p₁ p₂, p = p₁ ^⋏ p₂ ∧ subst L w p₁ = q₁ ∧ subst L w p₂ = q₂ := by
  rcases hp.case with (⟨k', R', v', hR, hv, rfl⟩ | ⟨k', R', v', hR, hv, rfl⟩ | rfl | rfl |
    ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, hp₁, rfl⟩ | ⟨p₁, hp₁, rfl⟩) <;>
    simp_all
  all_goals simp_all [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs]

lemma exists_eq_all_of_subst_eq (hp : IsUFormula L p) (h : subst L w p = ^∀ q) :
    ∃ p₁, p = ^∀ p₁ ∧ subst L (qVec L w) p₁ = q := by
  rcases hp.case with (⟨k', R', v', hR, hv, rfl⟩ | ⟨k', R', v', hR, hv, rfl⟩ | rfl | rfl |
    ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, hp₁, rfl⟩ | ⟨p₁, hp₁, rfl⟩) <;>
    simp_all
  all_goals simp_all [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs]

lemma exists_eq_exs_of_subst_eq (hp : IsUFormula L p) (h : subst L w p = ^∃ q) :
    ∃ p₁, p = ^∃ p₁ ∧ subst L (qVec L w) p₁ = q := by
  rcases hp.case with (⟨k', R', v', hR, hv, rfl⟩ | ⟨k', R', v', hR, hv, rfl⟩ | rfl | rfl |
    ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, hp₁, rfl⟩ | ⟨p₁, hp₁, rfl⟩) <;>
    simp_all
  all_goals simp_all [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs]

lemma exists_eq_rel_of_subst_eq (hp : IsUFormula L p) (h : subst L w p = ^rel k R v) :
    ∃ v', IsUTermVec L k v' ∧ p = ^rel k R v' ∧ termSubstVec L k w v' = v := by
  rcases hp.case with (⟨k', R', v', hR, hv, rfl⟩ | ⟨k', R', v', hR, hv, rfl⟩ | rfl | rfl |
    ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, hp₁, rfl⟩ | ⟨p₁, hp₁, rfl⟩)
  case inl =>
    rw [substs_rel hR hv, qqRel_inj] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨v', hv, rfl, rfl⟩
  all_goals simp_all
  all_goals simp_all [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs]

lemma exists_eq_nrel_of_subst_eq (hp : IsUFormula L p) (h : subst L w p = ^nrel k R v) :
    ∃ v', IsUTermVec L k v' ∧ p = ^nrel k R v' ∧ termSubstVec L k w v' = v := by
  rcases hp.case with (⟨k', R', v', hR, hv, rfl⟩ | ⟨k', R', v', hR, hv, rfl⟩ | rfl | rfl |
    ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, hp₁, rfl⟩ | ⟨p₁, hp₁, rfl⟩)
  case inr.inl =>
    rw [substs_nrel hR hv, qqNRel_inj] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨v', hv, rfl, rfl⟩
  all_goals simp_all
  all_goals simp_all [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs]

lemma exists_eq_or_of_shift_eq (hp : IsUFormula L p) (h : shift L p = q₁ ^⋎ q₂) :
    ∃ p₁ p₂, p = p₁ ^⋎ p₂ ∧ shift L p₁ = q₁ ∧ shift L p₂ = q₂ := by
  rcases hp.case with (⟨k', R', v', hR, hv, rfl⟩ | ⟨k', R', v', hR, hv, rfl⟩ | rfl | rfl |
    ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, hp₁, rfl⟩ | ⟨p₁, hp₁, rfl⟩) <;>
    simp_all
  all_goals simp_all [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs]

lemma exists_eq_and_of_shift_eq (hp : IsUFormula L p) (h : shift L p = q₁ ^⋏ q₂) :
    ∃ p₁ p₂, p = p₁ ^⋏ p₂ ∧ shift L p₁ = q₁ ∧ shift L p₂ = q₂ := by
  rcases hp.case with (⟨k', R', v', hR, hv, rfl⟩ | ⟨k', R', v', hR, hv, rfl⟩ | rfl | rfl |
    ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, hp₁, rfl⟩ | ⟨p₁, hp₁, rfl⟩) <;>
    simp_all
  all_goals simp_all [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs]

lemma exists_eq_all_of_shift_eq (hp : IsUFormula L p) (h : shift L p = ^∀ q) :
    ∃ p₁, p = ^∀ p₁ ∧ shift L p₁ = q := by
  rcases hp.case with (⟨k', R', v', hR, hv, rfl⟩ | ⟨k', R', v', hR, hv, rfl⟩ | rfl | rfl |
    ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, hp₁, rfl⟩ | ⟨p₁, hp₁, rfl⟩) <;>
    simp_all
  all_goals simp_all [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs]

lemma exists_eq_exs_of_shift_eq (hp : IsUFormula L p) (h : shift L p = ^∃ q) :
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

lemma exists_map_qqConj {f : V → V} [𝚺ᴬ₁-Function₁ f]
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

lemma shift_imp (hp : IsSemiformula L n p) (hq : IsSemiformula L n q) :
    shift L (imp L p q) = imp L (shift L p) (shift L q) := by
  unfold imp
  rw [shift_or hp.isUFormula.neg hq.isUFormula, shift_neg hp]

lemma subst_eq_self_of_le (hp : IsSemiformula L m p) (hw : IsUTermVec L k w)
    (hk : m ≤ k) (H : ∀ i < m, w.[i] = ^#i) : subst L w p = p := by
  have h₁ : IsSemitermVec L m m (bvarVec 0 m) := IsSemitermVec.bvarVec (by simp)
  calc subst L w p = subst L (bvarVec 0 m) p := by
        apply subst_congr hp hw h₁.isUTerm hk le_rfl
        intro i hi
        rw [H i hi, nth_bvarVec _ _ _ hi, zero_add]
    _ = p := subst_eq_self hp h₁ fun i hi ↦ by rw [nth_bvarVec _ _ _ hi, zero_add]

lemma subst_imp (hw : IsSemitermVec L n m w) (hp : IsSemiformula L n p)
    (hq : IsSemiformula L n q) : subst L w (imp L p q) = imp L (subst L w p) (subst L w q) := by
  unfold imp
  rw [substs_or hp.isUFormula.neg hq.isUFormula, substs_neg hp hw]

lemma substs1_subst_fvar_bvar (ht : IsSemiterm L 0 t) (hq : IsSemiformula L 2 q) :
    substs1 L t (subst L ?[^&u, ^#(0 : V)] q) = substs1 L (^&u) (subst L ?[^#(0 : V), t] q) := by
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

lemma subst_iff (hp : IsSemiformula L 1 p) (hq : IsSemiformula L 1 q) (hw : IsSemitermVec L 1 m w) :
    subst L w (iff L p q) = iff L (subst L w p) (subst L w q) := by
  have hpq : IsUFormula L (neg L p ^⋎ q) := (IsSemiformula.imp.mpr ⟨hp, hq⟩).isUFormula
  have hqp : IsUFormula L (neg L q ^⋎ p) := (IsSemiformula.imp.mpr ⟨hq, hp⟩).isUFormula
  unfold iff imp
  rw [substs_and hpq hqp, substs_or hp.isUFormula.neg hq.isUFormula,
    substs_or hq.isUFormula.neg hp.isUFormula, substs_neg hp hw, substs_neg hq hw]

lemma substs1_and (hp : IsSemiformula L 1 p) (hq : IsSemiformula L 1 q) :
    substs1 L t (p ^⋏ q) = substs1 L t p ^⋏ substs1 L t q := by
  unfold substs1
  exact substs_and hp.isUFormula hq.isUFormula

lemma substs1_or (hp : IsSemiformula L 1 p) (hq : IsSemiformula L 1 q) :
    substs1 L t (p ^⋎ q) = substs1 L t p ^⋎ substs1 L t q := by
  unfold substs1
  exact substs_or hp.isUFormula hq.isUFormula

lemma pi2_qqAll_sub_one (q : V) : π₂ ((^∀ q) - 1) = q := by
  simp [qqAll]

lemma pi2_qqExs_sub_one (q : V) : π₂ ((^∃ q) - 1) = q := by
  simp [qqExs]

lemma shift_substs1_qqFvar (hp : IsSemiformula L 1 p) :
    shift L (substs1 L (^&j) p) = substs1 L (^&(j + 1)) (shift L p) := by
  have hv : IsSemitermVec L 1 (0 : V) ?[^&j] := by simp
  rw [substs1, shift_substs hp hv]
  congr 1
  apply nth_ext' 1 (by simp) (by simp)
  intro i hi
  rcases (show i = 0 by simpa using hi)
  simp

section sentence

variable (L)

/-- `p` codes a semisentence: a semiformula with `n` bound variables and no free variables. -/
def _root_.FFL.FirstOrder.Language.IsSemisentence (n p : V) : Prop :=
  IsSemiformula L n p ∧ freeVariables L p = ∅

/-- `p` codes a sentence: a formula with neither bound nor free variables left over. -/
abbrev _root_.FFL.FirstOrder.Language.IsSentence (p : V) : Prop := L.IsSemisentence 0 p

noncomputable def isSemisentence : 𝚫ᴬ₁.Semisentence 2 := .mkDelta
  (.mkSigma “n p. !(isSemiformula L).sigma n p ∧ !(freeVariablesGraph L) 0 p”)
  (.mkPi “n p. !(isSemiformula L).pi n p ∧ ∀ y, !(freeVariablesGraph L) y p → y = 0”)

instance _root_.FFL.FirstOrder.Language.IsSemisentence.defined :
    𝚫ᴬ₁-Relation (L.IsSemisentence (V := V)) via isSemisentence L := .mk <| by
  constructor
  · intro v
    simp [isSemisentence, Bounding.HierarchySymbol.Semiformula.val_sigma, IsSemiformula.defined.iff,
      freeVariables.defined.iff, eq_comm]
  · intro v
    simp [isSemisentence, Bounding.HierarchySymbol.Semiformula.val_sigma, IsSemiformula.defined.iff,
      freeVariables.defined.iff, Language.IsSemisentence, emptyset_def, eq_comm]

instance _root_.FFL.FirstOrder.Language.IsSemisentence.definable :
    𝚫ᴬ₁-Relation (L.IsSemisentence (V := V)) :=
  (Language.IsSemisentence.defined (L := L) (V := V)).to_definable

instance _root_.FFL.FirstOrder.Language.IsSemisentence.definable' {m : ℕ} {Γ : SigmaPiDelta} :
    Γᴬ_[m + 1]-Relation (L.IsSemisentence (V := V)) :=
  (Language.IsSemisentence.definable (L := L) (V := V)).of_deltaOne

noncomputable def isSentence : 𝚫ᴬ₁.Semisentence 1 := .mkDelta
  (.mkSigma “p. !(isSemisentence L).sigma 0 p”)
  (.mkPi “p. !(isSemisentence L).pi 0 p”)

variable {L}

instance _root_.FFL.FirstOrder.Language.IsSentence.defined :
    𝚫ᴬ₁-Predicate (L.IsSentence (V := V)) via isSentence L := .mk <| by
  constructor
  · intro v
    simp [isSentence, Bounding.HierarchySymbol.Semiformula.val_sigma]
  · intro v
    simp [isSentence, Bounding.HierarchySymbol.Semiformula.val_sigma]

lemma isSentence_sigma_iff (p : V) : V ⊧/![p] (isSentence L).sigma.val ↔ L.IsSentence p := by
  simp [isSentence, Bounding.HierarchySymbol.Semiformula.val_sigma]

lemma _root_.FFL.FirstOrder.Language.IsSemisentence.isSemiformula
    (h : L.IsSemisentence n p) : IsSemiformula L n p := h.1

lemma _root_.FFL.FirstOrder.Language.IsSemisentence.freeVariables_eq
    (h : L.IsSemisentence n p) : freeVariables L p = ∅ := h.2

lemma _root_.FFL.FirstOrder.Language.IsSemisentence.shift_eq (h : L.IsSemisentence n p) :
    shift L p = p :=
  (shift_eq_self_iff h.isSemiformula.isUFormula).mpr h.freeVariables_eq

lemma _root_.FFL.FirstOrder.Language.IsSemisentence.of_shift_eq
    (hp : IsSemiformula L n p) (h : shift L p = p) : L.IsSemisentence n p :=
  ⟨hp, (shift_eq_self_iff hp.isUFormula).mp h⟩

@[simp]
lemma _root_.FFL.FirstOrder.Language.IsSemisentence.quote {n : ℕ} (σ : Semisentence L n) :
    L.IsSemisentence (n : V) ⌜σ⌝ :=
  .of_shift_eq (Sentence.quote_isSemiformula σ) (Semisentence.shift_quote σ)

lemma _root_.FFL.FirstOrder.Language.IsSemisentence.sound {n p : ℕ} (h : L.IsSemisentence n p) :
    ∃ σ : Semisentence L n, ⌜σ⌝ = p := by
  obtain ⟨φ, rfl⟩ := IsSemiformula.sound h.isSemiformula
  have h₁ : Rewriting.shift φ = φ := by simpa [← Semiformula.quote_shift] using h.shift_eq
  use φ.toEmpty (Semiformula.freeVariables_eq_empty_of_shift_eq h₁)
  simp [Sentence.quote_def]

/-- A standard element coding a semisentence is the code of one. -/
lemma _root_.FFL.FirstOrder.Language.IsSemisentence.sound_natCast {n p : ℕ}
    (h : L.IsSemisentence (n : V) p) : ∃ σ : Semisentence L n, ⌜σ⌝ = p :=
  Language.IsSemisentence.sound <| (Defined.shigmaOne_absolute V (Language.IsSemisentence.defined L)
    (Language.IsSemisentence.defined L) ![n, p]).mpr h

@[simp]
lemma _root_.FFL.FirstOrder.Language.IsSentence.quote (σ : Sentence L) :
    L.IsSentence (⌜σ⌝ : V) :=
  .of_shift_eq (Sentence.quote_isSemiformula₀ σ) (Semisentence.shift_quote σ)

@[simp]
lemma _root_.FFL.FirstOrder.Language.IsSemisentence.verum (n : V) : L.IsSemisentence n ^⊤ := by
  simp [Language.IsSemisentence]

@[simp]
lemma _root_.FFL.FirstOrder.Language.IsSemisentence.falsum (n : V) : L.IsSemisentence n ^⊥ := by
  simp [Language.IsSemisentence]

@[simp]
lemma _root_.FFL.FirstOrder.Language.IsSemisentence.and_iff :
    L.IsSemisentence n (p ^⋏ q) ↔ L.IsSemisentence n p ∧ L.IsSemisentence n q := by
  constructor
  · intro h
    obtain ⟨hp, hq⟩ := IsSemiformula.and.mp h.isSemiformula
    have hs := h.shift_eq
    rw [shift_and hp.isUFormula hq.isUFormula, qqAnd_inj] at hs
    exact ⟨.of_shift_eq hp hs.1, .of_shift_eq hq hs.2⟩
  · rintro ⟨hp, hq⟩
    apply Language.IsSemisentence.of_shift_eq
    · simp [hp.isSemiformula, hq.isSemiformula]
    · rw [shift_and hp.isSemiformula.isUFormula hq.isSemiformula.isUFormula,
        hp.shift_eq, hq.shift_eq]

@[simp]
lemma _root_.FFL.FirstOrder.Language.IsSemisentence.or_iff :
    L.IsSemisentence n (p ^⋎ q) ↔ L.IsSemisentence n p ∧ L.IsSemisentence n q := by
  constructor
  · intro h
    obtain ⟨hp, hq⟩ := IsSemiformula.or.mp h.isSemiformula
    have hs := h.shift_eq
    rw [shift_or hp.isUFormula hq.isUFormula, qqOr_inj] at hs
    exact ⟨.of_shift_eq hp hs.1, .of_shift_eq hq hs.2⟩
  · rintro ⟨hp, hq⟩
    apply Language.IsSemisentence.of_shift_eq
    · simp [hp.isSemiformula, hq.isSemiformula]
    · rw [shift_or hp.isSemiformula.isUFormula hq.isSemiformula.isUFormula,
        hp.shift_eq, hq.shift_eq]

@[simp]
lemma _root_.FFL.FirstOrder.Language.IsSemisentence.all_iff :
    L.IsSemisentence n (^∀ p) ↔ L.IsSemisentence (n + 1) p := by
  simp only [Language.IsSemisentence, IsSemiformula.all]
  apply and_congr_right
  intro hp
  rw [freeVariables_all hp.isUFormula]

@[simp]
lemma _root_.FFL.FirstOrder.Language.IsSemisentence.exs_iff :
    L.IsSemisentence n (^∃ p) ↔ L.IsSemisentence (n + 1) p := by
  simp only [Language.IsSemisentence, IsSemiformula.exs]
  apply and_congr_right
  intro hp
  rw [freeVariables_exs hp.isUFormula]

@[simp]
lemma _root_.FFL.FirstOrder.Language.IsSemisentence.neg_iff :
    L.IsSemisentence n (neg L p) ↔ L.IsSemisentence n p := by
  constructor
  · intro h
    have hp : IsSemiformula L n p := IsSemiformula.neg_iff.mp h.isSemiformula
    exact ⟨hp, by rw [← freeVariables_neg hp.isUFormula]; exact h.freeVariables_eq⟩
  · intro h
    exact ⟨by simp [h.isSemiformula],
      by rw [freeVariables_neg h.isSemiformula.isUFormula]; exact h.freeVariables_eq⟩

end sentence

lemma shift_neg_substs1_qqFvar (hd : L.IsSemisentence 1 d) :
    shift L (neg L (substs1 L (^&j) d)) = neg L (substs1 L (^&(j + 1)) d) := by
  rw [shift_neg (IsSemiformula.substs1 (n := 0) (by simp) hd.isSemiformula),
    shift_substs1_qqFvar hd.isSemiformula, hd.shift_eq]

/-! ## Blocks of universal quantifiers -/

lemma shift_qqAlls (hp : IsUFormula L p) (k : V) : shift L (qqAlls p k) = qqAlls (shift L p) k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih => rw [qqAlls_succ, shift_all (isUFormula_qqAlls.mpr hp), ih, qqAlls_succ]

/-- Substituting terms `w` without bound variables for the outermost bound variables of a block of
`k` universal quantifiers: inside the block they become `w'`, which keeps the `k` variables bound
by the block and continues with `w`. -/
lemma subst_qqAlls {w' : V} (hw : IsSemitermVec L (len w) 0 w) (hp : IsUFormula L p)
    (hl : len w' = k + len w) (h₁ : ∀ i < k, w'.[i] = ^#i) (h₂ : ∀ i < len w, w'.[k + i] = w.[i]) :
    subst L w (qqAlls p k) = qqAlls (subst L w' p) k := by
  induction k using ISigma1.pi1_succ_induction generalizing p w'
  · definability
  case zero =>
    have : w' = w := nth_ext' (len w) (by simpa using hl) rfl fun i hi ↦ by simpa using h₂ i hi
    simp [this]
  case succ k ih =>
    obtain ⟨v, hvl, hv₁, hvk⟩ := exists_vec_bvar_append w k
    have hvu : IsUTermVec L (len v) v := ⟨rfl, fun i hi ↦ by
      rcases lt_or_ge i k with hik | hik
      · simp [hv₁ i hik]
      · obtain ⟨j, rfl⟩ := exists_add_of_le hik
        have hj : j < len w := by simpa [hvl] using hi
        simpa [hvk j hj] using (hw.nth hj).isUTerm⟩
    have hqv : qVec L v = w' := by
      apply nth_ext' (k + len w + 1) (by rw [len_qVec hvu, hvl]) (by rw [hl, add_right_comm])
      intro i hi
      rcases zero_or_succ i with rfl | ⟨i, rfl⟩
      · simp [qVec, h₁ 0 (by simp)]
      · have hi' : i < len v := by simpa [hvl] using hi
        rw [qVec, nth_adjoin_succ, nth_termBShiftVec hvu hi']
        rcases lt_or_ge i k with hik | hik
        · rw [hv₁ i hik, termBShift_bvar, h₁ (i + 1) (by simpa using hik)]
        · obtain ⟨j, rfl⟩ := exists_add_of_le hik
          have hj : j < len w := by simpa [hvl] using hi'
          rw [hvk j hj, termBShift_zero (hw.nth hj), ← h₂ j hj, add_right_comm]
    rw [qqAlls_succ', ih (by simpa using hp) hvl (fun i hi ↦ hv₁ i hi) hvk, substs_all hp,
      ← qqAlls_succ', hqv]

lemma free_qqAlls (hp : IsUFormula L p) (hl : len w = k + 1)
    (h₁ : ∀ i < k, w.[i] = ^#i) (h₂ : w.[k] = ^&0) :
    free L (qqAlls p k) = qqAlls (subst L w (shift L p)) k := by
  rw [free, substs1, shift_qqAlls hp]
  apply subst_qqAlls (by simp) hp.shift (by simpa using hl) h₁
  intro i hi
  obtain rfl : i = 0 := by simpa using hi
  simpa using h₂

/-! ## Blocks of existential quantifiers -/

def qqExss.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y x. y = x”
  succ := .mkSigma “y ih n x. !qqExsDef y ih”

noncomputable def qqExss.construction : PR.Construction V qqExss.blueprint where
  zero := fun x ↦ x 0
  succ := fun _ _ ih ↦ ^∃ ih
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint, qqExs]

/-- `qqExss p k = ^∃ ^∃ ⋯ ^∃ p`, with `k` existential quantifiers. -/
noncomputable def qqExss (p k : V) : V := qqExss.construction.result ![p] k

@[simp]
lemma qqExss_zero (p : V) : qqExss p 0 = p := by simp [qqExss, qqExss.construction]

@[simp]
lemma qqExss_succ (p k : V) : qqExss p (k + 1) = ^∃ (qqExss p k) := by
  simp [qqExss, qqExss.construction]

def _root_.FFL.FirstOrder.Arithmetic.qqExssDef : 𝚺ᴬ₁.Semisentence 3 :=
  qqExss.blueprint.resultDef |>.rew (Rew.subst ![#0, #2, #1])

instance qqExss.defined : 𝚺ᴬ₁-Function₂ (qqExss : V → V → V) via qqExssDef := .mk
  fun v ↦ by simp [qqExss.construction.result_defined_iff, qqExssDef]; rfl

instance qqExss.definable : 𝚺ᴬ₁-Function₂ (qqExss : V → V → V) := qqExss.defined.to_definable

instance qqExss.definable' {Γ : Polarity} {m : ℕ} :
    Γᴬ_[m + 1]-Function₂ (qqExss : V → V → V) := qqExss.definable.of_sigmaOne

lemma qqExss_exs (p k : V) : qqExss (^∃ p) k = ^∃ (qqExss p k) := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih => rw [qqExss_succ, ih, qqExss_succ]

lemma qqExss_succ' (p k : V) : qqExss p (k + 1) = qqExss (^∃ p) k := by
  rw [qqExss_succ, qqExss_exs]

@[simp]
lemma isUFormula_qqExss : IsUFormula L (qqExss p k) ↔ IsUFormula L p := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih => rw [qqExss_succ, IsUFormula.ex, ih]

lemma shift_qqExss (hp : IsUFormula L p) (k : V) : shift L (qqExss p k) = qqExss (shift L p) k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih => rw [qqExss_succ, shift_exs (isUFormula_qqExss.mpr hp), ih, qqExss_succ]

lemma neg_qqAlls (hp : IsUFormula L p) (k : V) : neg L (qqAlls p k) = qqExss (neg L p) k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    rw [qqAlls_succ, neg_all (isUFormula_qqAlls.mpr hp), ih, qqExss_succ]

lemma IsSemiformula.qqExss (h : IsSemiformula L (n + k) p) : IsSemiformula L n (qqExss p k) := by
  induction k using ISigma1.pi1_succ_induction generalizing n
  · definability
  case zero => simpa using h
  case succ k ih =>
    rw [qqExss_succ, IsSemiformula.exs]
    exact ih (by rwa [add_right_comm, add_assoc])

lemma qqExss_inj (hp : ∀ a, p ≠ ^∃ a) (hq : ∀ a, q ≠ ^∃ a)
    (h : qqExss p m = qqExss q n) : m = n ∧ p = q := by
  induction m using ISigma1.pi1_succ_induction generalizing n
  · definability
  case zero =>
    rcases zero_or_succ n with rfl | ⟨n, rfl⟩
    · simpa using h
    · exact absurd (by simpa using h) (hp _)
  case succ m ih =>
    rcases zero_or_succ n with rfl | ⟨n, rfl⟩
    · exact absurd (by simpa using h.symm) (hq _)
    · obtain ⟨rfl, rfl⟩ := ih (by simpa using h)
      exact ⟨rfl, rfl⟩

/-- Instantiating the outermost quantifier of `qqExss q r` with a closed term `t` instantiates the
outermost bound variable `^#r` of `q`, where `v` is the vector `^#0, …, ^#(r - 1), t`. -/
lemma substs1_qqExss {t q v r : V} (ht : IsSemiterm ℒₒᵣ 0 t) (hq : IsSemiformula ℒₒᵣ (r + 1) q)
    (hv : len v = r + 1) (hvb : ∀ i < r, v.[i] = ^#i) (hvr : v.[r] = t) :
    substs1 ℒₒᵣ t (qqExss q r) = qqExss (subst ℒₒᵣ v q) r := by
  induction r using ISigma1.pi1_succ_induction generalizing q v
  · definability
  case zero =>
    have : v = ?[t] := nth_ext' 1 (by simpa using hv) (by simp) (by
      intro i hi
      obtain rfl : i = 0 := by simpa using hi
      simpa using hvr)
    simp [substs1, this]
  case succ r ih =>
    obtain ⟨v', hv'l, hv'b, hv'r⟩ := exists_vec_bvar_term r t
    have hv'u : IsUTermVec ℒₒᵣ (r + 1) v' := by
      refine ⟨hv'l.symm, ?_⟩
      intro i hi
      rcases lt_or_eq_of_le (lt_succ_iff_le.mp hi) with hir | rfl
      · simp [hv'b i hir]
      · simpa [hv'r] using ht.isUTerm
    have hqv : qVec ℒₒᵣ v' = v := by
      apply nth_ext' (r + 1 + 1) (len_qVec hv'u) hv
      intro i hi
      rcases zero_or_succ i with rfl | ⟨i, rfl⟩
      · simp [qVec, hvb 0 (by simp)]
      · have hi : i < r + 1 := by simpa using hi
        rw [qVec, nth_adjoin_succ, hv'l, nth_termBShiftVec hv'u hi]
        rcases lt_or_eq_of_le (lt_succ_iff_le.mp hi) with hir | rfl
        · simp [hv'b i hir, hvb (i + 1) (by simpa using hir)]
        · rw [hv'r, termBShift_zero ht, hvr]
    rw [qqExss_succ', ih (by simpa using hq) hv'l hv'b hv'r, substs_ex hq.isUFormula, qqExss_exs,
      ← qqExss_succ, hqv]

lemma subst_qqAlls_vec (hw : IsSemitermVec L n m w) (hp : IsUFormula L p)
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
        · rw [nth_qVec_succ hv'.isUTerm (lt_of_lt_of_le hik le_add_self), hv'₁ i hik,
            termBShift_bvar, h₁ (i + 1) (by simpa using hik)]
        · obtain ⟨j, rfl⟩ := exists_add_of_le hik
          have hj : j < n := by
            have e : n + (k + 1) = k + (n + 1) := by rw [← add_assoc, add_comm n k, add_assoc]
            rw [hv.lh, e, add_assoc k j 1] at hi
            exact (add_lt_add_iff_right 1).mp ((add_lt_add_iff_left k).mp hi)
          have hkj : k + j < n + k := by
            rw [add_comm n k]
            exact (add_lt_add_iff_left k).mpr hj
          rw [nth_qVec_succ hv'.isUTerm hkj, hv'₂ j hj, termBShift_termSubst_bvarVec k (hw.nth hj),
            show k + j + 1 = k + 1 + j by simp only [add_assoc, add_comm, add_left_comm], h₂ j hj]
    rw [qqAlls_succ' p k, qqAlls_succ' (subst L v p) k,
      ih (IsUFormula.all.mpr hp) hv' hv'₁ hv'₂, substs_all hp, hqv]

end Bootstrapping
end FFL.FirstOrder.Arithmetic
