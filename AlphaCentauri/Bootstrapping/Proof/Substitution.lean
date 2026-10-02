module

public import AlphaCentauri.Bootstrapping.Proof.FvSubst
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.Basic

/-!
# Free-variable substitution on internal derivations

Foundation's internal one-sided calculus has no rule renaming free variables, and its
`allIntro` rule fixes `^&0` as the eigenvariable.  This module closes internal derivability
under the free-variable substitutions of `AlphaCentauri.Bootstrapping.Proof.FvSubst` and
derives from it the internal quantifier rules whose eigenvariable is an arbitrary fresh free
variable.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

open PeanoMinus ISigma0 ISigma1

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]
variable {T : Theory L} [T.Δ₁]

section image

@[simp] lemma fvSubstImage_empty (w : V) : fvSubstImage (L := L) w ∅ = ∅ :=
  mem_ext fun x ↦ by simp [mem_fvSubstImage_iff]

lemma fvSubstImage_insert (w p s : V) :
    fvSubstImage (L := L) w (insert p s) =
      insert (fvSubst L w p) (fvSubstImage (L := L) w s) :=
  mem_ext fun x ↦ by
    simp only [mem_fvSubstImage_iff, mem_bitInsert_iff]
    constructor
    · rintro ⟨q, (rfl | hq), rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨q, hq, rfl⟩
    · rintro (rfl | ⟨q, hq, rfl⟩)
      · exact ⟨p, Or.inl rfl, rfl⟩
      · exact ⟨q, Or.inr hq, rfl⟩

end image

/-- Internal derivability is closed under free-variable substitution by a vector of terms
without bound variables. -/
axiom Derivable.rewrite {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {L : Language} [L.Encodable] [L.LORDefinable] {T : Theory L} [T.Δ₁] {w s : V}
    (hw : IsSemitermVec L (len w) 0 w) (h : Derivable T s) :
    Derivable T (fvSubstImage (L := L) w s)

section eqShift

variable {u w : V}

/-- A substitution vector reaching past `u` and sending `^&x` to `^&(x + 1)` below `u` acts on
the terms coded by a number at most `u` as the shift of free variables. -/
lemma termFvSubst_eq_termShift (hu : u < len w) (hw : ∀ x < u, w.[x] = ^&(x + 1))
    {n t : V} (ht : IsSemiterm L n t) (h : t ≤ u) : termFvSubst L w t = termShift L t := by
  revert h
  apply IsSemiterm.induction 𝚷
    (P := fun t ↦ t ≤ u → termFvSubst L w t = termShift L t) ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z _ _; simp
  · intro x hx
    have hxu : x < u := lt_of_lt_of_le (by simp) hx
    rw [termFvSubst_fvar, ite_eq_left (lt_trans hxu hu), hw x hxu, termShift_fvar]
  · intro k f v hf hv ih hle
    rw [termFvSubst_func hf hv.isUTerm, termShift_func hf hv.isUTerm]
    refine congrArg _ (nth_ext' k (by simp [hv.isUTerm]) (by simp [hv.isUTerm]) fun i hi ↦ ?_)
    rw [nth_termFvSubstVec hv.isUTerm hi, nth_termShiftVec hv.isUTerm hi]
    exact ih i hi
      (le_of_lt <| lt_of_lt_of_le (nth_lt_qqFunc_of_lt (by rw [hv.lh]; exact hi)) hle)

/-- A substitution vector reaching past `u` and sending `^&x` to `^&(x + 1)` below `u` acts on
the formulas coded by a number at most `u` as the shift of free variables. -/
lemma fvSubst_eq_shift (hu : u < len w) (hw : ∀ x < u, w.[x] = ^&(x + 1))
    {n p : V} (hp : IsSemiformula L n p) (h : p ≤ u) : fvSubst L w p = shift L p := by
  revert h
  apply IsSemiformula.pi1_structural_induction
    (P := fun _ p ↦ p ≤ u → fvSubst L w p = shift L p) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R v hR hv hle
    rw [fvSubst_rel hR hv.isUTerm, shift_rel hR hv.isUTerm]
    refine congrArg _ (nth_ext' k (by simp [hv.isUTerm]) (by simp [hv.isUTerm]) fun i hi ↦ ?_)
    rw [nth_termFvSubstVec hv.isUTerm hi, nth_termShiftVec hv.isUTerm hi]
    exact termFvSubst_eq_termShift hu hw (hv.nth hi)
      (le_of_lt <| lt_of_lt_of_le (nth_lt_qqRel_of_lt (by rw [hv.lh]; exact hi)) hle)
  · intro n k R v hR hv hle
    rw [fvSubst_nrel hR hv.isUTerm, shift_nrel hR hv.isUTerm]
    refine congrArg _ (nth_ext' k (by simp [hv.isUTerm]) (by simp [hv.isUTerm]) fun i hi ↦ ?_)
    rw [nth_termFvSubstVec hv.isUTerm hi, nth_termShiftVec hv.isUTerm hi]
    exact termFvSubst_eq_termShift hu hw (hv.nth hi)
      (le_of_lt <| lt_of_lt_of_le (nth_lt_qqNRel_of_lt (by rw [hv.lh]; exact hi)) hle)
  · intro n _; simp
  · intro n _; simp
  · intro n p q hp hq ihp ihq hle
    rw [fvSubst_and hp.isUFormula hq.isUFormula, shift_and hp.isUFormula hq.isUFormula,
      ihp (le_of_lt <| lt_of_lt_of_le (by simp) hle),
      ihq (le_of_lt <| lt_of_lt_of_le (by simp) hle)]
  · intro n p q hp hq ihp ihq hle
    rw [fvSubst_or hp.isUFormula hq.isUFormula, shift_or hp.isUFormula hq.isUFormula,
      ihp (le_of_lt <| lt_of_lt_of_le (by simp) hle),
      ihq (le_of_lt <| lt_of_lt_of_le (by simp) hle)]
  · intro n p hp ih hle
    rw [fvSubst_all hp.isUFormula, shift_all hp.isUFormula,
      ih (le_of_lt <| lt_of_lt_of_le (by simp) hle)]
  · intro n p hp ih hle
    rw [fvSubst_exs hp.isUFormula, shift_exs hp.isUFormula,
      ih (le_of_lt <| lt_of_lt_of_le (by simp) hle)]

/-- A substitution vector reaching past `u` and sending `^&x` to `^&(x + 1)` below `u` acts on
a coded formula set bounded by `u` as `setShift`. -/
lemma fvSubstImage_eq_setShift (hu : u < len w) (hw : ∀ x < u, w.[x] = ^&(x + 1))
    {s : V} (hs : IsFormulaSet L s) (h : s ≤ u) :
    fvSubstImage (L := L) w s = setShift L s :=
  mem_ext fun x ↦ by
    simp only [mem_fvSubstImage_iff, mem_setShift_iff]
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q, hq, fvSubst_eq_shift hu hw (hs q hq) (le_of_lt <| lt_of_lt_of_le (lt_of_mem hq) h)⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q, hq,
        (fvSubst_eq_shift hu hw (hs q hq) (le_of_lt <| lt_of_lt_of_le (lt_of_mem hq) h)).symm⟩

end eqShift

section shiftComp

variable {u w v : V}

/-- If `v` sends `^&x` to the image of `^&(x + 1)` under `w` for every `x < u`, then substituting
by `w` after the shift of free variables is substituting by `v`, on the terms coded by a number
at most `u`. -/
lemma termFvSubst_termShift (hv : ∀ x < u, x < len v ∧ v.[x] = termFvSubst L w ^&(x + 1))
    {n t : V} (ht : IsSemiterm L n t) (h : t ≤ u) :
    termFvSubst L w (termShift L t) = termFvSubst L v t := by
  revert h
  apply IsSemiterm.induction 𝚷
    (P := fun t ↦ t ≤ u → termFvSubst L w (termShift L t) = termFvSubst L v t) ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z _ _; simp
  · intro x hx
    have hxu : x < u := lt_of_lt_of_le (by simp) hx
    rw [termShift_fvar, termFvSubst_fvar v, ite_eq_left (hv x hxu).1, (hv x hxu).2]
  · intro k f ts hf hts ih hle
    rw [termShift_func hf hts.isUTerm, termFvSubst_func hf hts.termShiftVec.isUTerm,
      termFvSubst_func hf hts.isUTerm]
    refine congrArg _ (nth_ext' k (by simp [hts.isUTerm]) (by simp [hts.isUTerm]) fun i hi ↦ ?_)
    rw [nth_termFvSubstVec hts.termShiftVec.isUTerm hi, nth_termShiftVec hts.isUTerm hi,
      nth_termFvSubstVec hts.isUTerm hi]
    exact ih i hi
      (le_of_lt <| lt_of_lt_of_le (nth_lt_qqFunc_of_lt (by rw [hts.lh]; exact hi)) hle)

/-- If `v` sends `^&x` to the image of `^&(x + 1)` under `w` for every `x < u`, then substituting
by `w` after the shift of free variables is substituting by `v`, on the formulas coded by a number
at most `u`. -/
lemma fvSubst_shift (hv : ∀ x < u, x < len v ∧ v.[x] = termFvSubst L w ^&(x + 1))
    {n p : V} (hp : IsSemiformula L n p) (h : p ≤ u) :
    fvSubst L w (shift L p) = fvSubst L v p := by
  revert h
  apply IsSemiformula.pi1_structural_induction
    (P := fun _ p ↦ p ≤ u → fvSubst L w (shift L p) = fvSubst L v p)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R ts hR hts hle
    rw [shift_rel hR hts.isUTerm, fvSubst_rel hR hts.termShiftVec.isUTerm,
      fvSubst_rel hR hts.isUTerm]
    refine congrArg _ (nth_ext' k (by simp [hts.isUTerm]) (by simp [hts.isUTerm]) fun i hi ↦ ?_)
    rw [nth_termFvSubstVec hts.termShiftVec.isUTerm hi, nth_termShiftVec hts.isUTerm hi,
      nth_termFvSubstVec hts.isUTerm hi]
    exact termFvSubst_termShift hv (hts.nth hi)
      (le_of_lt <| lt_of_lt_of_le (nth_lt_qqRel_of_lt (by rw [hts.lh]; exact hi)) hle)
  · intro n k R ts hR hts hle
    rw [shift_nrel hR hts.isUTerm, fvSubst_nrel hR hts.termShiftVec.isUTerm,
      fvSubst_nrel hR hts.isUTerm]
    refine congrArg _ (nth_ext' k (by simp [hts.isUTerm]) (by simp [hts.isUTerm]) fun i hi ↦ ?_)
    rw [nth_termFvSubstVec hts.termShiftVec.isUTerm hi, nth_termShiftVec hts.isUTerm hi,
      nth_termFvSubstVec hts.isUTerm hi]
    exact termFvSubst_termShift hv (hts.nth hi)
      (le_of_lt <| lt_of_lt_of_le (nth_lt_qqNRel_of_lt (by rw [hts.lh]; exact hi)) hle)
  · intro n _; simp
  · intro n _; simp
  · intro n p q hp hq ihp ihq hle
    rw [shift_and hp.isUFormula hq.isUFormula,
      fvSubst_and hp.shift.isUFormula hq.shift.isUFormula, fvSubst_and hp.isUFormula hq.isUFormula,
      ihp (le_of_lt <| lt_of_lt_of_le (by simp) hle),
      ihq (le_of_lt <| lt_of_lt_of_le (by simp) hle)]
  · intro n p q hp hq ihp ihq hle
    rw [shift_or hp.isUFormula hq.isUFormula,
      fvSubst_or hp.shift.isUFormula hq.shift.isUFormula, fvSubst_or hp.isUFormula hq.isUFormula,
      ihp (le_of_lt <| lt_of_lt_of_le (by simp) hle),
      ihq (le_of_lt <| lt_of_lt_of_le (by simp) hle)]
  · intro n p hp ih hle
    rw [shift_all hp.isUFormula, fvSubst_all hp.shift.isUFormula, fvSubst_all hp.isUFormula,
      ih (le_of_lt <| lt_of_lt_of_le (by simp) hle)]
  · intro n p hp ih hle
    rw [shift_exs hp.isUFormula, fvSubst_exs hp.shift.isUFormula, fvSubst_exs hp.isUFormula,
      ih (le_of_lt <| lt_of_lt_of_le (by simp) hle)]

/-- If `v` sends `^&x` to the image of `^&(x + 1)` under `w` for every `x < u`, then the image
under `w` of the shift of a coded formula set bounded by `u` is its image under `v`. -/
lemma fvSubstImage_setShift (hv : ∀ x < u, x < len v ∧ v.[x] = termFvSubst L w ^&(x + 1))
    {s : V} (hs : IsFormulaSet L s) (h : s ≤ u) :
    fvSubstImage (L := L) w (setShift L s) = fvSubstImage (L := L) v s :=
  mem_ext fun x ↦ by
    constructor
    · intro hx
      obtain ⟨_, hy, rfl⟩ := mem_fvSubstImage_iff.mp hx
      obtain ⟨q, hq, rfl⟩ := mem_setShift_iff.mp hy
      exact mem_fvSubstImage_iff.mpr
        ⟨q, hq, fvSubst_shift hv (hs q hq) (le_of_lt <| lt_of_lt_of_le (lt_of_mem hq) h)⟩
    · intro hx
      obtain ⟨q, hq, rfl⟩ := mem_fvSubstImage_iff.mp hx
      exact mem_fvSubstImage_iff.mpr ⟨shift L q, shift_mem_setShift hq,
        (fvSubst_shift hv (hs q hq) (le_of_lt <| lt_of_lt_of_le (lt_of_mem hq) h)).symm⟩

/-- A substitution vector sending `^&x` to itself for every `x < u` fixes the terms coded by a
number at most `u`. -/
lemma termFvSubst_eq_self (hv : ∀ x < u, x < len v ∧ v.[x] = ^&x)
    {n t : V} (ht : IsSemiterm L n t) (h : t ≤ u) : termFvSubst L v t = t := by
  revert h
  apply IsSemiterm.induction 𝚷 (P := fun t ↦ t ≤ u → termFvSubst L v t = t) ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z _ _; simp
  · intro x hx
    have hxu : x < u := lt_of_lt_of_le (by simp) hx
    rw [termFvSubst_fvar, ite_eq_left (hv x hxu).1, (hv x hxu).2]
  · intro k f ts hf hts ih hle
    rw [termFvSubst_func hf hts.isUTerm]
    refine congrArg _ (nth_ext' k (by simp [hts.isUTerm]) hts.lh fun i hi ↦ ?_)
    rw [nth_termFvSubstVec hts.isUTerm hi]
    exact ih i hi
      (le_of_lt <| lt_of_lt_of_le (nth_lt_qqFunc_of_lt (by rw [hts.lh]; exact hi)) hle)

/-- A substitution vector sending `^&x` to itself for every `x < u` fixes the formulas coded by a
number at most `u`. -/
lemma fvSubst_eq_self (hv : ∀ x < u, x < len v ∧ v.[x] = ^&x)
    {n p : V} (hp : IsSemiformula L n p) (h : p ≤ u) : fvSubst L v p = p := by
  revert h
  apply IsSemiformula.pi1_structural_induction (P := fun _ p ↦ p ≤ u → fvSubst L v p = p)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R ts hR hts hle
    rw [fvSubst_rel hR hts.isUTerm]
    refine congrArg _ (nth_ext' k (by simp [hts.isUTerm]) hts.lh fun i hi ↦ ?_)
    rw [nth_termFvSubstVec hts.isUTerm hi]
    exact termFvSubst_eq_self hv (hts.nth hi)
      (le_of_lt <| lt_of_lt_of_le (nth_lt_qqRel_of_lt (by rw [hts.lh]; exact hi)) hle)
  · intro n k R ts hR hts hle
    rw [fvSubst_nrel hR hts.isUTerm]
    refine congrArg _ (nth_ext' k (by simp [hts.isUTerm]) hts.lh fun i hi ↦ ?_)
    rw [nth_termFvSubstVec hts.isUTerm hi]
    exact termFvSubst_eq_self hv (hts.nth hi)
      (le_of_lt <| lt_of_lt_of_le (nth_lt_qqNRel_of_lt (by rw [hts.lh]; exact hi)) hle)
  · intro n _; simp
  · intro n _; simp
  · intro n p q hp hq ihp ihq hle
    rw [fvSubst_and hp.isUFormula hq.isUFormula,
      ihp (le_of_lt <| lt_of_lt_of_le (by simp) hle),
      ihq (le_of_lt <| lt_of_lt_of_le (by simp) hle)]
  · intro n p q hp hq ihp ihq hle
    rw [fvSubst_or hp.isUFormula hq.isUFormula,
      ihp (le_of_lt <| lt_of_lt_of_le (by simp) hle),
      ihq (le_of_lt <| lt_of_lt_of_le (by simp) hle)]
  · intro n p hp ih hle
    rw [fvSubst_all hp.isUFormula, ih (le_of_lt <| lt_of_lt_of_le (by simp) hle)]
  · intro n p hp ih hle
    rw [fvSubst_exs hp.isUFormula, ih (le_of_lt <| lt_of_lt_of_le (by simp) hle)]

/-- A substitution vector sending `^&x` to itself for every `x < u` fixes a coded formula set
bounded by `u`. -/
lemma fvSubstImage_eq_self (hv : ∀ x < u, x < len v ∧ v.[x] = ^&x)
    {s : V} (hs : IsFormulaSet L s) (h : s ≤ u) : fvSubstImage (L := L) v s = s :=
  mem_ext fun x ↦ by
    constructor
    · intro hx
      obtain ⟨q, hq, rfl⟩ := mem_fvSubstImage_iff.mp hx
      rwa [fvSubst_eq_self hv (hs q hq) (le_of_lt <| lt_of_lt_of_le (lt_of_mem hq) h)]
    · intro hx
      exact mem_fvSubstImage_iff.mpr
        ⟨x, hx, (fvSubst_eq_self hv (hs x hx) (le_of_lt <| lt_of_lt_of_le (lt_of_mem hx) h)).symm⟩

/-- If `v` sends the entry of `w` at `x` back to `^&x` for every `x < u`, then substituting by `w`
and then by `v` fixes the terms coded by a number at most `u`. -/
lemma termFvSubst_termFvSubst_eq_self (hw : IsSemitermVec L (len w) 0 w)
    (h : ∀ x < u, x < len w ∧ termFvSubst L v w.[x] = ^&x)
    {n t : V} (ht : IsSemiterm L n t) (htu : t ≤ u) :
    termFvSubst L v (termFvSubst L w t) = t := by
  revert htu
  apply IsSemiterm.induction 𝚷
    (P := fun t ↦ t ≤ u → termFvSubst L v (termFvSubst L w t) = t) ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z _ _; simp
  · intro x hx
    have hxu : x < u := lt_of_lt_of_le (by simp) hx
    rw [termFvSubst_fvar w, ite_eq_left (h x hxu).1, (h x hxu).2]
  · intro k f ts hf hts ih hle
    have hts' : IsUTermVec L k (termFvSubstVec L k w ts) :=
      hw.isUTerm.termFvSubstVec hts.isUTerm
    rw [termFvSubst_func hf hts.isUTerm, termFvSubst_func hf hts']
    refine congrArg _ (nth_ext' k (by simp [hts']) hts.lh fun i hi ↦ ?_)
    rw [nth_termFvSubstVec hts' hi, nth_termFvSubstVec hts.isUTerm hi]
    exact ih i hi
      (le_of_lt <| lt_of_lt_of_le (nth_lt_qqFunc_of_lt (by rw [hts.lh]; exact hi)) hle)

/-- If `v` sends the entry of `w` at `x` back to `^&x` for every `x < u`, then substituting by `w`
and then by `v` fixes the formulas coded by a number at most `u`. -/
lemma fvSubst_fvSubst_eq_self (hw : IsSemitermVec L (len w) 0 w)
    (h : ∀ x < u, x < len w ∧ termFvSubst L v w.[x] = ^&x)
    {n p : V} (hp : IsSemiformula L n p) (hpu : p ≤ u) :
    fvSubst L v (fvSubst L w p) = p := by
  revert hpu
  apply IsSemiformula.pi1_structural_induction
    (P := fun _ p ↦ p ≤ u → fvSubst L v (fvSubst L w p) = p) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R ts hR hts hle
    have hts' : IsUTermVec L k (termFvSubstVec L k w ts) :=
      hw.isUTerm.termFvSubstVec hts.isUTerm
    rw [fvSubst_rel hR hts.isUTerm, fvSubst_rel hR hts']
    refine congrArg _ (nth_ext' k (by simp [hts']) hts.lh fun i hi ↦ ?_)
    rw [nth_termFvSubstVec hts' hi, nth_termFvSubstVec hts.isUTerm hi]
    exact termFvSubst_termFvSubst_eq_self hw h (hts.nth hi)
      (le_of_lt <| lt_of_lt_of_le (nth_lt_qqRel_of_lt (by rw [hts.lh]; exact hi)) hle)
  · intro n k R ts hR hts hle
    have hts' : IsUTermVec L k (termFvSubstVec L k w ts) :=
      hw.isUTerm.termFvSubstVec hts.isUTerm
    rw [fvSubst_nrel hR hts.isUTerm, fvSubst_nrel hR hts']
    refine congrArg _ (nth_ext' k (by simp [hts']) hts.lh fun i hi ↦ ?_)
    rw [nth_termFvSubstVec hts' hi, nth_termFvSubstVec hts.isUTerm hi]
    exact termFvSubst_termFvSubst_eq_self hw h (hts.nth hi)
      (le_of_lt <| lt_of_lt_of_le (nth_lt_qqNRel_of_lt (by rw [hts.lh]; exact hi)) hle)
  · intro n _; simp
  · intro n _; simp
  · intro n p q hp hq ihp ihq hle
    have hw' : IsSemitermVec L (len w) n w := hw.weaken (by simp)
    rw [fvSubst_and hp.isUFormula hq.isUFormula,
      fvSubst_and (hp.fvSubst hw').isUFormula (hq.fvSubst hw').isUFormula,
      ihp (le_of_lt <| lt_of_lt_of_le (by simp) hle),
      ihq (le_of_lt <| lt_of_lt_of_le (by simp) hle)]
  · intro n p q hp hq ihp ihq hle
    have hw' : IsSemitermVec L (len w) n w := hw.weaken (by simp)
    rw [fvSubst_or hp.isUFormula hq.isUFormula,
      fvSubst_or (hp.fvSubst hw').isUFormula (hq.fvSubst hw').isUFormula,
      ihp (le_of_lt <| lt_of_lt_of_le (by simp) hle),
      ihq (le_of_lt <| lt_of_lt_of_le (by simp) hle)]
  · intro n p hp ih hle
    rw [fvSubst_all hp.isUFormula, fvSubst_all (hp.fvSubst (hw.weaken (by simp))).isUFormula,
      ih (le_of_lt <| lt_of_lt_of_le (by simp) hle)]
  · intro n p hp ih hle
    rw [fvSubst_exs hp.isUFormula, fvSubst_exs (hp.fvSubst (hw.weaken (by simp))).isUFormula,
      ih (le_of_lt <| lt_of_lt_of_le (by simp) hle)]

/-- If `v` sends the entry of `w` at `x` back to `^&x` for every `x < u`, then the image under `v`
of the image under `w` of a coded formula set bounded by `u` is the set itself. -/
lemma fvSubstImage_fvSubstImage_eq_self (hw : IsSemitermVec L (len w) 0 w)
    (h : ∀ x < u, x < len w ∧ termFvSubst L v w.[x] = ^&x)
    {s : V} (hs : IsFormulaSet L s) (hsu : s ≤ u) :
    fvSubstImage (L := L) v (fvSubstImage (L := L) w s) = s :=
  mem_ext fun x ↦ by
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := mem_fvSubstImage_iff.mp hx
      obtain ⟨q, hq, rfl⟩ := mem_fvSubstImage_iff.mp hy
      rwa [fvSubst_fvSubst_eq_self hw h (hs q hq) (le_of_lt <| lt_of_lt_of_le (lt_of_mem hq) hsu)]
    · intro hx
      exact mem_fvSubstImage_iff.mpr ⟨fvSubst L w x, mem_fvSubstImage_iff.mpr ⟨x, hx, rfl⟩,
        (fvSubst_fvSubst_eq_self hw h (hs x hx)
          (le_of_lt <| lt_of_lt_of_le (lt_of_mem hx) hsu)).symm⟩

end shiftComp

section freshVec

lemma freshVec_exists_aux (u : V) : ∀ j, ∀ m ≤ u, j + m = u →
    ∃ w : V, len w = j + 1 ∧ (∀ x < j, w.[x] = ^&(m + x + 1)) ∧ w.[j] = ^&0 := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro m _ _; exact ⟨?[^&0], by simp, by simp, by simp⟩
  case succ j ih =>
    intro m _ hjm
    have hjm' : j + (m + 1) = u := by
      rw [← hjm, add_assoc, add_comm (1 : V) m]
    have hm : m + 1 ≤ u := by rw [← hjm']; simp
    obtain ⟨w, hlen, hlt, hlast⟩ := ih (m + 1) hm hjm'
    refine ⟨^&(m + 1) ∷ w, by simp [hlen], ?_, by simp [hlast]⟩
    intro x hx
    rcases zero_or_succ x with (rfl | ⟨x, rfl⟩)
    · simp
    · rw [nth_adjoin_succ, hlt x (by simpa using hx)]
      congr 2
      rw [add_assoc, add_comm (1 : V) x]

lemma freshVec_existsUnique (u : V) :
    ∃! w : V, len w = u + 1 ∧ (∀ x < u, w.[x] = ^&(x + 1)) ∧ w.[u] = ^&0 := by
  obtain ⟨w, hlen, hlt, hlast⟩ := freshVec_exists_aux u u 0 (by simp) (by simp)
  refine ⟨w, ⟨hlen, by simpa using hlt, hlast⟩, ?_⟩
  rintro v ⟨hlen', hlt', hlast'⟩
  apply nth_ext' (u + 1) hlen' hlen
  intro i hi
  rcases lt_or_eq_of_le (lt_succ_iff_le.mp hi) with (h | rfl)
  · rw [hlt' i h]
    simpa using (hlt i h).symm
  · rw [hlast', hlast]

/-- `freshVec u` is the term vector of length `u + 1` whose entry at `x < u` is `^&(x + 1)` and
whose entry at `u` is `^&0`. -/
noncomputable def freshVec (u : V) : V := Classical.choose! (freshVec_existsUnique u)

@[simp] lemma len_freshVec (u : V) : len (freshVec u : V) = u + 1 :=
  (Classical.choose!_spec (freshVec_existsUnique u)).1

lemma nth_freshVec_of_lt {u x : V} (h : x < u) : (freshVec u : V).[x] = ^&(x + 1) :=
  (Classical.choose!_spec (freshVec_existsUnique u)).2.1 x h

@[simp] lemma nth_freshVec_self (u : V) : (freshVec u : V).[u] = ^&0 :=
  (Classical.choose!_spec (freshVec_existsUnique u)).2.2

lemma isSemitermVec_freshVec (u : V) :
    IsSemitermVec L (len (freshVec u : V)) 0 (freshVec u) :=
  IsSemitermVec.iff.mpr ⟨rfl, fun i hi ↦ by
    rcases lt_or_eq_of_le (lt_succ_iff_le.mp (by simpa using hi)) with (h | rfl)
    · simp [nth_freshVec_of_lt h]
    · simp⟩

/-- For every `u` there is a closed term vector `w` such that `w` and `freshVec u` undo each
other on the free variables below `u`. -/
lemma exists_inverse_freshVec (u : V) : ∃ w : V, IsSemitermVec L (len w) 0 w ∧
    (∀ x < u, x < len (freshVec u : V) ∧ termFvSubst L w (freshVec u : V).[x] = ^&x) ∧
    (∀ x < u, x < len w ∧ termFvSubst L (freshVec u) w.[x] = ^&x) := by
  obtain ⟨ι, hιl, hι⟩ := sigmaOne_skolem_vec (R := fun x y : V ↦ y = ^&x) (by definability)
    (l := u) (fun x _ ↦ ⟨_, rfl⟩)
  have hιc : IsSemitermVec L (len ι) 0 ι := IsSemitermVec.iff.mpr ⟨rfl, fun i hi ↦ by
    rw [hι i (by rwa [hιl] at hi)]
    simp⟩
  refine ⟨^&u ∷ ι, by simp [hιc], ?_, ?_⟩
  · intro x hx
    exact ⟨lt_trans hx (by simp), by simp [nth_freshVec_of_lt hx, hιl, hx, hι x hx]⟩
  · intro x hx
    rcases zero_or_succ x with rfl | ⟨x, rfl⟩
    · simp
    · have hx' : x < u := lt_trans (by simp) hx
      have hx₁ : x < u + 1 := lt_trans hx' (by simp)
      exact ⟨by simp [hιl, hx'], by simp [hι x hx', hx₁, nth_freshVec_of_lt hx']⟩

end freshVec

/-- The internal `∀`-introduction rule with an arbitrary free variable as eigenvariable: `w`
carries the sequent to its shift and sends `^&u` to `^&0`. -/
lemma Derivable.all_of_free {w u p s : V}
    (hw : IsSemitermVec L (len w) 0 w) (hu : u < len w) (hwu : w.[u] = ^&0)
    (hws : fvSubstImage (L := L) w s = setShift L s)
    (hwp : fvSubst L w p = Bootstrapping.shift L p)
    (hp : IsSemiformula L 1 p) (h : Derivable T (insert (substs1 L ^&u p) s)) :
    Derivable T (insert (^∀ p) s) := by
  have h : Derivable T (fvSubstImage (L := L) w (insert (substs1 L ^&u p) s)) :=
    Derivable.rewrite hw h
  rw [fvSubstImage_insert, hws,
    fvSubst_substs1 hw (show IsSemiterm L 0 ^&u from by simp) hp,
    hwp, termFvSubst_fvar, ite_eq_left hu, hwu] at h
  exact Derivable.all hp h

/-- The internal `∃`-elimination rule with an arbitrary free variable as eigenvariable: `w`
carries the sequent to its shift and sends `^&u` to `^&0`.
- [HP98, Theorem I.4.9] -/
lemma Derivable.neg_exs_of_free {w u p s : V}
    (hw : IsSemitermVec L (len w) 0 w) (hu : u < len w) (hwu : w.[u] = ^&0)
    (hws : fvSubstImage (L := L) w s = setShift L s)
    (hwp : fvSubst L w p = Bootstrapping.shift L p)
    (hp : IsSemiformula L 1 p) (h : Derivable T (insert (neg L (substs1 L ^&u p)) s)) :
    Derivable T (insert (neg L (^∃ p)) s) := by
  have e : substs1 L ^&u (neg L p) = neg L (substs1 L ^&u p) :=
    substs_neg hp (show IsSemitermVec L 1 0 ?[^&u] from by simp)
  rw [neg_ex hp.isUFormula]
  refine Derivable.all_of_free hw hu hwu hws ?_ hp.neg ?_
  · rw [fvSubst_neg (hw.weaken (by simp)) hp, hwp, shift_neg hp]
  · rwa [e]

/-- The internal `∀`-introduction rule with the free variable `^&u` as eigenvariable, where `u`
bounds the codes of the sequent and of the quantified formula. -/
lemma Derivable.all_of_fresh {u p s : V} (hsu : s ≤ u) (hpu : p ≤ u) (hp : IsSemiformula L 1 p)
    (h : Derivable T (insert (substs1 L ^&u p) s)) : Derivable T (insert (^∀ p) s) :=
  Derivable.all_of_free (isSemitermVec_freshVec u) (by simp) (by simp)
    (fvSubstImage_eq_setShift (by simp) (fun _ hx ↦ nth_freshVec_of_lt hx)
      (IsFormulaSet.insert_iff.mp h.isFormulaSet).2 hsu)
    (fvSubst_eq_shift (by simp) (fun _ hx ↦ nth_freshVec_of_lt hx) hp hpu) hp h

/-- The internal `∃`-elimination rule with the free variable `^&u` as eigenvariable, where `u`
bounds the codes of the sequent and of the quantified formula.
- [HP98, Theorem I.4.9] -/
lemma Derivable.neg_exs_of_fresh {u p s : V} (hsu : s ≤ u) (hpu : p ≤ u)
    (hp : IsSemiformula L 1 p) (h : Derivable T (insert (neg L (substs1 L ^&u p)) s)) :
    Derivable T (insert (neg L (^∃ p)) s) :=
  Derivable.neg_exs_of_free (isSemitermVec_freshVec u) (by simp) (by simp)
    (fvSubstImage_eq_setShift (by simp) (fun _ hx ↦ nth_freshVec_of_lt hx)
      (IsFormulaSet.insert_iff.mp h.isFormulaSet).2 hsu)
    (fvSubst_eq_shift (by simp) (fun _ hx ↦ nth_freshVec_of_lt hx) hp hpu) hp h

end FFL.FirstOrder.Arithmetic.Bootstrapping
