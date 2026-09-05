module

public import Foundation.FirstOrder.Bootstrapping.Syntax

/-!
# Internal substitution for free variables

Foundation provides internal substitution for bound variables, but not the corresponding
operation on free variables.  This module supplies finite free-variable substitutions for coded
terms and formulas.  Entries below the length of the substitution vector are replaced; all other
free variables are left unchanged.
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* ISigma 1]
variable {L : Language} [L.Encodable] [L.LORDefinable]

namespace TermFvSubst

def blueprint : Language.TermRec.Blueprint 1 where
  bvar := .mkSigma “y z w. !qqBvarDef y z”
  fvar := .mkSigma
    “y x w. (∃ k, !lenDef k w ∧ x < k ∧ !nthDef y w x) ∨
      (∃ k, !lenDef k w ∧ ¬x < k ∧ !qqFvarDef y x)”
  func := .mkSigma “y k f v v' w. !qqFuncDef y k f v'”

noncomputable def construction : Language.TermRec.Construction V blueprint where
  bvar (_ z) := ^#z
  fvar (param x) := if x < len (param 0) then (param 0).[x] else ^&x
  func (_ k f _ v') := ^func k f v'
  bvar_defined := .mk fun v ↦ by simp [blueprint]
  fvar_defined := .mk fun v ↦ by
    by_cases h : v 1 < len (v 2)
    · simp [blueprint, h]
    · simp [blueprint, h, not_lt.mp h]
  func_defined := .mk fun v ↦ by simp [blueprint]

end TermFvSubst

open TermFvSubst

variable (L)

noncomputable def termFvSubst (w t : V) : V := construction.result L ![w] t

noncomputable def termFvSubstVec (k w v : V) : V := construction.resultVec L ![w] k v

noncomputable def termFvSubstGraph : HierarchySymbol.sigmaOne.Semisentence 3 :=
  (blueprint.result L).rew <| Rew.subst ![#0, #2, #1]

noncomputable def termFvSubstVecGraph : HierarchySymbol.sigmaOne.Semisentence 4 :=
  (blueprint.resultVec L).rew <| Rew.subst ![#0, #1, #3, #2]

variable {L}

@[simp] lemma termFvSubst_bvar (w z : V) : termFvSubst L w ^#z = ^#z := by
  simp [termFvSubst, construction]

@[simp] lemma termFvSubst_fvar (w x : V) :
    termFvSubst L w ^&x = if x < len w then w.[x] else ^&x := by
  simp [termFvSubst, construction]

@[simp] lemma termFvSubst_func {w k f v : V} (hf : L.IsFunc k f)
    (hv : IsUTermVec L k v) :
    termFvSubst L w (^func k f v) = ^func k f (termFvSubstVec L k w v) := by
  simp [termFvSubst, construction, hf, hv]
  rfl

section

instance termFvSubst.defined : HierarchySymbol.sigmaOne-Function₂ termFvSubst (V := V) L via termFvSubstGraph L :=
  .mk fun v ↦ by
    simpa [termFvSubstGraph, termFvSubst, Matrix.constant_eq_singleton,
      Matrix.comp_vecCons'] using construction.result_defined.defined ![v 0, v 2, v 1]

instance termFvSubst.definable : HierarchySymbol.sigmaOne-Function₂ termFvSubst (V := V) L :=
  termFvSubst.defined.to_definable

instance termFvSubst.definable' : Γ-[m + 1]-Function₂ termFvSubst (V := V) L :=
  termFvSubst.definable.of_sigmaOne

instance termFvSubstVec.defined :
    HierarchySymbol.sigmaOne-Function₃ termFvSubstVec (V := V) L via termFvSubstVecGraph L := .mk fun v ↦ by
  simpa [termFvSubstVecGraph, termFvSubstVec, Matrix.constant_eq_singleton,
    Matrix.comp_vecCons'] using construction.resultVec_defined.defined ![v 0, v 1, v 3, v 2]

instance termFvSubstVec.definable : HierarchySymbol.sigmaOne-Function₃ termFvSubstVec (V := V) L :=
  termFvSubstVec.defined.to_definable

instance termFvSubstVec.definable' : Γ-[m + 1]-Function₃ termFvSubstVec (V := V) L :=
  termFvSubstVec.definable.of_sigmaOne

end

@[simp] lemma len_termFvSubstVec {k w v : V} (hv : IsUTermVec L k v) :
    len (termFvSubstVec L k w v) = k := construction.resultVec_lh L _ hv

@[simp] lemma nth_termFvSubstVec {k w v i : V} (hv : IsUTermVec L k v) (hi : i < k) :
    (termFvSubstVec L k w v).[i] = termFvSubst L w v.[i] :=
  construction.nth_resultVec L _ hv hi

@[simp] lemma termFvSubstVec_nil (w : V) : termFvSubstVec L 0 w 0 = 0 :=
  construction.resultVec_nil L _

lemma termFvSubstVec_cons {k w t v : V} (ht : IsUTerm L t) (hv : IsUTermVec L k v) :
    termFvSubstVec L (k + 1) w (t ∷ v) =
      termFvSubst L w t ∷ termFvSubstVec L k w v :=
  construction.resultVec_cons L ![w] hv ht

@[simp] lemma IsSemiterm.termFvSubst {n w t : V} (hw : IsSemitermVec L (len w) n w)
    (ht : IsSemiterm L n t) : IsSemiterm L n (termFvSubst L w t) := by
  apply IsSemiterm.induction SigmaSymbol.sigma ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz
    simp [hz]
  · intro x
    by_cases hx : x < len w
    · simpa [hx] using hw.nth hx
    · simp [hx]
  · intro k f v hf hv ih
    simp only [termFvSubst_func hf hv.isUTerm, IsSemiterm.func, hf, true_and]
    exact IsSemitermVec.iff.mpr
      ⟨by simp [hv.isUTerm], fun i hi ↦ by rw [nth_termFvSubstVec hv.isUTerm hi]; exact ih i hi⟩

@[simp] lemma IsSemitermVec.termFvSubstVec {k n w v : V} (hw : IsSemitermVec L (len w) n w)
    (hv : IsSemitermVec L k n v) : IsSemitermVec L k n (termFvSubstVec L k w v) :=
  IsSemitermVec.iff.mpr ⟨by simp [hv.isUTerm], fun i hi ↦ by
    rw [nth_termFvSubstVec hv.isUTerm hi]
    exact (hv.nth hi).termFvSubst hw⟩

lemma IsSemitermVec.weaken {k n m v : V} (hv : IsSemitermVec L k n v) (hnm : n ≤ m) :
    IsSemitermVec L k m v :=
  ⟨hv.isUTerm, fun {_i} hi ↦ le_trans (hv.bv hi) hnm⟩

lemma IsSemitermVec.succ {k n v : V} (hv : IsSemitermVec L k n v) :
    IsSemitermVec L k (n + 1) v := hv.weaken (by simp)

lemma IsUTermVec.termFvSubstVec {k w v : V} (hw : IsUTermVec L (len w) w)
    (hv : IsUTermVec L k v) : IsUTermVec L k (termFvSubstVec L k w v) := by
  exact (hw.isSemitermVec.weaken (le_max_left _ _)).termFvSubstVec
    (hv.isSemitermVec.weaken (le_max_right _ _)) |>.isUTerm

lemma IsSemiformula.weaken {n m p : V} (hp : IsSemiformula L n p) (hnm : n ≤ m) :
    IsSemiformula L m p := ⟨hp.isUFormula, le_trans hp.bv_le hnm⟩

namespace FvSubst

noncomputable def blueprint (L : Language) [L.Encodable] [L.LORDefinable] : UformulaRec1.Blueprint where
  rel := .mkSigma
    “y w k R v. ∃ v', !(termFvSubstVecGraph L) v' k w v ∧ !qqRelDef y k R v'”
  nrel := .mkSigma
    “y w k R v. ∃ v', !(termFvSubstVecGraph L) v' k w v ∧ !qqNRelDef y k R v'”
  verum := .mkSigma “y w. !qqVerumDef y”
  falsum := .mkSigma “y w. !qqFalsumDef y”
  and := .mkSigma “y w p q p' q'. !qqAndDef y p' q'”
  or := .mkSigma “y w p q p' q'. !qqOrDef y p' q'”
  all := .mkSigma “y w p p'. !qqAllDef y p'”
  exs := .mkSigma “y w p p'. !qqExsDef y p'”
  allChanges := .mkSigma “w' w. w' = w”
  exsChanges := .mkSigma “w' w. w' = w”

noncomputable def construction (L : Language) [L.Encodable] [L.LORDefinable] :
    UformulaRec1.Construction V (blueprint L) where
  rel w := fun k R v ↦ ^rel k R (termFvSubstVec L k w v)
  nrel w := fun k R v ↦ ^nrel k R (termFvSubstVec L k w v)
  verum _ := ^⊤
  falsum _ := ^⊥
  and _ := fun _ _ p q ↦ p ^⋏ q
  or _ := fun _ _ p q ↦ p ^⋎ q
  all _ := fun _ p ↦ ^∀ p
  exs _ := fun _ p ↦ ^∃ p
  allChanges := id
  exsChanges := id
  rel_defined := .mk fun v ↦ by simp [blueprint]
  nrel_defined := .mk fun v ↦ by simp [blueprint]
  verum_defined := .mk fun v ↦ by simp [blueprint]
  falsum_defined := .mk fun v ↦ by simp [blueprint]
  and_defined := .mk fun v ↦ by simp [blueprint]
  or_defined := .mk fun v ↦ by simp [blueprint]
  all_defined := .mk fun v ↦ by simp [blueprint]
  exs_defined := .mk fun v ↦ by simp [blueprint]
  allChanges_defined := .mk fun v ↦ by simp [blueprint]
  exChanges_defined := .mk fun v ↦ by simp [blueprint]

end FvSubst

open FvSubst

variable (L)

noncomputable def fvSubst (w p : V) : V := (FvSubst.construction L).result L w p

noncomputable def fvSubstGraph : HierarchySymbol.sigmaOne.Semisentence 3 := (blueprint L).result L

variable {L}

section

instance fvSubst.defined : HierarchySymbol.sigmaOne-Function₂[V] fvSubst L via fvSubstGraph L :=
  (FvSubst.construction L).result_defined

instance fvSubst.definable : HierarchySymbol.sigmaOne-Function₂[V] fvSubst L := fvSubst.defined.to_definable

instance fvSubst.definable' : Γ-[m + 1]-Function₂[V] fvSubst L :=
  fvSubst.definable.of_sigmaOne

end

@[simp] lemma fvSubst_rel {w k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    fvSubst L w (^relk R v) = ^relk R (termFvSubstVec L k w v) := by
  simp [fvSubst, hR, hv, FvSubst.construction]

@[simp] lemma fvSubst_nrel {w k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    fvSubst L w (^nrelk R v) = ^nrelk R (termFvSubstVec L k w v) := by
  simp [fvSubst, hR, hv, FvSubst.construction]

@[simp] lemma fvSubst_verum (w : V) : fvSubst L w ^⊤ = ^⊤ := by
  simp [fvSubst, FvSubst.construction]

@[simp] lemma fvSubst_falsum (w : V) : fvSubst L w ^⊥ = ^⊥ := by
  simp [fvSubst, FvSubst.construction]

@[simp] lemma fvSubst_and {w p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    fvSubst L w (p ^⋏ q) = fvSubst L w p ^⋏ fvSubst L w q := by
  simp [fvSubst, hp, hq, FvSubst.construction]

@[simp] lemma fvSubst_or {w p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    fvSubst L w (p ^⋎ q) = fvSubst L w p ^⋎ fvSubst L w q := by
  simp [fvSubst, hp, hq, FvSubst.construction]

@[simp] lemma fvSubst_all {w p : V} (hp : IsUFormula L p) :
    fvSubst L w (^∀ p) = ^∀ (fvSubst L w p) := by
  simp [fvSubst, hp, FvSubst.construction]

@[simp] lemma fvSubst_exs {w p : V} (hp : IsUFormula L p) :
    fvSubst L w (^∃ p) = ^∃ (fvSubst L w p) := by
  simp [fvSubst, hp, FvSubst.construction]

lemma fvSubst_not_uformula {w p : V} (hp : ¬IsUFormula L p) : fvSubst L w p = 0 :=
  (FvSubst.construction L).result_prop_not _ hp

@[simp] lemma IsSemiformula.fvSubst {n w p : V} (hw : IsSemitermVec L (len w) n w)
    (hp : IsSemiformula L n p) : IsSemiformula L n (fvSubst L w p) := by
  apply IsSemiformula.pi1_structural_induction
    (P := fun n p ↦ ∀ w, IsSemitermVec L (len w) n w →
      IsSemiformula L n (LO.FirstOrder.Arithmetic.Bootstrapping.fvSubst L w p))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp w hw
  · definability
  · intro n k R v hR hv w hw
    simp [hR, hv.isUTerm, hw.termFvSubstVec hv]
  · intro n k R v hR hv w hw
    simp [hR, hv.isUTerm, hw.termFvSubstVec hv]
  · simp
  · simp
  · intro n p q hp hq ihp ihq w hw
    simp [hp.isUFormula, hq.isUFormula, ihp, ihq]
  · intro n p q hp hq ihp ihq w hw
    simp [hp.isUFormula, hq.isUFormula, ihp, ihq]
  · intro n p hp ihp w hw
    simp [hp.isUFormula, ihp (w := w) hw.succ]
  · intro n p hp ihp w hw
    simp [hp.isUFormula, ihp (w := w) hw.succ]

lemma fvSubst_neg {n w p : V} (hw : IsSemitermVec L (len w) n w)
    (hp : IsSemiformula L n p) : fvSubst L w (neg L p) = neg L (fvSubst L w p) := by
  revert w
  apply IsSemiformula.pi1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R v hR hv w hw
    have htv : IsUTermVec L k (termFvSubstVec L k w v) :=
      (hw.termFvSubstVec hv).isUTerm
    rw [neg_rel hR hv.isUTerm, fvSubst_nrel hR hv.isUTerm, fvSubst_rel hR hv.isUTerm,
      neg_rel hR htv]
  · intro n k R v hR hv w hw
    have htv : IsUTermVec L k (termFvSubstVec L k w v) :=
      (hw.termFvSubstVec hv).isUTerm
    rw [neg_nrel hR hv.isUTerm, fvSubst_rel hR hv.isUTerm, fvSubst_nrel hR hv.isUTerm,
      neg_nrel hR htv]
  · simp
  · simp
  · intro n p q hp hq ihp ihq w hw
    rw [neg_and hp.isUFormula hq.isUFormula,
      fvSubst_or hp.isUFormula.neg hq.isUFormula.neg,
      ihp (w := w) hw, ihq (w := w) hw,
      fvSubst_and hp.isUFormula hq.isUFormula,
      neg_and (hp.fvSubst hw).isUFormula (hq.fvSubst hw).isUFormula]
  · intro n p q hp hq ihp ihq w hw
    rw [neg_or hp.isUFormula hq.isUFormula,
      fvSubst_and hp.isUFormula.neg hq.isUFormula.neg,
      ihp (w := w) hw, ihq (w := w) hw,
      fvSubst_or hp.isUFormula hq.isUFormula,
      neg_or (hp.fvSubst hw).isUFormula (hq.fvSubst hw).isUFormula]
  · intro n p hp ihp w hw
    rw [neg_all hp.isUFormula,
      fvSubst_exs hp.isUFormula.neg,
      ihp (w := w) hw.succ,
      fvSubst_all hp.isUFormula,
      neg_all (hp.fvSubst hw.succ).isUFormula]
  · intro n p hp ihp w hw
    rw [neg_ex hp.isUFormula,
      fvSubst_all hp.isUFormula.neg,
      ihp (w := w) hw.succ,
      fvSubst_exs hp.isUFormula,
      neg_ex (hp.fvSubst hw.succ).isUFormula]

lemma termShift_termFvSubst {n w t : V}
    (hw : IsSemitermVec L (len w) n w) (ht : IsSemiterm L n t) :
    termShift L (termFvSubst L w t) =
      termFvSubst L (^&0 ∷ termShiftVec L (len w) w) (termShift L t) := by
  apply IsSemiterm.induction SigmaSymbol.sigma ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z _
    simp
  · intro x
    by_cases hx : x < len w
    · simp [termFvSubst_fvar, termShift_fvar, hx,
        len_termShiftVec hw.isUTerm, nth_termShiftVec hw.isUTerm hx]
    · simp [termFvSubst_fvar, termShift_fvar, hx, len_termShiftVec hw.isUTerm]
  · intro k f v hf hv ih
    rw [termFvSubst_func hf hv.isUTerm,
      termShift_func hf (hw.termFvSubstVec hv).isUTerm,
      termShift_func hf hv.isUTerm,
      termFvSubst_func hf hv.termShiftVec.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k (by rw [len_termShiftVec (hw.termFvSubstVec hv).isUTerm])
      (by rw [len_termFvSubstVec hv.termShiftVec.isUTerm])
    intro i hi
    rw [nth_termShiftVec (hw.termFvSubstVec hv).isUTerm hi,
      nth_termFvSubstVec hv.termShiftVec.isUTerm hi,
      nth_termShiftVec hv.isUTerm hi,
      nth_termFvSubstVec hv.isUTerm hi]
    exact ih i hi

lemma shift_fvSubst {n w p : V} (hw : IsSemitermVec L (len w) n w)
    (hp : IsSemiformula L n p) :
    shift L (fvSubst L w p) =
      fvSubst L (^&0 ∷ termShiftVec L (len w) w) (shift L p) := by
  revert w
  apply IsSemiformula.pi1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R v hR hv w hw
    rw [fvSubst_rel hR hv.isUTerm,
      shift_rel hR (hw.termFvSubstVec hv).isUTerm,
      shift_rel hR hv.isUTerm,
      fvSubst_rel hR hv.termShiftVec.isUTerm]
    simp only [qqRel_inj, true_and]
    apply nth_ext' k
      (by rw [len_termShiftVec (hw.termFvSubstVec hv).isUTerm])
      (by rw [len_termFvSubstVec hv.termShiftVec.isUTerm])
    intro i hi
    rw [nth_termShiftVec (hw.termFvSubstVec hv).isUTerm hi,
      nth_termFvSubstVec hv.termShiftVec.isUTerm hi,
      nth_termShiftVec hv.isUTerm hi,
      nth_termFvSubstVec hv.isUTerm hi]
    exact termShift_termFvSubst hw (hv.nth hi)
  · intro n k R v hR hv w hw
    rw [fvSubst_nrel hR hv.isUTerm,
      shift_nrel hR (hw.termFvSubstVec hv).isUTerm,
      shift_nrel hR hv.isUTerm,
      fvSubst_nrel hR hv.termShiftVec.isUTerm]
    simp only [qqNRel_inj, true_and]
    apply nth_ext' k
      (by rw [len_termShiftVec (hw.termFvSubstVec hv).isUTerm])
      (by rw [len_termFvSubstVec hv.termShiftVec.isUTerm])
    intro i hi
    rw [nth_termShiftVec (hw.termFvSubstVec hv).isUTerm hi,
      nth_termFvSubstVec hv.termShiftVec.isUTerm hi,
      nth_termShiftVec hv.isUTerm hi,
      nth_termFvSubstVec hv.isUTerm hi]
    exact termShift_termFvSubst hw (hv.nth hi)
  · simp
  · simp
  · intro n p q hp hq ihp ihq w hw
    rw [fvSubst_and hp.isUFormula hq.isUFormula,
      shift_and (hp.fvSubst hw).isUFormula (hq.fvSubst hw).isUFormula,
      shift_and hp.isUFormula hq.isUFormula,
      fvSubst_and hp.shift.isUFormula hq.shift.isUFormula,
      ihp hw, ihq hw]
  · intro n p q hp hq ihp ihq w hw
    rw [fvSubst_or hp.isUFormula hq.isUFormula,
      shift_or (hp.fvSubst hw).isUFormula (hq.fvSubst hw).isUFormula,
      shift_or hp.isUFormula hq.isUFormula,
      fvSubst_or hp.shift.isUFormula hq.shift.isUFormula,
      ihp hw, ihq hw]
  · intro n p hp ihp w hw
    rw [fvSubst_all hp.isUFormula,
      shift_all (hp.fvSubst hw.succ).isUFormula,
      shift_all hp.isUFormula,
      fvSubst_all hp.shift.isUFormula,
      ihp hw.succ]
  · intro n p hp ihp w hw
    rw [fvSubst_exs hp.isUFormula,
      shift_exs (hp.fvSubst hw.succ).isUFormula,
      shift_exs hp.isUFormula,
      fvSubst_exs hp.shift.isUFormula,
      ihp hw.succ]

lemma termSubst_zero {v t : V} (ht : IsSemiterm L 0 t) : termSubst L v t = t := by
  apply IsSemiterm.induction SigmaSymbol.sigma ?_ ?_ ?_ ?_ t ht
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

lemma termBShift_zero {t : V} (ht : IsSemiterm L 0 t) : termBShift L t = t := by
  apply IsSemiterm.induction SigmaSymbol.sigma ?_ ?_ ?_ ?_ t ht
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

lemma termFvSubst_termBShift_closed {n w t : V}
    (hw : IsSemitermVec L (len w) 0 w) (ht : IsSemiterm L n t) :
    termFvSubst L w (termBShift L t) = termBShift L (termFvSubst L w t) := by
  have hw' : IsSemitermVec L (len w) n w := hw.weaken (by simp)
  apply IsSemiterm.induction SigmaSymbol.sigma ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z _
    simp
  · intro x
    by_cases hx : x < len w
    · rw [termBShift_fvar, termFvSubst_fvar, if_pos hx]
      exact (termBShift_zero (hw.nth hx)).symm
    · simp [termFvSubst_fvar, termBShift_fvar, hx]
  · intro k f ts hf hts ih
    rw [termBShift_func hf hts.isUTerm,
      termFvSubst_func hf hts.termBShiftVec.isUTerm,
      termFvSubst_func hf hts.isUTerm,
      termBShift_func hf (hw'.termFvSubstVec hts).isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k
      (by rw [len_termFvSubstVec hts.termBShiftVec.isUTerm])
      (by rw [len_termBShiftVec (hw'.termFvSubstVec hts).isUTerm])
    intro i hi
    rw [nth_termFvSubstVec hts.termBShiftVec.isUTerm hi,
      nth_termBShiftVec (hw'.termFvSubstVec hts).isUTerm hi,
      nth_termFvSubstVec hts.isUTerm hi,
      nth_termBShiftVec hts.isUTerm hi]
    exact ih i hi

lemma termFvSubst_termSubst {n m w v t : V}
    (hw : IsSemitermVec L (len w) 0 w) (hv : IsSemitermVec L n m v)
    (ht : IsSemiterm L n t) :
    termFvSubst L w (termSubst L v t) =
      termSubst L (termFvSubstVec L n w v) (termFvSubst L w t) := by
  have hw' : IsSemitermVec L (len w) n w := hw.weaken (by simp)
  apply IsSemiterm.induction SigmaSymbol.sigma ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz
    rw [termSubst_bvar, termFvSubst_bvar, termSubst_bvar,
      nth_termFvSubstVec hv.isUTerm hz]
  · intro x
    by_cases hx : x < len w
    · rw [termFvSubst_fvar, termSubst_fvar, termFvSubst_fvar, if_pos hx]
      exact (termSubst_zero (v := termFvSubstVec L n w v) (hw.nth hx)).symm
    · simp [termFvSubst_fvar, termSubst_fvar, hx]
  · intro k f ts hf hts ih
    rw [termSubst_func hf hts.isUTerm,
      termFvSubst_func hf (hv.termSubstVec hts).isUTerm,
      termFvSubst_func hf hts.isUTerm,
      termSubst_func hf (hw'.termFvSubstVec hts).isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k
      (by rw [len_termFvSubstVec (hv.termSubstVec hts).isUTerm])
      (by rw [len_termSubstVec (hw'.termFvSubstVec hts).isUTerm])
    intro i hi
    rw [nth_termFvSubstVec (hv.termSubstVec hts).isUTerm hi,
      nth_termSubstVec (hw'.termFvSubstVec hts).isUTerm hi,
      nth_termFvSubstVec hts.isUTerm hi,
      nth_termSubstVec hts.isUTerm hi]
    exact ih i hi

lemma termFvSubstVec_qVec_closed {n m w v : V}
    (hw : IsSemitermVec L (len w) 0 w) (hv : IsSemitermVec L n m v) :
    termFvSubstVec L (n + 1) w (qVec L v) =
      qVec L (termFvSubstVec L n w v) := by
  apply nth_ext' (len v + 1)
    (by simpa [← hv.lh] using (len_termFvSubstVec hv.qVec.isUTerm))
    (by simp [qVec, len_termFvSubstVec hv.isUTerm,
      len_termBShiftVec (hw.isUTerm.termFvSubstVec hv.isUTerm), hv.lh])
  intro i hi
  rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
  · rw [qVec, hv.lh, termFvSubstVec_cons (by simp) hv.termBShiftVec.isUTerm]
    simp [qVec]
  · have hi' : i < len v := by simpa using hi
    have hi'' : i < n := by simpa [hv.lh] using hi'
    rw [qVec, hv.lh, termFvSubstVec_cons (by simp) hv.termBShiftVec.isUTerm, qVec]
    simp only [nth_adjoin_succ]
    simp only [len_termFvSubstVec hv.isUTerm]
    rw [nth_termFvSubstVec hv.termBShiftVec.isUTerm hi'',
      nth_termBShiftVec hv.isUTerm hi'',
      nth_termBShiftVec (hw.isUTerm.termFvSubstVec hv.isUTerm) hi'',
      nth_termFvSubstVec hv.isUTerm hi'']
    exact termFvSubst_termBShift_closed hw (hv.nth hi'')

noncomputable def fvSubstImage (w s : V) : V := by
  letI : HierarchySymbol.sigmaOne-Function₁ (fvSubst L w) := by definability
  exact hfsImage (fvSubst L w) s

lemma mem_fvSubstImage_iff {w s p : V} :
    p ∈ fvSubstImage (L := L) w s ↔ ∃ q ∈ s, p = fvSubst L w q := by
  let _ : HierarchySymbol.sigmaOne-Function₁ (fvSubst L w) := by definability
  exact mem_hfsImage_iff

lemma formulaSet_fvSubstImage {w s : V} (hw : IsSemitermVec L (len w) 0 w)
    (hs : IsFormulaSet L s) : IsFormulaSet L (fvSubstImage (L := L) w s) := by
  intro p hp
  rcases mem_fvSubstImage_iff.mp hp with ⟨q, hq, rfl⟩
  exact IsSemiformula.fvSubst hw (hs q hq)

lemma fvSubst_subst {n m w v p : V}
    (hw : IsSemitermVec L (len w) 0 w) (hv : IsSemitermVec L n m v)
    (hp : IsSemiformula L n p) :
    fvSubst L w (subst L v p) =
      subst L (termFvSubstVec L n w v) (fvSubst L w p) := by
  revert m w v
  apply IsSemiformula.pi1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R ts hR hts m w v hw hv
    have hw' : IsSemitermVec L (len w) n w := hw.weaken (by simp)
    rw [substs_rel hR hts.isUTerm,
      fvSubst_rel hR (hv.termSubstVec hts).isUTerm,
      fvSubst_rel hR hts.isUTerm,
      substs_rel hR (hw'.termFvSubstVec hts).isUTerm]
    simp only [qqRel_inj, true_and]
    apply nth_ext' k
      (by rw [len_termFvSubstVec (hv.termSubstVec hts).isUTerm])
      (by rw [len_termSubstVec (hw'.termFvSubstVec hts).isUTerm])
    intro i hi
    rw [nth_termFvSubstVec (hv.termSubstVec hts).isUTerm hi,
      nth_termSubstVec (hw'.termFvSubstVec hts).isUTerm hi,
      nth_termFvSubstVec hts.isUTerm hi,
      nth_termSubstVec hts.isUTerm hi]
    exact termFvSubst_termSubst hw hv (hts.nth hi)
  · intro n k R ts hR hts m w v hw hv
    have hw' : IsSemitermVec L (len w) n w := hw.weaken (by simp)
    rw [substs_nrel hR hts.isUTerm,
      fvSubst_nrel hR (hv.termSubstVec hts).isUTerm,
      fvSubst_nrel hR hts.isUTerm,
      substs_nrel hR (hw'.termFvSubstVec hts).isUTerm]
    simp only [qqNRel_inj, true_and]
    apply nth_ext' k
      (by rw [len_termFvSubstVec (hv.termSubstVec hts).isUTerm])
      (by rw [len_termSubstVec (hw'.termFvSubstVec hts).isUTerm])
    intro i hi
    rw [nth_termFvSubstVec (hv.termSubstVec hts).isUTerm hi,
      nth_termSubstVec (hw'.termFvSubstVec hts).isUTerm hi,
      nth_termFvSubstVec hts.isUTerm hi,
      nth_termSubstVec hts.isUTerm hi]
    exact termFvSubst_termSubst hw hv (hts.nth hi)
  · intros
    simp
  · intros
    simp
  · intro n p q hp hq ihp ihq m w v hw hv
    have hw' : IsSemitermVec L (len w) n w := hw.weaken (by simp)
    rw [substs_and hp.isUFormula hq.isUFormula,
      fvSubst_and (hp.subst hv).isUFormula (hq.subst hv).isUFormula,
      fvSubst_and hp.isUFormula hq.isUFormula,
      substs_and (hp.fvSubst hw').isUFormula (hq.fvSubst hw').isUFormula,
      ihp hw hv, ihq hw hv]
  · intro n p q hp hq ihp ihq m w v hw hv
    have hw' : IsSemitermVec L (len w) n w := hw.weaken (by simp)
    rw [substs_or hp.isUFormula hq.isUFormula,
      fvSubst_or (hp.subst hv).isUFormula (hq.subst hv).isUFormula,
      fvSubst_or hp.isUFormula hq.isUFormula,
      substs_or (hp.fvSubst hw').isUFormula (hq.fvSubst hw').isUFormula,
      ihp hw hv, ihq hw hv]
  · intro n p hp ihp m w v hw hv
    have hw' : IsSemitermVec L (len w) n w := hw.weaken (by simp)
    rw [substs_all hp.isUFormula,
      fvSubst_all (hp.subst hv.qVec).isUFormula,
      fvSubst_all hp.isUFormula,
      substs_all (hp.fvSubst hw'.succ).isUFormula,
      ihp hw hv.qVec, termFvSubstVec_qVec_closed hw hv]
  · intro n p hp ihp m w v hw hv
    have hw' : IsSemitermVec L (len w) n w := hw.weaken (by simp)
    rw [substs_ex hp.isUFormula,
      fvSubst_exs (hp.subst hv.qVec).isUFormula,
      fvSubst_exs hp.isUFormula,
      substs_ex (hp.fvSubst hw'.succ).isUFormula,
      ihp hw hv.qVec, termFvSubstVec_qVec_closed hw hv]

lemma fvSubst_substs1 {n w t p : V}
    (hw : IsSemitermVec L (len w) 0 w) (ht : IsSemiterm L n t)
    (hp : IsSemiformula L 1 p) :
    fvSubst L w (substs1 L t p) =
      substs1 L (termFvSubst L w t) (fvSubst L w p) := by
  have hv : IsSemitermVec L 1 n ?[t] := by simp [ht]
  rw [show substs1 L t p = subst L ?[t] p by rfl,
    fvSubst_subst hw hv hp]
  simp only [substs1]
  have hvec : termFvSubstVec L 1 w (t ∷ 0) = termFvSubst L w t ∷ 0 := by
    simpa using (termFvSubstVec_cons (L := L) (k := 0) (w := w) (t := t) (v := 0)
      ht.isUTerm (by simp))
  rw [hvec]

end LO.FirstOrder.Arithmetic.Bootstrapping
