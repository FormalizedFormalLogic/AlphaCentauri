module

public import AlphaCentauri.ToFoundation.ElementaryArithmetic.Bootstrapping.Syntax.Term.Basic
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Term.Functions

/-!
# Functions on codes of terms in models of $\mathsf{EA}$

The part of `Foundation/FirstOrder/Arithmetic/Bootstrapping/Syntax/Term/Functions.lean` on
operations on codes of terms, ported to models of $\mathsf{EA}$: substitution `termSubst`, the
shifts `termShift` and `termBShift`, the quotation of a list of terms `qVec`, the codes of the
numerals and the predicate `IsTermFVFree`. The blueprints and formulas are Foundation's; the
recursions on terms carry a bound on their values, and inductions are on locally $\Delta_0$
predicates.

- [HP98, §V.3]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.ElementaryArithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗘𝗔]

section

variable {L : Language} [L.Encodable] [L.LORDefinable]

namespace TermSubst

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst (blueprint) in
/-- The recursion on terms substituting the list `w` for the bound variables. -/
noncomputable def construction : Language.TermRec.Construction V blueprint where
  bvar param z := (param 0).[z]
  fvar _ x := ^&x
  func _ k f _ v' := ^func k f v'
  bvar_defined := .mk fun v ↦ by simp [blueprint]
  fvar_defined := .mk fun v ↦ by simp [blueprint]
  func_defined := .mk fun v ↦ by simp [blueprint]
  bvar_locallyDelta0 := nth_locallyDelta0.comp₂ (LocallyDelta0Function.var 1)
    (LocallyDelta0Function.var 0)
  fvar_locallyDelta0 := qqFvar_locallyDelta0.comp₁ (LocallyDelta0Function.var 0)
  func_locallyDelta0 := qqFunc_locallyDelta0.comp₃ (LocallyDelta0Function.var 0)
    (LocallyDelta0Function.var 1) (LocallyDelta0Function.var 3)
  bound param t := Exp.exp (Exp.exp (8 * t + (param 0 + 4)))
  bvar_le_bound param z :=
    le_exp_exp <| le_trans (le_trans (nth_le _ _) le_self_add) le_add_self
  fvar_le_bound _ _ := le_exp_exp_eight_mul_add _ _
  func_le_bound param k f v w hv hw h :=
    qqFunc_le_exp_exp_of_nth_le (le_trans (by simp) le_add_self) hv hw h
  bound_monotone _ _ _ h := exp_monotone_le.mpr (exp_monotone_le.mpr (by gcongr))
  bound_locallyDelta0 := LocallyDelta0Function.exp_exp_mul_add 8 (LocallyDelta0Function.var 0)
    (LocallyDelta0Function.add.comp₂ (LocallyDelta0Function.var 1) (LocallyDelta0Function.const 4))

end TermSubst

section termSubst

open TermSubst

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping (termSubstGraph termSubstVecGraph)

variable (L)

/-- The substitution of the list `w` for the bound variables in the code `t` of a term. -/
noncomputable def termSubst (w t : V) : V := construction.result L ![w] t

/-- The substitution of the list `w` for the bound variables in the list `v` of `k` terms. -/
noncomputable def termSubstVec (k w v : V) : V := construction.resultVec L ![w] k v

variable {L}

variable {n m w : V}

@[simp] lemma termSubst_bvar (z) :
    termSubst L w ^#z = w.[z] := by simp [termSubst, construction]

@[simp] lemma termSubst_fvar (x) :
    termSubst L w ^&x = ^&x := by simp [termSubst, construction]

@[simp] lemma termSubst_func {k f v} (hkf : L.IsFunc k f) (hv : IsUTermVec L k v) :
    termSubst L w (^func k f v) = ^func k f (termSubstVec L k w v) := by
  simp [termSubst, construction, hkf, hv]; rfl

section

instance termSubst.defined : 𝚺ᴬ₁-Function₂ termSubst (V := V) L via termSubstGraph L :=
  .mk fun v ↦ by
    simpa [termSubstGraph, termSubst, Matrix.constant_eq_singleton, Matrix.comp_vecCons']
      using construction.result_defined.defined ![v 0, v 2, v 1]

instance termSubst.definable : 𝚺ᴬ₁-Function₂ termSubst (V := V) L := termSubst.defined.to_definable

instance termSubst.definable' (Γ k) : Γᴬ_[k + 1]-Function₂ termSubst (V := V) L :=
  termSubst.definable.of_sigmaOne

instance termSubstVec.defined : 𝚺ᴬ₁-Function₃ termSubstVec (V := V) L via termSubstVecGraph L :=
  .mk fun v ↦ by
    simpa [termSubstVecGraph, termSubstVec, Matrix.constant_eq_singleton, Matrix.comp_vecCons']
      using construction.resultVec_defined.defined ![v 0, v 1, v 3, v 2]

instance termSubstVec.definable : 𝚺ᴬ₁-Function₃ termSubstVec (V := V) L :=
  termSubstVec.defined.to_definable

instance termSubstVec.definable' (Γ i) : Γᴬ_[i + 1]-Function₃ termSubstVec (V := V) L :=
  termSubstVec.definable.of_sigmaOne

end

lemma termSubst_locallyDelta0 : LocallyDelta0Function₂ (termSubst L : V → V → V) := by
  convert (construction.result_locallyDelta0 (V := V) L).retraction (![1, 0] : Fin 2 → Fin 2)
    using 3
  simp [termSubst, Matrix.constant_eq_singleton]

lemma termSubstVec_locallyDelta0 :
    LocallyDelta0Function fun u : Fin 3 → V ↦ termSubstVec L (u 0) (u 1) (u 2) := by
  convert (construction.resultVec_locallyDelta0 (V := V) L).retraction
    (![0, 2, 1] : Fin 3 → Fin 3) using 3
  simp [termSubstVec, Matrix.constant_eq_singleton]

lemma termSubst_le_exp_exp (w t : V) : termSubst L w t ≤ Exp.exp (Exp.exp (8 * t + (w + 4))) :=
  construction.result_le_bound L ![w] t

lemma termSubstVec_le_exp_exp (k w v : V) :
    termSubstVec L k w v ≤ Exp.exp (Exp.exp (8 * v + (w + 4))) :=
  construction.resultVec_le_exp_exp L ![w] (le_trans (by simp) le_add_self) (fun _ ↦ le_rfl) k v

@[simp] lemma len_termSubstVec {k ts : V} (hts : IsUTermVec L k ts) :
    len (termSubstVec L k w ts) = k := construction.resultVec_lh L _ hts

@[simp] lemma nth_termSubstVec {k ts i : V} (hts : IsUTermVec L k ts) (hi : i < k) :
    (termSubstVec L k w ts).[i] = termSubst L w ts.[i] :=
  construction.nth_resultVec L _ hts hi

@[simp] lemma termSubstVec_nil (w : V) : termSubstVec L 0 w 0 = 0 := construction.resultVec_nil L _

lemma termSubstVec_cons {k t ts : V} (ht : IsUTerm L t) (hts : IsUTermVec L k ts) :
    termSubstVec L (k + 1) w (t ∷ ts) = termSubst L w t ∷ termSubstVec L k w ts :=
  construction.resultVec_cons L ![w] hts ht

@[simp] lemma termSubstVec_cons₁ {t : V} (ht : IsUTerm L t) :
    termSubstVec L 1 w ?[t] = ?[termSubst L w t] := by
  rw [show (1 : V) = 0 + 1  by simp, termSubstVec_cons] <;> simp [*]

@[simp] lemma termSubstVec_cons₂ {t₁ t₂ : V} (ht₁ : IsUTerm L t₁) (ht₂ : IsUTerm L t₂) :
    termSubstVec L 2 w ?[t₁, t₂] = ?[termSubst L w t₁, termSubst L w t₂] := by
  rw [show (2 : V) = 0 + 1 + 1  by simp [one_add_one_eq_two], termSubstVec_cons] <;> simp [*]

@[simp] lemma IsSemitermVec.termSubst {t} (hw : IsSemitermVec L n m w) (ht : IsSemiterm L n t) :
    IsSemiterm L m (termSubst L w t) := by
  refine IsSemiterm.induction
    (P := fun t ↦ IsSemiterm L m (Bootstrapping.termSubst L w t)) ?_ ?_ ?_ ?_ t ht
  · exact isSemiterm_locallyDelta0.rel_comp₂ (LocallyDelta0Function.const m)
      (termSubst_locallyDelta0.comp₂ (LocallyDelta0Function.const w) (LocallyDelta0Function.var 0))
  · intro z hz; simpa using hw.nth hz
  · intro x; simp
  · intro k f v hkf hv ih
    simp only [hkf, hv.isUTerm, termSubst_func, IsSemiterm.func, true_and]
    exact IsSemitermVec.iff.mpr
      ⟨by simp [hv.isUTerm], fun i hi ↦ by rw [nth_termSubstVec hv.isUTerm hi]; exact ih i hi⟩

@[simp] lemma IsUTermVec.termSubst {t} (hw : IsUTermVec L n w) (ht : IsSemiterm L n t) :
    IsUTerm L (termSubst L w t) :=
  IsSemitermVec.termSubst hw.isSemitermVec ht |>.isUTerm

@[simp] lemma IsSemitermVec.termSubstVec {k n m v}
    (hw : IsSemitermVec L n m w) (hv : IsSemitermVec L k n v) :
    IsSemitermVec L k m (termSubstVec L k w v) :=
  IsSemitermVec.iff.mpr
    ⟨by simp [hv.isUTerm], fun i hi ↦ by
      rw [nth_termSubstVec hv.isUTerm hi]; exact hw.termSubst (hv.nth hi)⟩

@[simp] lemma substs_nil {t : V} (ht : IsSemiterm L 0 t) : termSubst L 0 t = t := by
  refine IsSemiterm.induction (P := fun t ↦ termSubst L 0 t = t) ?_ ?_ ?_ ?_ t ht
  · exact LocallyDelta0.eq (termSubst_locallyDelta0.comp₂ (LocallyDelta0Function.const 0)
      (LocallyDelta0Function.var 0)) (LocallyDelta0Function.var 0)
  · intro z; simp
  · intro x; simp
  · intro k f v hf hv ih
    simp only [hf, hv.isUTerm, termSubst_func, qqFunc_inj, true_and]
    apply nth_ext' k (by simp [hv.isUTerm]) (by simp [hv.lh])
    intro i hi
    simp [nth_termSubstVec hv.isUTerm hi, ih i hi]

lemma termSubst_termSubst {l n w v t : V} (hv : IsSemitermVec L l n v) (ht : IsSemiterm L l t) :
    termSubst L w (termSubst L v t) = termSubst L (termSubstVec L l w v) t := by
  refine IsSemiterm.induction
    (P := fun t ↦ termSubst L w (termSubst L v t) = termSubst L (termSubstVec L l w v) t)
    ?_ ?_ ?_ ?_ t ht
  · exact LocallyDelta0.eq (termSubst_locallyDelta0.comp₂ (LocallyDelta0Function.const w)
      (termSubst_locallyDelta0.comp₂ (LocallyDelta0Function.const v)
        (LocallyDelta0Function.var 0)))
      (termSubst_locallyDelta0.comp₂ (LocallyDelta0Function.const _) (LocallyDelta0Function.var 0))
  · intro z hz
    rw [termSubst_bvar z, termSubst_bvar z, nth_termSubstVec hv.isUTerm hz]
  · intro x; simp
  · intro k f ts hf hts ih
    rw [termSubst_func hf hts.isUTerm,
      termSubst_func hf (hv.termSubstVec hts).isUTerm,
      termSubst_func hf hts.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k (by rw [len_termSubstVec (hv.termSubstVec hts).isUTerm])
      (by rw [len_termSubstVec hts.isUTerm])
    intro i hi
    rw [nth_termSubstVec (hv.termSubstVec hts).isUTerm hi,
      nth_termSubstVec hts.isUTerm hi, nth_termSubstVec hts.isUTerm hi, ih i hi]

lemma termSubst_eq_self {n w t : V} (ht : IsSemiterm L n t) (H : ∀ i < n, w.[i] = ^#i) :
    termSubst L w t = t := by
  refine IsSemiterm.induction (P := fun t ↦ termSubst L w t = t) ?_ ?_ ?_ ?_ t ht
  · exact LocallyDelta0.eq (termSubst_locallyDelta0.comp₂ (LocallyDelta0Function.const w)
      (LocallyDelta0Function.var 0)) (LocallyDelta0Function.var 0)
  · intro z hz; simp [hz, H]
  · intro x; simp
  · intro k f v hf hv ih
    rw [termSubst_func hf hv.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k (by rw [len_termSubstVec hv.isUTerm]) (by simp [hv.lh])
    intro i hi
    rw [nth_termSubstVec hv.isUTerm hi, ih i hi]

end termSubst

lemma qqBvar_add_one_le (z : V) : ^#(z + 1) ≤ Exp.exp (Exp.exp (8 * ^#z + 2)) := by
  have : ^#(z + 1) = 0 ∷ (z + 1) := by rw [adjoin_def]; rfl
  rw [this]
  have hn : 1 ≤ ^#z := le_trans (by simp) (succ_le_iff_lt.mpr (var_lt_qqBvar z))
  refine le_trans (adjoin_le_exp_exp hn (le_exp_exp (le_trans zero_le hn))
    (le_exp_exp (succ_le_iff_lt.mpr (var_lt_qqBvar z)))) ?_
  exact exp_monotone_le.mpr (exp_monotone_le.mpr
    (add_le_add (le_mul_of_one_le_left zero_le (by norm_num)) le_rfl))

lemma qqFvar_add_one_le (x : V) : ^&(x + 1) ≤ Exp.exp (Exp.exp (8 * ^&x + 2)) := by
  have : ^&(x + 1) = 1 ∷ (x + 1) := by rw [adjoin_def]; rfl
  rw [this]
  have hn : 1 ≤ ^&x := le_trans (by simp) (succ_le_iff_lt.mpr (var_lt_qqFvar x))
  refine le_trans (adjoin_le_exp_exp hn (le_exp_exp hn)
    (le_exp_exp (succ_le_iff_lt.mpr (var_lt_qqFvar x)))) ?_
  exact exp_monotone_le.mpr (exp_monotone_le.mpr
    (add_le_add (le_mul_of_one_le_left zero_le (by norm_num)) le_rfl))

namespace TermShift

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping.TermShift (blueprint) in
/-- The recursion on terms raising the indices of the free variables by one. -/
noncomputable def construction : Language.TermRec.Construction V blueprint where
  bvar _ z := ^#z
  fvar _ x := ^&(x + 1)
  func _ k f _ v' := ^func k f v'
  bvar_defined := .mk fun v ↦ by simp [blueprint]
  fvar_defined := .mk fun v ↦ by simp [blueprint]
  func_defined := .mk fun v ↦ by simp [blueprint]
  bvar_locallyDelta0 := qqBvar_locallyDelta0.comp₁ (LocallyDelta0Function.var 0)
  fvar_locallyDelta0 := qqFvar_locallyDelta0.comp₁
    (LocallyDelta0Function.add_one (LocallyDelta0Function.var 0))
  func_locallyDelta0 := qqFunc_locallyDelta0.comp₃ (LocallyDelta0Function.var 0)
    (LocallyDelta0Function.var 1) (LocallyDelta0Function.var 3)
  bound _ t := Exp.exp (Exp.exp (8 * t + 2))
  bvar_le_bound _ _ := le_exp_exp_eight_mul_add _ _
  fvar_le_bound _ x := qqFvar_add_one_le x
  func_le_bound _ _ _ _ _ hv hw h := qqFunc_le_exp_exp_of_nth_le (by norm_num) hv hw h
  bound_monotone _ _ _ h := exp_monotone_le.mpr (exp_monotone_le.mpr (by gcongr))
  bound_locallyDelta0 := LocallyDelta0Function.exp_exp_mul_add 8 (LocallyDelta0Function.var 0)
    (LocallyDelta0Function.const 2)

end TermShift

section termShift

open TermShift

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping (termShiftGraph termShiftVecGraph)

variable (L)

/-- The code of the term obtained by raising the indices of the free variables of `t` by one. -/
noncomputable def termShift (t : V) : V := construction.result L ![] t

/-- The list obtained by shifting each of the `k` terms in `v`. -/
noncomputable def termShiftVec (k v : V) : V := construction.resultVec L ![] k v

variable {L}

variable {n : V}

@[simp] lemma termShift_bvar (z : V) :
    termShift L ^#z = ^#z := by simp [termShift, construction]

@[simp] lemma termShift_fvar (x : V) :
    termShift L ^&x = ^&(x + 1) := by simp [termShift, construction]

@[simp] lemma termShift_func {k f v : V} (hkf : L.IsFunc k f) (hv : IsUTermVec L k v) :
    termShift L (^func k f v) = ^func k f (termShiftVec L k v) := by
  simp [termShift, construction, hkf, hv]; rfl

section

instance termShift.defined : 𝚺ᴬ₁-Function₁ termShift (V := V) L via termShiftGraph L :=
  .mk fun v ↦ by simpa [termShiftGraph, termShift] using! construction.result_defined.defined v

instance termShift.definable : 𝚺ᴬ₁-Function₁ termShift (V := V) L := termShift.defined.to_definable

instance termShift.definable' (Γ i) : Γᴬ_[i + 1]-Function₁ termShift (V := V) L :=
  termShift.definable.of_sigmaOne

instance termShiftVec.defined : 𝚺ᴬ₁-Function₂ termShiftVec (V := V) L via termShiftVecGraph L :=
  .mk fun v ↦ by
    simpa [termShiftVecGraph, termShiftVec] using! construction.resultVec_defined.defined v

instance termShiftVec.definable : 𝚺ᴬ₁-Function₂ termShiftVec (V := V) L :=
  termShiftVec.defined.to_definable

instance termShiftVec.definable' (Γ i) : Γᴬ_[i + 1]-Function₂ termShiftVec (V := V) L :=
  termShiftVec.definable.of_sigmaOne

end

lemma termShift_locallyDelta0 : LocallyDelta0Function₁ (termShift L : V → V) := by
  convert construction.result_locallyDelta0 (V := V) L using 3
  simp [termShift, Matrix.empty_eq]

lemma termShiftVec_locallyDelta0 : LocallyDelta0Function₂ (termShiftVec L : V → V → V) := by
  convert construction.resultVec_locallyDelta0 (V := V) L using 3
  simp [termShiftVec, Matrix.empty_eq]

lemma termShiftVec_le_exp_exp (k v : V) : termShiftVec L k v ≤ Exp.exp (Exp.exp (8 * v + 2)) :=
  construction.resultVec_le_exp_exp L ![] one_le_two (fun _ ↦ le_rfl) k v

@[simp] lemma len_termShiftVec {k ts : V} (hts : IsUTermVec L k ts) :
    len (termShiftVec L k ts) = k := construction.resultVec_lh L _ hts

@[simp] lemma nth_termShiftVec {k ts i : V} (hts : IsUTermVec L k ts) (hi : i < k) :
    (termShiftVec L k ts).[i] = termShift L ts.[i] := construction.nth_resultVec L _ hts hi

@[simp] lemma termShiftVec_nil : termShiftVec (V := V) L 0 0 = 0 := construction.resultVec_nil L ![]

lemma termShiftVec_cons {k t ts : V} (ht : IsUTerm L t) (hts : IsUTermVec L k ts) :
    termShiftVec L (k + 1) (t ∷ ts) = termShift L t ∷ termShiftVec L k ts :=
  construction.resultVec_cons L ![] hts ht

@[simp] lemma termShiftVec_cons₁ {t₁ : V} (ht₁ : IsUTerm L t₁) :
    termShiftVec L 1 (?[t₁] : V) = ?[termShift L t₁] := by
  rw [show (1 : V) = 0 + 1  by simp, termShiftVec_cons] <;> simp [*]

@[simp] lemma termShiftVec_cons₂ {t₁ t₂ : V} (ht₁ : IsUTerm L t₁) (ht₂ : IsUTerm L t₂) :
    termShiftVec L 2 (?[t₁, t₂] : V) = ?[termShift L t₁, termShift L t₂] := by
  rw [show (2 : V) = 0 + 1 + 1  by simp [one_add_one_eq_two], termShiftVec_cons] <;> simp [ht₁, ht₂]

@[simp] lemma IsUTerm.termShift {t} (ht : IsUTerm L t) : IsUTerm L (termShift L t : V) := by
  refine IsUTerm.induction (P := fun t ↦ IsUTerm L (Bootstrapping.termShift L t : V)) ?_ ?_ ?_ ?_
    t ht
  · exact isUTerm_locallyDelta0.pred_comp (termShift_locallyDelta0.comp₁
      (LocallyDelta0Function.var (0 : Fin 1)))
  · intro z; simp
  · intro x; simp
  · intro k f v hkf hv ih;
    simp only [hkf, hv, termShift_func, func_iff, true_and]
    exact ⟨by simp [hv], by intro i hi; rw [nth_termShiftVec hv hi]; exact ih i hi⟩

@[simp] lemma IsSemiterm.termShift {t : V} (ht : IsSemiterm L n t) :
    IsSemiterm L n (termShift L t) := by
  refine IsSemiterm.induction (P := fun t ↦ IsSemiterm L n (Bootstrapping.termShift L t)) ?_ ?_ ?_
    ?_ t ht
  · exact isSemiterm_locallyDelta0.rel_comp₂ (LocallyDelta0Function.const n)
      (termShift_locallyDelta0.comp₁ (LocallyDelta0Function.var (0 : Fin 1)))
  · intro z hz; simp [hz]
  · intro x; simp
  · intro k f v hkf hv ih;
    simp only [hkf, hv.isUTerm, termShift_func, func, true_and]
    apply IsSemitermVec.iff.mpr
    constructor
    · simp [termShiftVec, hv.isUTerm]
    · intro i hi
      rw [nth_termShiftVec hv.isUTerm hi]
      exact ih i hi

@[simp] lemma IsUTermVec.termShiftVec {k v : V} (hv : IsUTermVec L k v) :
    IsUTermVec L k (termShiftVec L k v) :=
    ⟨by simp [hv], fun i hi ↦ by rw [nth_termShiftVec hv hi]; exact (hv.nth hi).termShift⟩

@[simp] lemma IsSemitermVec.termShiftVec {k n v : V} (hv : IsSemitermVec L k n v) :
    IsSemitermVec L k n (termShiftVec L k v) :=
  IsSemitermVec.iff.mpr
    ⟨by simp [hv.isUTerm], fun i hi ↦ by
      rw [nth_termShiftVec hv.isUTerm hi]; exact (hv.nth hi).termShift⟩

@[simp] lemma IsUTerm.termBVtermShift {t : V} (ht : IsUTerm L t) :
    termBV L (Bootstrapping.termShift L t) = termBV L t := by
  refine IsUTerm.induction (P := fun t ↦ termBV L (Bootstrapping.termShift L t) = termBV L t) ?_
    ?_ ?_ ?_ t ht
  · exact LocallyDelta0.eq (termBV_locallyDelta0.comp₁ (termShift_locallyDelta0.comp₁
      (LocallyDelta0Function.var (0 : Fin 1)))) (termBV_locallyDelta0.comp₁
        (LocallyDelta0Function.var (0 : Fin 1)))
  · simp
  · simp
  · intro k f v hf hv ih
    rw [termShift_func hf hv,
      termBV_func hf hv.termShiftVec,
      termBV_func hf hv]
    congr 1
    apply nth_ext' k (by simp [*]) (by simp [*])
    intro i hi
    simp [*]

@[simp] lemma IsUTermVec.termBVVectermShiftVec {k v : V} (hv : IsUTermVec L k v) :
    termBVVec L k (Bootstrapping.termShiftVec L k v) = termBVVec L k v := by
  apply nth_ext' k (by simp [*]) (by simp [*])
  intro i hi
  simp [*, IsUTerm.termBVtermShift (hv.nth hi)]

end termShift

namespace TermBShift

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping.TermBShift (blueprint) in
/-- The recursion on terms raising the indices of the bound variables by one. -/
noncomputable def construction : Language.TermRec.Construction V blueprint where
  bvar _ z := ^#(z + 1)
  fvar _ x := ^&x
  func _ k f _ v' := ^func k f v'
  bvar_defined := .mk fun v ↦ by simp [blueprint]
  fvar_defined := .mk fun v ↦ by simp [blueprint]
  func_defined := .mk fun v ↦ by simp [blueprint]
  bvar_locallyDelta0 := qqBvar_locallyDelta0.comp₁
    (LocallyDelta0Function.add_one (LocallyDelta0Function.var 0))
  fvar_locallyDelta0 := qqFvar_locallyDelta0.comp₁ (LocallyDelta0Function.var 0)
  func_locallyDelta0 := qqFunc_locallyDelta0.comp₃ (LocallyDelta0Function.var 0)
    (LocallyDelta0Function.var 1) (LocallyDelta0Function.var 3)
  bound _ t := Exp.exp (Exp.exp (8 * t + 2))
  bvar_le_bound _ z := qqBvar_add_one_le z
  fvar_le_bound _ _ := le_exp_exp_eight_mul_add _ _
  func_le_bound _ _ _ _ _ hv hw h := qqFunc_le_exp_exp_of_nth_le (by norm_num) hv hw h
  bound_monotone _ _ _ h := exp_monotone_le.mpr (exp_monotone_le.mpr (by gcongr))
  bound_locallyDelta0 := LocallyDelta0Function.exp_exp_mul_add 8 (LocallyDelta0Function.var 0)
    (LocallyDelta0Function.const 2)

end TermBShift

section termBShift

open TermBShift

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping (termBShiftGraph termBShiftVecGraph)

variable (L)

/-- The code of the term obtained by raising the indices of the bound variables of `t` by one. -/
noncomputable def termBShift (t : V) : V := construction.result L ![] t

/-- The list obtained by raising the bound variables in each of the `k` terms in `v`. -/
noncomputable def termBShiftVec (k v : V) : V := construction.resultVec L ![] k v

variable {L}

@[simp] lemma termBShift_bvar (z : V) :
    termBShift L ^#z = ^#(z + 1) := by simp [termBShift, construction]

@[simp] lemma termBShift_fvar (x : V) :
    termBShift L ^&x = ^&x := by simp [termBShift, construction]

@[simp] lemma termBShift_func {k f v : V} (hkf : L.IsFunc k f) (hv : IsUTermVec L k v) :
    termBShift L (^func k f v) = ^func k f (termBShiftVec L k v) := by
  simp [termBShift, construction, hkf, hv]; rfl

section

instance termBShift.defined : 𝚺ᴬ₁-Function₁ termBShift (V := V) L via termBShiftGraph L :=
  .mk fun v ↦ by simpa using! construction.result_defined.defined v

instance termBShift.definable : 𝚺ᴬ₁-Function₁ termBShift (V := V) L :=
  termBShift.defined.to_definable

instance termBShift.definable' (Γ i) : Γᴬ_[i + 1]-Function₁ termBShift (V := V) L :=
  termBShift.definable.of_sigmaOne

instance termBShiftVec.defined : 𝚺ᴬ₁-Function₂ termBShiftVec (V := V) L via termBShiftVecGraph L :=
  .mk fun v ↦ by simpa using! construction.resultVec_defined.defined v

instance termBShiftVec.definable : 𝚺ᴬ₁-Function₂ termBShiftVec (V := V) L :=
  termBShiftVec.defined.to_definable

instance termBShiftVec.definable' (Γ i) : Γᴬ_[i + 1]-Function₂ termBShiftVec (V := V) L :=
  termBShiftVec.definable.of_sigmaOne

end

lemma termBShift_locallyDelta0 : LocallyDelta0Function₁ (termBShift L : V → V) := by
  convert construction.result_locallyDelta0 (V := V) L using 3
  simp [termBShift, Matrix.empty_eq]

lemma termBShiftVec_locallyDelta0 : LocallyDelta0Function₂ (termBShiftVec L : V → V → V) := by
  convert construction.resultVec_locallyDelta0 (V := V) L using 3
  simp [termBShiftVec, Matrix.empty_eq]

@[simp] lemma len_termBShiftVec {k ts : V} (hts : IsUTermVec L k ts) :
    len (termBShiftVec L k ts) = k := construction.resultVec_lh L _ hts

@[simp] lemma nth_termBShiftVec {k ts i : V} (hts : IsUTermVec L k ts) (hi : i < k) :
    (termBShiftVec L k ts).[i] = termBShift L ts.[i] :=
  construction.nth_resultVec L _ hts hi

@[simp] lemma termBShiftVec_nil : termBShiftVec (V := V) L 0 0 = 0 :=
  construction.resultVec_nil L ![]

lemma termBShiftVec_cons {k t ts : V} (ht : IsUTerm L t) (hts : IsUTermVec L k ts) :
    termBShiftVec L (k + 1) (t ∷ ts) = termBShift L t ∷ termBShiftVec L k ts :=
  construction.resultVec_cons L ![] hts ht

@[simp] lemma termBShiftVec_cons₁ {t₁ : V} (ht₁ : IsUTerm L t₁) :
    termBShiftVec L 1 (?[t₁] : V) = ?[termBShift L t₁] := by
  rw [show (1 : V) = 0 + 1  by simp, termBShiftVec_cons] <;> simp [*]

@[simp] lemma termBShiftVec_cons₂ {t₁ t₂ : V} (ht₁ : IsUTerm L t₁) (ht₂ : IsUTerm L t₂) :
    termBShiftVec L 2 (?[t₁, t₂] : V) = ?[termBShift L t₁, termBShift L t₂] := by
  rw [show (2 : V) = 0 + 1 + 1  by simp [one_add_one_eq_two], termBShiftVec_cons] <;> simp [*]

@[simp] lemma IsSemiterm.termBShift {n t : V} (ht : IsSemiterm L n t) :
    IsSemiterm L (n + 1) (termBShift L t) := by
  refine IsSemiterm.induction (P := fun t ↦ IsSemiterm L (n + 1) (Bootstrapping.termBShift L t))
    ?_ ?_ ?_ ?_ t ht
  · exact isSemiterm_locallyDelta0.rel_comp₂ (LocallyDelta0Function.const (n + 1))
      (termBShift_locallyDelta0.comp₁ (LocallyDelta0Function.var (0 : Fin 1)))
  · intro z hz; simp [hz]
  · intro x; simp
  · intro k f v hkf hv ih;
    simp only [hkf, hv.isUTerm, termBShift_func, func, true_and]
    apply IsSemitermVec.iff.mpr
    constructor
    · simp [hv.isUTerm]
    · intro i hi
      rw [nth_termBShiftVec hv.isUTerm hi]
      exact ih i hi

@[simp] lemma IsSemitermVec.termBShiftVec {k n v : V} (hv : IsSemitermVec L k n v) :
    IsSemitermVec L k (n + 1) (termBShiftVec L k v) :=
  IsSemitermVec.iff.mpr
  ⟨by simp [hv.isUTerm], fun i hi ↦ by
    rw [nth_termBShiftVec hv.isUTerm hi]; exact (hv.nth hi).termBShift⟩

lemma termBShift_termShift {n t : V} (ht : IsSemiterm L n t) :
    termBShift L (termShift L t) = termShift L (termBShift L t) := by
  refine IsSemiterm.induction
    (P := fun t ↦ termBShift L (termShift L t) = termShift L (termBShift L t)) ?_ ?_ ?_ ?_ t ht
  · exact LocallyDelta0.eq
      (termBShift_locallyDelta0.comp₁ (termShift_locallyDelta0.comp₁
        (LocallyDelta0Function.var (0 : Fin 1))))
      (termShift_locallyDelta0.comp₁ (termBShift_locallyDelta0.comp₁
        (LocallyDelta0Function.var (0 : Fin 1))))
  · intro z hz; simp
  · intro x; simp
  · intro k f v hkf hv ih
    rw [termShift_func hkf hv.isUTerm,
      termBShift_func hkf hv.termShiftVec.isUTerm,
      termBShift_func hkf hv.isUTerm,
      termShift_func hkf hv.termBShiftVec.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k
      (by rw [len_termBShiftVec hv.termShiftVec.isUTerm])
      (by rw [len_termShiftVec hv.termBShiftVec.isUTerm])
    intro i hi
    rw [nth_termBShiftVec hv.termShiftVec.isUTerm hi, nth_termShiftVec hv.isUTerm hi,
      nth_termShiftVec hv.termBShiftVec.isUTerm hi, nth_termBShiftVec hv.isUTerm hi, ih i hi]

lemma le_termBShift {t : V} (ht : IsUTerm L t) : t ≤ termBShift L t := by
  refine IsUTerm.induction (P := fun t ↦ t ≤ Bootstrapping.termBShift L t) ?_ ?_ ?_ ?_ t ht
  · exact LocallyDelta0.le (LocallyDelta0Function.var (0 : Fin 1))
      (termBShift_locallyDelta0.comp₁ (LocallyDelta0Function.var (0 : Fin 1)))
  · intro z
    rw [termBShift_bvar]
    simp only [qqBvar]
    exact add_le_add (pair_le_pair_right (0 : V) le_self_add) (le_refl 1)
  · intro x; simp
  · intro k f v hf hv ih
    rw [termBShift_func hf hv]
    have hvle : v ≤ termBShiftVec L k v := by
      apply le_of_nth_le_nth
      · rw [len_termBShiftVec hv]; exact hv.1.symm
      · intro i hi
        rw [← hv.1] at hi
        rw [nth_termBShiftVec hv hi]
        exact ih i hi
    simp only [qqFunc]
    exact add_le_add
      (pair_le_pair_right 2 (pair_le_pair_right k (pair_le_pair_right f hvle))) (le_refl 1)

lemma IsUTerm.termBShift {t : V} (ht : IsUTerm L t) : IsUTerm L (termBShift L t) :=
  (ht.isSemiterm.termBShift).isUTerm

lemma IsUTermVec.termBShiftVec {k v : V} (hv : IsUTermVec L k v) :
    IsUTermVec L k (termBShiftVec L k v) :=
  ⟨(len_termBShiftVec hv).symm, fun i hi ↦ by
    rw [nth_termBShiftVec hv hi]; exact (hv.nth hi).termBShift⟩

lemma termBV_termBShift_le {t : V} (ht : IsUTerm L t) (m : V) :
    termBV L (termBShift L t) ≤ m + 1 ↔ termBV L t ≤ m := by
  refine IsUTerm.induction
    (P := fun t ↦ termBV L (Bootstrapping.termBShift L t) ≤ m + 1 ↔ termBV L t ≤ m) ?_ ?_ ?_ ?_ t ht
  · exact LocallyDelta0.iff
      (LocallyDelta0.le (termBV_locallyDelta0.comp₁ (termBShift_locallyDelta0.comp₁
        (LocallyDelta0Function.var (0 : Fin 1)))) (LocallyDelta0Function.const (m + 1)))
      (LocallyDelta0.le (termBV_locallyDelta0.comp₁ (LocallyDelta0Function.var (0 : Fin 1)))
        (LocallyDelta0Function.const m))
  · intro z; simp only [termBShift_bvar, termBV_bvar]; exact add_le_add_iff_right 1
  · intro x; simp only [termBShift_fvar, termBV_fvar]; exact iff_of_true zero_le zero_le
  · intro k f v hf hv ih
    rw [termBShift_func hf hv, termBV_func hf hv.termBShiftVec, termBV_func hf hv,
      listMaxss_le_iff, listMaxss_le_iff]
    constructor
    · intro H i hi
      rw [len_termBVVec hv] at hi
      rw [nth_termBVVec hv hi, ← ih i hi]
      have := H i (by rw [len_termBVVec hv.termBShiftVec]; exact hi)
      rwa [nth_termBVVec hv.termBShiftVec hi, nth_termBShiftVec hv hi] at this
    · intro H i hi
      rw [len_termBVVec hv.termBShiftVec] at hi
      rw [nth_termBVVec hv.termBShiftVec hi, nth_termBShiftVec hv hi, ih i hi]
      have := H i (by rw [len_termBVVec hv]; exact hi)
      rwa [nth_termBVVec hv hi] at this

end termBShift

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping (qVecGraph)

variable (L)

/-- The list `^#0 ∷ w` extended by the bound-shifted terms of `w`, used to substitute below a
quantifier. -/
noncomputable def qVec (w : V) : V := ^#0 ∷ termBShiftVec L (len w) w

variable {L}

section

instance qVec.defined : 𝚺ᴬ₁-Function₁ (qVec (V := V) L) via qVecGraph L :=
  .mk fun v ↦ by simp [qVecGraph]; rfl

instance qVec.definable : 𝚺ᴬ₁-Function₁ (qVec (V := V) L) := qVec.defined.to_definable

instance qVec.definable' (Γ m) : Γᴬ_[m + 1]-Function₁ (qVec (V := V) L) :=
  qVec.definable.of_sigmaOne

end

lemma qVec_locallyDelta0 : LocallyDelta0Function₁ (qVec L : V → V) :=
  LocallyDelta0Function.adjoin.comp₂ (LocallyDelta0Function.const _)
    (termBShiftVec_locallyDelta0.comp₂ (len_locallyDelta0.comp₁ (LocallyDelta0Function.var 0))
      (LocallyDelta0Function.var 0))

@[simp] lemma len_qVec {k w : V} (h : IsUTermVec L k w) : len (qVec L w) = k + 1 := by
  rcases h.lh; simp [qVec, h]

lemma IsSemitermVec.qVec {k n w : V} (h : IsSemitermVec L k n w) :
    IsSemitermVec L (k + 1) (n + 1) (qVec L w) := by
  rcases h.lh
  apply IsSemitermVec.iff.mpr
  constructor
  · simp [h.isUTerm, Bootstrapping.qVec]
  · intro i hi
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp [Bootstrapping.qVec]
    · simpa [Bootstrapping.qVec, nth_termBShiftVec h.isUTerm (by simpa using hi)] using
        h.nth (by simpa using hi) |>.termBShift

lemma substs_cons_bShift {n u t w : V} (ht : IsSemiterm L n t) :
    termSubst L (u ∷ w) (termBShift L t) = termSubst L w t := by
  refine IsSemiterm.induction
    (P := fun t ↦ termSubst L (u ∷ w) (termBShift L t) = termSubst L w t) ?_ ?_ ?_ ?_ t ht
  · exact LocallyDelta0.eq (termSubst_locallyDelta0.comp₂ (LocallyDelta0Function.const (u ∷ w))
      (termBShift_locallyDelta0.comp₁ (LocallyDelta0Function.var (0 : Fin 1))))
      (termSubst_locallyDelta0.comp₂ (LocallyDelta0Function.const w)
        (LocallyDelta0Function.var (0 : Fin 1)))
  · intro z hz; simp
  · intro x; simp
  · intro k f v hf hv ih
    rw [termBShift_func hf hv.isUTerm,
      termSubst_func hf hv.termBShiftVec.isUTerm,
      termSubst_func hf hv.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k
      (by rw [len_termSubstVec hv.termBShiftVec.isUTerm])
      (by rw [len_termSubstVec hv.isUTerm])
    intro i hi
    rw [nth_termSubstVec hv.termBShiftVec.isUTerm hi,
      nth_termSubstVec hv.isUTerm hi,
      nth_termBShiftVec hv.isUTerm hi,
      ih i hi]

lemma termShift_termSubsts {n m w t : V} (ht : IsSemiterm L n t) (hw : IsSemitermVec L n m w) :
    termShift L (termSubst L w t) = termSubst L (termShiftVec L n w) (termShift L t) := by
  refine IsSemiterm.induction
    (P := fun t ↦ termShift L (termSubst L w t) = termSubst L (termShiftVec L n w) (termShift L t))
    ?_ ?_ ?_ ?_ t ht
  · exact LocallyDelta0.eq
      (termShift_locallyDelta0.comp₁ (termSubst_locallyDelta0.comp₂
        (LocallyDelta0Function.const w) (LocallyDelta0Function.var (0 : Fin 1))))
      (termSubst_locallyDelta0.comp₂ (LocallyDelta0Function.const _)
        (termShift_locallyDelta0.comp₁ (LocallyDelta0Function.var (0 : Fin 1))))
  · intro z hz; simp [nth_termShiftVec hw.isUTerm hz]
  · intro x; simp
  · intro k f v hf hv ih
    rw [termSubst_func hf hv.isUTerm,
      termShift_func hf (hw.termSubstVec hv).isUTerm,
      termShift_func hf hv.isUTerm,
      termSubst_func hf hv.termShiftVec.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k
      (by rw [len_termShiftVec (hw.termSubstVec hv).isUTerm])
      (by rw [len_termSubstVec hv.termShiftVec.isUTerm])
    intro i hi
    rw [nth_termShiftVec (hw.termSubstVec hv).isUTerm hi,
      nth_termSubstVec hv.isUTerm hi,
      nth_termSubstVec hv.termShiftVec.isUTerm hi,
      nth_termShiftVec hv.isUTerm hi, ih i hi]

lemma bShift_substs {n m w t : V} (ht : IsSemiterm L n t) (hw : IsSemitermVec L n m w) :
    termBShift L (termSubst L w t) = termSubst L (termBShiftVec L n w) t := by
  refine IsSemiterm.induction
    (P := fun t ↦ termBShift L (termSubst L w t) = termSubst L (termBShiftVec L n w) t)
    ?_ ?_ ?_ ?_ t ht
  · exact LocallyDelta0.eq
      (termBShift_locallyDelta0.comp₁ (termSubst_locallyDelta0.comp₂
        (LocallyDelta0Function.const w) (LocallyDelta0Function.var (0 : Fin 1))))
      (termSubst_locallyDelta0.comp₂ (LocallyDelta0Function.const _)
        (LocallyDelta0Function.var (0 : Fin 1)))
  · intro z hz; simp [nth_termBShiftVec hw.isUTerm hz]
  · intro x; simp
  · intro k f v hf hv ih
    rw [termSubst_func hf hv.isUTerm,
      termBShift_func hf (hw.termSubstVec hv).isUTerm,
      termSubst_func hf hv.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k
      (by rw [len_termBShiftVec (hw.termSubstVec hv).isUTerm])
      (by rw [len_termSubstVec hv.isUTerm])
    intro i hi
    simp [nth_termBShiftVec (hw.termSubstVec hv).isUTerm hi, nth_termSubstVec hv.isUTerm hi,
      ih i hi]

lemma substs_qVec_bShift {n t m w : V} (ht : IsSemiterm L n t) (hw : IsSemitermVec L n m w) :
    termSubst L (qVec L w) (termBShift L t) = termBShift L (termSubst L w t) := by
  rcases hw.lh
  simp [qVec, substs_cons_bShift ht, bShift_substs ht hw]

lemma termSubstVec_qVec_qVec {l n m v w : V}
    (hv : IsSemitermVec L l n v) (hw : IsSemitermVec L n m w) :
    termSubstVec L (l + 1) (qVec L w) (qVec L v) = qVec L (termSubstVec L l w v) := by
  apply nth_ext' (len v + 1)
    (by rw [len_termSubstVec hv.qVec.isUTerm, hv.lh])
    (by rw [len_qVec (hw.termSubstVec hv).isUTerm, hv.lh])
  intro i hi
  unfold qVec
  rcases hv.lh; rcases hw.lh
  rw [(hw.termSubstVec hv).lh]
  rw [termSubstVec_cons (by simp) (by rcases hv.lh; exact hv.termBShiftVec.isUTerm)]
  rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
  · simp
  · have hi : i < len v := by simpa using hi
    simp [nth_termSubstVec hv.termBShiftVec.isUTerm hi,
      nth_termBShiftVec hv.isUTerm hi,
      nth_termBShiftVec (hw.termSubstVec hv).isUTerm hi,
      nth_termSubstVec hv.isUTerm hi,
      substs_cons_bShift (hv.nth hi),
      bShift_substs (hv.nth hi) hw]

lemma termShift_qVec {n m w : V} (hw : IsSemitermVec L n m w) :
    termShiftVec L (n + 1) (qVec L w) = qVec L (termShiftVec L n w) := by
  apply nth_ext' (n + 1)
    (by rw [len_termShiftVec hw.qVec.isUTerm])
    (by rw [len_qVec hw.termShiftVec.isUTerm])
  intro i hi
  rw [nth_termShiftVec hw.qVec.isUTerm hi]
  unfold qVec
  rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
  · simp
  · rcases hw.lh
    rw [nth_adjoin_succ, nth_adjoin_succ,
      nth_termBShiftVec hw.isUTerm (by simpa using hi),
      nth_termBShiftVec (by simp [hw.isUTerm]) (by simpa [hw.isUTerm] using hi),
      nth_termShiftVec hw.isUTerm (by simpa using hi),
      termBShift_termShift (hw.nth (by simpa using hi))]

section fvfree

variable (L)

/-- The code `t` is a semiterm with bound variables below `n` and no free variable. -/
def IsTermFVFree (n t : V) : Prop := IsSemiterm L n t ∧ termShift L t = t

variable {L}

@[simp] lemma IsTermFVFree.bvar {n : V} (x : V) : IsTermFVFree L n ^#x ↔ x < n := by
  simp [IsTermFVFree]

@[simp] lemma IsTermFVFree.fvar {n : V} (x : V) : ¬IsTermFVFree L n ^&x := by
  simp [IsTermFVFree]

end fvfree

namespace Arithmetic

-- `Arithmetic` is intentionally re-opened here to match the names in Foundation.
set_option linter.dupNamespace false

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
  (addIndex mulIndex zeroIndex oneIndex qqAddGraph qqMulGraph)

/-- The code of the sum of the terms `x` and `y`. -/
noncomputable def qqAdd (x y : V) : V := ^func 2 (addIndex : V) ?[x, y]

/-- The code of the product of the terms `x` and `y`. -/
noncomputable def qqMul (x y : V) : V := ^func 2 (mulIndex : V) ?[x, y]

scoped infixl:80 " ^+ " => qqAdd

scoped infixl:82 " ^* " => qqMul

section

instance qqAdd_defined : 𝚺ᴬ₁-Function₂ (qqAdd : V → V → V) via qqAddGraph := .mk fun v ↦ by
  simp [qqAddGraph, numeral_eq_natCast, qqAdd]

instance qqMul_defined : 𝚺ᴬ₁-Function₂ (qqMul : V → V → V) via qqMulGraph := .mk fun v ↦ by
  simp [qqMulGraph, numeral_eq_natCast, qqMul]

instance (Γ m) : Γᴬ_[m + 1]-Function₂ (qqAdd : V → V → V) := .of_sigmaOne qqAdd_defined.to_definable

instance (Γ m) : Γᴬ_[m + 1]-Function₂ (qqMul : V → V → V) := .of_sigmaOne qqMul_defined.to_definable

end

@[simp] lemma lt_qqAdd_left (x y : V) : x < x ^+ y := by
  simpa using! nth_lt_qqFunc_of_lt (i := 0) (k := 2) (f := (addIndex : V)) (v := ?[x, y]) (by simp)

@[simp] lemma lt_qqAdd_right (x y : V) : y < x ^+ y := by
  simpa using! nth_lt_qqFunc_of_lt (i := 1) (k := 2) (f := (addIndex : V)) (v := ?[x, y]) (by simp)

@[simp] lemma lt_qqMul_left (x y : V) : x < x ^* y := by
  simpa using! nth_lt_qqFunc_of_lt (i := 0) (k := 2) (f := (mulIndex : V)) (v := ?[x, y]) (by simp)

@[simp] lemma lt_qqMul_right (x y : V) : y < x ^* y := by
  simpa using! nth_lt_qqFunc_of_lt (i := 1) (k := 2) (f := (mulIndex : V)) (v := ?[x, y]) (by simp)

lemma qqFunc_absolute (k f v : ℕ) : ((^func k f v : ℕ) : V) = ^func (k : V) (f : V) (v : V) := by
  simp [qqFunc, nat_cast_pair]
  rfl

lemma qqAdd_locallyDelta0 : LocallyDelta0Function₂ (qqAdd : V → V → V) :=
  qqFunc_locallyDelta0.comp₃ (LocallyDelta0Function.const 2)
    (LocallyDelta0Function.const (addIndex : V))
    (LocallyDelta0Function.adjoin.comp₂ (LocallyDelta0Function.var 0)
      (LocallyDelta0Function.adjoin.comp₂ (LocallyDelta0Function.var 1)
        (LocallyDelta0Function.const 0)))

lemma qqZero_eq_qqFunc : (𝟎 : V) = ^func 0 (zeroIndex : V) 0 := by
  have h : (𝟎 : ℕ) = qqFuncN 0 zeroIndex 0 := rfl
  rw [h, qqFuncN_eq_qqFunc]
  simpa using qqFunc_absolute (V := V) 0 zeroIndex 0

lemma qqOne_eq_qqFunc : (𝟏 : V) = ^func 0 (oneIndex : V) 0 := by
  have h : (𝟏 : ℕ) = qqFuncN 0 oneIndex 0 := rfl
  rw [h, qqFuncN_eq_qqFunc]
  simpa using qqFunc_absolute (V := V) 0 oneIndex 0

@[simp] lemma zero_semiterm {n : V} : IsSemiterm ℒₒᵣ n (𝟎 : V) := by
  simp [qqZero_eq_qqFunc]

@[simp] lemma one_semiterm {n : V} : IsSemiterm ℒₒᵣ n (𝟏 : V) := by
  simp [qqOne_eq_qqFunc]

lemma coe_zero_eq : (𝟎 : V) = (^func 0 ⌜(Language.Zero.zero : (ℒₒᵣ).Func 0)⌝ 0) :=
  qqZero_eq_qqFunc

lemma coe_one_eq : (𝟏 : V) = (^func 0 ⌜(Language.One.one : (ℒₒᵣ).Func 0)⌝ 0) :=
  qqOne_eq_qqFunc

namespace Numeral

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic.Numeral
  (blueprint numeralAuxGraph)

lemma qqAdd_one_le_exp_exp {t n : V} (hn : ((𝟏 + addIndex + 2 : ℕ) : V) ≤ n)
    (ht : t ≤ Exp.exp (Exp.exp n)) : t ^+ 𝟏 ≤ Exp.exp (Exp.exp (n + 10)) := by
  have hle {a m m' : V} (h : a ≤ Exp.exp (Exp.exp m)) (hm : m ≤ m') : a ≤ Exp.exp (Exp.exp m') :=
    le_trans h (exp_monotone_le.mpr (exp_monotone_le.mpr hm))
  have hpa (a b : V) : ⟪a, b⟫ ≤ a ∷ b := by rw [adjoin_def]; exact le_self_add
  have hcast {a : ℕ} (h : a ≤ 𝟏 + addIndex + 2) : (a : V) ≤ n :=
    le_trans (by exact_mod_cast h) hn
  have h1n : 1 ≤ n := by simpa using hcast (a := 1) (by omega)
  have m1 : n ≤ n + 2 := le_self_add
  have m2 : n + 2 ≤ n + 2 + 2 := le_self_add
  have m3 : n + 2 + 2 ≤ n + 2 + 2 + 2 := le_self_add
  have m4 : n + 2 + 2 + 2 ≤ n + 2 + 2 + 2 + 2 := le_self_add
  have hone : (𝟏 : V) ≤ Exp.exp (Exp.exp n) := le_exp_exp (hcast (by omega))
  have hadd : (addIndex : V) ≤ Exp.exp (Exp.exp n) := le_exp_exp (hcast (by omega))
  have h2 : (2 : V) ≤ Exp.exp (Exp.exp n) := le_exp_exp (by simpa using hcast (a := 2) (by omega))
  have w1 : ?[(𝟏 : V)] ≤ Exp.exp (Exp.exp (n + 2)) := adjoin_le_exp_exp h1n hone zero_le
  have w2 : ?[t, (𝟏 : V)] ≤ Exp.exp (Exp.exp (n + 2 + 2)) :=
    adjoin_le_exp_exp (le_trans h1n m1) (hle ht m1) w1
  have h3 : ⟪(addIndex : V), ?[t, (𝟏 : V)]⟫ ≤ Exp.exp (Exp.exp (n + 2 + 2 + 2)) :=
    le_trans (hpa _ _) (adjoin_le_exp_exp (le_trans h1n (m1.trans m2))
      (hle hadd (m1.trans m2)) w2)
  have h4 : ⟪(2 : V), ⟪(addIndex : V), ?[t, (𝟏 : V)]⟫⟫ ≤ Exp.exp (Exp.exp (n + 2 + 2 + 2 + 2)) :=
    le_trans (hpa _ _) (adjoin_le_exp_exp (le_trans h1n (m1.trans (m2.trans m3)))
      (hle h2 (m1.trans (m2.trans m3))) h3)
  have h5 : ^func 2 (addIndex : V) ?[t, (𝟏 : V)] ≤ Exp.exp (Exp.exp (n + 2 + 2 + 2 + 2 + 2)) :=
    adjoin_le_exp_exp (le_trans h1n (m1.trans (m2.trans (m3.trans m4))))
      (hle h2 (m1.trans (m2.trans (m3.trans m4)))) h4
  refine le_trans h5 (exp_monotone_le.mpr (exp_monotone_le.mpr (le_of_eq ?_)))
  grind

noncomputable def construction : PR.Construction V blueprint where
  zero _ := 𝟏
  succ _ _ t := t ^+ 𝟏
  zero_defined := .mk fun v ↦ by simp [blueprint, numeral_eq_natCast]
  succ_defined := .mk fun v ↦ by simp [qqAdd, blueprint, numeral_eq_natCast]
  zero_locallyDelta0 := LocallyDelta0Function.const (𝟏 : V)
  succ_locallyDelta0 := qqAdd_locallyDelta0.comp₂ (LocallyDelta0Function.var 0)
    (LocallyDelta0Function.const (𝟏 : V))
  bound _ i := Exp.exp (Exp.exp (16 * i + ((𝟏 + addIndex + 2 : ℕ) : V)))
  zero_lt_bound _ := by
    rw [mul_zero, zero_add]
    exact lt_of_le_of_lt (by exact_mod_cast (by omega : 𝟏 ≤ 𝟏 + addIndex + 2))
      (lt_trans (lt_exp _) (exp_monotone.mpr (lt_exp _)))
  succ_lt_bound _ i z h := by
    refine lt_of_le_of_lt (qqAdd_one_le_exp_exp le_add_self h.le)
      (exp_monotone.mpr (exp_monotone.mpr ?_))
    rw [show 16 * (i + 1) + ((𝟏 + addIndex + 2 : ℕ) : V) =
      (16 * i + ((𝟏 + addIndex + 2 : ℕ) : V)) + 16 by grind]
    gcongr
    exact_mod_cast (by norm_num : (10 : ℕ) < 16)
  bound_monotone _ _ _ h := exp_monotone_le.mpr (exp_monotone_le.mpr (by gcongr))
  bound_locallyDelta0 := LocallyDelta0Function.exp_exp_mul_add 16 (LocallyDelta0Function.var 0)
    (LocallyDelta0Function.const (((𝟏 + addIndex + 2 : ℕ) : V)))

/-- The code of the numeral for `x + 1`. -/
noncomputable def numeralAux (x : V) : V := construction.result ![] x

@[simp] lemma numeralAux_zero : numeralAux (0 : V) = 𝟏 := by simp [numeralAux, construction]

@[simp] lemma numeralAux_succ (x : V) : numeralAux (x + 1) = numeralAux x ^+ 𝟏 := by
  simp [numeralAux, construction]

section

instance numeralAux.defined : 𝚺ᴬ₁-Function₁ (numeralAux : V → V) via numeralAuxGraph := .mk
  fun v ↦ by simp [construction.result_defined_iff, numeralAuxGraph]; rfl

instance numeralAux.definable : 𝚺ᴬ₁-Function₁ (numeralAux : V → V) :=
  numeralAux.defined.to_definable

end

lemma numeralAux_locallyDelta0 : LocallyDelta0Function₁ (numeralAux : V → V) := by
  convert construction.result_locallyDelta0 (V := V) using 3
  simp [numeralAux, Matrix.empty_eq]

@[simp] lemma lt_numeralAux_self (n : V) : n < numeralAux n := by
  refine LocallyDelta0Pred.succ_induction (P := fun n ↦ n < numeralAux n) ?_ ?_ ?_ n
  · exact LocallyDelta0.lt (LocallyDelta0Function.var (0 : Fin 1))
      (numeralAux_locallyDelta0.comp₁ (LocallyDelta0Function.var (0 : Fin 1)))
  · rw [numeralAux_zero, qqOne_eq_qqFunc]
    exact arity_lt_qqFunc 0 _ 0
  · intro n ih
    exact lt_of_lt_of_le ((add_lt_add_iff_right 1).mpr ih) (by simp [succ_le_iff_lt])

@[simp] lemma numeralAux_semiterm (n x : V) : IsSemiterm ℒₒᵣ n (numeralAux x) := by
  refine LocallyDelta0Pred.succ_induction (P := fun x ↦ IsSemiterm ℒₒᵣ n (numeralAux x)) ?_ ?_ ?_ x
  · exact isSemiterm_locallyDelta0.rel_comp₂ (LocallyDelta0Function.const n)
      (numeralAux_locallyDelta0.comp₁ (LocallyDelta0Function.var (0 : Fin 1)))
  · simp
  · intro x ih; simp [qqAdd, ih]

end Numeral

section numeral

open Numeral

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic (numeralGraph)

/-- The code of the numeral of `x`. -/
noncomputable def numeral (x : V) : V := if x = 0 then 𝟎 else numeralAux (x - 1)

@[simp] lemma numeral_zero : numeral (0 : V) = 𝟎 := by simp [numeral]

@[simp] lemma numeral_one : numeral (1 : V) = 𝟏 := by simp [numeral]

@[simp] lemma numeral_add_two {n : V} : numeral (n + 1 + 1 : V) = numeral (n + 1) ^+ 𝟏 := by
  simp [numeral]

lemma numeral_succ_pos {n : V} (pos : 0 < n) : numeral (n + 1 : V) = numeral n ^+ 𝟏 := by
  rcases zero_or_succ n with (rfl | ⟨n, rfl⟩)
  · simp at pos
  simp [numeral]

@[simp] lemma numeral_semiterm (n x : V) : IsSemiterm ℒₒᵣ n (numeral x) := by
  by_cases hx : x = 0 <;> simp [hx, numeral]

@[simp] lemma numeral_uterm (x : V) : IsUTerm ℒₒᵣ (numeral x) := (numeral_semiterm 0 x).isUTerm

@[simp] lemma le_numeral_self (n : V) : n ≤ numeral n := by
  rcases zero_or_succ n with (rfl | ⟨n, rfl⟩)
  · simp
  · simp [numeral, succ_le_iff_lt]

section

instance numeral_defined : 𝚺ᴬ₁-Function₁ (numeral : V → V) via numeralGraph := .mk fun v ↦ by
  simp [numeralGraph, numeral_eq_natCast]
  by_cases hv1 : v 1 = 0 <;> simp [hv1, numeral]

instance numeral_definable : 𝚺ᴬ₁-Function₁ (numeral : V → V) := numeral_defined.to_definable

instance numeral_definable' (Γ m) : Γᴬ_[m + 1]-Function₁ (numeral : V → V) :=
  .of_sigmaOne numeral_definable

end

lemma numeral_locallyDelta0 : LocallyDelta0Function₁ (numeral : V → V) :=
  LocallyDelta0Function.ite (Q := fun v : Fin 1 → V ↦ v 0 = 0)
    (LocallyDelta0.eq (LocallyDelta0Function.var 0) (LocallyDelta0Function.const 0))
    (LocallyDelta0Function.const (𝟎 : V)) <|
    numeralAux_locallyDelta0.comp₁ (LocallyDelta0Function.sub.comp₂
      (LocallyDelta0Function.var 0) (LocallyDelta0Function.const 1))

@[simp] lemma numeral_substs {n m w : V} (_ : IsSemitermVec ℒₒᵣ n m w) (x : V) :
    termSubst ℒₒᵣ w (numeral x) = numeral x := by
  refine LocallyDelta0Pred.succ_induction (P := fun x ↦ termSubst ℒₒᵣ w (numeral x) = numeral x)
    ?_ ?_ ?_ x
  · exact LocallyDelta0.eq (termSubst_locallyDelta0.comp₂ (LocallyDelta0Function.const w)
      (numeral_locallyDelta0.comp₁ (LocallyDelta0Function.var (0 : Fin 1))))
      (numeral_locallyDelta0.comp₁ (LocallyDelta0Function.var (0 : Fin 1)))
  · simp [qqZero_eq_qqFunc]
  · intro x ih
    rcases zero_or_succ x with (rfl | ⟨x, rfl⟩)
    · simp [qqOne_eq_qqFunc]
    · simp only [numeral_add_two, qqAdd]
      rw [termSubst_func (L := ℒₒᵣ) (by simp) (by simp [qqOne_eq_qqFunc])]
      simp [ih, qqOne_eq_qqFunc]

@[simp] lemma numeral_shift (x : V) :
    termShift ℒₒᵣ (numeral x) = numeral x := by
  refine LocallyDelta0Pred.succ_induction (P := fun x ↦ termShift ℒₒᵣ (numeral x) = numeral x)
    ?_ ?_ ?_ x
  · exact LocallyDelta0.eq (termShift_locallyDelta0.comp₁
      (numeral_locallyDelta0.comp₁ (LocallyDelta0Function.var (0 : Fin 1))))
      (numeral_locallyDelta0.comp₁ (LocallyDelta0Function.var (0 : Fin 1)))
  · simp [qqZero_eq_qqFunc]
  · intro x ih
    rcases zero_or_succ x with (rfl | ⟨x, rfl⟩)
    · simp [qqOne_eq_qqFunc]
    · simp only [numeral_add_two, qqAdd]
      rw [termShift_func (L := ℒₒᵣ) (by simp) (by simp [qqOne_eq_qqFunc])]
      simp [ih, qqOne_eq_qqFunc]

@[simp] lemma numeral_bShift (x : V) :
    termBShift ℒₒᵣ (numeral x) = numeral x := by
  refine LocallyDelta0Pred.succ_induction (P := fun x ↦ termBShift ℒₒᵣ (numeral x) = numeral x)
    ?_ ?_ ?_ x
  · exact LocallyDelta0.eq (termBShift_locallyDelta0.comp₁
      (numeral_locallyDelta0.comp₁ (LocallyDelta0Function.var (0 : Fin 1))))
      (numeral_locallyDelta0.comp₁ (LocallyDelta0Function.var (0 : Fin 1)))
  · simp [qqZero_eq_qqFunc]
  · intro x ih
    rcases zero_or_succ x with (rfl | ⟨x, rfl⟩)
    · simp [qqOne_eq_qqFunc]
    · simp [qqAdd, ih, qqOne_eq_qqFunc]

end numeral

end Arithmetic

end

end FFL.FirstOrder.Arithmetic.ElementaryArithmetic.Bootstrapping
