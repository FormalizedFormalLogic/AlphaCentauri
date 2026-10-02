module

public import AlphaCentauri.Bootstrapping.PartialTruth.Substitution
public import AlphaCentauri.Bootstrapping.Proof.FvSubst

/-!
# Numeral assignments to free variables

`fvAssign f p` replaces every free variable `^&i` of the coded formula `p` by the numeral of
`f.[i]`, the `i`-th entry of the sequence `f` (which is `0` beyond the length of `f`). It commutes
with the connectives, negation, substitution for bound variables, the shift of free variables and
`free`, and preserves the internal $\Delta_0$ and prenex classes; so does `fvSubst` by closed
terms.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

open Arithmetic (numeral numeralGraph numeral_uterm numeral_semiterm numeral_substs qqNLT qqLT)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Terms -/

namespace TermFvAssign

def blueprint : Language.TermRec.Blueprint 1 where
  bvar := .mkSigma “y z f. !qqBvarDef y z”
  fvar := .mkSigma “y x f. ∃ a, !nthDef a f x ∧ !numeralGraph y a”
  func := .mkSigma “y k g v v' f. !qqFuncDef y k g v'”

noncomputable def construction : Language.TermRec.Construction V blueprint where
  bvar (_ z) := ^#z
  fvar (param x) := numeral (param 0).[x]
  func (_ k g _ v') := ^func k g v'
  bvar_defined := .mk fun v ↦ by simp [blueprint]
  fvar_defined := .mk fun v ↦ by simp [blueprint, Arithmetic.numeral_defined.df]
  func_defined := .mk fun v ↦ by simp [blueprint]

end TermFvAssign

open TermFvAssign

/-- `termFvAssign f t` is the coded term `t` with each free variable `^&i` replaced by the
numeral of `f.[i]`. -/
noncomputable def termFvAssign (f t : V) : V := construction.result ℒₒᵣ ![f] t

/-- `termFvAssignVec k f v` applies `termFvAssign f` to each entry of the coded `k`-vector `v`. -/
noncomputable def termFvAssignVec (k f v : V) : V := construction.resultVec ℒₒᵣ ![f] k v

noncomputable def termFvAssignGraph : 𝚺ᴬ₁.Semisentence 3 :=
  (blueprint.result ℒₒᵣ).rew <| Rew.subst ![#0, #2, #1]

noncomputable def termFvAssignVecGraph : 𝚺ᴬ₁.Semisentence 4 :=
  (blueprint.resultVec ℒₒᵣ).rew <| Rew.subst ![#0, #1, #3, #2]

section

variable {Γ : SigmaPiDelta} {m : ℕ}

instance termFvAssign.defined :
    𝚺ᴬ₁-Function₂ (termFvAssign : V → V → V) via termFvAssignGraph := .mk fun v ↦ by
  simpa [termFvAssignGraph, termFvAssign, Matrix.constant_eq_singleton, Matrix.comp_vecCons']
    using construction.result_defined.defined ![v 0, v 2, v 1]

instance termFvAssign.definable : 𝚺ᴬ₁-Function₂ (termFvAssign : V → V → V) :=
  termFvAssign.defined.to_definable

instance termFvAssign.definable' : Γᴬ-[m + 1]-Function₂ (termFvAssign : V → V → V) :=
  termFvAssign.definable.of_sigmaOne

instance termFvAssignVec.defined :
    𝚺ᴬ₁-Function₃ (termFvAssignVec : V → V → V → V) via termFvAssignVecGraph := .mk fun v ↦ by
  simpa [termFvAssignVecGraph, termFvAssignVec, Matrix.constant_eq_singleton,
    Matrix.comp_vecCons'] using construction.resultVec_defined.defined ![v 0, v 1, v 3, v 2]

instance termFvAssignVec.definable : 𝚺ᴬ₁-Function₃ (termFvAssignVec : V → V → V → V) :=
  termFvAssignVec.defined.to_definable

instance termFvAssignVec.definable' : Γᴬ-[m + 1]-Function₃ (termFvAssignVec : V → V → V → V) :=
  termFvAssignVec.definable.of_sigmaOne

end

section

variable {f : V}

@[simp] lemma termFvAssign_bvar (z : V) : termFvAssign f ^#z = ^#z := by
  simp [termFvAssign, construction]

@[simp] lemma termFvAssign_fvar (x : V) : termFvAssign f ^&x = numeral f.[x] := by
  simp [termFvAssign, construction]

@[simp] lemma termFvAssign_func {k g v : V} (hg : (ℒₒᵣ).IsFunc k g) (hv : IsUTermVec ℒₒᵣ k v) :
    termFvAssign f (^func k g v) = ^func k g (termFvAssignVec k f v) := by
  simp [termFvAssign, construction, hg, hv]
  rfl

@[simp] lemma len_termFvAssignVec {k v : V} (hv : IsUTermVec ℒₒᵣ k v) :
    len (termFvAssignVec k f v) = k :=
  construction.resultVec_lh ℒₒᵣ _ hv

@[simp] lemma nth_termFvAssignVec {k v i : V} (hv : IsUTermVec ℒₒᵣ k v) (hi : i < k) :
    (termFvAssignVec k f v).[i] = termFvAssign f v.[i] :=
  construction.nth_resultVec ℒₒᵣ _ hv hi

@[simp] lemma termFvAssignVec_nil : termFvAssignVec 0 f (0 : V) = 0 :=
  construction.resultVec_nil ℒₒᵣ _

lemma termFvAssignVec_cons {k t v : V} (ht : IsUTerm ℒₒᵣ t) (hv : IsUTermVec ℒₒᵣ k v) :
    termFvAssignVec (k + 1) f (t ∷ v) = termFvAssign f t ∷ termFvAssignVec k f v :=
  construction.resultVec_cons ℒₒᵣ ![f] hv ht

@[simp] lemma termFvAssignVec_cons₁ {t : V} (ht : IsUTerm ℒₒᵣ t) :
    termFvAssignVec 1 f ?[t] = ?[termFvAssign f t] := by
  simpa using termFvAssignVec_cons (f := f) ht IsUTermVec.empty

@[simp] lemma termFvAssignVec_cons₂ {t₁ t₂ : V} (ht₁ : IsUTerm ℒₒᵣ t₁) (ht₂ : IsUTerm ℒₒᵣ t₂) :
    termFvAssignVec 2 f ?[t₁, t₂] = ?[termFvAssign f t₁, termFvAssign f t₂] := by
  rw [show (2 : V) = 0 + 1 + 1 by simp [one_add_one_eq_two], termFvAssignVec_cons] <;>
    simp [*]

@[simp] lemma IsSemiterm.termFvAssign {n t : V} (ht : IsSemiterm ℒₒᵣ n t) :
    IsSemiterm ℒₒᵣ n (termFvAssign f t) := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz
    simp [hz]
  · intro x
    simp
  · intro k g v hg hv ih
    simp only [termFvAssign_func hg hv.isUTerm, IsSemiterm.func, hg, true_and]
    exact IsSemitermVec.iff.mpr
      ⟨by simp [hv.isUTerm], fun i hi ↦ by rw [nth_termFvAssignVec hv.isUTerm hi]; exact ih i hi⟩

@[simp] lemma IsSemitermVec.termFvAssignVec {k n v : V} (hv : IsSemitermVec ℒₒᵣ k n v) :
    IsSemitermVec ℒₒᵣ k n (termFvAssignVec k f v) :=
  IsSemitermVec.iff.mpr ⟨by simp [hv.isUTerm], fun i hi ↦ by
    rw [nth_termFvAssignVec hv.isUTerm hi]
    exact (hv.nth hi).termFvAssign⟩

lemma IsUTermVec.termFvAssignVec {k v : V} (hv : IsUTermVec ℒₒᵣ k v) :
    IsUTermVec ℒₒᵣ k (termFvAssignVec k f v) :=
  hv.isSemitermVec.termFvAssignVec.isUTerm

@[simp] lemma termFvAssign_numeral (x : V) : termFvAssign f (numeral x) = numeral x := by
  induction x using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp [Arithmetic.zero, Arithmetic.qqFunc_absolute, qqFuncN_eq_qqFunc]
  case succ x ih =>
    rcases zero_or_succ x with rfl | ⟨x, rfl⟩
    · simp [Arithmetic.one, Arithmetic.qqFunc_absolute, qqFuncN_eq_qqFunc]
    · simp only [Arithmetic.numeral_add_two, Arithmetic.qqAdd]
      rw [termFvAssign_func (by simp)
        (by simp [Arithmetic.one, Arithmetic.qqFunc_absolute, qqFuncN_eq_qqFunc])]
      simp [ih, Arithmetic.one, Arithmetic.qqFunc_absolute, qqFuncN_eq_qqFunc]

lemma termFvAssign_termShift {b t : V} (ht : IsUTerm ℒₒᵣ t) :
    termFvAssign (b ∷ f) (termShift ℒₒᵣ t) = termFvAssign f t := by
  apply IsUTerm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z
    simp
  · intro x
    simp
  · intro k g v hg hv ih
    rw [termShift_func hg hv, termFvAssign_func hg hv.termShiftVec, termFvAssign_func hg hv]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k (by simp [hv.termShiftVec]) (by simp [hv])
    intro i hi
    rw [nth_termFvAssignVec hv.termShiftVec hi, nth_termShiftVec hv hi,
      nth_termFvAssignVec hv hi, ih i hi]

lemma termFvAssign_termBShift {t : V} (ht : IsUTerm ℒₒᵣ t) :
    termFvAssign f (termBShift ℒₒᵣ t) = termBShift ℒₒᵣ (termFvAssign f t) := by
  apply IsUTerm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z
    simp
  · intro x
    simp [termBShift_zero (numeral_semiterm 0 f.[x])]
  · intro k g v hg hv ih
    rw [termBShift_func hg hv, termFvAssign_func hg hv.termBShiftVec, termFvAssign_func hg hv,
      termBShift_func hg hv.termFvAssignVec]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k (by simp [hv.termBShiftVec]) (by simp [hv.termFvAssignVec])
    intro i hi
    rw [nth_termFvAssignVec hv.termBShiftVec hi, nth_termBShiftVec hv hi,
      nth_termBShiftVec hv.termFvAssignVec hi, nth_termFvAssignVec hv hi, ih i hi]

lemma termFvAssign_termSubst {n m w t : V} (hw : IsSemitermVec ℒₒᵣ n m w)
    (ht : IsSemiterm ℒₒᵣ n t) :
    termFvAssign f (termSubst ℒₒᵣ w t) =
      termSubst ℒₒᵣ (termFvAssignVec n f w) (termFvAssign f t) := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz
    simp [nth_termFvAssignVec hw.isUTerm hz]
  · intro x
    simp [numeral_substs hw.termFvAssignVec]
  · intro k g v hg hv ih
    rw [termSubst_func hg hv.isUTerm, termFvAssign_func hg (hw.termSubstVec hv).isUTerm,
      termFvAssign_func hg hv.isUTerm, termSubst_func hg hv.termFvAssignVec.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k (by simp [(hw.termSubstVec hv).isUTerm])
      (by simp [hv.termFvAssignVec.isUTerm])
    intro i hi
    rw [nth_termFvAssignVec (hw.termSubstVec hv).isUTerm hi, nth_termSubstVec hv.isUTerm hi,
      nth_termSubstVec hv.termFvAssignVec.isUTerm hi, nth_termFvAssignVec hv.isUTerm hi, ih i hi]

lemma termFvAssignVec_qVec {n m w : V} (hw : IsSemitermVec ℒₒᵣ n m w) :
    termFvAssignVec (n + 1) f (qVec ℒₒᵣ w) = qVec ℒₒᵣ (termFvAssignVec n f w) := by
  apply nth_ext' (n + 1) (len_termFvAssignVec hw.qVec.isUTerm)
    (len_qVec hw.termFvAssignVec.isUTerm)
  intro i hi
  rw [nth_termFvAssignVec hw.qVec.isUTerm hi]
  rcases zero_or_succ i with rfl | ⟨j, rfl⟩
  · simp [qVec]
  · have hj : j < n := by simpa using hi
    have h₁ : (qVec ℒₒᵣ w).[j + 1] = termBShift ℒₒᵣ w.[j] := by
      rw [qVec, hw.lh]
      simp [nth_termBShiftVec hw.isUTerm hj]
    have h₂ : (qVec ℒₒᵣ (termFvAssignVec n f w)).[j + 1] =
        termBShift ℒₒᵣ (termFvAssign f w.[j]) := by
      rw [qVec, len_termFvAssignVec hw.isUTerm]
      simp [nth_termBShiftVec hw.termFvAssignVec.isUTerm hj, hw.isUTerm, hj]
    rw [h₁, h₂, termFvAssign_termBShift (hw.isUTerm.nth hj)]

end

/-! ## Formulas -/

namespace FvAssign

noncomputable def blueprint : UformulaRec1.Blueprint where
  rel := .mkSigma “y f k R v. ∃ v', !termFvAssignVecGraph v' k f v ∧ !qqRelDef y k R v'”
  nrel := .mkSigma “y f k R v. ∃ v', !termFvAssignVecGraph v' k f v ∧ !qqNRelDef y k R v'”
  verum := .mkSigma “y f. !qqVerumDef y”
  falsum := .mkSigma “y f. !qqFalsumDef y”
  and := .mkSigma “y f p q p' q'. !qqAndDef y p' q'”
  or := .mkSigma “y f p q p' q'. !qqOrDef y p' q'”
  all := .mkSigma “y f p ys. ∃ p', !nthDef p' ys 0 ∧ !qqAllDef y p'”
  exs := .mkSigma “y f p ys. ∃ p', !nthDef p' ys 0 ∧ !qqExsDef y p'”

noncomputable def construction : UformulaRec1.Construction V blueprint where
  rel f k R v := ^rel k R (termFvAssignVec k f v)
  nrel f k R v := ^nrel k R (termFvAssignVec k f v)
  verum _ := ^⊤
  falsum _ := ^⊥
  and _ _ _ p q := p ^⋏ q
  or _ _ _ p q := p ^⋎ q
  all _ _ ys := ^∀ ys.[0]
  exs _ _ ys := ^∃ ys.[0]
  rel_defined := .mk fun v ↦ by simp [blueprint]
  nrel_defined := .mk fun v ↦ by simp [blueprint]
  verum_defined := .mk fun v ↦ by simp [blueprint]
  falsum_defined := .mk fun v ↦ by simp [blueprint]
  and_defined := .mk fun v ↦ by simp [blueprint]
  or_defined := .mk fun v ↦ by simp [blueprint]
  all_defined := .mk fun v ↦ by simp [blueprint]
  exs_defined := .mk fun v ↦ by simp [blueprint]

end FvAssign

/-- `fvAssign f p` is the coded formula `p` with each free variable `^&i` replaced by the numeral
of `f.[i]`. -/
noncomputable def fvAssign (f p : V) : V := FvAssign.construction.result ℒₒᵣ f p

noncomputable def fvAssignGraph : 𝚺ᴬ₁.Semisentence 3 := FvAssign.blueprint.result ℒₒᵣ

section

variable {Γ : SigmaPiDelta} {m : ℕ}

instance fvAssign.defined : 𝚺ᴬ₁-Function₂ (fvAssign : V → V → V) via fvAssignGraph :=
  FvAssign.construction.result_defined

instance fvAssign.definable : 𝚺ᴬ₁-Function₂ (fvAssign : V → V → V) :=
  fvAssign.defined.to_definable

instance fvAssign.definable' : Γᴬ-[m + 1]-Function₂ (fvAssign : V → V → V) :=
  fvAssign.definable.of_sigmaOne

end

section

variable {f : V}

@[simp] lemma fvAssign_rel {k R v : V} (hR : (ℒₒᵣ).IsRel k R) (hv : IsUTermVec ℒₒᵣ k v) :
    fvAssign f (^rel k R v) = ^rel k R (termFvAssignVec k f v) := by
  simp [fvAssign, hR, hv, FvAssign.construction]

@[simp] lemma fvAssign_nrel {k R v : V} (hR : (ℒₒᵣ).IsRel k R) (hv : IsUTermVec ℒₒᵣ k v) :
    fvAssign f (^nrel k R v) = ^nrel k R (termFvAssignVec k f v) := by
  simp [fvAssign, hR, hv, FvAssign.construction]

@[simp] lemma fvAssign_verum : fvAssign f (^⊤ : V) = ^⊤ := by
  simp [fvAssign, FvAssign.construction]

@[simp] lemma fvAssign_falsum : fvAssign f (^⊥ : V) = ^⊥ := by
  simp [fvAssign, FvAssign.construction]

@[simp] lemma fvAssign_and {p q : V} (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q) :
    fvAssign f (p ^⋏ q) = fvAssign f p ^⋏ fvAssign f q := by
  simp [fvAssign, hp, hq, FvAssign.construction]

@[simp] lemma fvAssign_or {p q : V} (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q) :
    fvAssign f (p ^⋎ q) = fvAssign f p ^⋎ fvAssign f q := by
  simp [fvAssign, hp, hq, FvAssign.construction]

@[simp] lemma fvAssign_all {p : V} (hp : IsUFormula ℒₒᵣ p) :
    fvAssign f (^∀ p) = ^∀ (fvAssign f p) := by
  simp [fvAssign, hp, FvAssign.construction]

@[simp] lemma fvAssign_exs {p : V} (hp : IsUFormula ℒₒᵣ p) :
    fvAssign f (^∃ p) = ^∃ (fvAssign f p) := by
  simp [fvAssign, hp, FvAssign.construction]

lemma fvAssign_not_uformula {p : V} (hp : ¬IsUFormula ℒₒᵣ p) : fvAssign f p = 0 :=
  FvAssign.construction.result_prop_not _ hp

@[simp] lemma IsSemiformula.fvAssign {n p : V} (hp : IsSemiformula ℒₒᵣ n p) :
    IsSemiformula ℒₒᵣ n (fvAssign f p) := by
  apply IsSemiformula.pi1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R v hR hv
    simp [hR, hv.isUTerm, hv.termFvAssignVec]
  · intro n k R v hR hv
    simp [hR, hv.isUTerm, hv.termFvAssignVec]
  · simp
  · simp
  · intro n p q hp hq ihp ihq
    simp [hp.isUFormula, hq.isUFormula, ihp, ihq]
  · intro n p q hp hq ihp ihq
    simp [hp.isUFormula, hq.isUFormula, ihp, ihq]
  · intro n p hp ihp
    simp [hp.isUFormula, ihp]
  · intro n p hp ihp
    simp [hp.isUFormula, ihp]

lemma IsUFormula.fvAssign {p : V} (hp : IsUFormula ℒₒᵣ p) : IsUFormula ℒₒᵣ (fvAssign f p) :=
  hp.isSemiformula.fvAssign.isUFormula

lemma fvAssign_neg {p : V} (hp : IsUFormula ℒₒᵣ p) :
    fvAssign f (neg ℒₒᵣ p) = neg ℒₒᵣ (fvAssign f p) := by
  apply IsUFormula.induction1 𝚺 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · definability
  · intro k R v hR hv
    rw [neg_rel hR hv, fvAssign_nrel hR hv, fvAssign_rel hR hv, neg_rel hR hv.termFvAssignVec]
  · intro k R v hR hv
    rw [neg_nrel hR hv, fvAssign_rel hR hv, fvAssign_nrel hR hv, neg_nrel hR hv.termFvAssignVec]
  · simp
  · simp
  · intro p q hp hq ihp ihq
    rw [neg_and hp hq, fvAssign_or hp.neg hq.neg, fvAssign_and hp hq,
      neg_and hp.fvAssign hq.fvAssign, ihp, ihq]
  · intro p q hp hq ihp ihq
    rw [neg_or hp hq, fvAssign_and hp.neg hq.neg, fvAssign_or hp hq,
      neg_or hp.fvAssign hq.fvAssign, ihp, ihq]
  · intro p hp ih
    rw [neg_all hp, fvAssign_exs hp.neg, fvAssign_all hp, neg_all hp.fvAssign, ih]
  · intro p hp ih
    rw [neg_ex hp, fvAssign_all hp.neg, fvAssign_exs hp, neg_ex hp.fvAssign, ih]

lemma fvAssign_shift {b p : V} (hp : IsUFormula ℒₒᵣ p) :
    fvAssign (b ∷ f) (shift ℒₒᵣ p) = fvAssign f p := by
  apply IsUFormula.induction1 𝚺 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · definability
  · intro k R v hR hv
    rw [shift_rel hR hv, fvAssign_rel hR hv.termShiftVec, fvAssign_rel hR hv]
    simp only [qqRel_inj, true_and]
    apply nth_ext' k (by simp [hv.termShiftVec]) (by simp [hv])
    intro i hi
    rw [nth_termFvAssignVec hv.termShiftVec hi, nth_termShiftVec hv hi,
      nth_termFvAssignVec hv hi, termFvAssign_termShift (hv.nth hi)]
  · intro k R v hR hv
    rw [shift_nrel hR hv, fvAssign_nrel hR hv.termShiftVec, fvAssign_nrel hR hv]
    simp only [qqNRel_inj, true_and]
    apply nth_ext' k (by simp [hv.termShiftVec]) (by simp [hv])
    intro i hi
    rw [nth_termFvAssignVec hv.termShiftVec hi, nth_termShiftVec hv hi,
      nth_termFvAssignVec hv hi, termFvAssign_termShift (hv.nth hi)]
  · simp
  · simp
  · intro p q hp hq ihp ihq
    rw [shift_and hp hq, fvAssign_and hp.shift hq.shift, fvAssign_and hp hq, ihp, ihq]
  · intro p q hp hq ihp ihq
    rw [shift_or hp hq, fvAssign_or hp.shift hq.shift, fvAssign_or hp hq, ihp, ihq]
  · intro p hp ih
    rw [shift_all hp, fvAssign_all hp.shift, fvAssign_all hp, ih]
  · intro p hp ih
    rw [shift_exs hp, fvAssign_exs hp.shift, fvAssign_exs hp, ih]

lemma fvAssign_subst {n m w p : V} (hw : IsSemitermVec ℒₒᵣ n m w) (hp : IsSemiformula ℒₒᵣ n p) :
    fvAssign f (subst ℒₒᵣ w p) = subst ℒₒᵣ (termFvAssignVec n f w) (fvAssign f p) := by
  revert m w
  apply IsSemiformula.pi1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R v hR hv m w hw
    rw [substs_rel hR hv.isUTerm, fvAssign_rel hR (hw.termSubstVec hv).isUTerm,
      fvAssign_rel hR hv.isUTerm, substs_rel hR hv.termFvAssignVec.isUTerm]
    simp only [qqRel_inj, true_and]
    apply nth_ext' k (by simp [(hw.termSubstVec hv).isUTerm])
      (by simp [hv.termFvAssignVec.isUTerm])
    intro i hi
    rw [nth_termFvAssignVec (hw.termSubstVec hv).isUTerm hi, nth_termSubstVec hv.isUTerm hi,
      nth_termSubstVec hv.termFvAssignVec.isUTerm hi, nth_termFvAssignVec hv.isUTerm hi,
      termFvAssign_termSubst hw (hv.nth hi)]
  · intro n k R v hR hv m w hw
    rw [substs_nrel hR hv.isUTerm, fvAssign_nrel hR (hw.termSubstVec hv).isUTerm,
      fvAssign_nrel hR hv.isUTerm, substs_nrel hR hv.termFvAssignVec.isUTerm]
    simp only [qqNRel_inj, true_and]
    apply nth_ext' k (by simp [(hw.termSubstVec hv).isUTerm])
      (by simp [hv.termFvAssignVec.isUTerm])
    intro i hi
    rw [nth_termFvAssignVec (hw.termSubstVec hv).isUTerm hi, nth_termSubstVec hv.isUTerm hi,
      nth_termSubstVec hv.termFvAssignVec.isUTerm hi, nth_termFvAssignVec hv.isUTerm hi,
      termFvAssign_termSubst hw (hv.nth hi)]
  · intros
    simp
  · intros
    simp
  · intro n p q hp hq ihp ihq m w hw
    rw [substs_and hp.isUFormula hq.isUFormula,
      fvAssign_and (hp.subst hw).isUFormula (hq.subst hw).isUFormula,
      fvAssign_and hp.isUFormula hq.isUFormula,
      substs_and hp.fvAssign.isUFormula hq.fvAssign.isUFormula, ihp hw, ihq hw]
  · intro n p q hp hq ihp ihq m w hw
    rw [substs_or hp.isUFormula hq.isUFormula,
      fvAssign_or (hp.subst hw).isUFormula (hq.subst hw).isUFormula,
      fvAssign_or hp.isUFormula hq.isUFormula,
      substs_or hp.fvAssign.isUFormula hq.fvAssign.isUFormula, ihp hw, ihq hw]
  · intro n p hp ih m w hw
    rw [substs_all hp.isUFormula, fvAssign_all (hp.subst hw.qVec).isUFormula,
      fvAssign_all hp.isUFormula, substs_all hp.fvAssign.isUFormula, ih hw.qVec,
      termFvAssignVec_qVec hw]
  · intro n p hp ih m w hw
    rw [substs_ex hp.isUFormula, fvAssign_exs (hp.subst hw.qVec).isUFormula,
      fvAssign_exs hp.isUFormula, substs_ex hp.fvAssign.isUFormula, ih hw.qVec,
      termFvAssignVec_qVec hw]

lemma fvAssign_substs1 {m t p : V} (ht : IsSemiterm ℒₒᵣ m t) (hp : IsSemiformula ℒₒᵣ 1 p) :
    fvAssign f (substs1 ℒₒᵣ t p) = substs1 ℒₒᵣ (termFvAssign f t) (fvAssign f p) := by
  have hw : IsSemitermVec ℒₒᵣ 1 m (?[t] : V) := by simp [ht]
  rw [substs1, fvAssign_subst hw hp, substs1, termFvAssignVec_cons₁ ht.isUTerm]

lemma fvAssign_free {b p : V} (hp : IsSemiformula ℒₒᵣ 1 p) :
    fvAssign (b ∷ f) (free ℒₒᵣ p) = substs1 ℒₒᵣ (numeral b) (fvAssign f p) := by
  rw [free, fvAssign_substs1 (m := 0) (by simp) hp.shift, fvAssign_shift hp.isUFormula]
  simp

lemma fvAssign_qqBall {t q : V} (ht : IsUTerm ℒₒᵣ t) (hq : IsUFormula ℒₒᵣ q) :
    fvAssign f (qqBall (termBShift ℒₒᵣ t) q) =
      qqBall (termBShift ℒₒᵣ (termFvAssign f t)) (fvAssign f q) := by
  have hv : IsUTermVec ℒₒᵣ 2 (?[^#0, termBShift ℒₒᵣ t] : V) := by simp [ht.termBShift]
  have hn : IsUFormula ℒₒᵣ (qqNLT (^#0 : V) (termBShift ℒₒᵣ t)) := by
    simp [qqNLT, ht.termBShift]
  rw [qqBall, fvAssign_all (by simp [hn, hq]), fvAssign_or hn hq, qqNLT,
    fvAssign_nrel (by simp) hv]
  simp [qqBall, qqNLT, ht.termBShift, termFvAssign_termBShift ht]

lemma fvAssign_qqBex {t q : V} (ht : IsUTerm ℒₒᵣ t) (hq : IsUFormula ℒₒᵣ q) :
    fvAssign f (qqBex (termBShift ℒₒᵣ t) q) =
      qqBex (termBShift ℒₒᵣ (termFvAssign f t)) (fvAssign f q) := by
  have hv : IsUTermVec ℒₒᵣ 2 (?[^#0, termBShift ℒₒᵣ t] : V) := by simp [ht.termBShift]
  have hn : IsUFormula ℒₒᵣ (qqLT (^#0 : V) (termBShift ℒₒᵣ t)) := by
    simp [qqLT, ht.termBShift]
  rw [qqBex, fvAssign_exs (by simp [hn, hq]), fvAssign_and hn hq, qqLT,
    fvAssign_rel (by simp) hv]
  simp [qqBex, qqLT, ht.termBShift, termFvAssign_termBShift ht]

lemma fvAssign_qqToPrenex {Γ : Polarity} {s : ℕ} {θ : V} (hθ : IsUFormula ℒₒᵣ θ) :
    fvAssign f (qqToPrenex Γ s θ) = qqToPrenex Γ s (fvAssign f θ) := by
  induction s generalizing Γ with
  | zero => simp
  | succ s ih => cases Γ <;> simp [isUFormula_qqToPrenex.mpr hθ, ih]

lemma IsBounded.fvAssign {p : V} (hp : IsUFormula ℒₒᵣ p) (h : IsBounded p) :
    IsBounded (fvAssign f p) := by
  suffices ∀ p : V, IsBounded p → IsUFormula ℒₒᵣ p → IsBounded (Bootstrapping.fvAssign f p) from
    this p h hp
  apply IsBounded.induction 𝚷
    (P := fun p ↦ IsUFormula ℒₒᵣ p → IsBounded (Bootstrapping.fvAssign f p)) (by definability)
  · simp
  · simp
  · intro k r v h
    obtain ⟨hr, hv⟩ := IsUFormula.rel.mp h
    simp [hr, hv]
  · intro k r v h
    obtain ⟨hr, hv⟩ := IsUFormula.nrel.mp h
    simp [hr, hv]
  · intro p q _ _ ihp ihq h
    obtain ⟨hp, hq⟩ := IsUFormula.and.mp h
    simpa [hp, hq] using ⟨ihp hp, ihq hq⟩
  · intro p q _ _ ihp ihq h
    obtain ⟨hp, hq⟩ := IsUFormula.or.mp h
    simpa [hp, hq] using ⟨ihp hp, ihq hq⟩
  · intro t q ht _ ih h
    have hq : IsUFormula ℒₒᵣ q := by simp_all [qqBall]
    rw [fvAssign_qqBall ht hq]
    exact IsBounded.ball ht.isSemiterm.termFvAssign.isUTerm (ih hq)
  · intro t q ht _ ih h
    have hq : IsUFormula ℒₒᵣ q := by simp_all [qqBex]
    rw [fvAssign_qqBex ht hq]
    exact IsBounded.bex ht.isSemiterm.termFvAssign.isUTerm (ih hq)

lemma IsPrenexHierarchy.fvAssign {Γ : Polarity} {s : ℕ} {p : V} (hp : IsUFormula ℒₒᵣ p)
    (h : IsPrenexHierarchy Γ s p) : IsPrenexHierarchy Γ s (fvAssign f p) := by
  obtain ⟨θ, rfl, hθ⟩ := isPrenexHierarchy_iff_exists_qqToPrenex.mp h
  have hθ' : IsUFormula ℒₒᵣ θ := isUFormula_qqToPrenex.mp hp
  exact isPrenexHierarchy_iff_exists_qqToPrenex.mpr
    ⟨_, fvAssign_qqToPrenex hθ', hθ.fvAssign hθ'⟩

end

/-! ## Free-variable substitution by closed terms -/

section fvSubst

variable {w : V}

lemma fvSubst_qqToPrenex {Γ : Polarity} {s : ℕ} {θ : V} (hθ : IsUFormula ℒₒᵣ θ) :
    fvSubst ℒₒᵣ w (qqToPrenex Γ s θ) = qqToPrenex Γ s (fvSubst ℒₒᵣ w θ) := by
  induction s generalizing Γ with
  | zero => simp
  | succ s ih => cases Γ <;> simp [isUFormula_qqToPrenex.mpr hθ, ih]

lemma IsBounded.fvSubst (hw : IsSemitermVec ℒₒᵣ (len w) 0 w) {p : V} (hp : IsUFormula ℒₒᵣ p)
    (h : IsBounded p) : IsBounded (fvSubst ℒₒᵣ w p) := by
  suffices ∀ p : V, IsBounded p → IsUFormula ℒₒᵣ p →
      IsBounded (Bootstrapping.fvSubst ℒₒᵣ w p) from this p h hp
  apply IsBounded.induction 𝚷
    (P := fun p ↦ IsUFormula ℒₒᵣ p → IsBounded (Bootstrapping.fvSubst ℒₒᵣ w p))
    (by definability)
  · simp
  · simp
  · intro k r v h
    obtain ⟨hr, hv⟩ := IsUFormula.rel.mp h
    simp [hr, hv]
  · intro k r v h
    obtain ⟨hr, hv⟩ := IsUFormula.nrel.mp h
    simp [hr, hv]
  · intro p q _ _ ihp ihq h
    obtain ⟨hp, hq⟩ := IsUFormula.and.mp h
    simpa [hp, hq] using ⟨ihp hp, ihq hq⟩
  · intro p q _ _ ihp ihq h
    obtain ⟨hp, hq⟩ := IsUFormula.or.mp h
    simpa [hp, hq] using ⟨ihp hp, ihq hq⟩
  · intro t q ht _ ih h
    have hq : IsUFormula ℒₒᵣ q := by simp_all [qqBall]
    have hts : IsSemiterm ℒₒᵣ (termBV ℒₒᵣ t) t := IsSemiterm.def.mpr ⟨ht, le_rfl⟩
    have hv : IsUTermVec ℒₒᵣ 2 (?[^#0, termBShift ℒₒᵣ t] : V) := by simp [ht.termBShift]
    have hn : IsUFormula ℒₒᵣ (qqNLT (^#0 : V) (termBShift ℒₒᵣ t)) := by
      simp [qqNLT, ht.termBShift]
    have he : Bootstrapping.fvSubst ℒₒᵣ w (qqBall (termBShift ℒₒᵣ t) q) =
        qqBall (termBShift ℒₒᵣ (termFvSubst ℒₒᵣ w t)) (Bootstrapping.fvSubst ℒₒᵣ w q) := by
      rw [qqBall, fvSubst_all (by simp [hn, hq]), fvSubst_or hn hq, qqNLT,
        fvSubst_nrel (by simp) hv]
      rw [show (2 : V) = 0 + 1 + 1 by simp [one_add_one_eq_two],
        termFvSubstVec_cons (by simp) (by simp [ht.termBShift]), termFvSubstVec_cons ht.termBShift
          (by simp), termFvSubstVec_nil, termFvSubst_termBShift_closed hw hts]
      simp [qqBall, qqNLT, one_add_one_eq_two]
    rw [he]
    exact IsBounded.ball (hts.termFvSubst (hw.weaken (by simp))).isUTerm (ih hq)
  · intro t q ht _ ih h
    have hq : IsUFormula ℒₒᵣ q := by simp_all [qqBex]
    have hts : IsSemiterm ℒₒᵣ (termBV ℒₒᵣ t) t := IsSemiterm.def.mpr ⟨ht, le_rfl⟩
    have hv : IsUTermVec ℒₒᵣ 2 (?[^#0, termBShift ℒₒᵣ t] : V) := by simp [ht.termBShift]
    have hn : IsUFormula ℒₒᵣ (qqLT (^#0 : V) (termBShift ℒₒᵣ t)) := by
      simp [qqLT, ht.termBShift]
    have he : Bootstrapping.fvSubst ℒₒᵣ w (qqBex (termBShift ℒₒᵣ t) q) =
        qqBex (termBShift ℒₒᵣ (termFvSubst ℒₒᵣ w t)) (Bootstrapping.fvSubst ℒₒᵣ w q) := by
      rw [qqBex, fvSubst_exs (by simp [hn, hq]), fvSubst_and hn hq, qqLT,
        fvSubst_rel (by simp) hv]
      rw [show (2 : V) = 0 + 1 + 1 by simp [one_add_one_eq_two],
        termFvSubstVec_cons (by simp) (by simp [ht.termBShift]), termFvSubstVec_cons ht.termBShift
          (by simp), termFvSubstVec_nil, termFvSubst_termBShift_closed hw hts]
      simp [qqBex, qqLT, one_add_one_eq_two]
    rw [he]
    exact IsBounded.bex (hts.termFvSubst (hw.weaken (by simp))).isUTerm (ih hq)

lemma IsPrenexHierarchy.fvSubst {Γ : Polarity} {s : ℕ} (hw : IsSemitermVec ℒₒᵣ (len w) 0 w)
    {p : V} (hp : IsUFormula ℒₒᵣ p) (h : IsPrenexHierarchy Γ s p) :
    IsPrenexHierarchy Γ s (fvSubst ℒₒᵣ w p) := by
  obtain ⟨θ, rfl, hθ⟩ := isPrenexHierarchy_iff_exists_qqToPrenex.mp h
  have hθ' : IsUFormula ℒₒᵣ θ := isUFormula_qqToPrenex.mp hp
  exact isPrenexHierarchy_iff_exists_qqToPrenex.mpr
    ⟨_, fvSubst_qqToPrenex hθ', hθ.fvSubst hw hθ'⟩

end fvSubst

end FFL.FirstOrder.Arithmetic.Bootstrapping
