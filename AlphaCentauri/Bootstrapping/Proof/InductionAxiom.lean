module

public import AlphaCentauri.Bootstrapping.Proof.UniversalClosure
public import AlphaCentauri.Bootstrapping.Syntax.SubstInversion
public import AlphaCentauri.Bootstrapping.PartialTruth.Combination
public import AlphaCentauri.Bootstrapping.Proof.ReadableSoundness
public import Foundation.FirstOrder.Incompleteness.Definability

/-!
# Induction axioms in prenex form

An induction axiom of `𝗜𝚺 n` is coded as `qqAlls b m`, where `b` is the body
`K(0) → ∀x (K(x) → K(x + 1)) → ∀x K(x)` of a prenex $\Sigma_n$ formula `K` whose parameters are
the variables bound by the block. If `Z` codes `K` with its parameters as the bound variables
`1, …, m`, then `prenexInductionAxiom m Z` codes the prenex form
`∀p⃗ ∀x ∃y (¬K(0) ∨ ((K(y) ∧ ¬K(y + 1)) ∨ K(x)))` of the axiom. The induction axiom follows from
its prenex form in pure logic. The negation of the prenex form is a block of existential
quantifiers over `∀y ¬B`, where `B` is the matrix above; for `n ≤ k`, this formula belongs to
`IsReadable k 3`, and in a model of `𝗜𝚺⁺ (k + 1)` each of its instances by closed terms is false.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

open PeanoMinus ISigma0 ISigma1
open Arithmetic (numeral numeral_semiterm)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## The prenex form -/

section prenexInductionAxiom

/-- `K(t)` inside the two quantifiers `∀x ∃y`: the instance of `Z` by `t` for the induction
variable, with the parameters of `Z` moved past `x` and `y`. -/
noncomputable def prenexInductionAtom (m Z t : V) : V := subst ℒₒᵣ (t ∷ bvarVec 2 m) Z

/-- `¬K(0) ∨ ((K(y) ∧ ¬K(y + 1)) ∨ K(x))`, where `y` and `x` are the bound variables `0` and `1`. -/
noncomputable def prenexInductionMatrix (m Z : V) : V :=
  neg ℒₒᵣ (prenexInductionAtom m Z (numeral 0)) ^⋎
    ((prenexInductionAtom m Z ^#0 ^⋏ neg ℒₒᵣ (prenexInductionAtom m Z (^#0 ^+ numeral 1))) ^⋎
      prenexInductionAtom m Z ^#1)

/-- The prenex form `∀p⃗ ∀x ∃y (¬K(0) ∨ ((K(y) ∧ ¬K(y + 1)) ∨ K(x)))` of the induction axiom of `Z`,
with a block of `m` universal quantifiers over the parameters.
- [HP98, Lemma I.2.4] -/
noncomputable def prenexInductionAxiom (m Z : V) : V :=
  qqAlls (^∀ ^∃ prenexInductionMatrix m Z) m

/-- `Z` is a prenex $\Sigma_n$ formula without free variables, whose bound variable `0` is the
induction variable and whose bound variables `1, …, m` are the parameters. -/
def IsInductionMatrix (n : ℕ) (m Z : V) : Prop :=
  IsSemiformula ℒₒᵣ (m + 1) Z ∧ shift ℒₒᵣ Z = Z ∧ IsPrenexHierarchy 𝚺 n Z

section definability

instance prenexInductionAtom.definable :
    𝚺ᴬ₁-Function₃ (prenexInductionAtom : V → V → V → V) := by
  unfold prenexInductionAtom
  definability

instance prenexInductionMatrix.definable :
    𝚺ᴬ₁-Function₂ (prenexInductionMatrix : V → V → V) := by
  unfold prenexInductionMatrix
  definability

instance prenexInductionAxiom.definable : 𝚺ᴬ₁-Function₂ (prenexInductionAxiom : V → V → V) := by
  unfold prenexInductionAxiom
  definability

instance IsInductionMatrix.definable (n : ℕ) :
    𝚫ᴬ₁-Relation (IsInductionMatrix n : V → V → Prop) := by
  unfold IsInductionMatrix
  definability

end definability

variable {n : ℕ} {m Z : V}

private lemma isSemitermVec_cons_bvarVec {t : V} (ht : IsSemiterm ℒₒᵣ (m + 2) t) :
    IsSemitermVec ℒₒᵣ (m + 1) (m + 2) (t ∷ bvarVec 2 m) :=
  IsSemitermVec.cons_iff.mpr ⟨ht, IsSemitermVec.bvarVec (by rw [add_comm])⟩

private lemma isSemiformula_prenexInductionAtom (hZ : IsSemiformula ℒₒᵣ (m + 1) Z) {t : V}
    (ht : IsSemiterm ℒₒᵣ (m + 2) t) : IsSemiformula ℒₒᵣ (m + 2) (prenexInductionAtom m Z t) :=
  hZ.subst (isSemitermVec_cons_bvarVec ht)

private lemma shift_prenexInductionAtom (hZ : IsSemiformula ℒₒᵣ (m + 1) Z)
    (hsZ : shift ℒₒᵣ Z = Z) {t : V} (ht : IsSemiterm ℒₒᵣ (m + 2) t) (hst : termShift ℒₒᵣ t = t) :
    shift ℒₒᵣ (prenexInductionAtom m Z t) = prenexInductionAtom m Z t := by
  have hw := isSemitermVec_cons_bvarVec ht
  rw [prenexInductionAtom, shift_substs hZ hw, hsZ]
  congr 1
  apply nth_ext' (m + 1) (by simp [hw.isUTerm]) (by simp)
  intro i hi
  rw [nth_termShiftVec hw.isUTerm hi]
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simpa using hst
  · simp [nth_bvarVec 2 m i (by simpa using hi)]

private lemma isSemiterm_bvar_zero : IsSemiterm ℒₒᵣ (m + 2) (^#0 : V) := by simp

private lemma isSemiterm_bvar_one : IsSemiterm ℒₒᵣ (m + 2) (^#1 : V) :=
  IsSemiterm.bvar.mpr <| lt_of_lt_of_le one_lt_two le_add_self

private lemma isSemiterm_succ_bvar_zero : IsSemiterm ℒₒᵣ (m + 2) (^#0 ^+ numeral 1 : V) := by
  simp [Arithmetic.qqAdd]

lemma IsInductionMatrix.isSemiformula_prenexInductionMatrix (h : IsInductionMatrix n m Z) :
    IsSemiformula ℒₒᵣ (m + 2) (prenexInductionMatrix m Z) := by
  have hA {t : V} (ht : IsSemiterm ℒₒᵣ (m + 2) t) := isSemiformula_prenexInductionAtom h.1 ht
  simp only [prenexInductionMatrix, IsSemiformula.or, IsSemiformula.and, IsSemiformula.neg_iff]
  exact ⟨hA (numeral_semiterm _ _), ⟨hA isSemiterm_bvar_zero, hA isSemiterm_succ_bvar_zero⟩,
    hA isSemiterm_bvar_one⟩

private lemma shift_or_and {a₀ a₁ a₂ a₃ : V} (h₀ : IsUFormula ℒₒᵣ a₀) (h₁ : IsUFormula ℒₒᵣ a₁)
    (h₂ : IsUFormula ℒₒᵣ a₂) (h₃ : IsUFormula ℒₒᵣ a₃) (hs₀ : shift ℒₒᵣ a₀ = a₀)
    (hs₁ : shift ℒₒᵣ a₁ = a₁) (hs₂ : shift ℒₒᵣ a₂ = a₂) (hs₃ : shift ℒₒᵣ a₃ = a₃) :
    shift ℒₒᵣ (neg ℒₒᵣ a₀ ^⋎ ((a₁ ^⋏ neg ℒₒᵣ a₂) ^⋎ a₃)) =
      neg ℒₒᵣ a₀ ^⋎ ((a₁ ^⋏ neg ℒₒᵣ a₂) ^⋎ a₃) := by
  simp [h₀, h₁, h₂, h₃, hs₁, hs₃, shift_neg h₀.isSemiformula, shift_neg h₂.isSemiformula, hs₀,
    hs₂]

private lemma termShift_succ_bvar_zero :
    termShift ℒₒᵣ (^#0 ^+ numeral 1 : V) = ^#0 ^+ numeral 1 := by
  have hv : IsSemitermVec ℒₒᵣ 2 1 (?[^#0, numeral 1] : V) :=
    IsSemitermVec.doubleton.mpr ⟨by simp, numeral_semiterm 1 1⟩
  rw [Arithmetic.qqAdd, termShift_func (by simp) hv.isUTerm,
    termShiftVec_cons₂ (by simp) (Arithmetic.numeral_uterm 1), termShift_bvar,
    Arithmetic.numeral_shift]

lemma IsInductionMatrix.shift_prenexInductionMatrix (h : IsInductionMatrix n m Z) :
    shift ℒₒᵣ (prenexInductionMatrix m Z) = prenexInductionMatrix m Z :=
  shift_or_and (isSemiformula_prenexInductionAtom h.1 (numeral_semiterm _ 0)).isUFormula
    (isSemiformula_prenexInductionAtom h.1 isSemiterm_bvar_zero).isUFormula
    (isSemiformula_prenexInductionAtom h.1 isSemiterm_succ_bvar_zero).isUFormula
    (isSemiformula_prenexInductionAtom h.1 isSemiterm_bvar_one).isUFormula
    (shift_prenexInductionAtom h.1 h.2.1 (numeral_semiterm _ 0) (Arithmetic.numeral_shift 0))
    (shift_prenexInductionAtom h.1 h.2.1 isSemiterm_bvar_zero (termShift_bvar 0))
    (shift_prenexInductionAtom h.1 h.2.1 isSemiterm_succ_bvar_zero termShift_succ_bvar_zero)
    (shift_prenexInductionAtom h.1 h.2.1 isSemiterm_bvar_one (termShift_bvar 1))

lemma IsInductionMatrix.isFormula_prenexInductionAxiom (h : IsInductionMatrix n m Z) :
    IsFormula ℒₒᵣ (prenexInductionAxiom m Z) := by
  apply IsSemiformula.qqAlls
  rw [zero_add, IsSemiformula.all, IsSemiformula.exs, add_assoc, one_add_one_eq_two]
  exact h.isSemiformula_prenexInductionMatrix

lemma IsInductionMatrix.shift_prenexInductionAxiom (h : IsInductionMatrix n m Z) :
    shift ℒₒᵣ (prenexInductionAxiom m Z) = prenexInductionAxiom m Z := by
  have hB := h.isSemiformula_prenexInductionMatrix.isUFormula
  rw [prenexInductionAxiom, shift_qqAlls (by simpa using hB), shift_all (by simpa using hB),
    shift_exs hB, h.shift_prenexInductionMatrix]

end prenexInductionAxiom

/-! ## Deriving the induction axiom from its prenex form -/

section derivation

variable {m Z : V}

private lemma coe_substCode_zero :
    ((substCode (‘0’ : ArithmeticSemiterm ℕ 0) : ℕ) : V) =
      SemitermVec.val (![Arithmetic.typedNumeral 0] : SemitermVec V ℒₒᵣ 1 0) := by
  have := Semiterm.quote_eq_encode' (V := V) ![(‘0’ : ArithmeticSemiterm ℕ 0)]
  simp only [substCode]
  rw [← this]
  congr 1
  ext i
  obtain rfl := Fin.fin_one_eq_zero i
  simp

private lemma coe_substCode_succ :
    ((substCode (‘#0 + 1’ : ArithmeticSemiterm ℕ 1) : ℕ) : V) =
      SemitermVec.val (![Semiterm.bvar 0 + Arithmetic.typedNumeral 1] : SemitermVec V ℒₒᵣ 1 1) := by
  have := Semiterm.quote_eq_encode' (V := V) ![(‘#0 + 1’ : ArithmeticSemiterm ℕ 1)]
  simp only [substCode]
  rw [← this]
  congr 1
  ext i
  obtain rfl := Fin.fin_one_eq_zero i
  simp

private lemma isSemitermVec_fvarVec (m n : V) : IsSemitermVec ℒₒᵣ m n (fvarVec m) :=
  IsSemitermVec.iff.mpr ⟨len_fvarVec m, fun i hi ↦ by simp [nth_fvarVec m i hi]⟩

private lemma nth_qVec_succ {k w j : V} (hw : IsUTermVec ℒₒᵣ k w) (hj : j < k) :
    (qVec ℒₒᵣ w).[j + 1] = termBShift ℒₒᵣ w.[j] := by
  rw [qVec, ← hw.lh, nth_adjoin_succ, nth_termBShiftVec hw hj]

private lemma nth_qVec_qVec_fvarVec {m i : V} (hi : i < m) :
    (qVec ℒₒᵣ (qVec ℒₒᵣ (fvarVec m))).[i + 1 + 1] = ^&i := by
  have h₁ : IsUTermVec ℒₒᵣ m (fvarVec m) := (isSemitermVec_fvarVec m 0).isUTerm
  have h₂ : IsUTermVec ℒₒᵣ (m + 1) (qVec ℒₒᵣ (fvarVec m)) :=
    (isSemitermVec_fvarVec m 0).qVec.isUTerm
  rw [nth_qVec_succ h₂ (by simpa using hi), nth_qVec_succ h₁ hi, nth_fvarVec m i hi]
  simp

private lemma subst_subst_qVec_fvarVec {t : V} (hZ : IsSemiformula ℒₒᵣ (m + 1) Z)
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

private lemma subst_qVec_qVec_prenexInductionAtom {t : V} (hZ : IsSemiformula ℒₒᵣ (m + 1) Z)
    (ht : IsSemiterm ℒₒᵣ 2 t) :
    subst ℒₒᵣ (qVec ℒₒᵣ (qVec ℒₒᵣ (fvarVec m))) (prenexInductionAtom m Z t) =
      subst ℒₒᵣ (t ∷ fvarVec m) Z := by
  have ht' : IsSemiterm ℒₒᵣ (m + 2) t :=
    IsSemiterm.def.mpr ⟨ht.isUTerm, (IsSemiterm.def.mp ht).2.trans le_add_self⟩
  have hv : IsSemitermVec ℒₒᵣ (m + 2) 2 (qVec ℒₒᵣ (qVec ℒₒᵣ (fvarVec m))) := by
    simpa [add_assoc, one_add_one_eq_two] using (isSemitermVec_fvarVec m 0).qVec.qVec
  have hb : IsSemitermVec ℒₒᵣ m (m + 2) (bvarVec 2 m) := IsSemitermVec.bvarVec (by rw [add_comm])
  have h₁ : IsUTermVec ℒₒᵣ m (fvarVec m) := (isSemitermVec_fvarVec m 0).isUTerm
  have h₂ : IsUTermVec ℒₒᵣ (m + 1) (qVec ℒₒᵣ (fvarVec m)) :=
    (isSemitermVec_fvarVec m 0).qVec.isUTerm
  rw [prenexInductionAtom, substs_substs hZ hv (isSemitermVec_cons_bvarVec ht'),
    termSubstVec_cons ht'.isUTerm hb.isUTerm]
  congr 2
  · apply termSubst_eq_self ht
    intro i hi
    rcases zero_or_succ i with rfl | ⟨i, rfl⟩
    · simp [qVec]
    · have hi' : i + 1 < 1 + 1 := by rwa [one_add_one_eq_two]
      obtain rfl : i = 0 := lt_one_iff_eq_zero.mp (lt_of_add_lt_add_right hi')
      rw [nth_qVec_succ h₂ (by simp : (0 : V) < m + 1)]
      simp [qVec]
  · apply nth_ext' m (hv.termSubstVec hb).lh (by simp)
    intro i hi
    rw [nth_termSubstVec hb.isUTerm hi, nth_bvarVec 2 m i hi, termSubst_bvar,
      show (2 + i : V) = i + 1 + 1 by rw [add_comm, add_assoc, one_add_one_eq_two],
      nth_qVec_qVec_fvarVec hi, nth_fvarVec m i hi]

section typed

variable (K : Semiformula V ℒₒᵣ 1)

/-- `K(0) → ∀x (K(x) → K(x + 1)) → ∀x K(x)`. -/
private noncomputable def indFormula : Formula V ℒₒᵣ :=
  K.subst ![Arithmetic.typedNumeral 0] 🡒
    ((∀¹ (K 🡒 K.subst ![Semiterm.bvar 0 + Arithmetic.typedNumeral 1])) 🡒 ∀¹ K)

/-- `∀x ∃y (¬K(0) ∨ ((K(y) ∧ ¬K(y + 1)) ∨ K(x)))`. -/
private noncomputable def prenexIndFormula : Formula V ℒₒᵣ :=
  ∀¹ ∃¹ (∼K.subst ![Arithmetic.typedNumeral 0] ⋎
    ((K.subst ![Semiterm.bvar 0] ⋏ ∼K.subst ![Semiterm.bvar 0 + Arithmetic.typedNumeral 1]) ⋎
      K.subst ![Semiterm.bvar 1]))

private lemma derivable_prenexIndFormula :
    Derivable (∅ : Theory ℒₒᵣ)
      (insert (neg ℒₒᵣ (prenexIndFormula K).val) ({(indFormula K).val} : V)) := by
  have d : (∅ : Theory ℒₒᵣ).internalize V ⊢!ᵈᵉʳ indFormula K ⫽ ∼prenexIndFormula K ⫽ ∅ := by
    simp only [indFormula, Semiformula.imp_def]
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.all
    simp only [Sequent.shift_insert, Sequent.shift_empty]
    apply TDerivation.rotate₃
    simp only [prenexIndFormula, Semiformula.shift_neg, Semiformula.shift_all,
      Semiformula.shift_exs, Semiformula.neg_all, Semiformula.neg_ex]
    apply TDerivation.exs (Semiterm.fvar 0)
    simp only [Semiformula.substs_all]
    apply TDerivation.all
    simp only [Semiformula.free, Semiformula.shift_substs, Semiformula.substs_substs,
      SemitermVec.q, Fin.isValue, Semiformula.shift_or, Semiformula.shift_neg,
      Semiformula.shift_and,
      LogicalConnective.DeMorgan.or, TildeInvolutive.tilde_involutive,
      LogicalConnective.DeMorgan.and, Semiformula.substs_and, Semiformula.substs_or,
      Semiformula.substs_neg, Sequent.shift_insert, Semiformula.shift_exs, Sequent.shift_empty]
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.Fin1.eq_one, Fin.isValue,
      Matrix.vecMap_cons', Matrix.head_cons, Semiterm.bShift_fvar, Matrix.tail_cons,
      Matrix.vecMap_nil, Arithmetic.shift_numeral, Arithmetic.subst_numeral, Semiterm.shift_bvar,
      Semiterm.substs_bvar, Matrix.cons_val_zero, Matrix.cons_val_fin_one, Arithmetic.shift_add,
      Arithmetic.subst_add, Matrix.cons_val_one, Semiterm.shift_fvar, zero_add,
      Semiterm.substs_fvar]
    generalize K.shift.shift = K
    apply TDerivation.and (TDerivation.em (K.subst ![Arithmetic.typedNumeral 0]))
    apply TDerivation.and ?_ (TDerivation.em (K.subst ![Semiterm.fvar 1]))
    apply TDerivation.or
    apply TDerivation.rotate₂
    apply TDerivation.exs (Semiterm.fvar 0)
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Semiformula.substs_and,
      Semiformula.substs_neg, Semiformula.substs_substs, Matrix.vecMap_cons', Matrix.head_cons,
      Arithmetic.subst_add, Semiterm.substs_bvar, Matrix.cons_val_fin_one,
      Arithmetic.subst_numeral, Matrix.tail_cons, Matrix.vecMap_nil]
    exact TDerivation.and (TDerivation.em (K.subst ![Semiterm.fvar 0]))
      (TDerivation.em (K.subst ![Semiterm.fvar 0 + Arithmetic.typedNumeral 1]))
  exact d.toDerivable.ofSetEq fun x ↦ by simp; tauto

private lemma indBodyVal_val : indBodyVal K.val = (indFormula K).val := by
  rw [indBodyVal, coe_substCode_zero, coe_substCode_succ]
  simp [indFormula]

private lemma prenexIndFormula_val {n : ℕ} (h : IsInductionMatrix n m Z)
    (hK : K.val = subst ℒₒᵣ (qVec ℒₒᵣ (fvarVec m)) Z) :
    (prenexIndFormula K).val = subst ℒₒᵣ (fvarVec m) (^∀ ^∃ prenexInductionMatrix m Z) := by
  simp only [prenexIndFormula, Nat.reduceAdd, Nat.succ_eq_add_one, Fin.isValue,
    Semiformula.val_all, Semiformula.val_exs, Semiformula.val_or, Semiformula.val_neg,
    Semiformula.val_substs, SemitermVec.val_succ, Matrix.head_cons, Arithmetic.val_numeral,
    Matrix.tail_cons, SemitermVec.val_nil, Semiformula.val_and, Semiterm.bvar_val,
    Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.cast_zero, Arithmetic.val_add, Nat.mod_succ,
    Nat.cast_one]
  have hv : IsSemitermVec ℒₒᵣ (m + 2) 2 (qVec ℒₒᵣ (qVec ℒₒᵣ (fvarVec m))) := by
    simpa [add_assoc, one_add_one_eq_two] using (isSemitermVec_fvarVec m 0).qVec.qVec
  have hB := h.isSemiformula_prenexInductionMatrix
  have h₀ := isSemiformula_prenexInductionAtom h.1 (numeral_semiterm _ 0)
  have h₁ := isSemiformula_prenexInductionAtom h.1 isSemiterm_bvar_zero
  have h₂ := isSemiformula_prenexInductionAtom h.1 isSemiterm_succ_bvar_zero
  have h₃ := isSemiformula_prenexInductionAtom h.1 isSemiterm_bvar_one
  have hY := IsUFormula.and.mpr ⟨h₁.isUFormula, h₂.isUFormula.neg⟩
  rw [substs_all (by simpa using hB.isUFormula), substs_ex hB.isUFormula, prenexInductionMatrix,
    substs_or h₀.isUFormula.neg (IsUFormula.or.mpr ⟨hY, h₃.isUFormula⟩), substs_neg h₀ hv,
    substs_or hY h₃.isUFormula, substs_and h₁.isUFormula h₂.isUFormula.neg, substs_neg h₂ hv,
    subst_qVec_qVec_prenexInductionAtom h.1 (numeral_semiterm _ 0),
    subst_qVec_qVec_prenexInductionAtom h.1 (by simp),
    subst_qVec_qVec_prenexInductionAtom h.1 (by simp [Arithmetic.qqAdd]),
    subst_qVec_qVec_prenexInductionAtom h.1 (IsSemiterm.bvar.mpr one_lt_two), hK,
    subst_subst_qVec_fvarVec h.1 (numeral_semiterm _ 0), subst_subst_qVec_fvarVec h.1 (by simp),
    subst_subst_qVec_fvarVec h.1 (by simp [Arithmetic.qqAdd]),
    subst_subst_qVec_fvarVec h.1 (IsSemiterm.bvar.mpr one_lt_two)]

end typed

/-- In pure logic, every induction axiom of `𝗜𝚺 n` follows from the prenex form of the induction
axiom of a matrix `Z` coded below it.
- [HP98, Lemma I.2.4] -/
private lemma indBodyVal_eq_or (K : V) : ∃ X Y, indBodyVal K = X ^⋎ (Y ^⋎ ^∀ K) := ⟨_, _, rfl⟩

theorem exists_derivable_prenexInductionAxiom {n : ℕ} {p : V}
    (h : InductionR (IsPrenexHierarchy 𝚺 n) p) :
    ∃ m ≤ p, ∃ Z ≤ p, IsInductionMatrix n m Z ∧
      Derivable (∅ : Theory ℒₒᵣ) (insert (neg ℒₒᵣ (prenexInductionAxiom m Z)) ({p} : V)) := by
  obtain ⟨m, hm, b, hb, rfl, hU, hsh, hbv, K, hK, hKs, hKS, hsub⟩ := h
  have hbs : IsSemiformula ℒₒᵣ m b := hbv ▸ hU.isSemiformula
  have hfv := isSemitermVec_fvarVec m 0
  obtain ⟨X, Y, e⟩ := indBodyVal_eq_or K
  have hsub₀ := hsub
  rw [e] at hsub
  obtain ⟨b₁, b₂, rfl, -, h₂⟩ := exists_eq_or_of_subst_eq hU hsub
  obtain ⟨b₃, b₄, rfl, -, h₄⟩ := exists_eq_or_of_subst_eq (IsUFormula.or.mp hU).2 h₂
  obtain ⟨Z, rfl, hZK⟩ := exists_eq_all_of_subst_eq (IsUFormula.or.mp (IsUFormula.or.mp hU).2).2 h₄
  obtain ⟨hb₁, hb₂⟩ := IsSemiformula.or.mp hbs
  obtain ⟨hb₃, hb₄⟩ := IsSemiformula.or.mp hb₂
  have hZs : IsSemiformula ℒₒᵣ (m + 1) Z := IsSemiformula.all.mp hb₄
  have hsZ : shift ℒₒᵣ Z = Z := by
    rw [shift_or hb₁.isUFormula (IsUFormula.or.mpr ⟨hb₃.isUFormula, hb₄.isUFormula⟩),
      shift_or hb₃.isUFormula hb₄.isUFormula, shift_all hZs.isUFormula] at hsh
    exact (by simpa [qqOr_inj, qqAll_inj] using hsh : _ ∧ _ ∧ _).2.2
  have hZp : IsPrenexHierarchy 𝚺 n Z :=
    IsPrenexHierarchy.of_subst hfv.qVec hZs (hZK ▸ hKS)
  have hM : IsInductionMatrix n m Z := ⟨hZs, hsZ, hZp⟩
  have hZle : Z ≤ qqAlls (b₁ ^⋎ b₃ ^⋎ ^∀ Z) m :=
    (le_qqAll Z).trans <| (lt_or_right b₃ _).le.trans <| (lt_or_right b₁ _).le.trans hb
  refine ⟨m, hm, Z, hZle, hM, ?_⟩
  have hB := hM.isSemiformula_prenexInductionMatrix
  have hq : IsSemiformula ℒₒᵣ m (^∀ ^∃ prenexInductionMatrix m Z) := by
    rw [IsSemiformula.all, IsSemiformula.exs, add_assoc, one_add_one_eq_two]
    exact hB
  have hsq : shift ℒₒᵣ (^∀ ^∃ prenexInductionMatrix m Z) = ^∀ ^∃ prenexInductionMatrix m Z := by
    rw [shift_all (by simpa using hB.isUFormula), shift_exs hB.isUFormula,
      hM.shift_prenexInductionMatrix]
  let Kt : Semiformula V ℒₒᵣ 1 := ⟨K, by simpa using hKs⟩
  have d := derivable_prenexIndFormula Kt
  rw [prenexIndFormula_val Kt hM hZK.symm, ← indBodyVal_val Kt, ← hsub₀] at d
  exact Derivable.neg_qqAlls_qqAlls hbs hq hsh hsq d

end derivation

/-! ## The negated prenex form -/

section counterexample

variable {k : ℕ} {n : ℕ} {m Z : V}

lemma IsInductionMatrix.isPrenexHierarchy_prenexInductionAtom (h : IsInductionMatrix n m Z)
    {t : V} (ht : IsSemiterm ℒₒᵣ (m + 2) t) :
    IsPrenexHierarchy 𝚺 n (prenexInductionAtom m Z t) :=
  h.2.2.subst (isSemitermVec_cons_bvarVec ht) h.1

lemma IsInductionMatrix.neg_prenexInductionMatrix (h : IsInductionMatrix n m Z) :
    neg ℒₒᵣ (prenexInductionMatrix m Z) =
      prenexInductionAtom m Z (numeral 0) ^⋏
        ((neg ℒₒᵣ (prenexInductionAtom m Z ^#0) ^⋎
            prenexInductionAtom m Z (^#0 ^+ numeral 1)) ^⋏
          neg ℒₒᵣ (prenexInductionAtom m Z ^#1)) := by
  have h₀ := (isSemiformula_prenexInductionAtom h.1 (numeral_semiterm _ 0)).isUFormula
  have h₁ := (isSemiformula_prenexInductionAtom h.1 isSemiterm_bvar_zero).isUFormula
  have h₂ := (isSemiformula_prenexInductionAtom h.1 isSemiterm_succ_bvar_zero).isUFormula
  have h₃ := (isSemiformula_prenexInductionAtom h.1 isSemiterm_bvar_one).isUFormula
  have h₄ := IsUFormula.and.mpr ⟨h₁, h₂.neg⟩
  rw [prenexInductionMatrix, neg_or h₀.neg (IsUFormula.or.mpr ⟨h₄, h₃⟩), h₀.neg_neg,
    neg_or h₄ h₃, neg_and h₁ h₂.neg, h₂.neg_neg]

private lemma IsInductionMatrix.isCombination_prenexInductionAtom (h : IsInductionMatrix n m Z)
    (hn : n ≤ k) {t : V} (ht : IsSemiterm ℒₒᵣ (m + 2) t) {D : ℕ} :
    IsCombination k D (prenexInductionAtom m Z t) :=
  .of_isPrenexAtMost ⟨𝚺, n, hn, h.isPrenexHierarchy_prenexInductionAtom ht⟩

private lemma IsInductionMatrix.isCombination_neg_prenexInductionAtom
    (h : IsInductionMatrix n m Z) (hn : n ≤ k) {t : V} (ht : IsSemiterm ℒₒᵣ (m + 2) t) {D : ℕ} :
    IsCombination k D (neg ℒₒᵣ (prenexInductionAtom m Z t)) :=
  (h.isCombination_prenexInductionAtom hn ht).neg
    (isSemiformula_prenexInductionAtom h.1 ht).isUFormula

lemma IsInductionMatrix.isCombination_neg_prenexInductionMatrix (h : IsInductionMatrix n m Z)
    (hn : n ≤ k) : IsCombination k 3 (neg ℒₒᵣ (prenexInductionMatrix m Z)) := by
  rw [h.neg_prenexInductionMatrix]
  exact (h.isCombination_prenexInductionAtom hn (numeral_semiterm _ 0)).and <|
    (((h.isCombination_neg_prenexInductionAtom hn isSemiterm_bvar_zero).or
      (h.isCombination_prenexInductionAtom hn isSemiterm_succ_bvar_zero)).and
        (h.isCombination_neg_prenexInductionAtom hn isSemiterm_bvar_one))

lemma IsInductionMatrix.isReadable_all_neg_prenexInductionMatrix (h : IsInductionMatrix n m Z)
    (hn : n ≤ k) : IsReadable k 3 (^∀ neg ℒₒᵣ (prenexInductionMatrix m Z)) :=
  .all (h.isCombination_neg_prenexInductionMatrix hn)

private lemma isSemitermVec_cons_cons {a b w' : V} (ha : IsSemiterm ℒₒᵣ 0 a)
    (hb : IsSemiterm ℒₒᵣ 0 b) (hw' : IsSemitermVec ℒₒᵣ m 0 w') :
    IsSemitermVec ℒₒᵣ (m + 2) 0 (a ∷ b ∷ w') := by
  rw [← one_add_one_eq_two, ← add_assoc]
  simp [ha, hb, hw']

private lemma subst_prenexInductionAtom {a b w' t : V} (ha : IsSemiterm ℒₒᵣ 0 a)
    (hb : IsSemiterm ℒₒᵣ 0 b) (hw' : IsSemitermVec ℒₒᵣ m 0 w') (hZ : IsSemiformula ℒₒᵣ (m + 1) Z)
    (ht : IsSemiterm ℒₒᵣ (m + 2) t) :
    subst ℒₒᵣ (a ∷ b ∷ w') (prenexInductionAtom m Z t) =
      subst ℒₒᵣ (termSubst ℒₒᵣ (a ∷ b ∷ w') t ∷ w') Z := by
  have hu := isSemitermVec_cons_cons ha hb hw'
  have hv : IsSemitermVec ℒₒᵣ m (m + 2) (bvarVec 2 m) := IsSemitermVec.bvarVec (by rw [add_comm])
  rw [prenexInductionAtom, substs_substs hZ hu (isSemitermVec_cons_bvarVec ht),
    termSubstVec_cons ht.isUTerm hv.isUTerm]
  congr 2
  apply nth_ext' m (hu.termSubstVec hv).lh hw'.lh
  intro i hi
  rw [nth_termSubstVec hv.isUTerm hi, nth_bvarVec 2 m i hi, termSubst_bvar,
    show (2 + i : V) = i + 1 + 1 by rw [add_comm, add_assoc, one_add_one_eq_two]]
  simp

private lemma IsSemitermVec.exists_cons {w : V} (hw : IsSemitermVec ℒₒᵣ (m + 1) 0 w) :
    ∃ w₀ w', w = w₀ ∷ w' ∧ IsSemiterm ℒₒᵣ 0 w₀ ∧ IsSemitermVec ℒₒᵣ m 0 w' := by
  rcases nil_or_adjoin w with rfl | ⟨w₀, w', rfl⟩
  · simpa using hw.lh
  · exact ⟨w₀, w', rfl, IsSemitermVec.cons_iff.mp hw⟩

private lemma substs1_subst_qVec {j w q t : V} (hw : IsSemitermVec ℒₒᵣ j 0 w)
    (hq : IsSemiformula ℒₒᵣ (j + 1) q) (ht : IsSemiterm ℒₒᵣ 0 t) :
    substs1 ℒₒᵣ t (subst ℒₒᵣ (qVec ℒₒᵣ w) q) = subst ℒₒᵣ (t ∷ w) q := by
  have h₁ : IsSemitermVec ℒₒᵣ 1 0 (?[t] : V) := by simp [ht]
  have h₂ : IsSemitermVec ℒₒᵣ (j + 1) 1 (qVec ℒₒᵣ w) := by simpa using hw.qVec
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

private lemma readableTruth_subst_prenexInductionAtom_iff {D : ℕ} {θ a b w' t : V}
    (hθ : Z = qqToPrenex 𝚺 n θ) (hθb : IsBounded θ) (hZ : IsSemiformula ℒₒᵣ (m + 1) Z)
    (hn : n ≤ k) (ha : IsSemiterm ℒₒᵣ 0 a) (hb : IsSemiterm ℒₒᵣ 0 b)
    (hw' : IsSemitermVec ℒₒᵣ m 0 w') (ht : IsSemiterm ℒₒᵣ (m + 2) t) :
    ReadableTruth k D (subst ℒₒᵣ (a ∷ b ∷ w') (prenexInductionAtom m Z t)) ↔
      HierarchicalSatisfaction 𝚺 n θ
        (termVal 0 (termSubst ℒₒᵣ (a ∷ b ∷ w') t) ∷ termValVec 0 m w') := by
  have hu := isSemitermVec_cons_cons ha hb hw'
  have hc : IsSemiterm ℒₒᵣ 0 (termSubst ℒₒᵣ (a ∷ b ∷ w') t) := hu.termSubst ht
  have hcons : IsSemitermVec ℒₒᵣ (m + 1) 0 (termSubst ℒₒᵣ (a ∷ b ∷ w') t ∷ w') :=
    IsSemitermVec.cons_iff.mpr ⟨hc, hw'⟩
  have hθs : IsSemiformula ℒₒᵣ (m + 1 + n) θ := isSemiformula_qqToPrenex.mp (hθ ▸ hZ)
  rw [subst_prenexInductionAtom ha hb hw' hZ ht, hθ,
    ReadableTruth.subst_qqToPrenex_iff (.of_le hn) hθs hθb hcons,
    termValVec_cons hc.isUTerm hw'.isUTerm]

private lemma readableTruth_subst_neg_prenexInductionMatrix_iff {θ a b w' : V}
    (h : IsInductionMatrix n m Z) (hn : n ≤ k) (hθ : Z = qqToPrenex 𝚺 n θ) (hθb : IsBounded θ)
    (ha : IsSemiterm ℒₒᵣ 0 a) (hb : IsSemiterm ℒₒᵣ 0 b) (hw' : IsSemitermVec ℒₒᵣ m 0 w') :
    ReadableTruth k 3 (subst ℒₒᵣ (a ∷ b ∷ w') (neg ℒₒᵣ (prenexInductionMatrix m Z))) ↔
      HierarchicalSatisfaction 𝚺 n θ (0 ∷ termValVec 0 m w') ∧
        (¬HierarchicalSatisfaction 𝚺 n θ (termVal 0 a ∷ termValVec 0 m w') ∨
          HierarchicalSatisfaction 𝚺 n θ ((termVal 0 a + 1) ∷ termValVec 0 m w')) ∧
        ¬HierarchicalSatisfaction 𝚺 n θ (termVal 0 b ∷ termValVec 0 m w') := by
  have hu := isSemitermVec_cons_cons ha hb hw'
  have hA {t : V} (ht : IsSemiterm ℒₒᵣ (m + 2) t) :
      IsSemiformula ℒₒᵣ 0 (subst ℒₒᵣ (a ∷ b ∷ w') (prenexInductionAtom m Z t)) :=
    (isSemiformula_prenexInductionAtom h.1 ht).subst hu
  have hRd {t : V} (ht : IsSemiterm ℒₒᵣ (m + 2) t) :
      IsReadable k 3 (subst ℒₒᵣ (a ∷ b ∷ w') (prenexInductionAtom m Z t)) :=
    .of_isCombination <|
      (h.isCombination_prenexInductionAtom hn ht).subst hu
        (isSemiformula_prenexInductionAtom h.1 ht)
  have hT {t : V} (ht : IsSemiterm ℒₒᵣ (m + 2) t) :=
    readableTruth_subst_prenexInductionAtom_iff (D := 3) hθ hθb h.1 hn ha hb hw' ht
  have hV {t : V} (ht : IsSemiterm ℒₒᵣ (m + 2) t) :
      termVal 0 (termSubst ℒₒᵣ (a ∷ b ∷ w') t) = termVal (termValVec 0 (m + 2) (a ∷ b ∷ w')) t :=
    termVal_termSubst hu ht
  have hU₀ := (hA (numeral_semiterm _ 0)).isUFormula
  have hU₁ := (hA isSemiterm_bvar_zero).isUFormula
  have hU₂ := (hA isSemiterm_succ_bvar_zero).isUFormula
  have hU₃ := (hA isSemiterm_bvar_one).isUFormula
  have hsub : subst ℒₒᵣ (a ∷ b ∷ w') (neg ℒₒᵣ (prenexInductionMatrix m Z)) =
      subst ℒₒᵣ (a ∷ b ∷ w') (prenexInductionAtom m Z (numeral 0)) ^⋏
        ((neg ℒₒᵣ (subst ℒₒᵣ (a ∷ b ∷ w') (prenexInductionAtom m Z ^#0)) ^⋎
            subst ℒₒᵣ (a ∷ b ∷ w') (prenexInductionAtom m Z (^#0 ^+ numeral 1))) ^⋏
          neg ℒₒᵣ (subst ℒₒᵣ (a ∷ b ∷ w') (prenexInductionAtom m Z ^#1))) := by
    have hZ := h.1
    have h₀ := (isSemiformula_prenexInductionAtom hZ (numeral_semiterm _ 0))
    have h₁ := (isSemiformula_prenexInductionAtom hZ isSemiterm_bvar_zero)
    have h₂ := (isSemiformula_prenexInductionAtom hZ isSemiterm_succ_bvar_zero)
    have h₃ := (isSemiformula_prenexInductionAtom hZ isSemiterm_bvar_one)
    have hY := IsUFormula.or.mpr ⟨h₁.isUFormula.neg, h₂.isUFormula⟩
    rw [h.neg_prenexInductionMatrix, substs_and h₀.isUFormula
      (IsUFormula.and.mpr ⟨hY, h₃.isUFormula.neg⟩), substs_and hY h₃.isUFormula.neg,
      substs_or h₁.isUFormula.neg h₂.isUFormula, substs_neg h₁ hu, substs_neg h₃ hu]
  have hr : IsReadable k 3 (subst ℒₒᵣ (a ∷ b ∷ w') (neg ℒₒᵣ (prenexInductionMatrix m Z))) :=
    .of_isCombination <| (h.isCombination_neg_prenexInductionMatrix hn).subst hu
      h.isSemiformula_prenexInductionMatrix.neg
  rw [hsub] at hr ⊢
  obtain ⟨hr₀, hrX⟩ := hr.of_and
  obtain ⟨hrY, hr₃⟩ := hrX.of_and
  obtain ⟨hr₁, hr₂⟩ := hrY.of_or
  have hY := IsUFormula.or.mpr ⟨hU₁.neg, hU₂⟩
  rw [ReadableTruth.and_iff hr hU₀ (IsUFormula.and.mpr ⟨hY, hU₃.neg⟩),
    ReadableTruth.and_iff hrX hY hU₃.neg, ReadableTruth.or_iff hrY hU₁.neg hU₂,
    ReadableTruth.neg_iff (hRd isSemiterm_bvar_zero) hr₁ hU₁,
    ReadableTruth.neg_iff (hRd isSemiterm_bvar_one) hr₃ hU₃, hT (numeral_semiterm _ 0),
    hT isSemiterm_bvar_zero, hT isSemiterm_succ_bvar_zero, hT isSemiterm_bvar_one,
    hV (numeral_semiterm _ 0), hV isSemiterm_bvar_zero, hV isSemiterm_succ_bvar_zero,
    hV isSemiterm_bvar_one]
  have e₀ : termVal (termValVec 0 (m + 2) (a ∷ b ∷ w')) (^#0 : V) = termVal 0 a := by
    rw [termVal_bvar, nth_termValVec hu.isUTerm (by simp)]
    simp
  have e₁ : termVal (termValVec 0 (m + 2) (a ∷ b ∷ w')) (^#1 : V) = termVal 0 b := by
    rw [termVal_bvar, nth_termValVec hu.isUTerm (lt_of_lt_of_le one_lt_two le_add_self)]
    simp
  have e₂ : termVal (termValVec 0 (m + 2) (a ∷ b ∷ w')) (^#0 ^+ numeral 1 : V) =
      termVal 0 a + 1 := by
    rw [termVal_add (by simp) (Arithmetic.numeral_uterm 1), e₀, termVal_numeral]
  rw [termVal_numeral, e₀, e₁, e₂]

/-- In a model of `𝗜𝚺⁺ (k + 1)` with `n ≤ k`, no instance of `∀y ¬B(p⃗, x, y)` by closed terms is
true.
- [HP98, Lemma I.2.4] -/
theorem IsInductionMatrix.not_readableTruth_subst [V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺(k + 1)]
    (h : IsInductionMatrix n m Z) (hn : n ≤ k) {w : V} (hw : IsSemitermVec ℒₒᵣ (m + 1) 0 w) :
    ¬ReadableTruth k 3 (subst ℒₒᵣ w (^∀ neg ℒₒᵣ (prenexInductionMatrix m Z))) := by
  obtain ⟨w₀, w', rfl, hw₀, hw'⟩ := hw.exists_cons
  obtain ⟨θ, hθ, hθb⟩ := isPrenexHierarchy_iff_exists_qqToPrenex.mp h.2.2
  have hB : IsSemiformula ℒₒᵣ (m + 1 + 1) (neg ℒₒᵣ (prenexInductionMatrix m Z)) := by
    rw [add_assoc, one_add_one_eq_two]
    exact h.isSemiformula_prenexInductionMatrix.neg
  have hC := h.isCombination_neg_prenexInductionMatrix hn
  intro hT
  rw [substs_all hB.isUFormula] at hT
  have hR : IsReadable k 3
      (^∀ subst ℒₒᵣ (qVec ℒₒᵣ (w₀ ∷ w')) (neg ℒₒᵣ (prenexInductionMatrix m Z))) := by
    rw [← substs_all hB.isUFormula]
    exact (h.isReadable_all_neg_prenexInductionMatrix hn).subst hw (IsSemiformula.all.mpr hB)
  have hq : IsSemiformula ℒₒᵣ 1 (subst ℒₒᵣ (qVec ℒₒᵣ (w₀ ∷ w'))
      (neg ℒₒᵣ (prenexInductionMatrix m Z))) := hB.subst (by simpa using hw.qVec)
  rw [ReadableTruth.all_iff hR hq] at hT
  have hP : ∀ x : V, HierarchicalSatisfaction 𝚺 n θ (0 ∷ termValVec 0 m w') ∧
      (¬HierarchicalSatisfaction 𝚺 n θ (x ∷ termValVec 0 m w') ∨
        HierarchicalSatisfaction 𝚺 n θ ((x + 1) ∷ termValVec 0 m w')) ∧
      ¬HierarchicalSatisfaction 𝚺 n θ (termVal 0 w₀ ∷ termValVec 0 m w') := by
    intro x
    have := hT x
    rw [substs1_subst_qVec hw hB (numeral_semiterm 0 x),
      readableTruth_subst_neg_prenexInductionMatrix_iff h hn hθ hθb (numeral_semiterm 0 x) hw₀ hw',
      termVal_numeral] at this
    exact this
  have hd : 𝚷ᴬ-[k + 1].DefinablePred fun a : V ↦
      HierarchicalSatisfaction 𝚺 n θ (a ∷ termValVec 0 m w') := by
    have := HierarchicalSatisfaction.definable_of_isAtomLevel (V := V) (Γ := 𝚺) (.of_le hn)
    definability
  have hall := InductionOnHierarchy.succ_induction_sigma 𝚷 (k + 1) hd (hP 0).1
    fun x ih ↦ ((hP x).2.1).resolve_left (not_not.mpr ih)
  exact (hP 0).2.2 (hall _)

/-- The negation of the prenex form of an induction axiom of `𝗜𝚺 n`, with `n ≤ k`, is a block of
existential quantifiers over a closed matrix in `IsReadable k 3` all of whose instances are false.
- [HP98, Lemma I.2.4] -/
theorem IsInductionMatrix.isFalseBlock_neg_prenexInductionAxiom [V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺(k + 1)]
    (h : IsInductionMatrix n m Z) (hn : n ≤ k) :
    IsFalseBlock k 3 (neg ℒₒᵣ (prenexInductionAxiom m Z)) := by
  have hB := h.isSemiformula_prenexInductionMatrix
  have hnB : IsSemiformula ℒₒᵣ (m + 1 + 1) (neg ℒₒᵣ (prenexInductionMatrix m Z)) := by
    rw [add_assoc, one_add_one_eq_two]
    exact hB.neg
  refine ⟨m + 1, ^∀ neg ℒₒᵣ (prenexInductionMatrix m Z), ?_, IsSemiformula.all.mpr hnB, ?_, ?_,
    h.isReadable_all_neg_prenexInductionMatrix hn, fun w hw ↦ h.not_readableTruth_subst hn hw⟩
  · rw [prenexInductionAxiom, neg_qqAlls (IsUFormula.all.mpr (IsUFormula.ex.mpr hB.isUFormula)),
      neg_all (IsUFormula.ex.mpr hB.isUFormula), neg_ex hB.isUFormula, qqExss_succ']
  · rw [shift_all hB.neg.isUFormula, shift_neg hB, h.shift_prenexInductionMatrix]
  · intro p
    simp [qqAll, qqExs]

end counterexample

end FFL.FirstOrder.Arithmetic.Bootstrapping
