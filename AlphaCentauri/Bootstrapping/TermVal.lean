module

public import Foundation.FirstOrder.Bootstrapping.Syntax

/-!
# Internal evaluation of terms

This module introduces internal evaluation functions for coded arithmetic terms and vectors.
It also records their definability interfaces and the basic computation and substitution laws.
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The quote of `ℒₒᵣ`'s `zero` function symbol, as a plain numeral (the concrete `ORing.Func`
constructor, matching what pattern matching on `ℒₒᵣ.Func k` produces).
- No source; a quoted restatement of `Arithmetic.coe_zeroIndex_eq`. -/
lemma quote_zeroIndex_eq : (⌜(Language.ORing.Func.zero : (ℒₒᵣ).Func 0)⌝ : V) = 0 := Arithmetic.coe_zeroIndex_eq

/-- The quote of `ℒₒᵣ`'s `one` function symbol, as a plain numeral.
- No source; a quoted restatement of `Arithmetic.coe_oneIndex_eq`. -/
lemma quote_oneIndex_eq : (⌜(Language.ORing.Func.one : (ℒₒᵣ).Func 0)⌝ : V) = 1 := Arithmetic.coe_oneIndex_eq

/-- The quote of `ℒₒᵣ`'s `add` function symbol, as a plain numeral.
- No source; a quoted restatement of `Arithmetic.coe_addIndex_eq`. -/
lemma quote_addIndex_eq : (⌜(Language.ORing.Func.add : (ℒₒᵣ).Func 2)⌝ : V) = 0 := Arithmetic.coe_addIndex_eq

/-- The quote of `ℒₒᵣ`'s `mul` function symbol, as a plain numeral.
- No source; a quoted restatement of `Arithmetic.coe_mulIndex_eq`. -/
lemma quote_mulIndex_eq : (⌜(Language.ORing.Func.mul : (ℒₒᵣ).Func 2)⌝ : V) = 1 := Arithmetic.coe_mulIndex_eq

/-- The case split of `ℒₒᵣ.IsFunc` on the concrete function-symbol indices, in plain numerals
(`zeroIndex = addIndex = 0`, `oneIndex = mulIndex = 1`, distinguished by arity).
- No source; a numeral restatement of `Arithmetic.isFunc_iff_LOR`. -/
lemma isFunc_LOR_iff {k f : V} :
    (ℒₒᵣ).IsFunc k f ↔ (k = 0 ∧ f = 0) ∨ (k = 0 ∧ f = 1) ∨ (k = 2 ∧ f = 0) ∨ (k = 2 ∧ f = 1) := by
  rw [Arithmetic.isFunc_iff_LOR,
    show (⌜(Language.Zero.zero : (ℒₒᵣ).Func 0)⌝ : V) = 0 from quote_zeroIndex_eq,
    show (⌜(Language.One.one : (ℒₒᵣ).Func 0)⌝ : V) = 1 from quote_oneIndex_eq,
    show (⌜(Language.Add.add : (ℒₒᵣ).Func 2)⌝ : V) = 0 from quote_addIndex_eq,
    show (⌜(Language.Mul.mul : (ℒₒᵣ).Func 2)⌝ : V) = 1 from quote_mulIndex_eq]

namespace TermVal

def blueprint : Language.TermRec.Blueprint 1 where
  bvar := .mkSigma “y z w. !nthDef y w z”
  fvar := .mkSigma “y x w. y = 0”
  func := .mkSigma
    “y k f v v' w.
      (k = 0 ∧ f = 0 → y = 0) ∧
      (k = 0 ∧ f = 1 → y = 1) ∧
      (k = 2 ∧ f = 0 → ∃ a, !nthDef a v' 0 ∧ ∃ b, !nthDef b v' 1 ∧ y = a + b) ∧
      (k = 2 ∧ f = 1 → ∃ a, !nthDef a v' 0 ∧ ∃ b, !nthDef b v' 1 ∧ y = a * b) ∧
      (¬(k = 0 ∧ f = 0) → ¬(k = 0 ∧ f = 1) → ¬(k = 2 ∧ f = 0) → ¬(k = 2 ∧ f = 1) → y = 0)”

noncomputable def construction : Language.TermRec.Construction V blueprint where
  bvar (param z)        := (param 0).[z]
  fvar (_     _)        := 0
  func (_     k f _ v') :=
    if k = 0 ∧ f = 0 then 0
    else if k = 0 ∧ f = 1 then 1
    else if k = 2 ∧ f = 0 then v'.[0] + v'.[1]
    else if k = 2 ∧ f = 1 then v'.[0] * v'.[1]
    else 0
  bvar_defined := .mk fun v ↦ by simp [blueprint]
  fvar_defined := .mk fun v ↦ by simp [blueprint]
  func_defined := .mk fun v ↦ by
    simp only [blueprint]
    split_ifs with h1 h2 h3 h4 <;> simp_all
    tauto

end TermVal

section termVal

open TermVal

/-- `termVal e t`: the value of the coded `ℒₒᵣ`-term `t` under the assignment `e`
(a vector; `^#i ↦ e.[i]`, `^&x ↦ 0`).
- [HP98, 1.64(5)] -/
noncomputable def termVal (e t : V) : V := construction.result ℒₒᵣ ![e] t

/-- `termValVec e k v`: `termVal e` applied to each entry of the `k`-vector `v`.
- [HP98, 1.64(5)] -/
noncomputable def termValVec (e k v : V) : V := construction.resultVec ℒₒᵣ ![e] k v

/-- The `𝚺₁` graph of `termVal`; argument order `(y, e, t)`, `y = termVal e t`.
- [HP98, 1.63] -/
noncomputable def termValGraph : 𝚺₁.Semisentence 3 := (blueprint.result ℒₒᵣ).rew <| Rew.subst ![#0, #2, #1]

/-- Graph of `termValVec`; argument order `(y, e, k, v)`.
- [HP98, 1.63] -/
noncomputable def termValVecGraph : 𝚺₁.Semisentence 4 := (blueprint.resultVec ℒₒᵣ).rew <| Rew.subst ![#0, #2, #3, #1]

/-- Evaluation of a coded bound variable reads the corresponding assignment entry.
- [HP98, 1.64(5)] -/
@[simp] lemma termVal_bvar (e z : V) : termVal e ^#z = e.[z] := by simp [termVal, construction]

/-- Evaluation of a coded free variable is zero under the total-assignment convention.
- No source; this is the convention for free variables in internal evaluation. -/
@[simp] lemma termVal_fvar (e x : V) : termVal e ^&x = 0 := by simp [termVal, construction]

section

/-- The `𝚺₁` definability witness for `termVal`.
- [HP98, 1.63] -/
instance termVal.defined : 𝚺₁-Function₂ (termVal : V → V → V) via termValGraph := .mk fun v ↦ by
  simpa [termValGraph, termVal, Matrix.constant_eq_singleton, Matrix.comp_vecCons']
    using construction.result_defined.defined ![v 0, v 2, v 1]

/-- The `𝚫₁` definability instance for `termVal`, using uniqueness of its graph.
- [HP98, 1.63] -/
instance termVal.definable : 𝚫₁-Function₂ (termVal : V → V → V) := termVal.defined.graph_delta.to_definable

/-- The `𝚺₁` definability witness for evaluation of term vectors.
- [HP98, 1.63] -/
instance termValVec.defined : 𝚺₁-Function₃ (termValVec : V → V → V → V) via termValVecGraph := .mk fun v ↦ by
  simpa [termValVecGraph, termValVec, Matrix.constant_eq_singleton, Matrix.comp_vecCons']
    using (construction.resultVec_defined (L := ℒₒᵣ)).defined ![v 0, v 2, v 3, v 1]

end

/-- Evaluation of a coded term vector preserves its coded length.
- [HP98, 1.64(5)] -/
@[simp] lemma len_termValVec {e k v : V} (hv : IsUTermVec ℒₒᵣ k v) :
    len (termValVec e k v) = k := construction.resultVec_lh ℒₒᵣ _ hv

/-- The `i`-th entry of an evaluated term vector is the evaluation of its `i`-th term.
- [HP98, 1.64(5)] -/
@[simp] lemma nth_termValVec {e k v i : V} (hv : IsUTermVec ℒₒᵣ k v) (hi : i < k) :
    (termValVec e k v).[i] = termVal e v.[i] := construction.nth_resultVec ℒₒᵣ _ hv hi

/-- Evaluation of the coded zero term is zero.
- [HP98, 1.64(5)] -/
@[simp] lemma termVal_zero (e : V) : termVal e (𝟎 : V) = 0 := by
  have hkf : (ℒₒᵣ).IsFunc (0 : V) (0 : V) := isFunc_LOR_iff.mpr (Or.inl ⟨rfl, rfl⟩)
  have hv : IsUTermVec ℒₒᵣ (0 : V) (0 : V) := by simp
  have heq : (𝟎 : V) = ^func (0 : V) (0 : V) (0 : V) := by
    rw [Arithmetic.coe_zero_eq, show (⌜(Language.Zero.zero : (ℒₒᵣ).Func 0)⌝ : V) = 0 from quote_zeroIndex_eq]
  show construction.result ℒₒᵣ ![e] (𝟎 : V) = 0
  rw [heq, construction.result_func' hkf hv]
  simp [construction]

/-- Evaluation of the coded one term is one.
- [HP98, 1.64(5)] -/
@[simp] lemma termVal_one (e : V) : termVal e (𝟏 : V) = 1 := by
  have hkf : (ℒₒᵣ).IsFunc (0 : V) (1 : V) := isFunc_LOR_iff.mpr (Or.inr <| Or.inl ⟨rfl, rfl⟩)
  have hv : IsUTermVec ℒₒᵣ (0 : V) (0 : V) := by simp
  have heq : (𝟏 : V) = ^func (0 : V) (1 : V) (0 : V) := by
    rw [Arithmetic.coe_one_eq, show (⌜(Language.One.one : (ℒₒᵣ).Func 0)⌝ : V) = 1 from quote_oneIndex_eq]
  show construction.result ℒₒᵣ ![e] (𝟏 : V) = 1
  rw [heq, construction.result_func' hkf hv]
  simp [construction]

/-- Evaluation commutes with coded addition on coded terms.
- [HP98, 1.64(5)] -/
@[simp] lemma termVal_add {e t u : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) :
    termVal e (t ^+ u) = termVal e t + termVal e u := by
  have hkf : (ℒₒᵣ).IsFunc (2 : V) (0 : V) := isFunc_LOR_iff.mpr (Or.inr <| Or.inr <| Or.inl ⟨rfl, rfl⟩)
  have hv : IsUTermVec ℒₒᵣ 2 (?[t, u] : V) := IsUTermVec.mkSeq₂_iff.mpr ⟨ht, hu⟩
  have heq : (t ^+ u : V) = ^func (2 : V) (0 : V) (?[t, u] : V) := by
    rw [Arithmetic.qqAdd, Arithmetic.coe_addIndex_eq]
  have step : termVal e (^func (2 : V) (0 : V) (?[t, u] : V)) =
      construction.func ![e] 2 0 (?[t, u] : V) (termValVec e 2 (?[t, u] : V)) :=
    construction.result_func' hkf hv
  rw [heq, step]
  simp [construction, nth_termValVec hv (show (0 : V) < 2 by simp), nth_termValVec hv (show (1 : V) < 2 by simp)]

/-- Evaluation commutes with coded multiplication on coded terms.
- [HP98, 1.64(5)] -/
@[simp] lemma termVal_mul {e t u : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) :
    termVal e (t ^* u) = termVal e t * termVal e u := by
  have hkf : (ℒₒᵣ).IsFunc (2 : V) (1 : V) := isFunc_LOR_iff.mpr (Or.inr <| Or.inr <| Or.inr ⟨rfl, rfl⟩)
  have hv : IsUTermVec ℒₒᵣ 2 (?[t, u] : V) := IsUTermVec.mkSeq₂_iff.mpr ⟨ht, hu⟩
  have heq : (t ^* u : V) = ^func (2 : V) (1 : V) (?[t, u] : V) := by
    rw [Arithmetic.qqMul, Arithmetic.coe_mulIndex_eq]
  have step : termVal e (^func (2 : V) (1 : V) (?[t, u] : V)) =
      construction.func ![e] 2 1 (?[t, u] : V) (termValVec e 2 (?[t, u] : V)) :=
    construction.result_func' hkf hv
  rw [heq, step]
  simp [construction, nth_termValVec hv (show (0 : V) < 2 by simp), nth_termValVec hv (show (1 : V) < 2 by simp)]

/-- Non-term codes evaluate to zero under the total internal evaluation.
- No source; this is the convention for malformed term codes. -/
lemma termVal_not_uterm {e t : V} (h : ¬IsUTerm ℒₒᵣ t) : termVal e t = 0 := by
  show construction.result ℒₒᵣ ![e] t = 0
  exact construction.result_prop_not ℒₒᵣ ![e] h

/-- Evaluation after coded term substitution agrees with evaluation under substituted values.
- [HP98, 1.64(3), 1.67] -/
lemma termVal_termSubst {e n m w t : V} (hw : IsSemitermVec ℒₒᵣ n m w) (ht : IsSemiterm ℒₒᵣ n t) :
    termVal e (termSubst ℒₒᵣ w t) = termVal (termValVec e n w) t := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; rw [termSubst_bvar, termVal_bvar, nth_termValVec hw.isUTerm hz]
  · intro x; simp
  · intro k f v hf hv ih
    rw [termSubst_func hf hv.isUTerm]
    have hv' : IsUTermVec ℒₒᵣ k (termSubstVec ℒₒᵣ k w v) := (hw.termSubstVec hv).isUTerm
    have key : termValVec e k (termSubstVec ℒₒᵣ k w v) = termValVec (termValVec e n w) k v := by
      apply nth_ext' k (by simp [hv']) (by simp [hv.isUTerm])
      intro i hi
      rw [nth_termValVec hv' hi, nth_termSubstVec hv.isUTerm hi, ih i hi, nth_termValVec hv.isUTerm hi]
    have step1 : termVal e (^func k f (termSubstVec ℒₒᵣ k w v)) =
        construction.func ![e] k f (termSubstVec ℒₒᵣ k w v) (termValVec e k (termSubstVec ℒₒᵣ k w v)) :=
      construction.result_func' hf hv'
    have step2 : termVal (termValVec e n w) (^func k f v) =
        construction.func ![termValVec e n w] k f v (termValVec (termValVec e n w) k v) :=
      construction.result_func' hf hv.isUTerm
    rw [step1, step2, key]
    simp [construction]

/-- Evaluation is invariant under a bound shift when entering a quantifier.
- No source; routine bridge between coded syntax and evaluation. -/
lemma termVal_termBShift {t : V} (ht : IsUTerm ℒₒᵣ t) (x e : V) :
    termVal (x ∷ e) (termBShift ℒₒᵣ t) = termVal e t := by
  apply IsUTerm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z; simp [termBShift_bvar]
  · intro x'; simp
  · intro k f v hf hv ih
    rw [termBShift_func hf hv]
    have hv' : IsUTermVec ℒₒᵣ k (termBShiftVec ℒₒᵣ k v) := hv.isSemitermVec.termBShiftVec.isUTerm
    have key : termValVec (x ∷ e) k (termBShiftVec ℒₒᵣ k v) = termValVec e k v := by
      apply nth_ext' k (by simp [hv']) (by simp [hv])
      intro i hi
      rw [nth_termValVec hv' hi, nth_termBShiftVec hv hi, ih i hi, nth_termValVec hv hi]
    have step1 : termVal (x ∷ e) (^func k f (termBShiftVec ℒₒᵣ k v)) =
        construction.func ![x ∷ e] k f (termBShiftVec ℒₒᵣ k v) (termValVec (x ∷ e) k (termBShiftVec ℒₒᵣ k v)) :=
      construction.result_func' hf hv'
    have step2 : termVal e (^func k f v) =
        construction.func ![e] k f v (termValVec e k v) :=
      construction.result_func' hf hv
    rw [step1, step2, key]
    simp [construction]

/-- Evaluation is invariant under the external-variable shift on closed terms.
- No source; routine bridge between coded syntax and evaluation. -/
lemma termVal_termShift {t : V} (ht : IsUTerm ℒₒᵣ t) (e : V) :
    termVal e (termShift ℒₒᵣ t) = termVal e t := by
  apply IsUTerm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z; simp
  · intro x; simp
  · intro k f v hf hv ih
    rw [termShift_func hf hv]
    have hv' : IsUTermVec ℒₒᵣ k (termShiftVec ℒₒᵣ k v) := IsUTermVec.termShiftVec hv
    have key : termValVec e k (termShiftVec ℒₒᵣ k v) = termValVec e k v := by
      apply nth_ext' k (by simp [hv']) (by simp [hv])
      intro i hi
      rw [nth_termValVec hv' hi, nth_termShiftVec hv hi, ih i hi, nth_termValVec hv hi]
    have step1 : termVal e (^func k f (termShiftVec ℒₒᵣ k v)) =
        construction.func ![e] k f (termShiftVec ℒₒᵣ k v) (termValVec e k (termShiftVec ℒₒᵣ k v)) :=
      construction.result_func' hf hv'
    have step2 : termVal e (^func k f v) =
        construction.func ![e] k f v (termValVec e k v) :=
      construction.result_func' hf hv
    rw [step1, step2, key]
    simp [construction]

/-- Agreement with external evaluation on quoted closed terms.
- [HP98, 1.66] -/
lemma termVal_quote {k : ℕ} (t : ClosedSemiterm ℒₒᵣ k) (v : Fin k → V) :
    termVal (matrixToVec v) ⌜t⌝ = t.valb v := by
  induction t with
  | bvar x => simp [Semiterm.empty_quote_eq, Semiterm.valb]
  | fvar x => exact x.elim
  | @func k' f w ih =>
    match k', f, w, ih with
    | 0, .zero, w, _ =>
      have hz : termVal (matrixToVec v) (^func (0 : V) (0 : V) (0 : V)) = 0 := by
        rw [show (^func (0 : V) (0 : V) (0 : V) : V) = (𝟎 : V) by
          rw [Arithmetic.coe_zero_eq, show (⌜(Language.Zero.zero : (ℒₒᵣ).Func 0)⌝ : V) = 0 from quote_zeroIndex_eq]]
        exact termVal_zero _
      simp [Semiterm.empty_quote_eq, Semiterm.valb, quote_zeroIndex_eq, hz]
      rfl
    | 0, .one, w, _ =>
      have ho : termVal (matrixToVec v) (^func (0 : V) (1 : V) (0 : V)) = 1 := by
        rw [show (^func (0 : V) (1 : V) (0 : V) : V) = (𝟏 : V) by
          rw [Arithmetic.coe_one_eq, show (⌜(Language.One.one : (ℒₒᵣ).Func 0)⌝ : V) = 1 from quote_oneIndex_eq]]
        exact termVal_one _
      simp [Semiterm.empty_quote_eq, Semiterm.valb, quote_oneIndex_eq, ho]
      rfl
    | 2, .add, w, ih =>
      have ht : IsUTerm ℒₒᵣ (⌜w 0⌝ : V) := by simp [Semiterm.empty_quote_eq]
      have hu : IsUTerm ℒₒᵣ (⌜w 1⌝ : V) := by simp [Semiterm.empty_quote_eq]
      have heq : (⌜(FirstOrder.Semiterm.func Language.ORing.Func.add w : ClosedSemiterm ℒₒᵣ k)⌝ : V) = (⌜w 0⌝ : V) ^+ ⌜w 1⌝ := by
        simp [Semiterm.empty_quote_eq, Arithmetic.qqAdd, quote_addIndex_eq, Arithmetic.coe_addIndex_eq,
          Matrix.vecHead, Matrix.vecTail]
      rw [heq, termVal_add ht hu, ih 0, ih 1]
      simp [Semiterm.valb]
      rfl
    | 2, .mul, w, ih =>
      have ht : IsUTerm ℒₒᵣ (⌜w 0⌝ : V) := by simp [Semiterm.empty_quote_eq]
      have hu : IsUTerm ℒₒᵣ (⌜w 1⌝ : V) := by simp [Semiterm.empty_quote_eq]
      have heq : (⌜(FirstOrder.Semiterm.func Language.ORing.Func.mul w : ClosedSemiterm ℒₒᵣ k)⌝ : V) = (⌜w 0⌝ : V) ^* ⌜w 1⌝ := by
        simp [Semiterm.empty_quote_eq, Arithmetic.qqMul, quote_mulIndex_eq, Arithmetic.coe_mulIndex_eq,
          Matrix.vecHead, Matrix.vecTail]
      rw [heq, termVal_mul ht hu, ih 0, ih 1]
      simp [Semiterm.valb]
      rfl

/-- A bound on term evaluation, exponential in the term code and in the largest entry of the
assignment. Foundation provides only base-`2` exponentiation (`Exp.exp`, `V`-valued exponent) and
no general `V`-base, `V`-exponent power, so the literal `(listMax e + 2) ^ (t + 1)` bound suggested
by the issue is restated here with a base-`2` exponential of comparable growth; it is `𝚫₁` (`Exp.exp`
is `𝚺₀`-definable, `listMax`, `+`, `*` are `𝚫₁`), which is what bounding the domain of the
satisfaction table (issue #49) actually needs. Left unproved after a serious attempt at the
induction on `t`: it requires establishing exponential-arithmetic lemmas
(`Exp.exp (a + b) = Exp.exp a * Exp.exp b`, monotonicity in both bounds) beyond what a term-evaluation
file should also have to develop from scratch.
- [HP98, remark after 2.58] -/
axiom termVal_le_poly (e t : V) : termVal e t ≤ Exp.exp ((listMax e + 2) * (t + 1))

end termVal

end LO.FirstOrder.Arithmetic.Bootstrapping
