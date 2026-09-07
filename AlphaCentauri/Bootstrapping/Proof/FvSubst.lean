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

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* ISigma 1]
variable {L : Language} [L.Encodable] [L.LORDefinable]

namespace TermFvSubst

/-- Recursion blueprint for `termFvSubst`: a bound-variable code is left unchanged, a
free-variable code is replaced by the entry of `w` at its index when that index is within `w`'s
length (and left unchanged otherwise), and a function application code keeps its head symbol and
recurses into the vector of arguments.
- No source; a formalization device: Foundation has no substitution for free variables on codes. -/
def blueprint : Language.TermRec.Blueprint 1 where
  bvar := .mkSigma “y z w. !qqBvarDef y z”
  fvar := .mkSigma
    “y x w. (∃ k, !lenDef k w ∧ x < k ∧ !nthDef y w x) ∨
      (∃ k, !lenDef k w ∧ ¬x < k ∧ !qqFvarDef y x)”
  func := .mkSigma “y k f v v' w. !qqFuncDef y k f v'”

/-- The realization of `TermFvSubst.blueprint` as a `Language.TermRec.Construction`, together
with the `𝚺₁`-definability witness for each clause.
- No source; a formalization device: Foundation has no substitution for free variables on codes. -/
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

/-- `termFvSubst L w t`: the coded `L`-term obtained from `t` by substituting the free variables
below the length of `w` with the corresponding entries of `w`, leaving bound variables and
out-of-range free variables unchanged.
- No source; a formalization device: Foundation has no substitution for free variables on codes. -/
noncomputable def termFvSubst (w t : V) : V := construction.result L ![w] t

/-- `termFvSubstVec L k w v`: `termFvSubst L w` applied entrywise to the coded `k`-vector `v`.
- No source; a formalization device: Foundation has no substitution for free variables on codes. -/
noncomputable def termFvSubstVec (k w v : V) : V := construction.resultVec L ![w] k v

/-- The `𝚺₁` graph of `termFvSubst`; argument order `(y, w, t)`, `y = termFvSubst L w t`.
- No source; a formalization device: Foundation has no substitution for free variables on codes. -/
noncomputable def termFvSubstGraph : 𝚺₁.Semisentence 3 :=
  (blueprint.result L).rew <| Rew.subst ![#0, #2, #1]

/-- The `𝚺₁` graph of `termFvSubstVec`; argument order `(y, w, k, v)`.
- No source; a formalization device: Foundation has no substitution for free variables on codes. -/
noncomputable def termFvSubstVecGraph : 𝚺₁.Semisentence 4 :=
  (blueprint.resultVec L).rew <| Rew.subst ![#0, #1, #3, #2]

variable {L}

/-- Substitution of free variables leaves a coded bound variable unchanged.
- No source; a formalization device: Foundation has no substitution for free variables on codes. -/
@[simp] lemma termFvSubst_bvar (w z : V) : termFvSubst L w ^#z = ^#z := by
  simp [termFvSubst, construction]

/-- Substitution of free variables reads off the entry of `w` at index `x` when `x` is within
`w`'s length, and leaves `x` unchanged otherwise.
- No source; a formalization device: Foundation has no substitution for free variables on codes. -/
@[simp] lemma termFvSubst_fvar (w x : V) :
    termFvSubst L w ^&x = if x < len w then w.[x] else ^&x := by
  simp [termFvSubst, construction]

/-- Substitution of free variables commutes with a coded function application, keeping its
function symbol and recursing into the argument vector.
- No source; a formalization device: Foundation has no substitution for free variables on codes. -/
@[simp] lemma termFvSubst_func {w k f v : V} (hf : L.IsFunc k f)
    (hv : IsUTermVec L k v) :
    termFvSubst L w (^func k f v) = ^func k f (termFvSubstVec L k w v) := by
  simp [termFvSubst, construction, hf, hv]
  rfl

section

/-- The `𝚺₁` definability witness for `termFvSubst`, via `termFvSubstGraph`.
- No source; a formalization device: Foundation has no substitution for free variables on codes. -/
instance termFvSubst.defined : 𝚺₁-Function₂ termFvSubst (V := V) L via termFvSubstGraph L :=
  .mk fun v ↦ by
    simpa [termFvSubstGraph, termFvSubst, Matrix.constant_eq_singleton,
      Matrix.comp_vecCons'] using construction.result_defined.defined ![v 0, v 2, v 1]

/-- The `𝚺₁` definability instance for `termFvSubst`, forgetting the specific witness graph.
- No source; a formalization device: Foundation has no substitution for free variables on codes. -/
instance termFvSubst.definable : 𝚺₁-Function₂ termFvSubst (V := V) L :=
  termFvSubst.defined.to_definable

/-- `termFvSubst` is `Γ`-definable at every level `m + 1` above `𝚺₁`.
- No source; a formalization device: Foundation has no substitution for free variables on codes. -/
instance termFvSubst.definable' : Γ-[m + 1]-Function₂ termFvSubst (V := V) L :=
  termFvSubst.definable.of_sigmaOne

/-- The `𝚺₁` definability witness for `termFvSubstVec`, via `termFvSubstVecGraph`.
- No source; a formalization device: Foundation has no substitution for free variables on codes. -/
instance termFvSubstVec.defined :
    𝚺₁-Function₃ termFvSubstVec (V := V) L via termFvSubstVecGraph L := .mk fun v ↦ by
  simpa [termFvSubstVecGraph, termFvSubstVec, Matrix.constant_eq_singleton,
    Matrix.comp_vecCons'] using construction.resultVec_defined.defined ![v 0, v 1, v 3, v 2]

/-- The `𝚺₁` definability instance for `termFvSubstVec`, forgetting the specific witness graph.
- No source; a formalization device: Foundation has no substitution for free variables on codes. -/
instance termFvSubstVec.definable : 𝚺₁-Function₃ termFvSubstVec (V := V) L :=
  termFvSubstVec.defined.to_definable

/-- `termFvSubstVec` is `Γ`-definable at every level `m + 1` above `𝚺₁`.
- No source; a formalization device: Foundation has no substitution for free variables on codes. -/
instance termFvSubstVec.definable' : Γ-[m + 1]-Function₃ termFvSubstVec (V := V) L :=
  termFvSubstVec.definable.of_sigmaOne

end

/-- Free-variable substitution on a coded term vector preserves its coded length.
- No source; a formalization device: Foundation has no substitution for free variables on codes. -/
@[simp] lemma len_termFvSubstVec {k w v : V} (hv : IsUTermVec L k v) :
    len (termFvSubstVec L k w v) = k := construction.resultVec_lh L _ hv

/-- The `i`-th entry of a free-variable-substituted term vector is the substitution applied to
the `i`-th entry of the original.
- No source; a formalization device: Foundation has no substitution for free variables on codes. -/
@[simp] lemma nth_termFvSubstVec {k w v i : V} (hv : IsUTermVec L k v) (hi : i < k) :
    (termFvSubstVec L k w v).[i] = termFvSubst L w v.[i] :=
  construction.nth_resultVec L _ hv hi

/-- Free-variable substitution on the empty coded vector is the empty vector.
- No source; a formalization device: Foundation has no substitution for free variables on codes. -/
@[simp] lemma termFvSubstVec_nil (w : V) : termFvSubstVec L 0 w 0 = 0 :=
  construction.resultVec_nil L _

/-- Free-variable substitution on a coded vector distributes over prepending an entry.
- No source; a formalization device: Foundation has no substitution for free variables on codes. -/
lemma termFvSubstVec_cons {k w t v : V} (ht : IsUTerm L t) (hv : IsUTermVec L k v) :
    termFvSubstVec L (k + 1) w (t ∷ v) =
      termFvSubst L w t ∷ termFvSubstVec L k w v :=
  construction.resultVec_cons L ![w] hv ht

/-- Free-variable substitution by a vector of `n`-ary semiterms preserves being an `n`-ary
semiterm.
- No source; a formalization device: Foundation has no substitution for free variables on codes. -/
@[simp] lemma IsSemiterm.termFvSubst {n w t : V} (hw : IsSemitermVec L (len w) n w)
    (ht : IsSemiterm L n t) : IsSemiterm L n (termFvSubst L w t) := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
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

/-- Free-variable substitution by a vector of `n`-ary semiterms preserves being an `n`-ary
semiterm vector.
- No source; a formalization device: Foundation has no substitution for free variables on codes. -/
@[simp] lemma IsSemitermVec.termFvSubstVec {k n w v : V} (hw : IsSemitermVec L (len w) n w)
    (hv : IsSemitermVec L k n v) : IsSemitermVec L k n (termFvSubstVec L k w v) :=
  IsSemitermVec.iff.mpr ⟨by simp [hv.isUTerm], fun i hi ↦ by
    rw [nth_termFvSubstVec hv.isUTerm hi]
    exact (hv.nth hi).termFvSubst hw⟩

/-- A semiterm vector bounded by `n` free variables is also bounded by any larger `m`.
- No source; a routine monotonicity fact about the bound-variable count. -/
lemma IsSemitermVec.weaken {k n m v : V} (hv : IsSemitermVec L k n v) (hnm : n ≤ m) :
    IsSemitermVec L k m v :=
  ⟨hv.isUTerm, fun {_i} hi ↦ le_trans (hv.bv hi) hnm⟩

/-- A semiterm vector bounded by `n` free variables is also bounded by `n + 1`.
- No source; a routine monotonicity fact about the bound-variable count. -/
lemma IsSemitermVec.succ {k n v : V} (hv : IsSemitermVec L k n v) :
    IsSemitermVec L k (n + 1) v := hv.weaken (by simp)

/-- Free-variable substitution by a well-formed term vector preserves being a well-formed term
vector.
- No source; a formalization device: Foundation has no substitution for free variables on codes. -/
lemma IsUTermVec.termFvSubstVec {k w v : V} (hw : IsUTermVec L (len w) w)
    (hv : IsUTermVec L k v) : IsUTermVec L k (termFvSubstVec L k w v) := by
  exact (hw.isSemitermVec.weaken (le_max_left _ _)).termFvSubstVec
    (hv.isSemitermVec.weaken (le_max_right _ _)) |>.isUTerm

/-- A semiformula bounded by `n` free variables is also bounded by any larger `m`.
- No source; a routine monotonicity fact about the bound-variable count. -/
lemma IsSemiformula.weaken {n m p : V} (hp : IsSemiformula L n p) (hnm : n ≤ m) :
    IsSemiformula L m p := ⟨hp.isUFormula, le_trans hp.bv_le hnm⟩

namespace FvSubst

/-- Recursion blueprint for `fvSubst`: atomic (non-)relations substitute their argument vector via
`termFvSubstVec` and keep their relation symbol, the propositional connectives and quantifiers
pass through unchanged, and the substitution vector `w` is left untouched when crossing a
quantifier.
- No source; a formalization device: Foundation has no substitution for free variables on codes. -/
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

/-- The realization of `FvSubst.blueprint` as a `UformulaRec1.Construction`, together with the
`𝚺₁`-definability witness for each clause.
- No source; a formalization device: Foundation has no substitution for free variables on codes. -/
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

/-- `fvSubst L w p`: the coded `L`-formula obtained from `p` by substituting the free variables
below the length of `w` with the corresponding entries of `w` throughout, leaving bound variables
and out-of-range free variables unchanged.
- No source; a formalization device: Foundation has no substitution for free variables on codes. -/
noncomputable def fvSubst (w p : V) : V := (FvSubst.construction L).result L w p

/-- The `𝚺₁` graph of `fvSubst`; argument order `(y, w, p)`, `y = fvSubst L w p`.
- No source; a formalization device: Foundation has no substitution for free variables on codes. -/
noncomputable def fvSubstGraph : 𝚺₁.Semisentence 3 := (blueprint L).result L

variable {L}

section

/-- The `𝚺₁` definability witness for `fvSubst`, via `fvSubstGraph`.
- No source; a formalization device: Foundation has no substitution for free variables on codes. -/
instance fvSubst.defined : 𝚺₁-Function₂[V] fvSubst L via fvSubstGraph L :=
  (FvSubst.construction L).result_defined

/-- The `𝚺₁` definability instance for `fvSubst`, forgetting the specific witness graph.
- No source; a formalization device: Foundation has no substitution for free variables on codes. -/
instance fvSubst.definable : 𝚺₁-Function₂[V] fvSubst L := fvSubst.defined.to_definable

/-- `fvSubst` is `Γ`-definable at every level `m + 1` above `𝚺₁`.
- No source; a formalization device: Foundation has no substitution for free variables on codes. -/
instance fvSubst.definable' : Γ-[m + 1]-Function₂[V] fvSubst L :=
  fvSubst.definable.of_sigmaOne

end

/-- Substitution of free variables commutes with a coded relation atom, substituting its argument
vector and keeping the relation symbol.
- No source; a formalization device: Foundation has no substitution for free variables on codes. -/
@[simp] lemma fvSubst_rel {w k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    fvSubst L w (^relk R v) = ^relk R (termFvSubstVec L k w v) := by
  simp [fvSubst, hR, hv, FvSubst.construction]

/-- Substitution of free variables commutes with a coded negated relation atom, substituting its
argument vector and keeping the relation symbol.
- No source; a formalization device: Foundation has no substitution for free variables on codes. -/
@[simp] lemma fvSubst_nrel {w k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    fvSubst L w (^nrelk R v) = ^nrelk R (termFvSubstVec L k w v) := by
  simp [fvSubst, hR, hv, FvSubst.construction]

/-- Substitution of free variables leaves the coded `⊤` unchanged.
- No source; a formalization device: Foundation has no substitution for free variables on codes. -/
@[simp] lemma fvSubst_verum (w : V) : fvSubst L w ^⊤ = ^⊤ := by
  simp [fvSubst, FvSubst.construction]

/-- Substitution of free variables leaves the coded `⊥` unchanged.
- No source; a formalization device: Foundation has no substitution for free variables on codes. -/
@[simp] lemma fvSubst_falsum (w : V) : fvSubst L w ^⊥ = ^⊥ := by
  simp [fvSubst, FvSubst.construction]

/-- Substitution of free variables commutes with coded conjunction.
- No source; a formalization device: Foundation has no substitution for free variables on codes. -/
@[simp] lemma fvSubst_and {w p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    fvSubst L w (p ^⋏ q) = fvSubst L w p ^⋏ fvSubst L w q := by
  simp [fvSubst, hp, hq, FvSubst.construction]

/-- Substitution of free variables commutes with coded disjunction.
- No source; a formalization device: Foundation has no substitution for free variables on codes. -/
@[simp] lemma fvSubst_or {w p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    fvSubst L w (p ^⋎ q) = fvSubst L w p ^⋎ fvSubst L w q := by
  simp [fvSubst, hp, hq, FvSubst.construction]

/-- Substitution of free variables commutes with the coded universal quantifier.
- No source; a formalization device: Foundation has no substitution for free variables on codes. -/
@[simp] lemma fvSubst_all {w p : V} (hp : IsUFormula L p) :
    fvSubst L w (^∀ p) = ^∀ (fvSubst L w p) := by
  simp [fvSubst, hp, FvSubst.construction]

/-- Substitution of free variables commutes with the coded existential quantifier.
- No source; a formalization device: Foundation has no substitution for free variables on codes. -/
@[simp] lemma fvSubst_exs {w p : V} (hp : IsUFormula L p) :
    fvSubst L w (^∃ p) = ^∃ (fvSubst L w p) := by
  simp [fvSubst, hp, FvSubst.construction]

/-- Non-formula codes substitute to zero under the total internal substitution.
- No source; this is the convention for malformed formula codes. -/
lemma fvSubst_not_uformula {w p : V} (hp : ¬IsUFormula L p) : fvSubst L w p = 0 :=
  (FvSubst.construction L).result_prop_not _ hp

/-- Free-variable substitution by a vector of `n`-ary semiterms preserves being an `n`-ary
semiformula.
- No source; a formalization device: Foundation has no substitution for free variables on codes. -/
@[simp] lemma IsSemiformula.fvSubst {n w p : V} (hw : IsSemitermVec L (len w) n w)
    (hp : IsSemiformula L n p) : IsSemiformula L n (fvSubst L w p) := by
  apply IsSemiformula.pi1_structural_induction
    (P := fun n p ↦ ∀ w, IsSemitermVec L (len w) n w →
      IsSemiformula L n (FFL.FirstOrder.Arithmetic.Bootstrapping.fvSubst L w p))
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

/-- Substitution of free variables commutes with coded negation.
- No source; a formalization device: Foundation has no substitution for free variables on codes. -/
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

/-- The external-variable shift after free-variable substitution equals free-variable substitution
by the shifted substitution vector with a fresh variable `&0` prepended, applied after the shift.
- No source; a routine technical bridge. -/
lemma termShift_termFvSubst {n w t : V}
    (hw : IsSemitermVec L (len w) n w) (ht : IsSemiterm L n t) :
    termShift L (termFvSubst L w t) =
      termFvSubst L (^&0 ∷ termShiftVec L (len w) w) (termShift L t) := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
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

/-- The external-variable shift after free-variable substitution equals free-variable substitution,
by the shifted substitution vector with a fresh variable `&0` prepended, applied after the shift.
- No source; a routine technical bridge. -/
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

/-- Substituting the bound variables of a closed (`0`-ary) semiterm is the identity, since it has
none to replace.
- No source; a routine technical bridge. -/
lemma termSubst_zero {v t : V} (ht : IsSemiterm L 0 t) : termSubst L v t = t := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
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

/-- Bound-shifting a closed (`0`-ary) semiterm is the identity, since it has no bound variables to
shift.
- No source; a routine technical bridge. -/
lemma termBShift_zero {t : V} (ht : IsSemiterm L 0 t) : termBShift L t = t := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
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

/-- For a substitution vector of closed terms, free-variable substitution commutes with the
bound-variable shift.
- No source; a routine technical bridge. -/
lemma termFvSubst_termBShift_closed {n w t : V}
    (hw : IsSemitermVec L (len w) 0 w) (ht : IsSemiterm L n t) :
    termFvSubst L w (termBShift L t) = termBShift L (termFvSubst L w t) := by
  have hw' : IsSemitermVec L (len w) n w := hw.weaken (by simp)
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
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

/-- For a substitution vector of closed terms, free-variable substitution commutes with
bound-variable substitution, substituting the entries of the bound-variable substitution vector as
well.
- No source; a routine technical bridge. -/
lemma termFvSubst_termSubst {n m w v t : V}
    (hw : IsSemitermVec L (len w) 0 w) (hv : IsSemitermVec L n m v)
    (ht : IsSemiterm L n t) :
    termFvSubst L w (termSubst L v t) =
      termSubst L (termFvSubstVec L n w v) (termFvSubst L w t) := by
  have hw' : IsSemitermVec L (len w) n w := hw.weaken (by simp)
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
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

/-- For a substitution vector of closed terms, free-variable substitution commutes with prefixing
the bound variable `#0` used to enter a quantifier (`qVec`).
- No source; a routine technical bridge. -/
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

/-- `fvSubstImage w s`: the coded set obtained by applying `fvSubst L w` to every formula code in
the coded set `s`.
- No source; a formalization device: Foundation has no substitution for free variables on codes. -/
noncomputable def fvSubstImage (w s : V) : V := by
  letI : 𝚺₁-Function₁ (fvSubst L w) := by definability
  exact hfsImage (fvSubst L w) s

/-- A formula code belongs to `fvSubstImage w s` iff it is `fvSubst L w q` for some formula code
`q ∈ s`.
- No source; a formalization device: Foundation has no substitution for free variables on codes. -/
lemma mem_fvSubstImage_iff {w s p : V} :
    p ∈ fvSubstImage (L := L) w s ↔ ∃ q ∈ s, p = fvSubst L w q := by
  let _ : 𝚺₁-Function₁ (fvSubst L w) := by definability
  exact mem_hfsImage_iff

/-- Free-variable substitution by a vector of closed terms carries a coded formula set to a coded
formula set.
- No source; a formalization device: Foundation has no substitution for free variables on codes. -/
lemma formulaSet_fvSubstImage {w s : V} (hw : IsSemitermVec L (len w) 0 w)
    (hs : IsFormulaSet L s) : IsFormulaSet L (fvSubstImage (L := L) w s) := by
  intro p hp
  rcases mem_fvSubstImage_iff.mp hp with ⟨q, hq, rfl⟩
  exact IsSemiformula.fvSubst hw (hs q hq)

/-- For a substitution vector of closed terms, free-variable substitution commutes with
bound-variable substitution at the formula level, substituting the entries of the bound-variable
substitution vector as well.
- No source; a routine technical bridge. -/
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

/-- For a substitution vector of closed terms, free-variable substitution commutes with
single-variable substitution, substituting the term being substituted as well.
- No source; a routine technical bridge. -/
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

end FFL.FirstOrder.Arithmetic.Bootstrapping
