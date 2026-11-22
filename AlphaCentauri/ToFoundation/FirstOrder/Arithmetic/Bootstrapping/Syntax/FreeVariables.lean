module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.HFS.Vec

/-!
# Free variables of coded terms and formulas

`termFreeVariables L t` and `freeVariables L p` are the coded sets of the free variables of a coded
term `t` and a coded formula `p`. A coded formula has no free variables exactly when shifting its
free variables leaves it unchanged.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic
namespace Bootstrapping

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

variable {Γ : Polarity} {m : ℕ}

/-! ### Terms -/

namespace TermFreeVariables

def blueprint : Language.TermRec.Blueprint 0 where
  bvar := .mkSigma “y z. y = 0”
  fvar := .mkSigma “y x. !insertDef y x 0”
  func := .mkSigma “y k f v v'. !listUnionDef y v'”

noncomputable def construction : Language.TermRec.Construction V blueprint where
  bvar _ _          := ∅
  fvar _ x          := {x}
  func _ _ _ _ v'   := listUnion v'
  bvar_defined := .mk fun v ↦ by simp [blueprint, emptyset_def]
  fvar_defined := .mk fun v ↦ by simp [blueprint, singleton_eq_insert, emptyset_def]
  func_defined := .mk fun v ↦ by
    simp only [blueprint, Bounding.HierarchySymbol.Semiformula.val_mkSigma]; simp

end TermFreeVariables

section termFreeVariables

open TermFreeVariables

variable (L)

/-- The coded set of the free variables of the coded term `t`. -/
noncomputable def termFreeVariables (t : V) : V := construction.result L ![] t

/-- The vector of the coded sets of the free variables of the coded terms in `v`. -/
noncomputable def termFreeVariablesVec (k v : V) : V := construction.resultVec L ![] k v

noncomputable def termFreeVariablesGraph : 𝚺ᴬ₁.Semisentence 2 := blueprint.result L

noncomputable def termFreeVariablesVecGraph : 𝚺ᴬ₁.Semisentence 3 := blueprint.resultVec L

variable {L}

@[simp]
lemma termFreeVariables_bvar (z : V) :
    termFreeVariables L ^#z = ∅ := by simp [termFreeVariables, construction]

@[simp]
lemma termFreeVariables_fvar (x : V) :
    termFreeVariables L ^&x = {x} := by simp [termFreeVariables, construction]

@[simp]
lemma termFreeVariables_func {k f v : V} (hkf : L.IsFunc k f) (hv : IsUTermVec L k v) :
    termFreeVariables L (^func k f v) = listUnion (termFreeVariablesVec L k v) := by
  simp [termFreeVariables, construction, hkf, hv]; rfl

@[simp]
lemma len_termFreeVariablesVec {k v : V} (hv : IsUTermVec L k v) :
    len (termFreeVariablesVec L k v) = k := construction.resultVec_lh L _ hv

@[simp]
lemma nth_termFreeVariablesVec {k v i : V} (hv : IsUTermVec L k v) (hi : i < k) :
    (termFreeVariablesVec L k v).[i] = termFreeVariables L v.[i] :=
  construction.nth_resultVec L _ hv hi

section

instance termFreeVariables.defined :
    𝚺ᴬ₁-Function₁ (termFreeVariables (V := V) L) via termFreeVariablesGraph L :=
  construction.result_defined

instance termFreeVariables.definable : 𝚺ᴬ₁-Function₁ (termFreeVariables (V := V) L) :=
  termFreeVariables.defined.to_definable

instance termFreeVariables.definable' : Γᴬ_[m + 1]-Function₁ (termFreeVariables (V := V) L) :=
  termFreeVariables.definable.of_sigmaOne

instance termFreeVariablesVec.defined :
    𝚺ᴬ₁-Function₂ (termFreeVariablesVec (V := V) L) via termFreeVariablesVecGraph L :=
  construction.resultVec_defined

instance termFreeVariablesVec.definable : 𝚺ᴬ₁-Function₂ (termFreeVariablesVec (V := V) L) :=
  termFreeVariablesVec.defined.to_definable

instance termFreeVariablesVec.definable' :
    Γᴬ_[m + 1]-Function₂ (termFreeVariablesVec (V := V) L) :=
  termFreeVariablesVec.definable.of_sigmaOne

end

lemma termFreeVariablesVec_eq_empty_iff {k v : V} (hv : IsUTermVec L k v) :
    listUnion (termFreeVariablesVec L k v) = ∅ ↔ ∀ i < k, termFreeVariables L v.[i] = ∅ := by
  rw [listUnion_eq_empty_iff, len_termFreeVariablesVec hv]
  exact forall₂_congr fun i hi ↦ by rw [nth_termFreeVariablesVec hv hi]

lemma termShiftVec_eq_self_iff_forall {k v : V} (hv : IsUTermVec L k v) :
    termShiftVec L k v = v ↔ ∀ i < k, termShift L v.[i] = v.[i] := by
  constructor
  · intro h i hi
    rw [← nth_termShiftVec hv hi, h]
  · intro h
    apply nth_ext' k (by simp [hv]) hv.lh.symm
    intro i hi
    rw [nth_termShiftVec hv hi]
    exact h i hi

/-- A coded term has no free variables exactly when shifting its free variables leaves it
unchanged. -/
lemma termShift_eq_self_iff {t : V} (ht : IsUTerm L t) :
    termShift L t = t ↔ termFreeVariables L t = ∅ := by
  apply IsUTerm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z
    simp
  · intro x
    rw [termShift_fvar, termFreeVariables_fvar]
    exact iff_of_false (by simp [qqFvar]) fun h ↦ by simpa using congrArg (x ∈ ·) h
  · intro k f v hf hv ih
    rw [termShift_func hf hv, termFreeVariables_func hf hv, qqFunc_inj,
      termShiftVec_eq_self_iff_forall hv, termFreeVariablesVec_eq_empty_iff hv]
    simpa using forall₂_congr ih

lemma termShiftVec_eq_self_iff {k v : V} (hv : IsUTermVec L k v) :
    termShiftVec L k v = v ↔ listUnion (termFreeVariablesVec L k v) = ∅ := by
  rw [termShiftVec_eq_self_iff_forall hv, termFreeVariablesVec_eq_empty_iff hv]
  exact forall₂_congr fun i hi ↦ termShift_eq_self_iff (hv.nth hi)

end termFreeVariables

/-! ### Formulas -/

namespace FreeVariables

variable (L)

noncomputable def blueprint : UformulaRec1.Blueprint where
  rel := .mkSigma “y param k R v. ∃ M, !(termFreeVariablesVecGraph L) M k v ∧ !listUnionDef y M”
  nrel := .mkSigma “y param k R v. ∃ M, !(termFreeVariablesVecGraph L) M k v ∧ !listUnionDef y M”
  verum := .mkSigma “y param. y = 0”
  falsum := .mkSigma “y param. y = 0”
  and := .mkSigma “y param p₁ p₂ y₁ y₂. !unionDef y y₁ y₂”
  or := .mkSigma “y param p₁ p₂ y₁ y₂. !unionDef y y₁ y₂”
  all := .mkSigma “y param p₁ ys. ∃ y₁, !nthDef y₁ ys 0 ∧ y = y₁”
  exs := .mkSigma “y param p₁ ys. ∃ y₁, !nthDef y₁ ys 0 ∧ y = y₁”

noncomputable def construction : UformulaRec1.Construction V (blueprint L) where
  rel {_} := fun k _ v ↦ listUnion (termFreeVariablesVec L k v)
  nrel {_} := fun k _ v ↦ listUnion (termFreeVariablesVec L k v)
  verum {_} := ∅
  falsum {_} := ∅
  and {_} := fun _ _ y₁ y₂ ↦ y₁ ∪ y₂
  or {_} := fun _ _ y₁ y₂ ↦ y₁ ∪ y₂
  all {_} := fun _ ys ↦ ys.[0]
  exs {_} := fun _ ys ↦ ys.[0]
  rel_defined := .mk fun v ↦ by
    simp only [blueprint, Bounding.HierarchySymbol.Semiformula.val_mkSigma]; simp
  nrel_defined := .mk fun v ↦ by
    simp only [blueprint, Bounding.HierarchySymbol.Semiformula.val_mkSigma]; simp
  verum_defined := .mk fun v ↦ by simp [blueprint, emptyset_def]
  falsum_defined := .mk fun v ↦ by simp [blueprint, emptyset_def]
  and_defined := .mk fun v ↦ by simp [blueprint]
  or_defined := .mk fun v ↦ by simp [blueprint]
  all_defined := .mk fun v ↦ by simp [blueprint]
  exs_defined := .mk fun v ↦ by simp [blueprint]

end FreeVariables

section freeVariables

open FreeVariables

variable (L)

/-- The coded set of the free variables of the coded formula `p`. -/
noncomputable def freeVariables (p : V) : V := (construction L).result L 0 p

noncomputable def freeVariablesGraph : 𝚺ᴬ₁.Semisentence 2 :=
  (blueprint L).result L |>.rew (Rew.subst ![#0, ‘0’, #1])

variable {L}

section

instance freeVariables.defined : 𝚺ᴬ₁-Function₁[V] freeVariables L via freeVariablesGraph L :=
  .mk fun v ↦ by
    simpa [freeVariablesGraph, Matrix.comp_vecCons', Matrix.constant_eq_singleton]
      using! (construction L).result_defined.defined ![v 0, 0, v 1]

instance freeVariables.definable : 𝚺ᴬ₁-Function₁[V] freeVariables L :=
  freeVariables.defined.to_definable

instance freeVariables.definable' : Γᴬ_[m + 1]-Function₁[V] freeVariables L :=
  freeVariables.definable.of_sigmaOne

end

@[simp]
lemma freeVariables_rel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    freeVariables L (^rel k R v) = listUnion (termFreeVariablesVec L k v) := by
  simp [freeVariables, hR, hv, construction]

@[simp]
lemma freeVariables_nrel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    freeVariables L (^nrel k R v) = listUnion (termFreeVariablesVec L k v) := by
  simp [freeVariables, hR, hv, construction]

@[simp]
lemma freeVariables_verum : freeVariables L (^⊤ : V) = ∅ := by
  simp [freeVariables, construction]

@[simp]
lemma freeVariables_falsum : freeVariables L (^⊥ : V) = ∅ := by
  simp [freeVariables, construction]

@[simp]
lemma freeVariables_and {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    freeVariables L (p ^⋏ q) = freeVariables L p ∪ freeVariables L q := by
  simp [freeVariables, hp, hq, construction]

@[simp]
lemma freeVariables_or {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    freeVariables L (p ^⋎ q) = freeVariables L p ∪ freeVariables L q := by
  simp [freeVariables, hp, hq, construction]

@[simp]
lemma freeVariables_all {p : V} (hp : IsUFormula L p) :
    freeVariables L (^∀ p) = freeVariables L p := by
  simp [freeVariables, hp, construction]

@[simp]
lemma freeVariables_exs {p : V} (hp : IsUFormula L p) :
    freeVariables L (^∃ p) = freeVariables L p := by
  simp [freeVariables, hp, construction]

@[simp]
lemma freeVariables_neg {p : V} (hp : IsUFormula L p) :
    freeVariables L (neg L p) = freeVariables L p := by
  apply IsUFormula.ISigma1.sigma1_succ_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · definability
  · intro k R v hR hv
    simp [hR, hv]
  · intro k R v hR hv
    simp [hR, hv]
  · simp
  · simp
  · intro p q hp hq ihp ihq
    simp [hp, hq, hp.neg, hq.neg, ihp, ihq]
  · intro p q hp hq ihp ihq
    simp [hp, hq, hp.neg, hq.neg, ihp, ihq]
  · intro p hp ih
    simp [hp, hp.neg, ih]
  · intro p hp ih
    simp [hp, hp.neg, ih]

/-- A coded formula has no free variables exactly when shifting its free variables leaves it
unchanged. -/
lemma shift_eq_self_iff {p : V} (hp : IsUFormula L p) :
    shift L p = p ↔ freeVariables L p = ∅ := by
  apply IsUFormula.ISigma1.sigma1_succ_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · definability
  · intro k R v hR hv
    rw [shift_rel hR hv, freeVariables_rel hR hv, qqRel_inj, termShiftVec_eq_self_iff hv]
    simp
  · intro k R v hR hv
    rw [shift_nrel hR hv, freeVariables_nrel hR hv, qqNRel_inj, termShiftVec_eq_self_iff hv]
    simp
  · simp
  · simp
  · intro p q hp hq ihp ihq
    rw [shift_and hp hq, freeVariables_and hp hq, qqAnd_inj, ihp, ihq]
    simp [mem_ext_iff, forall_and]
  · intro p q hp hq ihp ihq
    rw [shift_or hp hq, freeVariables_or hp hq, qqOr_inj, ihp, ihq]
    simp [mem_ext_iff, forall_and]
  · intro p hp ih
    rw [shift_all hp, freeVariables_all hp, qqAll_inj, ih]
  · intro p hp ih
    rw [shift_exs hp, freeVariables_exs hp, qqExs_inj, ih]

end freeVariables

end Bootstrapping
end FFL.FirstOrder.Arithmetic
