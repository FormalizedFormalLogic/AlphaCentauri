module

public import AlphaCentauri.Bootstrapping.Proof.FvSubst

/-!
# Subformula codes

This module defines the internal (coded) set of all subformula codes of an internal formula
code `p`, including `p` itself, by structural recursion on `p` via `UformulaRec1`.
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* ISigma 1]
variable {L : Language} [L.Encodable] [L.LORDefinable]

namespace Subformula

/-- Blueprint of the primitive recursion computing, for a formula code, the coded set of all
its subformula codes.

No source; a formalization device mirroring `UformulaRec1.Blueprint` for a codomain of finite
sets rather than of formula/term codes.
-/
noncomputable def blueprint (L : Language) [L.Encodable] [L.LORDefinable] : UformulaRec1.Blueprint where
  rel := .mkSigma
    “y param k R v. ∃ z, !qqRelDef z k R v ∧ !insertDef y z 0”
  nrel := .mkSigma
    “y param k R v. ∃ z, !qqNRelDef z k R v ∧ !insertDef y z 0”
  verum := .mkSigma
    “y param. ∃ z, !qqVerumDef z ∧ !insertDef y z 0”
  falsum := .mkSigma
    “y param. ∃ z, !qqFalsumDef z ∧ !insertDef y z 0”
  and := .mkSigma
    “y param p₁ p₂ y₁ y₂. ∃ z, !qqAndDef z p₁ p₂ ∧ ∃ u, !unionDef u y₁ y₂ ∧ !insertDef y z u”
  or := .mkSigma
    “y param p₁ p₂ y₁ y₂. ∃ z, !qqOrDef z p₁ p₂ ∧ ∃ u, !unionDef u y₁ y₂ ∧ !insertDef y z u”
  all := .mkSigma
    “y param p₁ y₁. ∃ z, !qqAllDef z p₁ ∧ !insertDef y z y₁”
  exs := .mkSigma
    “y param p₁ y₁. ∃ z, !qqExsDef z p₁ ∧ !insertDef y z y₁”
  allChanges := .mkSigma “param' param. param' = param”
  exsChanges := .mkSigma “param' param. param' = param”

/-- Construction realizing `blueprint`: the immediate subformulas of a compound code are
inserted into the union of the subformula sets already computed for its parts; the parameter
is unused. -/
noncomputable def construction (L : Language) [L.Encodable] [L.LORDefinable] :
    UformulaRec1.Construction V (blueprint L) where
  rel _ := fun k R v ↦ insert (^rel k R v) (∅ : V)
  nrel _ := fun k R v ↦ insert (^nrel k R v) (∅ : V)
  verum _ := insert (^⊤ : V) ∅
  falsum _ := insert (^⊥ : V) ∅
  and _ := fun p₁ p₂ y₁ y₂ ↦ insert (p₁ ^⋏ p₂) (y₁ ∪ y₂)
  or _ := fun p₁ p₂ y₁ y₂ ↦ insert (p₁ ^⋎ p₂) (y₁ ∪ y₂)
  all _ := fun p₁ y₁ ↦ insert (^∀ p₁) y₁
  exs _ := fun p₁ y₁ ↦ insert (^∃ p₁) y₁
  allChanges := id
  exsChanges := id
  rel_defined := .mk fun v ↦ by simp [blueprint, emptyset_def]
  nrel_defined := .mk fun v ↦ by simp [blueprint, emptyset_def]
  verum_defined := .mk fun v ↦ by simp [blueprint, emptyset_def]
  falsum_defined := .mk fun v ↦ by simp [blueprint, emptyset_def]
  and_defined := .mk fun v ↦ by simp [blueprint]
  or_defined := .mk fun v ↦ by simp [blueprint]
  all_defined := .mk fun v ↦ by simp [blueprint]
  exs_defined := .mk fun v ↦ by simp [blueprint]
  allChanges_defined := .mk fun v ↦ by simp [blueprint]
  exChanges_defined := .mk fun v ↦ by simp [blueprint]

end Subformula

open Subformula

variable (L)

/-- The coded set of all subformula codes of the formula code `p`, including `p` itself:
codes of relation and negated-relation atoms are singletons, and the codes of a compound
formula's immediate parts are inserted into the union of their own subformula sets.

- [HP98, §V.3(g)]
-/
noncomputable def subformulas (p : V) : V := (Subformula.construction L).result L 0 p

/-- The Σ₁ graph of `subformulas`.

No source; a formalization device.
-/
noncomputable def subformulasGraph : 𝚺₁.Semisentence 2 :=
  ((Subformula.blueprint L).result L).rew (Rew.subst ![#0, ‘0’, #1])

variable {L}

section

/-- `subformulas` is `𝚺₁`-definable through `subformulasGraph`.
- No source; a formalization device mirroring the external subformula relation. -/
instance subformulas.defined : 𝚺₁-Function₁ subformulas (V := V) L via subformulasGraph L :=
  .mk fun v ↦ by
    simpa [subformulasGraph, subformulas, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using!
      (Subformula.construction L).result_defined.defined ![v 0, 0, v 1]

/-- `subformulas` is a `𝚺₁`-definable function.
- No source; a formalization device mirroring the external subformula relation. -/
instance subformulas.definable : 𝚺₁-Function₁ subformulas (V := V) L :=
  subformulas.defined.to_definable

/-- `subformulas` is definable at every level `Γ-[m + 1]` of the hierarchy.
- No source; a formalization device mirroring the external subformula relation. -/
instance subformulas.definable' : Γ-[m + 1]-Function₁ subformulas (V := V) L :=
  subformulas.definable.of_sigmaOne

end

/-- The subformulas of an atomic formula are the formula itself.
- No source; a formalization device mirroring the external subformula relation. -/
@[simp] lemma subformulas_rel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    subformulas L (^rel k R v) = insert (^rel k R v) ∅ := by
  simp [subformulas, hR, hv, Subformula.construction]

/-- The subformulas of a negated atomic formula are the formula itself.
- No source; a formalization device mirroring the external subformula relation. -/
@[simp] lemma subformulas_nrel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    subformulas L (^nrel k R v) = insert (^nrel k R v) ∅ := by
  simp [subformulas, hR, hv, Subformula.construction]

/-- The subformulas of `⊤` are `⊤` itself.
- No source; a formalization device mirroring the external subformula relation. -/
@[simp] lemma subformulas_verum : subformulas L (^⊤ : V) = insert (^⊤ : V) ∅ := by
  simp [subformulas, Subformula.construction]

/-- The subformulas of `⊥` are `⊥` itself.
- No source; a formalization device mirroring the external subformula relation. -/
@[simp] lemma subformulas_falsum : subformulas L (^⊥ : V) = insert (^⊥ : V) ∅ := by
  simp [subformulas, Subformula.construction]

/-- The subformulas of a conjunction are the conjunction and the subformulas of both
conjuncts.
- No source; a formalization device mirroring the external subformula relation. -/
@[simp] lemma subformulas_and {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    subformulas L (p ^⋏ q) = insert (p ^⋏ q) (subformulas L p ∪ subformulas L q) := by
  simp [subformulas, hp, hq, Subformula.construction]

/-- The subformulas of a disjunction are the disjunction and the subformulas of both
disjuncts.
- No source; a formalization device mirroring the external subformula relation. -/
@[simp] lemma subformulas_or {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    subformulas L (p ^⋎ q) = insert (p ^⋎ q) (subformulas L p ∪ subformulas L q) := by
  simp [subformulas, hp, hq, Subformula.construction]

/-- The subformulas of a universal formula are the formula and the subformulas of its body.
- No source; a formalization device mirroring the external subformula relation. -/
@[simp] lemma subformulas_all {p : V} (hp : IsUFormula L p) :
    subformulas L (^∀ p) = insert (^∀ p) (subformulas L p) := by
  simp [subformulas, hp, Subformula.construction]

/-- The subformulas of an existential formula are the formula and the subformulas of its
body.
- No source; a formalization device mirroring the external subformula relation. -/
@[simp] lemma subformulas_exs {p : V} (hp : IsUFormula L p) :
    subformulas L (^∃ p) = insert (^∃ p) (subformulas L p) := by
  simp [subformulas, hp, Subformula.construction]

/-- `subformulas` is not defined (returns `0`) on codes that are not formula codes. -/
lemma subformulas_not_uformula {p : V} (hp : ¬IsUFormula L p) : subformulas L p = 0 :=
  (Subformula.construction L).result_prop_not _ hp

/-- Every formula code is a subformula of itself.

- [HP98, §V.3(g)]
-/
lemma mem_subformulas_self {p : V} (hp : IsUFormula L p) : p ∈ subformulas L p := by
  have H : ∀ p : V, IsUFormula L p → p ∈ subformulas L p := by
    apply IsUFormula.ISigma1.sigma1_succ_induction (P := fun p ↦ p ∈ subformulas L p) (by definability)
    case hrel => intro k R v hR hv; simp [hR, hv]
    case hnrel => intro k R v hR hv; simp [hR, hv]
    case hverum => simp
    case hfalsum => simp
    case hand => intro p q hp hq _ _; simp [hp, hq]
    case hor => intro p q hp hq _ _; simp [hp, hq]
    case hall => intro p hp _; simp [hp]
    case hexs => intro p hp _; simp [hp]
  exact H p hp

/-- Every subformula code of a formula code is bounded by it.

- [HP98, §V.3(g)]
-/
lemma le_of_mem_subformulas {p q : V} (hp : IsUFormula L p) (hq : q ∈ subformulas L p) : q ≤ p := by
  have H : ∀ p : V, IsUFormula L p → ∀ q ∈ subformulas L p, q ≤ p := by
    apply IsUFormula.ISigma1.pi1_succ_induction
      (P := fun p ↦ ∀ q ∈ subformulas L p, q ≤ p) (by definability)
    case hrel =>
      intro k R v hR hv q hq
      simp only [subformulas_rel hR hv, mem_bitInsert_iff, not_mem_empty, or_false] at hq
      exact hq.le
    case hnrel =>
      intro k R v hR hv q hq
      simp only [subformulas_nrel hR hv, mem_bitInsert_iff, not_mem_empty, or_false] at hq
      exact hq.le
    case hverum =>
      intro q hq
      simp only [subformulas_verum, mem_bitInsert_iff, not_mem_empty, or_false] at hq
      exact hq.le
    case hfalsum =>
      intro q hq
      simp only [subformulas_falsum, mem_bitInsert_iff, not_mem_empty, or_false] at hq
      exact hq.le
    case hand =>
      intro p₁ p₂ hp₁ hp₂ ih₁ ih₂ q hq
      simp only [subformulas_and hp₁ hp₂, mem_bitInsert_iff, mem_cup_iff] at hq
      rcases hq with rfl | hq | hq
      · rfl
      · exact le_of_lt (lt_of_le_of_lt (ih₁ q hq) (by simp))
      · exact le_of_lt (lt_of_le_of_lt (ih₂ q hq) (by simp))
    case hor =>
      intro p₁ p₂ hp₁ hp₂ ih₁ ih₂ q hq
      simp only [subformulas_or hp₁ hp₂, mem_bitInsert_iff, mem_cup_iff] at hq
      rcases hq with rfl | hq | hq
      · rfl
      · exact le_of_lt (lt_of_le_of_lt (ih₁ q hq) (by simp))
      · exact le_of_lt (lt_of_le_of_lt (ih₂ q hq) (by simp))
    case hall =>
      intro p₁ hp₁ ih₁ q hq
      simp only [subformulas_all hp₁, mem_bitInsert_iff] at hq
      rcases hq with rfl | hq
      · rfl
      · exact le_of_lt (lt_of_le_of_lt (ih₁ q hq) (by simp))
    case hexs =>
      intro p₁ hp₁ ih₁ q hq
      simp only [subformulas_exs hp₁, mem_bitInsert_iff] at hq
      rcases hq with rfl | hq
      · rfl
      · exact le_of_lt (lt_of_le_of_lt (ih₁ q hq) (by simp))
  exact H p hp q hq

/-- Every subformula code of a formula code is itself a formula code.

- [HP98, §V.3(g)]
-/
lemma IsUFormula.of_mem_subformulas {p q : V} (hp : IsUFormula L p) (hq : q ∈ subformulas L p) :
    IsUFormula L q := by
  have H : ∀ p : V, IsUFormula L p → ∀ q ∈ subformulas L p, IsUFormula L q := by
    apply IsUFormula.ISigma1.pi1_succ_induction
      (P := fun p ↦ ∀ q ∈ subformulas L p, IsUFormula L q) (by definability)
    case hrel =>
      intro k R v hR hv q hq
      simp only [subformulas_rel hR hv, mem_bitInsert_iff, not_mem_empty, or_false] at hq
      simp [hq, hR, hv]
    case hnrel =>
      intro k R v hR hv q hq
      simp only [subformulas_nrel hR hv, mem_bitInsert_iff, not_mem_empty, or_false] at hq
      simp [hq, hR, hv]
    case hverum =>
      intro q hq
      simp only [subformulas_verum, mem_bitInsert_iff, not_mem_empty, or_false] at hq
      simp [hq]
    case hfalsum =>
      intro q hq
      simp only [subformulas_falsum, mem_bitInsert_iff, not_mem_empty, or_false] at hq
      simp [hq]
    case hand =>
      intro p₁ p₂ hp₁ hp₂ ih₁ ih₂ q hq
      simp only [subformulas_and hp₁ hp₂, mem_bitInsert_iff, mem_cup_iff] at hq
      rcases hq with rfl | hq | hq
      · simp [hp₁, hp₂]
      · exact ih₁ q hq
      · exact ih₂ q hq
    case hor =>
      intro p₁ p₂ hp₁ hp₂ ih₁ ih₂ q hq
      simp only [subformulas_or hp₁ hp₂, mem_bitInsert_iff, mem_cup_iff] at hq
      rcases hq with rfl | hq | hq
      · simp [hp₁, hp₂]
      · exact ih₁ q hq
      · exact ih₂ q hq
    case hall =>
      intro p₁ hp₁ ih₁ q hq
      simp only [subformulas_all hp₁, mem_bitInsert_iff] at hq
      rcases hq with rfl | hq
      · simp [hp₁]
      · exact ih₁ q hq
    case hexs =>
      intro p₁ hp₁ ih₁ q hq
      simp only [subformulas_exs hp₁, mem_bitInsert_iff] at hq
      rcases hq with rfl | hq
      · simp [hp₁]
      · exact ih₁ q hq
  exact H p hp q hq

/-- The subformula relation is transitive: the subformulas of a subformula of `p` are among
the subformulas of `p`.

- [HP98, §V.3(g)]
-/
lemma subformulas_subset_of_mem {p q : V} (hp : IsUFormula L p) (hq : q ∈ subformulas L p) :
    subformulas L q ⊆ subformulas L p := by
  have H : ∀ p : V, IsUFormula L p → ∀ q ∈ subformulas L p, subformulas L q ⊆ subformulas L p := by
    apply IsUFormula.ISigma1.pi1_succ_induction
      (P := fun p : V ↦ ∀ q ∈ subformulas L p, subformulas L q ⊆ subformulas L p) (by definability)
    case hrel =>
      intro k R v hR hv q hq
      simp only [subformulas_rel hR hv, mem_bitInsert_iff, not_mem_empty, or_false] at hq
      simp [hq]
    case hnrel =>
      intro k R v hR hv q hq
      simp only [subformulas_nrel hR hv, mem_bitInsert_iff, not_mem_empty, or_false] at hq
      simp [hq]
    case hverum =>
      intro q hq
      simp only [subformulas_verum, mem_bitInsert_iff, not_mem_empty, or_false] at hq
      simp [hq]
    case hfalsum =>
      intro q hq
      simp only [subformulas_falsum, mem_bitInsert_iff, not_mem_empty, or_false] at hq
      simp [hq]
    case hand =>
      intro p₁ p₂ hp₁ hp₂ ih₁ ih₂ q hq
      simp only [subformulas_and hp₁ hp₂, mem_bitInsert_iff, mem_cup_iff] at hq
      rcases hq with rfl | hq | hq
      · simp [hp₁, hp₂]
      · exact subset_trans (ih₁ q hq) (by
          rw [subformulas_and hp₁ hp₂]; exact subset_trans (union_succ_union_left _ _) (susbset_insert _ _))
      · exact subset_trans (ih₂ q hq) (by
          rw [subformulas_and hp₁ hp₂]; exact subset_trans (union_succ_union_right _ _) (susbset_insert _ _))
    case hor =>
      intro p₁ p₂ hp₁ hp₂ ih₁ ih₂ q hq
      simp only [subformulas_or hp₁ hp₂, mem_bitInsert_iff, mem_cup_iff] at hq
      rcases hq with rfl | hq | hq
      · simp [hp₁, hp₂]
      · exact subset_trans (ih₁ q hq) (by
          rw [subformulas_or hp₁ hp₂]; exact subset_trans (union_succ_union_left _ _) (susbset_insert _ _))
      · exact subset_trans (ih₂ q hq) (by
          rw [subformulas_or hp₁ hp₂]; exact subset_trans (union_succ_union_right _ _) (susbset_insert _ _))
    case hall =>
      intro p₁ hp₁ ih₁ q hq
      simp only [subformulas_all hp₁, mem_bitInsert_iff] at hq
      rcases hq with rfl | hq
      · simp [hp₁]
      · exact subset_trans (ih₁ q hq) (by rw [subformulas_all hp₁]; exact susbset_insert _ _)
    case hexs =>
      intro p₁ hp₁ ih₁ q hq
      simp only [subformulas_exs hp₁, mem_bitInsert_iff] at hq
      rcases hq with rfl | hq
      · simp [hp₁]
      · exact subset_trans (ih₁ q hq) (by rw [subformulas_exs hp₁]; exact susbset_insert _ _)
  exact H p hp q hq

variable (L)

/-- The union, over all codes in the coded set `s`, of their subformula sets.

No source; a formalization device.
-/
noncomputable def subformulasSet (s : V) : V := ⋃ʰᶠ (hfsImage (subformulas L) s)

variable {L}

/-- Membership in `subformulasSet L s`: `q` is a subformula of some code in `s`. -/
lemma mem_subformulasSet_iff {s q : V} : q ∈ subformulasSet L s ↔ ∃ p ∈ s, q ∈ subformulas L p := by
  have := (subformulas.definable : 𝚺₁-Function₁ subformulas (V := V) L)
  constructor
  · intro h
    rcases mem_sUnion_iff.mp h with ⟨c, hc, hqc⟩
    rcases mem_hfsImage_iff.mp hc with ⟨p, hp, rfl⟩
    exact ⟨p, hp, hqc⟩
  · rintro ⟨p, hp, hq⟩
    exact mem_sUnion_iff.mpr ⟨subformulas L p, app_mem_hfsImage hp, hq⟩

end LO.FirstOrder.Arithmetic.Bootstrapping
