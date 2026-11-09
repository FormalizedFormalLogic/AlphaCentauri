module

public import AlphaCentauri.Bootstrapping.Proof.FvSubst

/-!
# Subformula codes

This module defines the internal (coded) set of all subformula codes of an internal formula
code `p`, including `p` itself, by structural recursion on `p` via `UformulaRec1`.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* ISigma 1]
variable {L : Language} [L.Encodable] [L.LORDefinable]

namespace Subformula

/-- Blueprint of the primitive recursion computing, for a formula code, the coded set of all
its subformula codes. -/
noncomputable def blueprint (L : Language) [L.Encodable] [L.LORDefinable] :
    UformulaRec1.Blueprint where
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
    “y param p₁ ys. ∃ y₁, !nthDef y₁ ys 0 ∧ ∃ z, !qqAllDef z p₁ ∧ !insertDef y z y₁”
  exs := .mkSigma
    “y param p₁ ys. ∃ y₁, !nthDef y₁ ys 0 ∧ ∃ z, !qqExsDef z p₁ ∧ !insertDef y z y₁”

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
  all _ := fun p₁ ys ↦ insert (^∀ p₁) ys.[0]
  exs _ := fun p₁ ys ↦ insert (^∃ p₁) ys.[0]
  rel_defined := .mk fun v ↦ by simp [blueprint, emptyset_def]
  nrel_defined := .mk fun v ↦ by simp [blueprint, emptyset_def]
  verum_defined := .mk fun v ↦ by simp [blueprint, emptyset_def]
  falsum_defined := .mk fun v ↦ by simp [blueprint, emptyset_def]
  and_defined := .mk fun v ↦ by simp [blueprint]
  or_defined := .mk fun v ↦ by simp [blueprint]
  all_defined := .mk fun v ↦ by simp [blueprint]
  exs_defined := .mk fun v ↦ by simp [blueprint]

end Subformula

open Subformula

variable (L)

/-- The coded set of all subformula codes of the formula code `p`, including `p` itself:
codes of relation and negated-relation atoms are singletons, and the codes of a compound
formula's immediate parts are inserted into the union of their own subformula sets.

- [HP98, §V.3(g)]
-/
noncomputable def subformulas (p : V) : V := (Subformula.construction L).result L 0 p

/-- The Σ₁ graph of `subformulas`. -/
noncomputable def subformulasGraph : 𝚺ᴬ₁.Semisentence 2 :=
  ((Subformula.blueprint L).result L).rew (Rew.subst ![#0, ‘0’, #1])

variable {L}

section

variable {Γ : SigmaPiDelta} {m : ℕ}

instance subformulas.defined : 𝚺ᴬ₁-Function₁ subformulas (V := V) L via subformulasGraph L :=
  .mk fun v ↦ by
    simpa [subformulasGraph, subformulas, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using!
      (Subformula.construction L).result_defined.defined ![v 0, 0, v 1]

instance subformulas.definable : 𝚺ᴬ₁-Function₁ subformulas (V := V) L :=
  subformulas.defined.to_definable

instance subformulas.definable' : Γᴬ_[m + 1]-Function₁ subformulas (V := V) L :=
  subformulas.definable.of_sigmaOne

end

@[simp] lemma subformulas_rel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    subformulas L (^rel k R v) = insert (^rel k R v) ∅ := by
  simp [subformulas, hR, hv, Subformula.construction]

@[simp] lemma subformulas_nrel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    subformulas L (^nrel k R v) = insert (^nrel k R v) ∅ := by
  simp [subformulas, hR, hv, Subformula.construction]

@[simp] lemma subformulas_verum : subformulas L (^⊤ : V) = insert (^⊤ : V) ∅ := by
  simp [subformulas, Subformula.construction]

@[simp] lemma subformulas_falsum : subformulas L (^⊥ : V) = insert (^⊥ : V) ∅ := by
  simp [subformulas, Subformula.construction]

@[simp] lemma subformulas_and {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    subformulas L (p ^⋏ q) = insert (p ^⋏ q) (subformulas L p ∪ subformulas L q) := by
  simp [subformulas, hp, hq, Subformula.construction]

@[simp] lemma subformulas_or {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    subformulas L (p ^⋎ q) = insert (p ^⋎ q) (subformulas L p ∪ subformulas L q) := by
  simp [subformulas, hp, hq, Subformula.construction]

@[simp] lemma subformulas_all {p : V} (hp : IsUFormula L p) :
    subformulas L (^∀ p) = insert (^∀ p) (subformulas L p) := by
  simp [subformulas, hp, Subformula.construction]

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
    apply IsUFormula.ISigma1.sigma1_succ_induction (P := fun p ↦ p ∈ subformulas L p)
      (by definability)
    case hrel => intro k R v hR hv; simp [hR, hv]
    case hnrel => intro k R v hR hv; simp [hR, hv]
    case hverum => simp
    case hfalsum => simp
    case hand => intro p q hp hq _ _; simp [hp, hq]
    case hor => intro p q hp hq _ _; simp [hp, hq]
    case hall => intro p hp _; simp [hp]
    case hexs => intro p hp _; simp [hp]
  exact H p hp

variable (L) in
/-- `r` is an immediate subformula of `p`. -/
def IsImmediateSub (r p : V) : Prop :=
  IsUFormula L r ∧ ((∃ s, IsUFormula L s ∧
    (p = r ^⋏ s ∨ p = s ^⋏ r ∨ p = r ^⋎ s ∨ p = s ^⋎ r)) ∨ p = ^∀ r ∨ p = ^∃ r)

namespace IsImmediateSub

variable {r p : V}

lemma isUFormula (h : IsImmediateSub L r p) : IsUFormula L p := by
  rcases h with ⟨hr, ⟨s, hs, rfl | rfl | rfl | rfl⟩ | rfl | rfl⟩ <;> simp [*]

lemma lt (h : IsImmediateSub L r p) : r < p := by
  rcases h with ⟨hr, ⟨s, hs, rfl | rfl | rfl | rfl⟩ | rfl | rfl⟩ <;> simp

lemma subformulas_subset (h : IsImmediateSub L r p) : subformulas L r ⊆ subformulas L p := by
  rcases h with ⟨hr, ⟨s, hs, rfl | rfl | rfl | rfl⟩ | rfl | rfl⟩
  · rw [subformulas_and hr hs]
    exact subset_trans (union_succ_union_left _ _) (susbset_insert _ _)
  · rw [subformulas_and hs hr]
    exact subset_trans (union_succ_union_right _ _) (susbset_insert _ _)
  · rw [subformulas_or hr hs]
    exact subset_trans (union_succ_union_left _ _) (susbset_insert _ _)
  · rw [subformulas_or hs hr]
    exact subset_trans (union_succ_union_right _ _) (susbset_insert _ _)
  · rw [subformulas_all hr]
    exact susbset_insert _ _
  · rw [subformulas_exs hr]
    exact susbset_insert _ _

lemma shift_eq (h : IsImmediateSub L r p) (hp : shift L p = p) : shift L r = r := by
  rcases h with ⟨hr, ⟨s, hs, rfl | rfl | rfl | rfl⟩ | rfl | rfl⟩
  · exact (by simpa [shift_and hr hs] using hp : shift L r = r ∧ shift L s = s).1
  · exact (by simpa [shift_and hs hr] using hp : shift L s = s ∧ shift L r = r).2
  · exact (by simpa [shift_or hr hs] using hp : shift L r = r ∧ shift L s = s).1
  · exact (by simpa [shift_or hs hr] using hp : shift L s = s ∧ shift L r = r).2
  · simpa [shift_all hr] using hp
  · simpa [shift_exs hr] using hp

end IsImmediateSub

/-- Induction on the subformula relation: a property of pairs `(p, q)` with `q` a subformula of
`p` holds if it holds reflexively and is passed from an immediate subformula to the formula. -/
theorem subformulas_induction {P : V → V → Prop}
    (hP : 𝚷ᴬ₁-Predicate fun p : V ↦ ∀ q ∈ subformulas L p, P p q)
    (hself : ∀ p, IsUFormula L p → P p p)
    (hstep : ∀ r p q, IsImmediateSub L r p → P r q → P p q) {p q : V} (hp : IsUFormula L p)
    (hq : q ∈ subformulas L p) : P p q := by
  have H : ∀ p : V, IsUFormula L p → ∀ q ∈ subformulas L p, P p q := by
    apply IsUFormula.ISigma1.pi1_succ_induction (P := fun p ↦ ∀ q ∈ subformulas L p, P p q) hP
    case hrel =>
      intro k R v hR hv q hq
      simp only [subformulas_rel hR hv, mem_bitInsert_iff, not_mem_empty, or_false] at hq
      subst hq
      exact hself _ (by simp [hR, hv])
    case hnrel =>
      intro k R v hR hv q hq
      simp only [subformulas_nrel hR hv, mem_bitInsert_iff, not_mem_empty, or_false] at hq
      subst hq
      exact hself _ (by simp [hR, hv])
    case hverum =>
      intro q hq
      simp only [subformulas_verum, mem_bitInsert_iff, not_mem_empty, or_false] at hq
      subst hq
      exact hself _ (by simp)
    case hfalsum =>
      intro q hq
      simp only [subformulas_falsum, mem_bitInsert_iff, not_mem_empty, or_false] at hq
      subst hq
      exact hself _ (by simp)
    case hand =>
      intro p₁ p₂ hp₁ hp₂ ih₁ ih₂ q hq
      simp only [subformulas_and hp₁ hp₂, mem_bitInsert_iff, mem_cup_iff] at hq
      rcases hq with rfl | hq | hq
      · exact hself _ (by simp [hp₁, hp₂])
      · exact hstep _ _ _ ⟨hp₁, Or.inl ⟨p₂, hp₂, Or.inl rfl⟩⟩ (ih₁ q hq)
      · exact hstep _ _ _ ⟨hp₂, Or.inl ⟨p₁, hp₁, Or.inr <| Or.inl rfl⟩⟩ (ih₂ q hq)
    case hor =>
      intro p₁ p₂ hp₁ hp₂ ih₁ ih₂ q hq
      simp only [subformulas_or hp₁ hp₂, mem_bitInsert_iff, mem_cup_iff] at hq
      rcases hq with rfl | hq | hq
      · exact hself _ (by simp [hp₁, hp₂])
      · exact hstep _ _ _ ⟨hp₁, Or.inl ⟨p₂, hp₂, Or.inr <| Or.inr <| Or.inl rfl⟩⟩ (ih₁ q hq)
      · exact hstep _ _ _ ⟨hp₂, Or.inl ⟨p₁, hp₁, Or.inr <| Or.inr <| Or.inr rfl⟩⟩ (ih₂ q hq)
    case hall =>
      intro p₁ hp₁ ih₁ q hq
      simp only [subformulas_all hp₁, mem_bitInsert_iff] at hq
      rcases hq with rfl | hq
      · exact hself _ (by simp [hp₁])
      · exact hstep _ _ _ ⟨hp₁, Or.inr <| Or.inl rfl⟩ (ih₁ q hq)
    case hexs =>
      intro p₁ hp₁ ih₁ q hq
      simp only [subformulas_exs hp₁, mem_bitInsert_iff] at hq
      rcases hq with rfl | hq
      · exact hself _ (by simp [hp₁])
      · exact hstep _ _ _ ⟨hp₁, Or.inr <| Or.inr rfl⟩ (ih₁ q hq)
  exact H p hp q hq

/-- Every subformula code of a formula code is bounded by it.

- [HP98, §V.3(g)]
-/
lemma le_of_mem_subformulas {p q : V} (hp : IsUFormula L p) (hq : q ∈ subformulas L p) : q ≤ p :=
  subformulas_induction (P := fun p q ↦ q ≤ p) (by definability) (fun _ _ ↦ le_rfl)
    (fun _ _ _ h ih ↦ ih.trans h.lt.le) hp hq

/-- Every subformula code of a formula code is itself a formula code.

- [HP98, §V.3(g)]
-/
lemma IsUFormula.of_mem_subformulas {p q : V} (hp : IsUFormula L p) (hq : q ∈ subformulas L p) :
    IsUFormula L q :=
  subformulas_induction (P := fun _ q ↦ IsUFormula L q) (by definability) (fun _ hp ↦ hp)
    (fun _ _ _ _ ih ↦ ih) hp hq

/-- The subformula relation is transitive: the subformulas of a subformula of `p` and the
subformulas of `p`.

- [HP98, §V.3(g)]
-/
lemma subformulas_subset_of_mem {p q : V} (hp : IsUFormula L p) (hq : q ∈ subformulas L p) :
    subformulas L q ⊆ subformulas L p :=
  subformulas_induction (P := fun p q ↦ subformulas L q ⊆ subformulas L p) (by definability)
    (fun _ _ ↦ subset_refl _) (fun _ _ _ h ih ↦ subset_trans ih h.subformulas_subset) hp hq

variable (L)

/-- The union, over all codes in the coded set `s`, of their subformula sets. -/
noncomputable def subformulasSet (s : V) : V := ⋃ʰᶠ (hfsImage (subformulas L) s)

variable {L}

/-- Membership in `subformulasSet L s`: `q` is a subformula of some code in `s`. -/
lemma mem_subformulasSet_iff {s q : V} : q ∈ subformulasSet L s ↔ ∃ p ∈ s, q ∈ subformulas L p := by
  have := (subformulas.definable : 𝚺ᴬ₁-Function₁ subformulas (V := V) L)
  constructor
  · intro h
    rcases mem_sUnion_iff.mp h with ⟨c, hc, hqc⟩
    rcases mem_hfsImage_iff.mp hc with ⟨p, hp, rfl⟩
    exact ⟨p, hp, hqc⟩
  · rintro ⟨p, hp, hq⟩
    exact mem_sUnion_iff.mpr ⟨subformulas L p, app_mem_hfsImage hp, hq⟩

end FFL.FirstOrder.Arithmetic.Bootstrapping
