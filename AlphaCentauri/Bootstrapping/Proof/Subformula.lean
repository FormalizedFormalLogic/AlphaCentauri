module

public import AlphaCentauri.Bootstrapping.Proof.Inversion
public import AlphaCentauri.Bootstrapping.Proof.Substitution

/-!
# Subformulas and instances of coded formula sets

The coded set of all subformulas of an internal formula code, defined by structural recursion on
the code, and the subformula property of cut-free derivations: for a coded set `X` closed under
subformulas and free of free variables, the premises of every rule of a cut-free derivation over
the empty theory whose end-sequent consists of instances of `X` again consist of instances of `X`.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

section Subformulas

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

end Subformulas

section Instance

open PeanoMinus ISigma0 ISigma1

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

variable (L) in
/-- `Instance L X p`: `p` is obtained from a member of the coded set `X` of formula codes by
substituting terms for its bound variables. -/
def Instance (X p : V) : Prop :=
  ∃ r ∈ X, ∃ n w, IsSemiformula L n r ∧ IsSemitermVec L n 0 w ∧ p = subst L w r

instance Instance.definable : 𝚺ᴬ₁-Relation (Instance (V := V) L) := by
  unfold Instance
  definability

/-- A substitution vector sending `^&0` to itself and `^&(x + 1)` to `^&x` for every `x < N`
undoes the shift of the formulas coded by a number at most `N`. -/
lemma fvSubst_fvar_zero_cons_shift {N ι p : V} (hι : ∀ x < N, x < len ι ∧ ι.[x] = ^&x)
    (hp : IsUFormula L p) (hpN : p ≤ N) : fvSubst L (^&0 ∷ ι) (shift L p) = p := by
  have hv : ∀ x < N, x < len ι ∧ ι.[x] = termFvSubst L (^&0 ∷ ι) ^&(x + 1) := by
    intro x hx
    simp [(hι x hx).1]
  rw [fvSubst_shift hv hp.isSemiformula hpN, fvSubst_eq_self hι hp.isSemiformula hpN]

namespace Instance

variable {X : V}

/-- The shift of an instance of a set of formula codes without free variables is again an
instance. -/
lemma shift (hshift : ∀ r ∈ X, shift L r = r) {p : V} (h : Instance L X p) :
    Instance L X (shift L p) := by
  obtain ⟨r, hrX, n, w, hr, hw, rfl⟩ := h
  exact ⟨r, hrX, n, termShiftVec L n w, hr, hw.termShiftVec, by
    rw [shift_substs hr hw, hshift r hrX]⟩

/-- A formula code whose shift is an instance of a set of formula codes without free variables is
itself an instance. -/
lemma of_shift (hshift : ∀ r ∈ X, Bootstrapping.shift L r = r) {p : V} (hp : IsUFormula L p)
    (h : Instance L X (Bootstrapping.shift L p)) : Instance L X p := by
  obtain ⟨r, hrX, n, w, hr, hw, he⟩ := h
  obtain ⟨ι, hιl, hι⟩ := sigmaOne_skolem_vec (R := fun x y : V ↦ y = ^&x) (by definability)
    (l := p + X) (fun x _ ↦ ⟨_, rfl⟩)
  have hι' : ∀ x < p + X, x < len ι ∧ ι.[x] = ^&x := fun x hx ↦ ⟨by rwa [hιl], hι x hx⟩
  have hu : IsSemitermVec L (len (^&0 ∷ ι)) 0 (^&0 ∷ ι) := by
    simpa using IsSemitermVec.iff.mpr ⟨rfl, fun i hi ↦ by
      rw [hι i (by rwa [hιl] at hi)]
      simp⟩
  have hrN : r ≤ p + X := le_of_lt <| lt_of_lt_of_le (lt_of_mem hrX) (by simp)
  have h₁ : fvSubst L (^&0 ∷ ι) r = r := by
    simpa [hshift r hrX] using fvSubst_fvar_zero_cons_shift hι' hr.isUFormula hrN
  exact ⟨r, hrX, n, termFvSubstVec L n (^&0 ∷ ι) w, hr, hu.termFvSubstVec hw, by
    rw [← fvSubst_fvar_zero_cons_shift hι' hp (by simp), he, fvSubst_subst hu hw hr, h₁]⟩

/-- The left conjunct of an instance of a set closed under subformulas is an instance. -/
lemma of_and_left (hsub : ∀ r ∈ X, ∀ q ∈ subformulas L r, q ∈ X) {p q : V}
    (h : Instance L X (p ^⋏ q)) : Instance L X p := by
  obtain ⟨r, hrX, n, w, hr, hw, he⟩ := h
  obtain ⟨r₁, r₂, rfl, h₁, h₂⟩ := exists_eq_and_of_subst_eq hr.isUFormula he.symm
  obtain ⟨hr₁, hr₂⟩ := IsUFormula.and.mp hr.isUFormula
  have h₃ : IsSemiformula L n r₁ ∧ IsSemiformula L n r₂ := by simpa using hr
  exact ⟨r₁, hsub _ hrX r₁ (by simp [subformulas_and hr₁ hr₂, mem_subformulas_self hr₁]), n, w,
    h₃.1, hw, h₁.symm⟩

/-- The right conjunct of an instance of a set closed under subformulas is an instance. -/
lemma of_and_right (hsub : ∀ r ∈ X, ∀ q ∈ subformulas L r, q ∈ X) {p q : V}
    (h : Instance L X (p ^⋏ q)) : Instance L X q := by
  obtain ⟨r, hrX, n, w, hr, hw, he⟩ := h
  obtain ⟨r₁, r₂, rfl, h₁, h₂⟩ := exists_eq_and_of_subst_eq hr.isUFormula he.symm
  obtain ⟨hr₁, hr₂⟩ := IsUFormula.and.mp hr.isUFormula
  have h₃ : IsSemiformula L n r₁ ∧ IsSemiformula L n r₂ := by simpa using hr
  exact ⟨r₂, hsub _ hrX r₂ (by simp [subformulas_and hr₁ hr₂, mem_subformulas_self hr₂]), n, w,
    h₃.2, hw, h₂.symm⟩

/-- The left disjunct of an instance of a set closed under subformulas is an instance. -/
lemma of_or_left (hsub : ∀ r ∈ X, ∀ q ∈ subformulas L r, q ∈ X) {p q : V}
    (h : Instance L X (p ^⋎ q)) : Instance L X p := by
  obtain ⟨r, hrX, n, w, hr, hw, he⟩ := h
  obtain ⟨r₁, r₂, rfl, h₁, h₂⟩ := exists_eq_or_of_subst_eq hr.isUFormula he.symm
  obtain ⟨hr₁, hr₂⟩ := IsUFormula.or.mp hr.isUFormula
  have h₃ : IsSemiformula L n r₁ ∧ IsSemiformula L n r₂ := by simpa using hr
  exact ⟨r₁, hsub _ hrX r₁ (by simp [subformulas_or hr₁ hr₂, mem_subformulas_self hr₁]), n, w,
    h₃.1, hw, h₁.symm⟩

/-- The right disjunct of an instance of a set closed under subformulas is an instance. -/
lemma of_or_right (hsub : ∀ r ∈ X, ∀ q ∈ subformulas L r, q ∈ X) {p q : V}
    (h : Instance L X (p ^⋎ q)) : Instance L X q := by
  obtain ⟨r, hrX, n, w, hr, hw, he⟩ := h
  obtain ⟨r₁, r₂, rfl, h₁, h₂⟩ := exists_eq_or_of_subst_eq hr.isUFormula he.symm
  obtain ⟨hr₁, hr₂⟩ := IsUFormula.or.mp hr.isUFormula
  have h₃ : IsSemiformula L n r₁ ∧ IsSemiformula L n r₂ := by simpa using hr
  exact ⟨r₂, hsub _ hrX r₂ (by simp [subformulas_or hr₁ hr₂, mem_subformulas_self hr₂]), n, w,
    h₃.2, hw, h₂.symm⟩

/-- The free instance of the body of a universal instance of a set closed under subformulas and
without free variables is an instance. -/
lemma free_of_all (hsub : ∀ r ∈ X, ∀ q ∈ subformulas L r, q ∈ X)
    (hshift : ∀ r ∈ X, Bootstrapping.shift L r = r) {p : V} (h : Instance L X (^∀ p)) :
    Instance L X (free L p) := by
  obtain ⟨r, hrX, n, w, hr, hw, he⟩ := h
  obtain ⟨r₁, rfl, h₁⟩ := exists_eq_all_of_subst_eq hr.isUFormula he.symm
  have hr₁ := IsUFormula.all.mp hr.isUFormula
  have hr₁' : IsSemiformula L (n + 1) r₁ := by simpa using hr
  have hr₁X : r₁ ∈ X := hsub _ hrX r₁ (by simp [subformulas_all hr₁, mem_subformulas_self hr₁])
  exact ⟨r₁, hr₁X, n + 1, ^&0 ∷ termShiftVec L n w, hr₁', by simp [hw.termShiftVec], by
    rw [← h₁, free, shift_substs hr₁' hw.qVec, termShift_qVec hw, hshift r₁ hr₁X,
      substs1_subst_qVec hw.termShiftVec hr₁' (by simp)]⟩

/-- The instance at a term of the body of an existential instance of a set closed under
subformulas is an instance. -/
lemma substs1_of_exs (hsub : ∀ r ∈ X, ∀ q ∈ subformulas L r, q ∈ X) {p t : V}
    (h : Instance L X (^∃ p)) (ht : IsTerm L t) : Instance L X (substs1 L t p) := by
  obtain ⟨r, hrX, n, w, hr, hw, he⟩ := h
  obtain ⟨r₁, rfl, h₁⟩ := exists_eq_exs_of_subst_eq hr.isUFormula he.symm
  have hr₁ := IsUFormula.ex.mp hr.isUFormula
  have hr₁' : IsSemiformula L (n + 1) r₁ := by simpa using hr
  exact ⟨r₁, hsub _ hrX r₁ (by simp [subformulas_exs hr₁, mem_subformulas_self hr₁]), n + 1,
    t ∷ w, hr₁', by simp [ht, hw], by rw [← h₁, substs1_subst_qVec hw hr₁' ht]⟩

/-- The shift of a coded set of instances of a set without free variables consists of
instances. -/
lemma forall_mem_setShift (hshift : ∀ r ∈ X, Bootstrapping.shift L r = r) {s : V}
    (h : ∀ p ∈ s, Instance L X p) : ∀ p ∈ setShift L s, Instance L X p := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := mem_setShift_iff.mp hp
  exact (h q hq).shift hshift

/-- A coded formula set whose shift consists of instances of a set without free variables
consists of instances. -/
lemma of_forall_mem_setShift (hshift : ∀ r ∈ X, Bootstrapping.shift L r = r) {s : V}
    (hs : IsFormulaSet L s) (h : ∀ p ∈ setShift L s, Instance L X p) :
    ∀ p ∈ s, Instance L X p := by
  intro p hp
  exact of_shift hshift (hs p hp).isUFormula (h _ (shift_mem_setShift hp))

/-- Adding an instance to a coded set of instances yields a set of instances. -/
lemma insert {x s : V} (hx : Instance L X x) (hs : ∀ y ∈ s, Instance L X y) :
    ∀ y ∈ insert x s, Instance L X y := by
  intro y hy
  rcases mem_bitInsert_iff.mp hy with rfl | hy
  · exact hx
  · exact hs y hy

end Instance

namespace CutFreeDerivation

/-- A cut-free derivation over the empty theory whose end-sequent consists of instances of a set
`X` closed under subformulas and without free variables unfolds one step as in `case_iff`, with
the end-sequent of each immediate subderivation again consisting of instances of `X`; an axiom of
the empty theory never occurs. -/
theorem case_instance {X d : V} (hsub : ∀ r ∈ X, ∀ q ∈ subformulas L r, q ∈ X)
    (hshift : ∀ r ∈ X, shift L r = r) (hd : CutFreeDerivation (∅ : Theory L) d)
    (hX : ∀ p ∈ fstIdx d, Instance L X p) :
    IsFormulaSet L (fstIdx d) ∧
    ( (∃ s p, d = Bootstrapping.axL s p ∧ p ∈ s ∧ neg L p ∈ s) ∨
      (∃ s, d = Bootstrapping.verumIntro s ∧ ^⊤ ∈ s) ∨
      (∃ s p q dp dq, d = Bootstrapping.andIntro s p q dp dq ∧ p ^⋏ q ∈ s ∧
        (CutFreeDerivationOf (∅ : Theory L) dp (insert p s) ∧
          ∀ x ∈ insert p s, Instance L X x) ∧
        (CutFreeDerivationOf (∅ : Theory L) dq (insert q s) ∧
          ∀ x ∈ insert q s, Instance L X x)) ∨
      (∃ s p q dpq, d = Bootstrapping.orIntro s p q dpq ∧ p ^⋎ q ∈ s ∧
        CutFreeDerivationOf (∅ : Theory L) dpq (insert p (insert q s)) ∧
        ∀ x ∈ insert p (insert q s), Instance L X x) ∨
      (∃ s p dp, d = Bootstrapping.allIntro s p dp ∧ ^∀ p ∈ s ∧
        CutFreeDerivationOf (∅ : Theory L) dp (insert (free L p) (setShift L s)) ∧
        ∀ x ∈ insert (free L p) (setShift L s), Instance L X x) ∨
      (∃ s p t dp, d = Bootstrapping.exsIntro s p t dp ∧ ^∃ p ∈ s ∧ IsTerm L t ∧
        CutFreeDerivationOf (∅ : Theory L) dp (insert (substs1 L t p) s) ∧
        ∀ x ∈ insert (substs1 L t p) s, Instance L X x) ∨
      (∃ s d', d = Bootstrapping.wkRule s d' ∧ fstIdx d' ⊆ s ∧ CutFreeDerivation (∅ : Theory L) d' ∧
        ∀ x ∈ fstIdx d', Instance L X x) ∨
      (∃ s d', d = Bootstrapping.shiftRule s d' ∧ s = setShift L (fstIdx d') ∧
        CutFreeDerivation (∅ : Theory L) d' ∧ ∀ x ∈ fstIdx d', Instance L X x) ) := by
  rcases hd.case with ⟨hs,
    (h | h | ⟨s, p, q, dp, dq, rfl, hpq, hdp, hdq⟩ | ⟨s, p, q, dpq, rfl, hpq, hdpq⟩ |
      ⟨s, p, dp, rfl, hp, hdp⟩ | ⟨s, p, t, dp, rfl, hp, ht, hdp⟩ | ⟨s, d', rfl, hd's, hd'⟩ |
      ⟨s, d', rfl, rfl, hd'⟩ | ⟨s, p, rfl, -, hT⟩)⟩
  · exact ⟨hs, Or.inl h⟩
  · exact ⟨hs, Or.inr <| Or.inl h⟩
  · rw [fstIdx_andIntro] at hX
    exact ⟨hs, by
      disj 3
      exact ⟨s, p, q, dp, dq, rfl, hpq, ⟨hdp, ((hX _ hpq).of_and_left hsub).insert hX⟩,
        ⟨hdq, ((hX _ hpq).of_and_right hsub).insert hX⟩⟩⟩
  · rw [fstIdx_orIntro] at hX
    exact ⟨hs, by
      disj 4
      exact ⟨s, p, q, dpq, rfl, hpq, hdpq,
        ((hX _ hpq).of_or_left hsub).insert <| ((hX _ hpq).of_or_right hsub).insert hX⟩⟩
  · rw [fstIdx_allIntro] at hX
    exact ⟨hs, by
      disj 5
      exact ⟨s, p, dp, rfl, hp, hdp,
        ((hX _ hp).free_of_all hsub hshift).insert <| Instance.forall_mem_setShift hshift hX⟩⟩
  · rw [fstIdx_exsIntro] at hX
    exact ⟨hs, by
      disj 6
      exact ⟨s, p, t, dp, rfl, hp, ht, hdp, ((hX _ hp).substs1_of_exs hsub ht).insert hX⟩⟩
  · rw [fstIdx_wkRule] at hX
    exact ⟨hs, by
      disj 7
      exact ⟨s, d', rfl, hd's, hd', fun x hx ↦ hX x (hd's hx)⟩⟩
  · rw [fstIdx_shiftRule] at hX
    exact ⟨hs, by
      disj 8
      exact ⟨_, d', rfl, rfl, hd', Instance.of_forall_mem_setShift hshift hd'.isFormulaSet hX⟩⟩
  · exact absurd hT (not_mem_empty_Δ₁Class p)

end CutFreeDerivation

end Instance

end FFL.FirstOrder.Arithmetic.Bootstrapping
