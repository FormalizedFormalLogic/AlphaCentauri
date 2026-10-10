module

public import AlphaCentauri.Bootstrapping.Proof.Inversion
public import AlphaCentauri.Bootstrapping.Proof.Subformula
public import AlphaCentauri.Bootstrapping.Proof.Substitution

/-!
# Instances of a coded set of formulas in cut-free derivations

This module defines when a formula code is an instance of a member of a coded set `X` of formula
codes — the result of substituting terms for its bound variables — and shows that, for `X` closed
under subformulas and free of free variables, the premises of every rule of a cut-free derivation
over the empty theory whose end-sequent consists of instances of `X` again consist of instances of
`X`.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

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

section inversion

variable {w : V}

/-- The shape of a formula code, together with the value substitution by `w` takes on it. -/
private lemma subst_case {r : V} (hr : IsUFormula L r) :
    (∃ k R v, L.IsRel k R ∧ IsUTermVec L k v ∧ r = ^rel k R v ∧
      subst L w r = ^rel k R (termSubstVec L k w v)) ∨
    (∃ k R v, L.IsRel k R ∧ IsUTermVec L k v ∧ r = ^nrel k R v ∧
      subst L w r = ^nrel k R (termSubstVec L k w v)) ∨
    (r = ^⊤ ∧ subst L w r = (^⊤ : V)) ∨
    (r = ^⊥ ∧ subst L w r = (^⊥ : V)) ∨
    (∃ r₁ r₂, IsUFormula L r₁ ∧ IsUFormula L r₂ ∧ r = r₁ ^⋏ r₂ ∧
      subst L w r = subst L w r₁ ^⋏ subst L w r₂) ∨
    (∃ r₁ r₂, IsUFormula L r₁ ∧ IsUFormula L r₂ ∧ r = r₁ ^⋎ r₂ ∧
      subst L w r = subst L w r₁ ^⋎ subst L w r₂) ∨
    (∃ r₁, IsUFormula L r₁ ∧ r = ^∀ r₁ ∧ subst L w r = ^∀ (subst L (qVec L w) r₁)) ∨
    (∃ r₁, IsUFormula L r₁ ∧ r = ^∃ r₁ ∧ subst L w r = ^∃ (subst L (qVec L w) r₁)) := by
  rcases hr.case with (⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩ | rfl | rfl |
    ⟨r₁, r₂, hr₁, hr₂, rfl⟩ | ⟨r₁, r₂, hr₁, hr₂, rfl⟩ | ⟨r₁, hr₁, rfl⟩ | ⟨r₁, hr₁, rfl⟩)
  · disj 1; exact ⟨k, R, v, hR, hv, rfl, substs_rel hR hv⟩
  · disj 2; exact ⟨k, R, v, hR, hv, rfl, substs_nrel hR hv⟩
  · disj 3; exact ⟨rfl, by simp⟩
  · disj 4; exact ⟨rfl, by simp⟩
  · disj 5; exact ⟨r₁, r₂, hr₁, hr₂, rfl, substs_and hr₁ hr₂⟩
  · disj 6; exact ⟨r₁, r₂, hr₁, hr₂, rfl, substs_or hr₁ hr₂⟩
  · disj 7; exact ⟨r₁, hr₁, rfl, substs_all hr₁⟩
  · disj 8; exact ⟨r₁, hr₁, rfl, substs_ex hr₁⟩

/-- A formula code whose substitution instance is a conjunction is itself a conjunction, and its
conjuncts substitute to the given ones. -/
lemma exists_and_of_subst_eq_and {r p q : V} (hr : IsUFormula L r) (h : subst L w r = p ^⋏ q) :
    ∃ r₁ r₂, IsUFormula L r₁ ∧ IsUFormula L r₂ ∧ r = r₁ ^⋏ r₂ ∧
      subst L w r₁ = p ∧ subst L w r₂ = q := by
  rcases subst_case (w := w) hr with
    (⟨k, R, v, hR, hv, rfl, hs⟩ | ⟨k, R, v, hR, hv, rfl, hs⟩ | ⟨rfl, hs⟩ | ⟨rfl, hs⟩ |
      ⟨r₁, r₂, hr₁, hr₂, rfl, hs⟩ | ⟨r₁, r₂, hr₁, hr₂, rfl, hs⟩ |
      ⟨r₁, hr₁, rfl, hs⟩ | ⟨r₁, hr₁, rfl, hs⟩) <;> rw [hs] at h
  · simp [qqRel, qqAnd] at h
  · simp [qqNRel, qqAnd] at h
  · simp [qqVerum, qqAnd] at h
  · simp [qqFalsum, qqAnd] at h
  · obtain ⟨h₁, h₂⟩ : subst L w r₁ = p ∧ subst L w r₂ = q := by simpa using h
    exact ⟨r₁, r₂, hr₁, hr₂, rfl, h₁, h₂⟩
  · simp [qqAnd, qqOr] at h
  · simp [qqAnd, qqAll] at h
  · simp [qqAnd, qqExs] at h

/-- A formula code whose substitution instance is a disjunction is itself a disjunction, and its
disjuncts substitute to the given ones. -/
lemma exists_or_of_subst_eq_or {r p q : V} (hr : IsUFormula L r) (h : subst L w r = p ^⋎ q) :
    ∃ r₁ r₂, IsUFormula L r₁ ∧ IsUFormula L r₂ ∧ r = r₁ ^⋎ r₂ ∧
      subst L w r₁ = p ∧ subst L w r₂ = q := by
  rcases subst_case (w := w) hr with
    (⟨k, R, v, hR, hv, rfl, hs⟩ | ⟨k, R, v, hR, hv, rfl, hs⟩ | ⟨rfl, hs⟩ | ⟨rfl, hs⟩ |
      ⟨r₁, r₂, hr₁, hr₂, rfl, hs⟩ | ⟨r₁, r₂, hr₁, hr₂, rfl, hs⟩ |
      ⟨r₁, hr₁, rfl, hs⟩ | ⟨r₁, hr₁, rfl, hs⟩) <;> rw [hs] at h
  · simp [qqRel, qqOr] at h
  · simp [qqNRel, qqOr] at h
  · simp [qqVerum, qqOr] at h
  · simp [qqFalsum, qqOr] at h
  · simp [qqAnd, qqOr] at h
  · obtain ⟨h₁, h₂⟩ : subst L w r₁ = p ∧ subst L w r₂ = q := by simpa using h
    exact ⟨r₁, r₂, hr₁, hr₂, rfl, h₁, h₂⟩
  · simp [qqOr, qqAll] at h
  · simp [qqOr, qqExs] at h

/-- A formula code whose substitution instance is a universal quantification is itself one, and
its body substitutes, under the quantified vector, to the given one. -/
lemma exists_all_of_subst_eq_all {r p : V} (hr : IsUFormula L r) (h : subst L w r = ^∀ p) :
    ∃ r₁, IsUFormula L r₁ ∧ r = ^∀ r₁ ∧ subst L (qVec L w) r₁ = p := by
  rcases subst_case (w := w) hr with
    (⟨k, R, v, hR, hv, rfl, hs⟩ | ⟨k, R, v, hR, hv, rfl, hs⟩ | ⟨rfl, hs⟩ | ⟨rfl, hs⟩ |
      ⟨r₁, r₂, hr₁, hr₂, rfl, hs⟩ | ⟨r₁, r₂, hr₁, hr₂, rfl, hs⟩ |
      ⟨r₁, hr₁, rfl, hs⟩ | ⟨r₁, hr₁, rfl, hs⟩) <;> rw [hs] at h
  · simp [qqRel, qqAll] at h
  · simp [qqNRel, qqAll] at h
  · simp [qqVerum, qqAll] at h
  · simp [qqFalsum, qqAll] at h
  · simp [qqAnd, qqAll] at h
  · simp [qqOr, qqAll] at h
  · exact ⟨r₁, hr₁, rfl, by simpa using h⟩
  · simp [qqAll, qqExs] at h

/-- A formula code whose substitution instance is an existential quantification is itself one,
and its body substitutes, under the quantified vector, to the given one. -/
lemma exists_exs_of_subst_eq_exs {r p : V} (hr : IsUFormula L r) (h : subst L w r = ^∃ p) :
    ∃ r₁, IsUFormula L r₁ ∧ r = ^∃ r₁ ∧ subst L (qVec L w) r₁ = p := by
  rcases subst_case (w := w) hr with
    (⟨k, R, v, hR, hv, rfl, hs⟩ | ⟨k, R, v, hR, hv, rfl, hs⟩ | ⟨rfl, hs⟩ | ⟨rfl, hs⟩ |
      ⟨r₁, r₂, hr₁, hr₂, rfl, hs⟩ | ⟨r₁, r₂, hr₁, hr₂, rfl, hs⟩ |
      ⟨r₁, hr₁, rfl, hs⟩ | ⟨r₁, hr₁, rfl, hs⟩) <;> rw [hs] at h
  · simp [qqRel, qqExs] at h
  · simp [qqNRel, qqExs] at h
  · simp [qqVerum, qqExs] at h
  · simp [qqFalsum, qqExs] at h
  · simp [qqAnd, qqExs] at h
  · simp [qqOr, qqExs] at h
  · simp [qqAll, qqExs] at h
  · exact ⟨r₁, hr₁, rfl, by simpa using h⟩

end inversion

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
  obtain ⟨r₁, r₂, hr₁, hr₂, rfl, h₁, h₂⟩ := exists_and_of_subst_eq_and hr.isUFormula he.symm
  have h₃ : IsSemiformula L n r₁ ∧ IsSemiformula L n r₂ := by simpa using hr
  exact ⟨r₁, hsub _ hrX r₁ (by simp [subformulas_and hr₁ hr₂, mem_subformulas_self hr₁]), n, w,
    h₃.1, hw, h₁.symm⟩

/-- The right conjunct of an instance of a set closed under subformulas is an instance. -/
lemma of_and_right (hsub : ∀ r ∈ X, ∀ q ∈ subformulas L r, q ∈ X) {p q : V}
    (h : Instance L X (p ^⋏ q)) : Instance L X q := by
  obtain ⟨r, hrX, n, w, hr, hw, he⟩ := h
  obtain ⟨r₁, r₂, hr₁, hr₂, rfl, h₁, h₂⟩ := exists_and_of_subst_eq_and hr.isUFormula he.symm
  have h₃ : IsSemiformula L n r₁ ∧ IsSemiformula L n r₂ := by simpa using hr
  exact ⟨r₂, hsub _ hrX r₂ (by simp [subformulas_and hr₁ hr₂, mem_subformulas_self hr₂]), n, w,
    h₃.2, hw, h₂.symm⟩

/-- The left disjunct of an instance of a set closed under subformulas is an instance. -/
lemma of_or_left (hsub : ∀ r ∈ X, ∀ q ∈ subformulas L r, q ∈ X) {p q : V}
    (h : Instance L X (p ^⋎ q)) : Instance L X p := by
  obtain ⟨r, hrX, n, w, hr, hw, he⟩ := h
  obtain ⟨r₁, r₂, hr₁, hr₂, rfl, h₁, h₂⟩ := exists_or_of_subst_eq_or hr.isUFormula he.symm
  have h₃ : IsSemiformula L n r₁ ∧ IsSemiformula L n r₂ := by simpa using hr
  exact ⟨r₁, hsub _ hrX r₁ (by simp [subformulas_or hr₁ hr₂, mem_subformulas_self hr₁]), n, w,
    h₃.1, hw, h₁.symm⟩

/-- The right disjunct of an instance of a set closed under subformulas is an instance. -/
lemma of_or_right (hsub : ∀ r ∈ X, ∀ q ∈ subformulas L r, q ∈ X) {p q : V}
    (h : Instance L X (p ^⋎ q)) : Instance L X q := by
  obtain ⟨r, hrX, n, w, hr, hw, he⟩ := h
  obtain ⟨r₁, r₂, hr₁, hr₂, rfl, h₁, h₂⟩ := exists_or_of_subst_eq_or hr.isUFormula he.symm
  have h₃ : IsSemiformula L n r₁ ∧ IsSemiformula L n r₂ := by simpa using hr
  exact ⟨r₂, hsub _ hrX r₂ (by simp [subformulas_or hr₁ hr₂, mem_subformulas_self hr₂]), n, w,
    h₃.2, hw, h₂.symm⟩

/-- The free instance of the body of a universal instance of a set closed under subformulas and
without free variables is an instance. -/
lemma free_of_all (hsub : ∀ r ∈ X, ∀ q ∈ subformulas L r, q ∈ X)
    (hshift : ∀ r ∈ X, Bootstrapping.shift L r = r) {p : V} (h : Instance L X (^∀ p)) :
    Instance L X (free L p) := by
  obtain ⟨r, hrX, n, w, hr, hw, he⟩ := h
  obtain ⟨r₁, hr₁, rfl, h₁⟩ := exists_all_of_subst_eq_all hr.isUFormula he.symm
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
  obtain ⟨r₁, hr₁, rfl, h₁⟩ := exists_exs_of_subst_eq_exs hr.isUFormula he.symm
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

/-- The subformulas of a formula code without free variables have no free variables. -/
lemma shift_eq_self_of_mem_subformulas {p q : V} (hp : IsUFormula L p) (hps : shift L p = p)
    (hq : q ∈ subformulas L p) : shift L q = q := by
  have H : ∀ p : V, IsUFormula L p → shift L p = p → ∀ q ∈ subformulas L p, shift L q = q := by
    apply IsUFormula.ISigma1.pi1_succ_induction
      (P := fun p ↦ shift L p = p → ∀ q ∈ subformulas L p, shift L q = q) (by definability)
    case hrel =>
      intro k R v hR hv hps q hq
      simp only [subformulas_rel hR hv, mem_bitInsert_iff, not_mem_empty, or_false] at hq
      rwa [hq]
    case hnrel =>
      intro k R v hR hv hps q hq
      simp only [subformulas_nrel hR hv, mem_bitInsert_iff, not_mem_empty, or_false] at hq
      rwa [hq]
    case hverum =>
      intro _ q hq
      simp only [subformulas_verum, mem_bitInsert_iff, not_mem_empty, or_false] at hq
      simp [hq]
    case hfalsum =>
      intro _ q hq
      simp only [subformulas_falsum, mem_bitInsert_iff, not_mem_empty, or_false] at hq
      simp [hq]
    case hand =>
      intro p₁ p₂ hp₁ hp₂ ih₁ ih₂ hps q hq
      obtain ⟨h₁, h₂⟩ : shift L p₁ = p₁ ∧ shift L p₂ = p₂ := by
        simpa [shift_and hp₁ hp₂] using hps
      simp only [subformulas_and hp₁ hp₂, mem_bitInsert_iff, mem_cup_iff] at hq
      rcases hq with rfl | hq | hq
      · exact hps
      · exact ih₁ h₁ q hq
      · exact ih₂ h₂ q hq
    case hor =>
      intro p₁ p₂ hp₁ hp₂ ih₁ ih₂ hps q hq
      obtain ⟨h₁, h₂⟩ : shift L p₁ = p₁ ∧ shift L p₂ = p₂ := by
        simpa [shift_or hp₁ hp₂] using hps
      simp only [subformulas_or hp₁ hp₂, mem_bitInsert_iff, mem_cup_iff] at hq
      rcases hq with rfl | hq | hq
      · exact hps
      · exact ih₁ h₁ q hq
      · exact ih₂ h₂ q hq
    case hall =>
      intro p₁ hp₁ ih₁ hps q hq
      simp only [subformulas_all hp₁, mem_bitInsert_iff] at hq
      rcases hq with rfl | hq
      · exact hps
      · exact ih₁ (by simpa [shift_all hp₁] using hps) q hq
    case hexs =>
      intro p₁ hp₁ ih₁ hps q hq
      simp only [subformulas_exs hp₁, mem_bitInsert_iff] at hq
      rcases hq with rfl | hq
      · exact hps
      · exact ih₁ (by simpa [shift_exs hp₁] using hps) q hq
  exact H p hp hps q hq

/-- The members of a coded formula set fixed by the shift have no free variables. -/
lemma shift_eq_self_of_setShift_eq_self {s p : V} (hs : IsFormulaSet L s)
    (hss : setShift L s = s) (hp : p ∈ s) : shift L p = p := by
  have H : ∀ k : V, ∀ p ∈ s, s ≤ p + k → shift L p = p := by
    apply ISigma1.pi1_succ_induction (P := fun k ↦ ∀ p ∈ s, s ≤ p + k → shift L p = p)
      (by definability)
    · intro p hp hsp
      exact absurd (lt_of_mem hp) (not_lt.mpr (by simpa using hsp))
    · intro k ih p hp hsp
      by_contra hne
      have hq : shift L p ∈ s := hss ▸ shift_mem_setShift hp
      have hlt : p < shift L p := lt_of_le_of_ne (le_shift (hs p hp)) (Ne.symm hne)
      have h₂ : p + 1 + k ≤ shift L p + k := add_le_add_left (lt_iff_succ_le.mp hlt) k
      have h₁ : s ≤ shift L p + k := le_trans hsp (by rwa [add_assoc, add_comm 1 k] at h₂)
      exact hne <| shift_inj (hs _ hq).isUFormula (hs p hp).isUFormula <| ih _ hq h₁
  exact H s p hp (by simp)

/-- The subformulas of the members of a coded set form a set closed under subformulas. -/
lemma mem_subformulasSet_of_mem_subformulas {s r q : V} (hr : r ∈ subformulasSet L s)
    (hq : q ∈ subformulas L r) : q ∈ subformulasSet L s := by
  obtain ⟨p, hp, hrp⟩ := mem_subformulasSet_iff.mp hr
  by_cases hpU : IsUFormula L p
  · exact mem_subformulasSet_iff.mpr ⟨p, hp, subformulas_subset_of_mem hpU hrp hq⟩
  · simp [subformulas_not_uformula hpU] at hrp

/-- The subformulas of the members of a coded set of formula codes without free variables have no
free variables. -/
lemma shift_eq_self_of_mem_subformulasSet {s r : V} (hs : ∀ p ∈ s, shift L p = p)
    (hr : r ∈ subformulasSet L s) : shift L r = r := by
  obtain ⟨p, hp, hrp⟩ := mem_subformulasSet_iff.mp hr
  by_cases hpU : IsUFormula L p
  · exact shift_eq_self_of_mem_subformulas hpU (hs p hp) hrp
  · simp [subformulas_not_uformula hpU] at hrp

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

end FFL.FirstOrder.Arithmetic.Bootstrapping
