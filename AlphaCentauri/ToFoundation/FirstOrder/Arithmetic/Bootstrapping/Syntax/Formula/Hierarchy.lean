module

public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Functions
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Hierarchy

/-!
# Gaps in Foundation's `Syntax/Formula/Hierarchy`

Substitution preserves $\Delta_0$ formulas and prenex formulas of a class, and a substitution
instance of a formula is $\Delta_0$, or prenex of a class, only if the formula itself is. Prenex
decompositions `qqToPrenex Γ s θ` commute with negation, substitution and shift.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open Arithmetic (qqNLT)

/-! ## Substitution -/

section subst

lemma IsUFormula.rel_cases {k r v : V} (h : IsUFormula ℒₒᵣ (^rel k r v)) :
    (∃ t u, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ ^rel k r v = t ^= u) ∨
    (∃ t u, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ ^rel k r v = t ^< u) := by
  obtain ⟨hr, hv⟩ := IsUFormula.rel.mp h
  rcases Arithmetic.isRel_iff_LOR.mp hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    obtain ⟨a, b, ha, hb, rfl⟩ := IsUTermVec.two_iff.mp hv
  · exact Or.inl ⟨a, b, ha, hb, rfl⟩
  · exact Or.inr ⟨a, b, ha, hb, rfl⟩

lemma IsUFormula.nrel_cases {k r v : V} (h : IsUFormula ℒₒᵣ (^nrel k r v)) :
    (∃ t u, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ ^nrel k r v = t ^≠ u) ∨
    (∃ t u, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ ^nrel k r v = qqNLT t u) := by
  obtain ⟨hr, hv⟩ := IsUFormula.nrel.mp h
  rcases Arithmetic.isRel_iff_LOR.mp hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    obtain ⟨a, b, ha, hb, rfl⟩ := IsUTermVec.two_iff.mp hv
  · exact Or.inl ⟨a, b, ha, hb, rfl⟩
  · exact Or.inr ⟨a, b, ha, hb, rfl⟩

lemma IsSemiterm.of_termBShift {n t : V} (ht : IsUTerm ℒₒᵣ t)
    (h : IsSemiterm ℒₒᵣ (n + 1) (Bootstrapping.termBShift ℒₒᵣ t)) : IsSemiterm ℒₒᵣ n t :=
  IsSemiterm.def.mpr ⟨ht, (termBV_termBShift_le ht n).mp (IsSemiterm.def.mp h).2⟩

lemma IsSemiformula.of_qqBall {n t p : V} (ht : IsUTerm ℒₒᵣ t)
    (h : IsSemiformula ℒₒᵣ n (qqBall (termBShift ℒₒᵣ t) p)) :
    IsSemiterm ℒₒᵣ n t ∧ IsSemiformula ℒₒᵣ (n + 1) p := by
  have h' : IsSemiterm ℒₒᵣ (n + 1) (termBShift ℒₒᵣ t) ∧ IsSemiformula ℒₒᵣ (n + 1) p := by
    simpa [qqBall, Arithmetic.qqNLT] using h
  exact ⟨h'.1.of_termBShift ht, h'.2⟩

lemma IsSemiformula.of_qqBex {n t p : V} (ht : IsUTerm ℒₒᵣ t)
    (h : IsSemiformula ℒₒᵣ n (qqBex (termBShift ℒₒᵣ t) p)) :
    IsSemiterm ℒₒᵣ n t ∧ IsSemiformula ℒₒᵣ (n + 1) p := by
  have h' : IsSemiterm ℒₒᵣ (n + 1) (termBShift ℒₒᵣ t) ∧ IsSemiformula ℒₒᵣ (n + 1) p := by
    simpa [qqBex, Arithmetic.qqLT] using h
  exact ⟨h'.1.of_termBShift ht, h'.2⟩

section

variable {w t u : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u)
include ht hu

lemma subst_qqEQ : subst ℒₒᵣ w (t ^= u) = termSubst ℒₒᵣ w t ^= termSubst ℒₒᵣ w u := by
  simp [Arithmetic.qqEQ, ht, hu]

lemma subst_qqNEQ : subst ℒₒᵣ w (t ^≠ u) = termSubst ℒₒᵣ w t ^≠ termSubst ℒₒᵣ w u := by
  simp [Arithmetic.qqNEQ, ht, hu]

lemma subst_qqLT : subst ℒₒᵣ w (t ^< u) = termSubst ℒₒᵣ w t ^< termSubst ℒₒᵣ w u := by
  simp [Arithmetic.qqLT, ht, hu]

lemma subst_qqNLT :
    subst ℒₒᵣ w (qqNLT t u) = qqNLT (termSubst ℒₒᵣ w t) (termSubst ℒₒᵣ w u) := by
  simp [Arithmetic.qqNLT, ht, hu]

end

section

variable {n m w t p : V} (hw : IsSemitermVec ℒₒᵣ n m w) (ht : IsSemiterm ℒₒᵣ n t)
  (hp : IsUFormula ℒₒᵣ p)
include hw ht hp

lemma subst_qqBall :
    subst ℒₒᵣ w (qqBall (termBShift ℒₒᵣ t) p) =
      qqBall (termBShift ℒₒᵣ (termSubst ℒₒᵣ w t)) (subst ℒₒᵣ (qVec ℒₒᵣ w) p) := by
  have hbt : IsUTerm ℒₒᵣ (termBShift ℒₒᵣ t) := ht.isUTerm.termBShift
  have hlt : IsUFormula ℒₒᵣ (qqNLT (^#0 : V) (termBShift ℒₒᵣ t)) := by simp [Arithmetic.qqNLT, hbt]
  rw [qqBall, substs_all (by simp [hlt, hp]), substs_or hlt hp, subst_qqNLT (by simp) hbt,
    substs_qVec_bShift ht hw]
  simp [qVec, qqBall]

lemma subst_qqBex :
    subst ℒₒᵣ w (qqBex (termBShift ℒₒᵣ t) p) =
      qqBex (termBShift ℒₒᵣ (termSubst ℒₒᵣ w t)) (subst ℒₒᵣ (qVec ℒₒᵣ w) p) := by
  have hbt : IsUTerm ℒₒᵣ (termBShift ℒₒᵣ t) := ht.isUTerm.termBShift
  have hlt : IsUFormula ℒₒᵣ ((^#0 : V) ^< termBShift ℒₒᵣ t) := by simp [Arithmetic.qqLT, hbt]
  rw [qqBex, substs_ex (by simp [hlt, hp]), substs_and hlt hp, subst_qqLT (by simp) hbt,
    substs_qVec_bShift ht hw]
  simp [qVec, qqBex]

end

lemma IsBounded.subst {n m w p : V} (hw : IsSemitermVec ℒₒᵣ n m w)
    (hp : IsSemiformula ℒₒᵣ n p) (h : IsBounded p) : IsBounded (subst ℒₒᵣ w p) := by
  suffices ∀ p : V, IsBounded p → ∀ n m w, IsSemitermVec ℒₒᵣ n m w → IsSemiformula ℒₒᵣ n p →
      IsBounded (Bootstrapping.subst ℒₒᵣ w p) from this p h n m w hw hp
  apply IsBounded.induction 𝚷 (P := fun p ↦ ∀ n m w, IsSemitermVec ℒₒᵣ n m w →
    IsSemiformula ℒₒᵣ n p → IsBounded (Bootstrapping.subst ℒₒᵣ w p)) (by definability)
  · intro n m w _ _
    simp
  · intro n m w _ _
    simp
  · intro k r v n m w _ hp
    obtain ⟨hr, hv⟩ := IsUFormula.rel.mp hp.isUFormula
    simp [hr, hv]
  · intro k r v n m w _ hp
    obtain ⟨hr, hv⟩ := IsUFormula.nrel.mp hp.isUFormula
    simp [hr, hv]
  · intro p q _ _ ihp ihq n m w hw hpq
    obtain ⟨hp, hq⟩ := IsSemiformula.and.mp hpq
    rw [substs_and hp.isUFormula hq.isUFormula]
    exact IsBounded.and_iff.mpr ⟨ihp n m w hw hp, ihq n m w hw hq⟩
  · intro p q _ _ ihp ihq n m w hw hpq
    obtain ⟨hp, hq⟩ := IsSemiformula.or.mp hpq
    rw [substs_or hp.isUFormula hq.isUFormula]
    exact IsBounded.or_iff.mpr ⟨ihp n m w hw hp, ihq n m w hw hq⟩
  · intro t q ht _ ih n m w hw hpq
    obtain ⟨ht', hq⟩ := hpq.of_qqBall ht
    rw [subst_qqBall hw ht' hq.isUFormula]
    exact IsBounded.ball (hw.termSubst ht').isUTerm (ih (n + 1) (m + 1) _ hw.qVec hq)
  · intro t q ht _ ih n m w hw hpq
    obtain ⟨ht', hq⟩ := hpq.of_qqBex ht
    rw [subst_qqBex hw ht' hq.isUFormula]
    exact IsBounded.bex (hw.termSubst ht').isUTerm (ih (n + 1) (m + 1) _ hw.qVec hq)

end subst

/-! ## Formulas of complexity zero -/

section complexity

variable {p : V}

lemma IsUFormula.isBounded_of_formulaComplexity_eq_zero (hp : IsUFormula ℒₒᵣ p)
    (h : formulaComplexity ℒₒᵣ p = 0) : IsBounded p := by
  rcases hp.case with (⟨k, R, v, -, -, rfl⟩ | ⟨k, R, v, -, -, rfl⟩ | rfl | rfl |
    ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, hp₁, rfl⟩ | ⟨p₁, hp₁, rfl⟩) <;>
    simp_all

lemma IsUFormula.cases_of_formulaComplexity_ne_zero (hp : IsUFormula ℒₒᵣ p)
    (h : formulaComplexity ℒₒᵣ p ≠ 0) :
    (∃ q r, IsUFormula ℒₒᵣ q ∧ IsUFormula ℒₒᵣ r ∧ p = q ^⋏ r) ∨
    (∃ q r, IsUFormula ℒₒᵣ q ∧ IsUFormula ℒₒᵣ r ∧ p = q ^⋎ r) ∨
    (∃ q, IsUFormula ℒₒᵣ q ∧ p = ^∀ q) ∨ (∃ q, IsUFormula ℒₒᵣ q ∧ p = ^∃ q) := by
  rcases hp.case with (⟨k, R, v, -, -, rfl⟩ | ⟨k, R, v, -, -, rfl⟩ | rfl | rfl |
    ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, hp₁, rfl⟩ | ⟨p₁, hp₁, rfl⟩) <;>
    simp_all

end complexity

/-! ## Prenex decompositions -/

section qqToPrenex

variable {Γ Γ' : Polarity} {s s' : ℕ} {θ θ' : V}

@[simp] lemma isUFormula_qqToPrenex :
    IsUFormula ℒₒᵣ (qqToPrenex Γ s θ) ↔ IsUFormula ℒₒᵣ θ := by
  induction s generalizing Γ <;> simp [*]

@[simp] lemma isSemiformula_qqToPrenex {n : V} :
    IsSemiformula ℒₒᵣ n (qqToPrenex Γ s θ) ↔ IsSemiformula ℒₒᵣ (n + s) θ := by
  induction s generalizing Γ n with
  | zero => simp
  | succ s ih => cases Γ <;> simp [ih, add_assoc, add_comm (1 : V)]

lemma neg_qqToPrenex (hθ : IsUFormula ℒₒᵣ θ) :
    neg ℒₒᵣ (qqToPrenex Γ s θ) = qqToPrenex Γ.alt s (neg ℒₒᵣ θ) := by
  induction s generalizing Γ with
  | zero => simp
  | succ s ih => simp [neg_qqQuant (isUFormula_qqToPrenex.mpr hθ), ih]

lemma subst_qqToPrenex {w : V} (hθ : IsUFormula ℒₒᵣ θ) :
    subst ℒₒᵣ w (qqToPrenex Γ s θ) = qqToPrenex Γ s (subst ℒₒᵣ ((qVec ℒₒᵣ)^[s] w) θ) := by
  induction s generalizing Γ w with
  | zero => simp
  | succ s ih =>
    cases Γ <;> simp [isUFormula_qqToPrenex.mpr hθ, ih, Function.iterate_succ_apply]

lemma IsSemitermVec.iterate_qVec {n m w : V} (hw : IsSemitermVec ℒₒᵣ n m w) (s : ℕ) :
    IsSemitermVec ℒₒᵣ (n + s) (m + s) ((Bootstrapping.qVec ℒₒᵣ)^[s] w) := by
  induction s generalizing n m w with
  | zero => simpa using hw
  | succ s ih =>
    simpa [Function.iterate_succ_apply, add_assoc, add_comm (1 : V)] using ih hw.qVec

lemma IsPrenexHierarchy.subst {n m w p : V} (hw : IsSemitermVec ℒₒᵣ n m w)
    (hp : IsSemiformula ℒₒᵣ n p) (h : IsPrenexHierarchy Γ s p) :
    IsPrenexHierarchy Γ s (subst ℒₒᵣ w p) := by
  obtain ⟨θ, rfl, hθ⟩ := isPrenexHierarchy_iff_exists_qqToPrenex.mp h
  have hθs : IsSemiformula ℒₒᵣ (n + s) θ := isSemiformula_qqToPrenex.mp hp
  exact isPrenexHierarchy_iff_exists_qqToPrenex.mpr
    ⟨_, subst_qqToPrenex hθs.isUFormula, hθ.subst (hw.iterate_qVec s) hθs⟩

lemma shift_qqToPrenex (hθ : IsUFormula ℒₒᵣ θ) :
    shift ℒₒᵣ (qqToPrenex Γ s θ) = qqToPrenex Γ s (shift ℒₒᵣ θ) := by
  induction s generalizing Γ with
  | zero => simp
  | succ s ih => cases Γ <;> simp [isUFormula_qqToPrenex.mpr hθ, ih]

lemma IsPrenexHierarchy.shift {p : V} (hp : IsUFormula ℒₒᵣ p) (h : IsPrenexHierarchy Γ s p) :
    IsPrenexHierarchy Γ s (shift ℒₒᵣ p) := by
  obtain ⟨θ, rfl, hθ⟩ := isPrenexHierarchy_iff_exists_qqToPrenex.mp h
  have hθ' : IsUFormula ℒₒᵣ θ := isUFormula_qqToPrenex.mp hp
  exact isPrenexHierarchy_iff_exists_qqToPrenex.mpr ⟨_, shift_qqToPrenex hθ', hθ.shift hθ'⟩

/-- A $\Delta_0$ formula is of the form `qqToPrenex Γ s θ` only for `s ≤ 1`. -/
lemma le_one_of_isBounded_qqToPrenex (h : IsBounded (qqToPrenex Γ s θ)) : s ≤ 1 := by
  match s, h with
  | 0, _ => simp
  | 1, _ => simp
  | s + 2, h =>
    exfalso
    cases Γ
    · obtain ⟨_, _, -, -, he⟩ := IsBounded.of_ex h
      simp [qqAll, qqAnd] at he
    · obtain ⟨_, _, -, -, he⟩ := IsBounded.of_all h
      simp [qqExs, qqOr] at he

lemma qqToPrenex_eq_and {p q : V} (h : qqToPrenex Γ s θ = p ^⋏ q) : s = 0 := by
  rcases s with _ | s
  · rfl
  · cases Γ <;> simp [qqExs, qqAll, qqAnd] at h

lemma qqToPrenex_eq_or {p q : V} (h : qqToPrenex Γ s θ = p ^⋎ q) : s = 0 := by
  rcases s with _ | s
  · rfl
  · cases Γ <;> simp [qqExs, qqAll, qqOr] at h

end qqToPrenex

/-! ## Recovering a formula from a substitution instance -/

/-! ## The $\Delta_0$ and prenex classes -/

private lemma eq_bvar_zero_and_exists_termBShift {n m w a c u : V} (hw : IsSemitermVec ℒₒᵣ n m w)
    (ha : IsSemiterm ℒₒᵣ (n + 1) a) (hc : IsSemiterm ℒₒᵣ (n + 1) c) (hu : IsUTerm ℒₒᵣ u)
    (h : termSubstVec ℒₒᵣ 2 (qVec ℒₒᵣ w) (?[a, c] : V) = ?[^#0, termBShift ℒₒᵣ u]) :
    a = ^#0 ∧ ∃ t, IsUTerm ℒₒᵣ t ∧ c = termBShift ℒₒᵣ t := by
  simp only [termSubstVec_cons₂ ha.isUTerm hc.isUTerm, adjoin_inj] at h
  exact ⟨eq_bvar_zero_of_termSubst_qVec_eq hw ha h.1,
    exists_eq_termBShift_of_termSubst_qVec_eq hc hu h.2.1⟩

lemma IsBounded.of_subst {n m w p : V} (hw : IsSemitermVec ℒₒᵣ n m w)
    (hp : IsSemiformula ℒₒᵣ n p) (h : IsBounded (Bootstrapping.subst ℒₒᵣ w p)) : IsBounded p := by
  apply IsSemiformula.pi1_structural_induction (P := fun n p ↦ ∀ m w, IsSemitermVec ℒₒᵣ n m w →
    IsBounded (Bootstrapping.subst ℒₒᵣ w p) → IsBounded p) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp m w hw h
  · definability
  · simp
  · simp
  · simp
  · simp
  · intro n p q hp hq ihp ihq m w hw h
    rw [substs_and hp.isUFormula hq.isUFormula, IsBounded.and_iff] at h
    exact IsBounded.and_iff.mpr ⟨ihp m w hw h.1, ihq m w hw h.2⟩
  · intro n p q hp hq ihp ihq m w hw h
    rw [substs_or hp.isUFormula hq.isUFormula, IsBounded.or_iff] at h
    exact IsBounded.or_iff.mpr ⟨ihp m w hw h.1, ihq m w hw h.2⟩
  · intro n p hp ih m w hw h
    rw [substs_all hp.isUFormula] at h
    obtain ⟨_, q, ⟨u, hu, rfl⟩, hq, he⟩ := IsBounded.of_all h
    have hb := ih (m + 1) (qVec ℒₒᵣ w) hw.qVec (by simp [he, hq, Arithmetic.qqNLT])
    obtain ⟨p₁, p₂, rfl, h₁, -⟩ := exists_eq_or_of_subst_eq hp.isUFormula he
    obtain ⟨hp₁, -⟩ := IsSemiformula.or.mp hp
    obtain ⟨v, hv, rfl, hvv⟩ := exists_eq_nrel_of_subst_eq hp₁.isUFormula h₁
    obtain ⟨a, c, rfl⟩ := eq_doubleton_of_len_eq_two.mp hv.lh.symm
    obtain ⟨ha, hc⟩ : IsSemiterm ℒₒᵣ (n + 1) a ∧ IsSemiterm ℒₒᵣ (n + 1) c := by
      simpa using hp₁
    obtain ⟨rfl, t, ht, rfl⟩ := eq_bvar_zero_and_exists_termBShift hw ha hc hu hvv
    exact IsBounded.ball ht (IsBounded.or_iff.mp hb).2
  · intro n p hp ih m w hw h
    rw [substs_ex hp.isUFormula] at h
    obtain ⟨_, q, ⟨u, hu, rfl⟩, hq, he⟩ := IsBounded.of_ex h
    have hb := ih (m + 1) (qVec ℒₒᵣ w) hw.qVec (by simp [he, hq, Arithmetic.qqLT])
    obtain ⟨p₁, p₂, rfl, h₁, -⟩ := exists_eq_and_of_subst_eq hp.isUFormula he
    obtain ⟨hp₁, -⟩ := IsSemiformula.and.mp hp
    obtain ⟨v, hv, rfl, hvv⟩ := exists_eq_rel_of_subst_eq hp₁.isUFormula h₁
    obtain ⟨a, c, rfl⟩ := eq_doubleton_of_len_eq_two.mp hv.lh.symm
    obtain ⟨ha, hc⟩ : IsSemiterm ℒₒᵣ (n + 1) a ∧ IsSemiterm ℒₒᵣ (n + 1) c := by
      simpa using hp₁
    obtain ⟨rfl, t, ht, rfl⟩ := eq_bvar_zero_and_exists_termBShift hw ha hc hu hvv
    exact IsBounded.bex ht (IsBounded.and_iff.mp hb).2

lemma IsPrenexHierarchy.of_subst {Γ : Polarity} {s : ℕ} {n m w p : V}
    (hw : IsSemitermVec ℒₒᵣ n m w) (hp : IsSemiformula ℒₒᵣ n p)
    (h : IsPrenexHierarchy Γ s (Bootstrapping.subst ℒₒᵣ w p)) : IsPrenexHierarchy Γ s p := by
  induction s generalizing Γ n m w p with
  | zero => exact IsBounded.of_subst hw hp h
  | succ s ih =>
    obtain ⟨q, hq, hqs⟩ := h
    cases Γ
    · obtain ⟨p₁, rfl, hp₁⟩ := exists_eq_exs_of_subst_eq hp.isUFormula hq
      exact ⟨p₁, rfl, ih hw.qVec (IsSemiformula.exs.mp hp) (hp₁ ▸ hqs)⟩
    · obtain ⟨p₁, rfl, hp₁⟩ := exists_eq_all_of_subst_eq hp.isUFormula hq
      exact ⟨p₁, rfl, ih hw.qVec (IsSemiformula.all.mp hp) (hp₁ ▸ hqs)⟩

end FFL.FirstOrder.Arithmetic.Bootstrapping
