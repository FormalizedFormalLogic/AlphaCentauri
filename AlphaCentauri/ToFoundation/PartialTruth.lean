module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.PartialTruth.General

/-!
# Substitution and negation for the partial satisfaction predicates

`BoundedSatisfied` and `PrenexSatisfied` read a formula with closed-off bound
variables by putting the values of the substituted terms into the assignment, swap under negation,
and give the same value to every decomposition `qqToPrenex Γ s θ` of the same code.

## References

- [HP98, 1.64(5), Theorem I.1.75]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open Arithmetic (numeral numeral_add_two qqNLT)

/-! ## Values of substituted terms -/

section termVal

lemma termVal_not_uterm {e t : V} (h : ¬IsUTerm ℒₒᵣ t) : termVal e t = 0 :=
  TermVal.construction.result_prop_not ℒₒᵣ ![e] h

lemma termVal_termSubst {e n m w t : V} (hw : IsSemitermVec ℒₒᵣ n m w)
    (ht : IsSemiterm ℒₒᵣ n t) :
    termVal e (termSubst ℒₒᵣ w t) = termVal (termValVec e n w) t := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz
    rw [termSubst_bvar, termVal_bvar, nth_termValVec hw.isUTerm hz]
  · intro x
    simp
  · intro k f v hf hv ih
    rw [termSubst_func hf hv.isUTerm]
    apply termVal_func_congr hf (hw.termSubstVec hv).isUTerm hv.isUTerm
    intro i hi
    rw [nth_termSubstVec hv.isUTerm hi, ih i hi]

lemma termValVec_qVec {n m w e x : V} (hw : IsSemitermVec ℒₒᵣ n m w) :
    termValVec (x ∷ e) (n + 1) (qVec ℒₒᵣ w) = x ∷ termValVec e n w := by
  have hq : IsUTermVec ℒₒᵣ (n + 1) (qVec ℒₒᵣ w) := hw.qVec.isUTerm
  apply nth_ext' (n + 1) (by simp [hq]) (by simp [len_termValVec hw.isUTerm])
  intro i hi
  rw [nth_termValVec hq hi]
  rcases zero_or_succ i with rfl | ⟨j, rfl⟩
  · simp [qVec]
  · have hj : j < n := by simpa using hi
    have hnth : (qVec ℒₒᵣ w).[j + 1] = termBShift ℒₒᵣ w.[j] := by
      rw [qVec, hw.lh]
      simp [nth_termBShiftVec hw.isUTerm hj]
    rw [hnth, termVal_termBShift (hw.isUTerm.nth hj) x e]
    simp [nth_termValVec hw.isUTerm hj]

@[simp] lemma termValVec_cons₁ {e t : V} (ht : IsUTerm ℒₒᵣ t) :
    termValVec e 1 (?[t] : V) = ?[termVal e t] := by
  simpa [termValVec, termVal] using
    TermVal.construction.resultVec_cons ℒₒᵣ ![e] (IsUTermVec.empty (L := ℒₒᵣ)) ht

lemma termValVec_cons {e k t v : V} (ht : IsUTerm ℒₒᵣ t) (hv : IsUTermVec ℒₒᵣ k v) :
    termValVec e (k + 1) (t ∷ v) = termVal e t ∷ termValVec e k v := by
  simpa [termValVec, termVal] using TermVal.construction.resultVec_cons ℒₒᵣ ![e] hv ht

@[simp] lemma termVal_numeral (e x : V) : termVal e (numeral x) = x := by
  induction x using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ x ih =>
    rcases zero_or_succ x with rfl | ⟨x, rfl⟩
    · simp
    · rw [numeral_add_two, termVal_add (Arithmetic.numeral_uterm _)
        (Arithmetic.one_semiterm (n := 0)).isUTerm, ih, termVal_one]

end termVal

/-! ## Substitution for bound variables -/

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

/-! ## $\Delta_0$ satisfaction -/

namespace BoundedSatisfied

lemma neg_iff {p e : V} (hp : IsBounded p) (hp' : IsUFormula ℒₒᵣ p) :
    BoundedSatisfied e (neg ℒₒᵣ p) ↔ ¬BoundedSatisfied e p := by
  suffices ∀ p : V, IsBounded p → IsUFormula ℒₒᵣ p →
      ∀ e, (BoundedSatisfied e (neg ℒₒᵣ p) ↔ ¬BoundedSatisfied e p) from this p hp hp' e
  apply IsBounded.induction 𝚷 (P := fun p ↦ IsUFormula ℒₒᵣ p →
    ∀ e, (BoundedSatisfied e (neg ℒₒᵣ p) ↔ ¬BoundedSatisfied e p)) (by definability)
  · intro _ e
    simp
  · intro _ e
    simp
  · intro k r v h e
    rcases h.rel_cases with ⟨t, u, ht, hu, heq⟩ | ⟨t, u, ht, hu, heq⟩
    · rw [heq, Arithmetic.neg_eq ht hu, neq_iff ht hu, eq_iff ht hu]
    · rw [heq, Arithmetic.neg_lt ht hu, nlt_iff ht hu, lt_iff ht hu]
  · intro k r v h e
    rcases h.nrel_cases with ⟨t, u, ht, hu, heq⟩ | ⟨t, u, ht, hu, heq⟩
    · rw [heq, Arithmetic.neg_neq ht hu, eq_iff ht hu, neq_iff ht hu, not_not]
    · rw [heq, Arithmetic.neg_nlt ht hu, lt_iff ht hu, nlt_iff ht hu, not_not]
  · intro p q hdp hdq ihp ihq h e
    obtain ⟨hfp, hfq⟩ := IsUFormula.and.mp h
    rw [neg_and hfp hfq, or_iff (hdp.neg hfp) hfp.neg (hdq.neg hfq) hfq.neg, ihp hfp e, ihq hfq e,
      and_iff]
    tauto
  · intro p q hdp hdq ihp ihq h e
    obtain ⟨hfp, hfq⟩ := IsUFormula.or.mp h
    rw [neg_or hfp hfq, and_iff, ihp hfp e, ihq hfq e, or_iff hdp hfp hdq hfq]
    tauto
  · intro t q ht hdq ih h e
    have hfq : IsUFormula ℒₒᵣ q := by simp_all [qqBall]
    rw [neg_qqBall ht.termBShift hfq, bex_iff ht, ball_iff ht hdq hfq]
    simp only [ih hfq, not_forall, exists_prop]
  · intro t q ht hdq ih h e
    have hfq : IsUFormula ℒₒᵣ q := by simp_all [qqBex]
    rw [neg_qqBex ht.termBShift hfq, ball_iff ht (hdq.neg hfq) hfq.neg, bex_iff ht]
    simp only [ih hfq, not_exists, not_and]

private lemma subst_rel {n m w k r v e : V} (hw : IsSemitermVec ℒₒᵣ n m w)
    (hp : IsSemiformula ℒₒᵣ n (^rel k r v)) :
    BoundedSatisfied e (Bootstrapping.subst ℒₒᵣ w (^rel k r v)) ↔
      BoundedSatisfied (termValVec e n w) (^rel k r v) := by
  rcases hp.isUFormula.rel_cases with ⟨t, u, ht, hu, heq⟩ | ⟨t, u, ht, hu, heq⟩ <;>
    rw [heq] at hp ⊢
  · obtain ⟨hts, hus⟩ : IsSemiterm ℒₒᵣ n t ∧ IsSemiterm ℒₒᵣ n u := by
      simpa [Arithmetic.qqEQ] using hp
    rw [subst_qqEQ ht hu, eq_iff (hw.termSubst hts).isUTerm (hw.termSubst hus).isUTerm,
      eq_iff ht hu, termVal_termSubst hw hts, termVal_termSubst hw hus]
  · obtain ⟨hts, hus⟩ : IsSemiterm ℒₒᵣ n t ∧ IsSemiterm ℒₒᵣ n u := by
      simpa [Arithmetic.qqLT] using hp
    rw [subst_qqLT ht hu, lt_iff (hw.termSubst hts).isUTerm (hw.termSubst hus).isUTerm,
      lt_iff ht hu, termVal_termSubst hw hts, termVal_termSubst hw hus]

private lemma subst_nrel {n m w k r v e : V} (hw : IsSemitermVec ℒₒᵣ n m w)
    (hp : IsSemiformula ℒₒᵣ n (^nrel k r v)) :
    BoundedSatisfied e (Bootstrapping.subst ℒₒᵣ w (^nrel k r v)) ↔
      BoundedSatisfied (termValVec e n w) (^nrel k r v) := by
  rcases hp.isUFormula.nrel_cases with ⟨t, u, ht, hu, heq⟩ | ⟨t, u, ht, hu, heq⟩ <;>
    rw [heq] at hp ⊢
  · obtain ⟨hts, hus⟩ : IsSemiterm ℒₒᵣ n t ∧ IsSemiterm ℒₒᵣ n u := by
      simpa [Arithmetic.qqNEQ] using hp
    rw [subst_qqNEQ ht hu, neq_iff (hw.termSubst hts).isUTerm (hw.termSubst hus).isUTerm,
      neq_iff ht hu, termVal_termSubst hw hts, termVal_termSubst hw hus]
  · obtain ⟨hts, hus⟩ : IsSemiterm ℒₒᵣ n t ∧ IsSemiterm ℒₒᵣ n u := by
      simpa [qqNLT] using hp
    rw [subst_qqNLT ht hu, nlt_iff (hw.termSubst hts).isUTerm (hw.termSubst hus).isUTerm,
      nlt_iff ht hu, termVal_termSubst hw hts, termVal_termSubst hw hus]

/-- Substituting for the bound variables of `p` and reading the result agrees with reading `p` at
the values of the substituted terms. -/
private def SubstReads (p : V) : Prop :=
  ∀ n m w e, IsSemitermVec ℒₒᵣ n m w → IsSemiformula ℒₒᵣ n p →
    (BoundedSatisfied e (Bootstrapping.subst ℒₒᵣ w p) ↔
      BoundedSatisfied (termValVec e n w) p)

private lemma substReads_and {p q : V} (ihp : SubstReads p) (ihq : SubstReads q) :
    SubstReads (p ^⋏ q) := by
  intro n m w e hw hpq
  obtain ⟨hp, hq⟩ := IsSemiformula.and.mp hpq
  rw [substs_and hp.isUFormula hq.isUFormula, and_iff, and_iff, ihp n m w e hw hp,
    ihq n m w e hw hq]

private lemma substReads_or {p q : V} (hdp : IsBounded p) (hdq : IsBounded q)
    (ihp : SubstReads p) (ihq : SubstReads q) : SubstReads (p ^⋎ q) := by
  intro n m w e hw hpq
  obtain ⟨hp, hq⟩ := IsSemiformula.or.mp hpq
  rw [substs_or hp.isUFormula hq.isUFormula,
    or_iff (hdp.subst hw hp) (hp.subst hw).isUFormula (hdq.subst hw hq) (hq.subst hw).isUFormula,
    or_iff hdp hp.isUFormula hdq hq.isUFormula, ihp n m w e hw hp, ihq n m w e hw hq]

private lemma substReads_ball {t q : V} (ht : IsUTerm ℒₒᵣ t) (hdq : IsBounded q)
    (ih : SubstReads q) : SubstReads (qqBall (termBShift ℒₒᵣ t) q) := by
  intro n m w e hw hpq
  obtain ⟨hts, hq⟩ := hpq.of_qqBall ht
  rw [subst_qqBall hw hts hq.isUFormula,
    ball_iff (hw.termSubst hts).isUTerm (hdq.subst hw.qVec hq) (hq.subst hw.qVec).isUFormula,
    ball_iff ht hdq hq.isUFormula, termVal_termSubst hw hts]
  apply forall₂_congr
  intro x _
  rw [ih (n + 1) (m + 1) (qVec ℒₒᵣ w) (x ∷ e) hw.qVec hq, termValVec_qVec hw]

private lemma substReads_bex {t q : V} (ht : IsUTerm ℒₒᵣ t) (ih : SubstReads q) :
    SubstReads (qqBex (termBShift ℒₒᵣ t) q) := by
  intro n m w e hw hpq
  obtain ⟨hts, hq⟩ := hpq.of_qqBex ht
  rw [subst_qqBex hw hts hq.isUFormula, bex_iff (hw.termSubst hts).isUTerm, bex_iff ht,
    termVal_termSubst hw hts]
  apply exists_congr
  intro x
  apply and_congr_right
  intro _
  rw [ih (n + 1) (m + 1) (qVec ℒₒᵣ w) (x ∷ e) hw.qVec hq, termValVec_qVec hw]

lemma subst {n m w p e : V} (hw : IsSemitermVec ℒₒᵣ n m w)
    (hp : IsSemiformula ℒₒᵣ n p) (hp' : IsBounded p) :
    BoundedSatisfied e (Bootstrapping.subst ℒₒᵣ w p) ↔
      BoundedSatisfied (termValVec e n w) p := by
  suffices SubstReads p from this n m w e hw hp
  unfold SubstReads
  apply IsBounded.induction 𝚷 (by definability) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp'
  · intro n m w e _ _
    simp
  · intro n m w e _ _
    simp
  · intro k r v n m w e hw hp
    exact subst_rel hw hp
  · intro k r v n m w e hw hp
    exact subst_nrel hw hp
  · intro p q _ _ ihp ihq
    exact substReads_and ihp ihq
  · intro p q hdp hdq ihp ihq
    exact substReads_or hdp hdq ihp ihq
  · intro t q ht hdq ih
    exact substReads_ball ht hdq ih
  · intro t q ht hdq ih
    exact substReads_bex ht ih

/-- A $\Delta_0$ formula `qqQuant Γ θ` is satisfied exactly when `θ` is satisfied for all, or
some, values of the quantified variable. -/
lemma qqQuant_iff {Γ : Polarity} {θ e : V} (h : IsBounded (qqQuant Γ θ))
    (hθ : IsUFormula ℒₒᵣ θ) :
    BoundedSatisfied e (qqQuant Γ θ) ↔ PrenexSatisfied Γ 1 e θ := by
  cases Γ
  · obtain ⟨_, q, ⟨t, ht, rfl⟩, hq, rfl⟩ := IsBounded.of_ex h
    have hq' : IsUFormula ℒₒᵣ q := by simp_all [Arithmetic.qqLT]
    change BoundedSatisfied e (qqBex (termBShift ℒₒᵣ t) q) ↔ _
    rw [bex_iff ht]
    simp [ht.termBShift, termVal_termBShift ht]
  · obtain ⟨_, q, ⟨t, ht, rfl⟩, hq, rfl⟩ := IsBounded.of_all h
    have hq' : IsUFormula ℒₒᵣ q := by simp_all [qqNLT]
    change BoundedSatisfied e (qqBall (termBShift ℒₒᵣ t) q) ↔ _
    have hn : IsUFormula ℒₒᵣ (qqNLT (^#0 : V) (termBShift ℒₒᵣ t)) := by simp [qqNLT, ht.termBShift]
    have hb : IsBounded (qqNLT (^#0 : V) (termBShift ℒₒᵣ t)) := by simp [qqNLT]
    rw [ball_iff ht hq hq']
    apply forall_congr'
    intro x
    change _ ↔ BoundedSatisfied (x ∷ e) (qqNLT (^#0 : V) (termBShift ℒₒᵣ t) ^⋎ q)
    rw [or_iff hb hn hq hq', nlt_iff (by simp) ht.termBShift, termVal_termBShift ht]
    simp [or_iff_not_imp_left]

end BoundedSatisfied

/-! ## Prenex satisfaction -/

namespace PrenexSatisfied

variable {Γ Γ' : Polarity} {s s' : ℕ} {θ θ' : V}

lemma neg_iff (hθ : IsBounded θ) (hθ' : IsUFormula ℒₒᵣ θ) {e : V} :
    PrenexSatisfied Γ.alt s e (neg ℒₒᵣ θ) ↔ ¬PrenexSatisfied Γ s e θ := by
  induction s generalizing Γ e with
  | zero => simpa using BoundedSatisfied.neg_iff hθ hθ'
  | succ s ih =>
    have hσ : ∀ e, PrenexSatisfied 𝚷 s e (neg ℒₒᵣ θ) ↔
        ¬PrenexSatisfied 𝚺 s e θ := fun e ↦ ih (Γ := 𝚺)
    have hπ : ∀ e, PrenexSatisfied 𝚺 s e (neg ℒₒᵣ θ) ↔
        ¬PrenexSatisfied 𝚷 s e θ := fun e ↦ ih (Γ := 𝚷)
    cases Γ <;> simp [hσ, hπ]

lemma subst {n m w : V} (hw : IsSemitermVec ℒₒᵣ n m w) (hθ : IsSemiformula ℒₒᵣ (n + s) θ)
    (hθ' : IsBounded θ) {e : V} :
    PrenexSatisfied Γ s e (Bootstrapping.subst ℒₒᵣ ((qVec ℒₒᵣ)^[s] w) θ) ↔
      PrenexSatisfied Γ s (termValVec e n w) θ := by
  induction s generalizing Γ n m w e with
  | zero => simpa using BoundedSatisfied.subst hw (by simpa using hθ) hθ'
  | succ s ih =>
    have hθs : IsSemiformula ℒₒᵣ (n + 1 + s) θ := by
      simpa [add_assoc, add_comm (1 : V)] using hθ
    cases Γ <;> simp [Function.iterate_succ_apply, ih hw.qVec hθs, termValVec_qVec hw]

/-- A $\Delta_0$ formula `qqToPrenex Γ s θ` is read the same by `PrenexSatisfied Γ s`
and by `BoundedSatisfied`. -/
lemma iff_boundedSatisfied (h : IsBounded (qqToPrenex Γ s θ)) (hθ : IsUFormula ℒₒᵣ θ)
    {e : V} :
    PrenexSatisfied Γ s e θ ↔ BoundedSatisfied e (qqToPrenex Γ s θ) := by
  match s, le_one_of_isBounded_qqToPrenex h with
  | 0, _ => simp
  | 1, _ => exact (BoundedSatisfied.qqQuant_iff h hθ).symm

/-- Two decompositions of the same code as a prenex formula with a $\Delta_0$ matrix are read the
same. -/
lemma iff_of_qqToPrenex_eq (heq : qqToPrenex Γ s θ = qqToPrenex Γ' s' θ') (hθ : IsBounded θ)
    (hθ' : IsBounded θ') (hf : IsUFormula ℒₒᵣ θ) {e : V} :
    PrenexSatisfied Γ s e θ ↔ PrenexSatisfied Γ' s' e θ' := by
  have hf' : IsUFormula ℒₒᵣ θ' := isUFormula_qqToPrenex.mp (heq ▸ isUFormula_qqToPrenex.mpr hf)
  induction s generalizing Γ Γ' s' θ' e with
  | zero =>
    simp only [qqToPrenex_zero] at heq
    subst heq
    rw [zero_iff, iff_boundedSatisfied hθ hf']
  | succ s ih =>
    cases s' with
    | zero =>
      simp only [qqToPrenex_zero] at heq
      subst heq
      rw [zero_iff, iff_boundedSatisfied hθ' hf]
    | succ s' =>
      obtain ⟨rfl, heq⟩ := qqQuant_inj.mp heq
      cases Γ
      · exact exists_congr fun x ↦ ih heq hθ' hf'
      · exact forall_congr' fun x ↦ ih heq hθ' hf'

end PrenexSatisfied

end FFL.FirstOrder.Arithmetic.Bootstrapping
