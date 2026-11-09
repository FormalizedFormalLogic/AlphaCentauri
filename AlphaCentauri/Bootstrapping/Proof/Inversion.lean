module

public import AlphaCentauri.Bootstrapping.Proof.RankedDerivation
public import AlphaCentauri.ToFoundation.SubstInversion
public import AlphaCentauri.ToFoundation.Set
public import Foundation.Vorspiel.Tactic.Disj

/-!
# Inversion for the internal calculus of bounded cut rank

This module proves that the propositional rules of the internal calculus are invertible for
derivations of cut rank at most `r`: a derivation of a sequent containing a conjunction yields
derivations of the sequent with either conjunct in its place, and a derivation of a sequent
containing a disjunction yields a derivation of the sequent with both disjuncts in its place.
It also shows that `⊥` can be deleted from a derivable sequent, and records the injectivity of
the external-variable shift on codes, which the shift rule needs.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

open PeanoMinus ISigma0 ISigma1 InternalMeasures

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

/-- The external-variable shift is injective on term codes. -/
lemma termShift_inj {t u : V} (ht : IsUTerm L t) (hu : IsUTerm L u)
    (h : termShift L t = termShift L u) : t = u := by
  have H : ∀ t : V, IsUTerm L t → ∀ u, IsUTerm L u → termShift L t = termShift L u → t = u := by
    apply IsUTerm.induction 𝚷
      (P := fun t ↦ ∀ u, IsUTerm L u → termShift L t = termShift L u → t = u)
    · definability
    · intro z u hu h
      rcases hu.case with (⟨z', rfl⟩ | ⟨x', rfl⟩ | ⟨k', f', v', hf', hv', rfl⟩) <;> simp_all
      all_goals simp_all [qqBvar, qqFvar, qqFunc]
    · intro x u hu h
      rcases hu.case with (⟨z', rfl⟩ | ⟨x', rfl⟩ | ⟨k', f', v', hf', hv', rfl⟩) <;> simp_all
      all_goals simp_all [qqBvar, qqFvar, qqFunc]
    · intro k f v hf hv ih u hu h
      rcases hu.case with (⟨z', rfl⟩ | ⟨x', rfl⟩ | ⟨k', f', v', hf', hv', rfl⟩)
      case inr.inr =>
        rw [termShift_func hf hv, termShift_func hf' hv', qqFunc_inj] at h
        obtain ⟨rfl, rfl, hvv⟩ := h
        rw [nth_ext' k hv.lh.symm hv'.lh.symm fun i hi ↦ ih i hi _ (hv'.nth hi) <| by
          rw [← nth_termShiftVec hv hi, ← nth_termShiftVec hv' hi, hvv]]
      all_goals simp_all
      all_goals simp_all [qqBvar, qqFvar, qqFunc]
  exact H t ht u hu h

/-- The external-variable shift is injective on vectors of term codes. -/
lemma termShiftVec_inj {k v v' : V} (hv : IsUTermVec L k v) (hv' : IsUTermVec L k v')
    (h : termShiftVec L k v = termShiftVec L k v') : v = v' := by
  apply nth_ext' k hv.lh.symm hv'.lh.symm
  intro i hi
  apply termShift_inj (hv.nth hi) (hv'.nth hi)
  rw [← nth_termShiftVec hv hi, ← nth_termShiftVec hv' hi, h]

/-- The external-variable shift is injective on formula codes. -/
lemma shift_inj {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q)
    (h : shift L p = shift L q) : p = q := by
  have H : ∀ p : V, IsUFormula L p → ∀ q, IsUFormula L q → shift L p = shift L q → p = q := by
    apply IsUFormula.ISigma1.pi1_succ_induction
      (P := fun p ↦ ∀ q, IsUFormula L q → shift L p = shift L q → p = q) (by definability)
    case hrel =>
      intro k R v hR hv q hq h
      rcases hq.case with (⟨k', R', v', hR', hv', rfl⟩ | ⟨k', R', v', hR', hv', rfl⟩ | rfl | rfl |
        ⟨q₁, q₂, hq₁, hq₂, rfl⟩ | ⟨q₁, q₂, hq₁, hq₂, rfl⟩ | ⟨q₁, hq₁, rfl⟩ | ⟨q₁, hq₁, rfl⟩)
      case inl =>
        rw [shift_rel hR hv, shift_rel hR' hv', qqRel_inj] at h
        obtain ⟨rfl, rfl, h⟩ := h
        rw [termShiftVec_inj hv hv' h]
      all_goals simp_all
      all_goals simp_all [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs]
    case hnrel =>
      intro k R v hR hv q hq h
      rcases hq.case with (⟨k', R', v', hR', hv', rfl⟩ | ⟨k', R', v', hR', hv', rfl⟩ | rfl | rfl |
        ⟨q₁, q₂, hq₁, hq₂, rfl⟩ | ⟨q₁, q₂, hq₁, hq₂, rfl⟩ | ⟨q₁, hq₁, rfl⟩ | ⟨q₁, hq₁, rfl⟩)
      case inr.inl =>
        rw [shift_nrel hR hv, shift_nrel hR' hv', qqNRel_inj] at h
        obtain ⟨rfl, rfl, h⟩ := h
        rw [termShiftVec_inj hv hv' h]
      all_goals simp_all
      all_goals simp_all [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs]
    case hverum =>
      intro q hq h
      rcases hq.case with (⟨k', R', v', hR', hv', rfl⟩ | ⟨k', R', v', hR', hv', rfl⟩ | rfl | rfl |
        ⟨q₁, q₂, hq₁, hq₂, rfl⟩ | ⟨q₁, q₂, hq₁, hq₂, rfl⟩ | ⟨q₁, hq₁, rfl⟩ | ⟨q₁, hq₁, rfl⟩)
      all_goals simp_all
      all_goals simp_all [qqRel, qqNRel, qqVerum, qqAnd, qqOr, qqAll, qqExs]
    case hfalsum =>
      intro q hq h
      rcases hq.case with (⟨k', R', v', hR', hv', rfl⟩ | ⟨k', R', v', hR', hv', rfl⟩ | rfl | rfl |
        ⟨q₁, q₂, hq₁, hq₂, rfl⟩ | ⟨q₁, q₂, hq₁, hq₂, rfl⟩ | ⟨q₁, hq₁, rfl⟩ | ⟨q₁, hq₁, rfl⟩)
      all_goals simp_all
      all_goals simp_all [qqRel, qqNRel, qqFalsum, qqAnd, qqOr, qqAll, qqExs]
    case hand =>
      intro p₁ p₂ hp₁ hp₂ ih₁ ih₂ q hq h
      obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := exists_eq_and_of_shift_eq hq (by rw [← h, shift_and hp₁ hp₂])
      obtain ⟨hq₁, hq₂⟩ := IsUFormula.and.mp hq
      rw [ih₁ q₁ hq₁ h₁.symm, ih₂ q₂ hq₂ h₂.symm]
    case hor =>
      intro p₁ p₂ hp₁ hp₂ ih₁ ih₂ q hq h
      obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := exists_eq_or_of_shift_eq hq (by rw [← h, shift_or hp₁ hp₂])
      obtain ⟨hq₁, hq₂⟩ := IsUFormula.or.mp hq
      rw [ih₁ q₁ hq₁ h₁.symm, ih₂ q₂ hq₂ h₂.symm]
    case hall =>
      intro p₁ hp₁ ih₁ q hq h
      obtain ⟨q₁, rfl, h₁⟩ := exists_eq_all_of_shift_eq hq (by rw [← h, shift_all hp₁])
      rw [ih₁ q₁ (IsUFormula.all.mp hq) h₁.symm]
    case hexs =>
      intro p₁ hp₁ ih₁ q hq h
      obtain ⟨q₁, rfl, h₁⟩ := exists_eq_exs_of_shift_eq hq (by rw [← h, shift_exs hp₁])
      rw [ih₁ q₁ (IsUFormula.ex.mp hq) h₁.symm]
  exact H p hp q hq h

/-- Removing a formula from a coded set commutes with the external-variable shift. -/
lemma setShift_bitRemove {p s : V} (hs : IsFormulaSet L s) (hp : IsUFormula L p) :
    setShift L (bitRemove p s) = bitRemove (shift L p) (setShift L s) := by
  apply mem_ext
  intro y
  constructor
  · intro hy
    rcases mem_setShift_iff.mp hy with ⟨x, hx, rfl⟩
    have hx' := mem_bitRemove_iff.mp hx
    exact mem_bitRemove_iff.mpr
      ⟨fun e ↦ hx'.1 (shift_inj (hs x hx'.2).isUFormula hp e), shift_mem_setShift hx'.2⟩
  · intro hy
    have hy' := mem_bitRemove_iff.mp hy
    rcases mem_setShift_iff.mp hy'.2 with ⟨x, hx, rfl⟩
    exact mem_setShift_iff.mpr ⟨x, mem_bitRemove_iff.mpr ⟨fun e ↦ hy'.1 (by rw [e]), hx⟩, rfl⟩

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
/-- No code is an axiom of the empty theory. -/
lemma not_mem_empty_Δ₁Class (p : V) : p ∉ (∅ : Theory L).Δ₁Class := by
  intro h
  have : V ⊧/![p] (⊥ : 𝚫ᴬ₁.Semisentence 1).val := h
  simp at this

/-- The rest of an end-sequent split off by `insert` is bounded by the proof code. -/
lemma le_of_fstIdx_eq_insert {d x s : V} (h : fstIdx d = insert x s) : s ≤ d :=
  le_trans (le_of_subset (by rw [h]; exact susbset_insert x s)) (fstIdx_le_self d)

/-- A code in the end-sequent of a proof code is bounded by the proof code. -/
private lemma le_of_mem_fstIdx {x d : V} (h : x ∈ fstIdx d) : x ≤ d :=
  le_trans (le_of_lt (lt_of_mem h)) (fstIdx_le_self d)

/-- The formulas and the context of a conjunction inversion are bounded by the derivation. -/
private lemma and_bounds {p q c s d : V} (hc : c = p ∨ c = q)
    (h : fstIdx d = insert (p ^⋏ q) s) : p ≤ d ∧ q ≤ d ∧ c ≤ d ∧ s ≤ d := by
  have hb : p ^⋏ q ≤ d := le_of_mem_fstIdx (by rw [h]; simp)
  have hp : p ≤ d := le_trans (le_of_lt (by simp)) hb
  have hq : q ≤ d := le_trans (le_of_lt (by simp)) hb
  refine ⟨hp, hq, ?_, le_of_fstIdx_eq_insert h⟩
  rcases hc with rfl | rfl <;> assumption

/-- The formulas and the context of a disjunction inversion are bounded by the derivation. -/
private lemma or_bounds {p q s d : V} (h : fstIdx d = insert (p ^⋎ q) s) :
    p ≤ d ∧ q ≤ d ∧ s ≤ d := by
  have hb : p ^⋎ q ≤ d := le_of_mem_fstIdx (by rw [h]; simp)
  exact ⟨le_trans (le_of_lt (by simp)) hb, le_trans (le_of_lt (by simp)) hb,
    le_of_fstIdx_eq_insert h⟩

variable {r : V}

namespace RankedDerivation

variable (L) in
/-- Conjunction inversion holds for every derivation of cut rank at most `r` coded below `d`. -/
private def InvertsAndBelow (r d : V) : Prop :=
  ∀ d₀ < d, ∀ p q c s : V, (c = p ∨ c = q) →
    RankedDerivationOf (∅ : Theory L) r d₀ (insert (p ^⋏ q) s) →
    RankedDerivable (∅ : Theory L) r (insert c s)

section invertAnd

variable {p q c s : V}

private lemma inversion_and_axL {x : V} (hc : c = p ∨ c = q) (hpF : IsFormula L p)
    (hqF : IsFormula L q) (hfs : IsFormulaSet L (insert (p ^⋏ q) s))
    (hcsF : IsFormulaSet L (insert c s)) (hx : x ∈ insert (p ^⋏ q) s)
    (hnx : neg L x ∈ insert (p ^⋏ q) s) : RankedDerivable (∅ : Theory L) r (insert c s) := by
  have hnegpq : neg L (p ^⋏ q) = neg L p ^⋎ neg L q := neg_and hpF.isUFormula hqF.isUFormula
  by_cases hor : neg L p ^⋎ neg L q ∈ s
  · exact .or_m (p := neg L p) (q := neg L q) (by simp [hor])
      (.em (by simp [hcsF, hpF.neg, hqF.neg]) c (by simp) (by rcases hc with rfl | rfl <;> simp))
  · have hx' : x ≠ p ^⋏ q := by
      rintro rfl
      rw [hnegpq] at hnx
      exact hor (mem_of_mem_insert_of_ne hnx (by simp [qqAnd, qqOr]))
    have hnx' : neg L x ≠ p ^⋏ q := by
      intro h
      have : x = neg L p ^⋎ neg L q := by rw [← hnegpq, ← h, (hfs x hx).isUFormula.neg_neg]
      rw [this] at hx
      exact hor (mem_of_mem_insert_of_ne hx (by simp [qqAnd, qqOr]))
    exact .em hcsF x (by simp [mem_of_mem_insert_of_ne hx hx'])
      (by simp [mem_of_mem_insert_of_ne hnx hnx'])

private lemma inversion_and_and {a b dp dq : V} (hc : c = p ∨ c = q)
    (ih : InvertsAndBelow L r (andIntro (insert (p ^⋏ q) s) a b dp dq))
    (hab : a ^⋏ b ∈ insert (p ^⋏ q) s)
    (hdp : RankedDerivationOf (∅ : Theory L) r dp (insert a (insert (p ^⋏ q) s)))
    (hdq : RankedDerivationOf (∅ : Theory L) r dq (insert b (insert (p ^⋏ q) s))) :
    RankedDerivable (∅ : Theory L) r (insert c s) := by
  rw [insert_comm] at hdp hdq
  have hp := ih dp (dp_lt_andIntro _ _ _ _ _) p q c _ hc hdp
  have hq := ih dq (dq_lt_andIntro _ _ _ _ _) p q c _ hc hdq
  by_cases hab' : a ^⋏ b = p ^⋏ q
  · obtain ⟨rfl, rfl⟩ : a = p ∧ b = q := by simpa using hab'
    rcases hc with rfl | rfl
    · simpa [insert_insert_self] using hp
    · simpa [insert_insert_self] using hq
  · rw [insert_comm] at hp hq
    exact .and_m (by simp [mem_of_mem_insert_of_ne hab hab']) hp hq

private lemma inversion_and_or {a b d₀ : V} (hc : c = p ∨ c = q)
    (ih : InvertsAndBelow L r (orIntro (insert (p ^⋏ q) s) a b d₀))
    (hab : a ^⋎ b ∈ insert (p ^⋏ q) s)
    (hd₀ : RankedDerivationOf (∅ : Theory L) r d₀ (insert a (insert b (insert (p ^⋏ q) s)))) :
    RankedDerivable (∅ : Theory L) r (insert c s) := by
  rw [insert_comm b, insert_comm a] at hd₀
  have h := ih d₀ (d_lt_orIntro _ _ _ _) p q c _ hc hd₀
  rw [insert_comm c a, insert_comm c b] at h
  exact .or_m (by simp [mem_of_mem_insert_of_ne hab (by simp [qqOr, qqAnd])]) h

private lemma inversion_and_all {a d₀ : V} (hc : c = p ∨ c = q) (hpF : IsFormula L p)
    (hqF : IsFormula L q)
    (ih : InvertsAndBelow L r (allIntro (insert (p ^⋏ q) s) a d₀))
    (ha : ^∀ a ∈ insert (p ^⋏ q) s)
    (hd₀ : RankedDerivationOf (∅ : Theory L) r d₀
      (insert (free L a) (setShift L (insert (p ^⋏ q) s)))) :
    RankedDerivable (∅ : Theory L) r (insert c s) := by
  rw [mem_setShift_insert, shift_and hpF.isUFormula hqF.isUFormula, insert_comm] at hd₀
  have h := ih d₀ (s_lt_allIntro _ _ _) (shift L p) (shift L q) (shift L c) _
    (hc.imp (congrArg _) (congrArg _)) hd₀
  rw [insert_comm] at h
  exact .all_m (p := a) (by simp [mem_of_mem_insert_of_ne ha (by simp [qqAll, qqAnd])])
    (by simpa using h)

private lemma inversion_and_exs {a t d₀ : V} (hc : c = p ∨ c = q)
    (ih : InvertsAndBelow L r (exsIntro (insert (p ^⋏ q) s) a t d₀))
    (ha : ^∃ a ∈ insert (p ^⋏ q) s) (ht : IsTerm L t)
    (hd₀ : RankedDerivationOf (∅ : Theory L) r d₀ (insert (substs1 L t a) (insert (p ^⋏ q) s))) :
    RankedDerivable (∅ : Theory L) r (insert c s) := by
  rw [insert_comm] at hd₀
  have h := ih d₀ (d_lt_exsIntro _ _ _ _) p q c _ hc hd₀
  rw [insert_comm] at h
  exact .ex_m (by simp [mem_of_mem_insert_of_ne ha (by simp [qqExs, qqAnd])]) ht h

private lemma inversion_and_wk {d₀ : V} (hc : c = p ∨ c = q)
    (ih : InvertsAndBelow L r (wkRule (insert (p ^⋏ q) s) d₀))
    (hcsF : IsFormulaSet L (insert c s)) (hsub : fstIdx d₀ ⊆ insert (p ^⋏ q) s)
    (hd₀ : RankedDerivation (∅ : Theory L) r d₀) :
    RankedDerivable (∅ : Theory L) r (insert c s) := by
  by_cases hmem : p ^⋏ q ∈ fstIdx d₀
  · refine .wk hcsF ?_
      (ih d₀ (d_lt_wkRule _ _) p q c (bitRemove (p ^⋏ q) (fstIdx d₀)) hc
        ⟨(insert_remove hmem).symm, hd₀⟩)
    intro y hy
    rcases mem_bitInsert_iff.mp hy with rfl | hy
    · simp
    · have hy' := mem_bitRemove_iff.mp hy
      simp [mem_of_mem_insert_of_ne (hsub hy'.2) hy'.1]
  · refine .wk hcsF ?_ ⟨d₀, rfl, hd₀⟩
    intro y hy
    simp [mem_of_mem_insert_of_ne (hsub hy) (by rintro rfl; exact hmem hy)]

private lemma inversion_and_shift {d₀ : V} (hc : c = p ∨ c = q)
    (ih : InvertsAndBelow L r (shiftRule (insert (p ^⋏ q) s) d₀))
    (hcsF : IsFormulaSet L (insert c s)) (hsh : insert (p ^⋏ q) s = setShift L (fstIdx d₀))
    (hd₀ : RankedDerivation (∅ : Theory L) r d₀) :
    RankedDerivable (∅ : Theory L) r (insert c s) := by
  have hΔ := hd₀.isFormulaSet
  obtain ⟨x, hx, hxe⟩ :=
    mem_setShift_iff.mp (show p ^⋏ q ∈ setShift L (fstIdx d₀) by rw [← hsh]; simp)
  have hxF := (hΔ x hx).isUFormula
  obtain ⟨r₁, r₂, rfl, hs₁, hs₂⟩ := exists_eq_and_of_shift_eq hxF hxe.symm
  obtain ⟨c', hc', rfl⟩ : ∃ c', (c' = r₁ ∨ c' = r₂) ∧ shift L c' = c := by
    rcases hc with rfl | rfl
    · exact ⟨r₁, .inl rfl, hs₁⟩
    · exact ⟨r₂, .inr rfl, hs₂⟩
  have h := (ih d₀ (d_lt_shiftRule _ _) r₁ r₂ c' _ hc' ⟨(insert_remove hx).symm, hd₀⟩).shift_m
  rw [mem_setShift_insert, setShift_bitRemove hΔ hxF, ← hxe, ← hsh] at h
  refine .wk hcsF ?_ h
  intro y hy
  rcases mem_bitInsert_iff.mp hy with rfl | hy
  · simp
  · have hy' := mem_bitRemove_iff.mp hy
    simp [mem_of_mem_insert_of_ne hy'.2 hy'.1]

private lemma inversion_and_cut {e d₁ d₂ : V} (hc : c = p ∨ c = q)
    (ih : InvertsAndBelow L r (cutRule (insert (p ^⋏ q) s) e d₁ d₂))
    (he : formulaComplexity L e < r)
    (hd₁ : RankedDerivationOf (∅ : Theory L) r d₁ (insert e (insert (p ^⋏ q) s)))
    (hd₂ : RankedDerivationOf (∅ : Theory L) r d₂ (insert (neg L e) (insert (p ^⋏ q) s))) :
    RankedDerivable (∅ : Theory L) r (insert c s) := by
  rw [insert_comm] at hd₁ hd₂
  have h₁ := ih d₁ (d₁_lt_cutRule _ _ _ _) p q c _ hc hd₁
  have h₂ := ih d₂ (d₂_lt_cutRule _ _ _ _) p q c _ hc hd₂
  rw [insert_comm] at h₁ h₂
  exact .cut he h₁ h₂

end invertAnd

/-- The $\Sigma_1$ form of the conjunction inversion: every piece of data is bounded by the
derivation it is read off. -/
private lemma inversion_and_aux (r : V) :
    ∀ d : V, ∀ p ≤ d, ∀ q ≤ d, ∀ c ≤ d, ∀ s ≤ d, (c = p ∨ c = q) →
      RankedDerivationOf (∅ : Theory L) r d (insert (p ^⋏ q) s) →
      RankedDerivable (∅ : Theory L) r (insert c s) := by
  have hP : 𝚺ᴬ₁-Predicate fun d : V ↦ ∀ p ≤ d, ∀ q ≤ d, ∀ c ≤ d, ∀ s ≤ d, (c = p ∨ c = q) →
      RankedDerivationOf (∅ : Theory L) r d (insert (p ^⋏ q) s) →
      RankedDerivable (∅ : Theory L) r (insert c s) := by
    definability
  intro d
  refine ISigma1.order_induction 𝚺 hP ?_ d
  intro d ih
  have ih' : InvertsAndBelow L r d := by
    intro d₀ hd₀ p q c s hc h
    obtain ⟨b₁, b₂, b₃, b₄⟩ := and_bounds hc h.1
    exact ih d₀ hd₀ p b₁ q b₂ c b₃ s b₄ hc h
  rintro p - q - c - s - hc ⟨hd1, hd2⟩
  have hfs : IsFormulaSet L (insert (p ^⋏ q) s) := hd1 ▸ hd2.isFormulaSet
  have hF : (IsFormula L p ∧ IsFormula L q) ∧ IsFormulaSet L s := by simpa using hfs
  have hcsF : IsFormulaSet L (insert c s) :=
    IsFormulaSet.insert_iff.mpr ⟨by rcases hc with rfl | rfl <;> simp [hF], hF.2⟩
  rcases hd2.case.2 with (⟨Γ, x, rfl, hx, hnx⟩ | ⟨Γ, rfl, hv⟩ |
    ⟨Γ, a, b, dp, dq, rfl, hab, hdp, hdq⟩ | ⟨Γ, a, b, d₀, rfl, hab, hd₀⟩ |
    ⟨Γ, a, d₀, rfl, ha, hd₀⟩ | ⟨Γ, a, t, d₀, rfl, ha, ht, hd₀⟩ |
    ⟨Γ, d₀, rfl, hsub, hd₀⟩ | ⟨Γ, d₀, rfl, hsh, hd₀⟩ |
    ⟨Γ, e, d₁, d₂, rfl, he, hd₁, hd₂⟩ | ⟨Γ, x, rfl, -, hT⟩)
  · rw [fstIdx_axL] at hd1
    subst hd1
    exact inversion_and_axL hc hF.1.1 hF.1.2 hfs hcsF hx hnx
  · rw [fstIdx_verumIntro] at hd1
    subst hd1
    exact .verum hcsF (by simp [mem_of_mem_insert_of_ne hv (by simp [qqVerum, qqAnd])])
  · rw [fstIdx_andIntro] at hd1
    subst hd1
    exact inversion_and_and hc ih' hab hdp hdq
  · rw [fstIdx_orIntro] at hd1
    subst hd1
    exact inversion_and_or hc ih' hab hd₀
  · rw [fstIdx_allIntro] at hd1
    subst hd1
    exact inversion_and_all hc hF.1.1 hF.1.2 ih' ha hd₀
  · rw [fstIdx_exsIntro] at hd1
    subst hd1
    exact inversion_and_exs hc ih' ha ht hd₀
  · rw [fstIdx_wkRule] at hd1
    subst hd1
    exact inversion_and_wk hc ih' hcsF hsub hd₀
  · rw [fstIdx_shiftRule] at hd1
    subst hd1
    exact inversion_and_shift hc ih' hcsF hsh hd₀
  · rw [fstIdx_cutRule] at hd1
    subst hd1
    exact inversion_and_cut hc ih' he hd₁ hd₂
  · exact absurd hT (not_mem_empty_Δ₁Class x)

/-- Inversion for the conjunction rule: a derivation of cut rank at most `r` of a sequent
containing `p ^⋏ q` yields, for either conjunct `c`, a derivation of cut rank at most `r` of the
sequent with `c` in place of `p ^⋏ q`.
- [Bus98, Ch. I §2.4] -/
theorem inversion_and {p q c s d : V} (hc : c = p ∨ c = q)
    (hd : RankedDerivationOf (∅ : Theory L) r d (insert (p ^⋏ q) s)) :
    RankedDerivable (∅ : Theory L) r (insert c s) := by
  obtain ⟨b₁, b₂, b₃, b₄⟩ := and_bounds hc hd.1
  exact inversion_and_aux r d _ b₁ _ b₂ _ b₃ _ b₄ hc hd

variable (L) in
/-- Disjunction inversion holds for every derivation of cut rank at most `r` coded below `d`. -/
private def InvertsOrBelow (r d : V) : Prop :=
  ∀ d₀ < d, ∀ p q s : V, RankedDerivationOf (∅ : Theory L) r d₀ (insert (p ^⋎ q) s) →
    RankedDerivable (∅ : Theory L) r (insert p (insert q s))

section invertOr

variable {p q s : V}

private lemma inversion_or_axL {x : V} (hpF : IsFormula L p) (hqF : IsFormula L q)
    (hfs : IsFormulaSet L (insert (p ^⋎ q) s)) (htF : IsFormulaSet L (insert p (insert q s)))
    (hx : x ∈ insert (p ^⋎ q) s) (hnx : neg L x ∈ insert (p ^⋎ q) s) :
    RankedDerivable (∅ : Theory L) r (insert p (insert q s)) := by
  have hnegpq : neg L (p ^⋎ q) = neg L p ^⋏ neg L q := neg_or hpF.isUFormula hqF.isUFormula
  by_cases hand : neg L p ^⋏ neg L q ∈ s
  · exact .and_m (p := neg L p) (q := neg L q) (by simp [hand])
      (.em (by simp [htF, hpF.neg]) p (by simp) (by simp))
      (.em (by simp [htF, hqF.neg]) q (by simp) (by simp))
  · have hx' : x ≠ p ^⋎ q := by
      rintro rfl
      rw [hnegpq] at hnx
      exact hand (mem_of_mem_insert_of_ne hnx (by simp [qqAnd, qqOr]))
    have hnx' : neg L x ≠ p ^⋎ q := by
      intro h
      have : x = neg L p ^⋏ neg L q := by rw [← hnegpq, ← h, (hfs x hx).isUFormula.neg_neg]
      rw [this] at hx
      exact hand (mem_of_mem_insert_of_ne hx (by simp [qqAnd, qqOr]))
    exact .em htF x (by simp [mem_of_mem_insert_of_ne hx hx'])
      (by simp [mem_of_mem_insert_of_ne hnx hnx'])

private lemma inversion_or_and {a b dp dq : V}
    (ih : InvertsOrBelow L r (andIntro (insert (p ^⋎ q) s) a b dp dq))
    (hab : a ^⋏ b ∈ insert (p ^⋎ q) s)
    (hdp : RankedDerivationOf (∅ : Theory L) r dp (insert a (insert (p ^⋎ q) s)))
    (hdq : RankedDerivationOf (∅ : Theory L) r dq (insert b (insert (p ^⋎ q) s))) :
    RankedDerivable (∅ : Theory L) r (insert p (insert q s)) := by
  rw [insert_comm] at hdp hdq
  have hp := ih dp (dp_lt_andIntro _ _ _ _ _) p q _ hdp
  have hq := ih dq (dq_lt_andIntro _ _ _ _ _) p q _ hdq
  rw [insert_pair_comm] at hp hq
  exact .and_m (by simp [mem_of_mem_insert_of_ne hab (by simp [qqAnd, qqOr])]) hp hq

private lemma inversion_or_or {a b d₀ : V}
    (ih : InvertsOrBelow L r (orIntro (insert (p ^⋎ q) s) a b d₀))
    (hab : a ^⋎ b ∈ insert (p ^⋎ q) s)
    (hd₀ : RankedDerivationOf (∅ : Theory L) r d₀ (insert a (insert b (insert (p ^⋎ q) s)))) :
    RankedDerivable (∅ : Theory L) r (insert p (insert q s)) := by
  rw [insert_comm b, insert_comm a] at hd₀
  have h := ih d₀ (d_lt_orIntro _ _ _ _) p q _ hd₀
  by_cases hab' : a ^⋎ b = p ^⋎ q
  · obtain ⟨rfl, rfl⟩ : a = p ∧ b = q := by simpa using hab'
    simpa [insert_pair_absorb] using h
  · rw [insert_pair_comm₂] at h
    exact .or_m (by simp [mem_of_mem_insert_of_ne hab hab']) h

private lemma inversion_or_all {a d₀ : V} (hpF : IsFormula L p) (hqF : IsFormula L q)
    (ih : InvertsOrBelow L r (allIntro (insert (p ^⋎ q) s) a d₀))
    (ha : ^∀ a ∈ insert (p ^⋎ q) s)
    (hd₀ : RankedDerivationOf (∅ : Theory L) r d₀
      (insert (free L a) (setShift L (insert (p ^⋎ q) s)))) :
    RankedDerivable (∅ : Theory L) r (insert p (insert q s)) := by
  rw [mem_setShift_insert, shift_or hpF.isUFormula hqF.isUFormula, insert_comm] at hd₀
  have h := ih d₀ (s_lt_allIntro _ _ _) (shift L p) (shift L q) _ hd₀
  rw [insert_pair_comm] at h
  exact .all_m (p := a) (by simp [mem_of_mem_insert_of_ne ha (by simp [qqAll, qqOr])])
    (by simpa using h)

private lemma inversion_or_exs {a t d₀ : V}
    (ih : InvertsOrBelow L r (exsIntro (insert (p ^⋎ q) s) a t d₀))
    (ha : ^∃ a ∈ insert (p ^⋎ q) s) (ht : IsTerm L t)
    (hd₀ : RankedDerivationOf (∅ : Theory L) r d₀ (insert (substs1 L t a) (insert (p ^⋎ q) s))) :
    RankedDerivable (∅ : Theory L) r (insert p (insert q s)) := by
  rw [insert_comm] at hd₀
  have h := ih d₀ (d_lt_exsIntro _ _ _ _) p q _ hd₀
  rw [insert_pair_comm] at h
  exact .ex_m (by simp [mem_of_mem_insert_of_ne ha (by simp [qqExs, qqOr])]) ht h

private lemma inversion_or_wk {d₀ : V} (ih : InvertsOrBelow L r (wkRule (insert (p ^⋎ q) s) d₀))
    (htF : IsFormulaSet L (insert p (insert q s))) (hsub : fstIdx d₀ ⊆ insert (p ^⋎ q) s)
    (hd₀ : RankedDerivation (∅ : Theory L) r d₀) :
    RankedDerivable (∅ : Theory L) r (insert p (insert q s)) := by
  by_cases hmem : p ^⋎ q ∈ fstIdx d₀
  · refine .wk htF ?_
      (ih d₀ (d_lt_wkRule _ _) p q (bitRemove (p ^⋎ q) (fstIdx d₀))
        ⟨(insert_remove hmem).symm, hd₀⟩)
    intro y hy
    rcases mem_bitInsert_iff.mp hy with rfl | hy
    · simp
    · rcases mem_bitInsert_iff.mp hy with rfl | hy
      · simp
      · have hy' := mem_bitRemove_iff.mp hy
        simp [mem_of_mem_insert_of_ne (hsub hy'.2) hy'.1]
  · refine .wk htF ?_ ⟨d₀, rfl, hd₀⟩
    intro y hy
    simp [mem_of_mem_insert_of_ne (hsub hy) (by rintro rfl; exact hmem hy)]

private lemma inversion_or_shift {d₀ : V}
    (ih : InvertsOrBelow L r (shiftRule (insert (p ^⋎ q) s) d₀))
    (htF : IsFormulaSet L (insert p (insert q s)))
    (hsh : insert (p ^⋎ q) s = setShift L (fstIdx d₀))
    (hd₀ : RankedDerivation (∅ : Theory L) r d₀) :
    RankedDerivable (∅ : Theory L) r (insert p (insert q s)) := by
  have hΔ := hd₀.isFormulaSet
  obtain ⟨x, hx, hxe⟩ :=
    mem_setShift_iff.mp (show p ^⋎ q ∈ setShift L (fstIdx d₀) by rw [← hsh]; simp)
  have hxF := (hΔ x hx).isUFormula
  obtain ⟨r₁, r₂, rfl, hs₁, hs₂⟩ := exists_eq_or_of_shift_eq hxF hxe.symm
  have h := (ih d₀ (d_lt_shiftRule _ _) r₁ r₂ _ ⟨(insert_remove hx).symm, hd₀⟩).shift_m
  rw [mem_setShift_insert, mem_setShift_insert, hs₁, hs₂, setShift_bitRemove hΔ hxF, ← hxe,
    ← hsh] at h
  refine .wk htF ?_ h
  intro y hy
  rcases mem_bitInsert_iff.mp hy with rfl | hy
  · simp
  · rcases mem_bitInsert_iff.mp hy with rfl | hy
    · simp
    · have hy' := mem_bitRemove_iff.mp hy
      simp [mem_of_mem_insert_of_ne hy'.2 hy'.1]

private lemma inversion_or_cut {e d₁ d₂ : V}
    (ih : InvertsOrBelow L r (cutRule (insert (p ^⋎ q) s) e d₁ d₂))
    (he : formulaComplexity L e < r)
    (hd₁ : RankedDerivationOf (∅ : Theory L) r d₁ (insert e (insert (p ^⋎ q) s)))
    (hd₂ : RankedDerivationOf (∅ : Theory L) r d₂ (insert (neg L e) (insert (p ^⋎ q) s))) :
    RankedDerivable (∅ : Theory L) r (insert p (insert q s)) := by
  rw [insert_comm] at hd₁ hd₂
  have h₁ := ih d₁ (d₁_lt_cutRule _ _ _ _) p q _ hd₁
  have h₂ := ih d₂ (d₂_lt_cutRule _ _ _ _) p q _ hd₂
  rw [insert_pair_comm] at h₁ h₂
  exact .cut he h₁ h₂

end invertOr

/-- The $\Sigma_1$ form of the disjunction inversion: every piece of data is bounded by the
derivation it is read off. -/
private lemma inversion_or_aux (r : V) :
    ∀ d : V, ∀ p ≤ d, ∀ q ≤ d, ∀ s ≤ d,
      RankedDerivationOf (∅ : Theory L) r d (insert (p ^⋎ q) s) →
      RankedDerivable (∅ : Theory L) r (insert p (insert q s)) := by
  have hP : 𝚺ᴬ₁-Predicate fun d : V ↦ ∀ p ≤ d, ∀ q ≤ d, ∀ s ≤ d,
      RankedDerivationOf (∅ : Theory L) r d (insert (p ^⋎ q) s) →
      RankedDerivable (∅ : Theory L) r (insert p (insert q s)) := by
    definability
  intro d
  refine ISigma1.order_induction 𝚺 hP ?_ d
  intro d ih
  have ih' : InvertsOrBelow L r d := by
    intro d₀ hd₀ p q s h
    obtain ⟨b₁, b₂, b₃⟩ := or_bounds h.1
    exact ih d₀ hd₀ p b₁ q b₂ s b₃ h
  rintro p - q - s - ⟨hd1, hd2⟩
  have hfs : IsFormulaSet L (insert (p ^⋎ q) s) := hd1 ▸ hd2.isFormulaSet
  have hF : (IsFormula L p ∧ IsFormula L q) ∧ IsFormulaSet L s := by simpa using hfs
  have htF : IsFormulaSet L (insert p (insert q s)) := by simp [hF]
  rcases hd2.case.2 with (⟨Γ, x, rfl, hx, hnx⟩ | ⟨Γ, rfl, hv⟩ |
    ⟨Γ, a, b, dp, dq, rfl, hab, hdp, hdq⟩ | ⟨Γ, a, b, d₀, rfl, hab, hd₀⟩ |
    ⟨Γ, a, d₀, rfl, ha, hd₀⟩ | ⟨Γ, a, t, d₀, rfl, ha, ht, hd₀⟩ |
    ⟨Γ, d₀, rfl, hsub, hd₀⟩ | ⟨Γ, d₀, rfl, hsh, hd₀⟩ |
    ⟨Γ, e, d₁, d₂, rfl, he, hd₁, hd₂⟩ | ⟨Γ, x, rfl, -, hT⟩)
  · rw [fstIdx_axL] at hd1
    subst hd1
    exact inversion_or_axL hF.1.1 hF.1.2 hfs htF hx hnx
  · rw [fstIdx_verumIntro] at hd1
    subst hd1
    exact .verum htF (by simp [mem_of_mem_insert_of_ne hv (by simp [qqVerum, qqOr])])
  · rw [fstIdx_andIntro] at hd1
    subst hd1
    exact inversion_or_and ih' hab hdp hdq
  · rw [fstIdx_orIntro] at hd1
    subst hd1
    exact inversion_or_or ih' hab hd₀
  · rw [fstIdx_allIntro] at hd1
    subst hd1
    exact inversion_or_all hF.1.1 hF.1.2 ih' ha hd₀
  · rw [fstIdx_exsIntro] at hd1
    subst hd1
    exact inversion_or_exs ih' ha ht hd₀
  · rw [fstIdx_wkRule] at hd1
    subst hd1
    exact inversion_or_wk ih' htF hsub hd₀
  · rw [fstIdx_shiftRule] at hd1
    subst hd1
    exact inversion_or_shift ih' htF hsh hd₀
  · rw [fstIdx_cutRule] at hd1
    subst hd1
    exact inversion_or_cut ih' he hd₁ hd₂
  · exact absurd hT (not_mem_empty_Δ₁Class x)

/-- Inversion for the disjunction rule: a derivation of cut rank at most `r` of a sequent
containing `p ^⋎ q` yields a derivation of cut rank at most `r` of the sequent with both
disjuncts in place of `p ^⋎ q`.
- [Bus98, Ch. I §2.4] -/
theorem inversion_or {p q s d : V}
    (hd : RankedDerivationOf (∅ : Theory L) r d (insert (p ^⋎ q) s)) :
    RankedDerivable (∅ : Theory L) r (insert p (insert q s)) := by
  obtain ⟨b₁, b₂, b₃⟩ := or_bounds hd.1
  exact inversion_or_aux r d _ b₁ _ b₂ _ b₃ hd

end RankedDerivation

namespace RankedDerivable

variable (L) in
/-- `⊥` can be deleted from the end-sequent of every derivation of cut rank at most `r` coded
below `d`. -/
private def DeletesFalsumBelow (r d : V) : Prop :=
  ∀ d₀ < d, ∀ s₀ : V, RankedDerivationOf (∅ : Theory L) r d₀ (insert ^⊥ s₀) →
    RankedDerivable (∅ : Theory L) r s₀

section deleteFalsum

variable {s : V}

private lemma falsum_axL {x : V} (hfs : IsFormulaSet L (insert ^⊥ s)) (hx : x ∈ insert ^⊥ s)
    (hnx : neg L x ∈ insert ^⊥ s) : RankedDerivable (∅ : Theory L) r s := by
  have hsF : IsFormulaSet L s := fun y hy ↦ hfs y (by simp [hy])
  have hvf : (^⊤ : V) ≠ ^⊥ := by simp [qqVerum, qqFalsum]
  by_cases hv : (^⊤ : V) ∈ s
  · exact .verum hsF hv
  · have hx' : x ≠ ^⊥ := by
      rintro rfl
      rw [neg_falsum] at hnx
      exact hv (mem_of_mem_insert_of_ne hnx hvf)
    have hnx' : neg L x ≠ ^⊥ := by
      intro h
      have : x = ^⊤ := by rw [← (hfs x hx).isUFormula.neg_neg, h, neg_falsum]
      exact hv (mem_of_mem_insert_of_ne (this ▸ hx) hvf)
    exact .em hsF x (mem_of_mem_insert_of_ne hx hx') (mem_of_mem_insert_of_ne hnx hnx')

private lemma falsum_and {a b dp dq : V}
    (ih : DeletesFalsumBelow L r (andIntro (insert ^⊥ s) a b dp dq)) (hab : a ^⋏ b ∈ insert ^⊥ s)
    (hdp : RankedDerivationOf (∅ : Theory L) r dp (insert a (insert ^⊥ s)))
    (hdq : RankedDerivationOf (∅ : Theory L) r dq (insert b (insert ^⊥ s))) :
    RankedDerivable (∅ : Theory L) r s := by
  rw [insert_comm] at hdp hdq
  exact .and_m (mem_of_mem_insert_of_ne hab (by simp [qqAnd, qqFalsum]))
    (ih dp (dp_lt_andIntro _ _ _ _ _) _ hdp) (ih dq (dq_lt_andIntro _ _ _ _ _) _ hdq)

private lemma falsum_or {a b d₀ : V}
    (ih : DeletesFalsumBelow L r (orIntro (insert ^⊥ s) a b d₀)) (hab : a ^⋎ b ∈ insert ^⊥ s)
    (hd₀ : RankedDerivationOf (∅ : Theory L) r d₀ (insert a (insert b (insert ^⊥ s)))) :
    RankedDerivable (∅ : Theory L) r s := by
  rw [insert_comm b, insert_comm a] at hd₀
  exact .or_m (mem_of_mem_insert_of_ne hab (by simp [qqOr, qqFalsum]))
    (ih d₀ (d_lt_orIntro _ _ _ _) _ hd₀)

private lemma falsum_all {a d₀ : V} (ih : DeletesFalsumBelow L r (allIntro (insert ^⊥ s) a d₀))
    (ha : ^∀ a ∈ insert ^⊥ s)
    (hd₀ : RankedDerivationOf (∅ : Theory L) r d₀ (insert (free L a) (setShift L (insert ^⊥ s)))) :
    RankedDerivable (∅ : Theory L) r s := by
  rw [mem_setShift_insert, shift_falsum, insert_comm] at hd₀
  exact .all_m (mem_of_mem_insert_of_ne ha (by simp [qqAll, qqFalsum]))
    (ih d₀ (s_lt_allIntro _ _ _) _ hd₀)

private lemma falsum_exs {a t d₀ : V}
    (ih : DeletesFalsumBelow L r (exsIntro (insert ^⊥ s) a t d₀)) (ha : ^∃ a ∈ insert ^⊥ s)
    (ht : IsTerm L t)
    (hd₀ : RankedDerivationOf (∅ : Theory L) r d₀ (insert (substs1 L t a) (insert ^⊥ s))) :
    RankedDerivable (∅ : Theory L) r s := by
  rw [insert_comm] at hd₀
  exact .ex_m (mem_of_mem_insert_of_ne ha (by simp [qqExs, qqFalsum])) ht
    (ih d₀ (d_lt_exsIntro _ _ _ _) _ hd₀)

private lemma falsum_wk {d₀ : V} (ih : DeletesFalsumBelow L r (wkRule (insert ^⊥ s) d₀))
    (hsF : IsFormulaSet L s) (hsub : fstIdx d₀ ⊆ insert ^⊥ s)
    (hd₀ : RankedDerivation (∅ : Theory L) r d₀) : RankedDerivable (∅ : Theory L) r s := by
  by_cases hf : (^⊥ : V) ∈ fstIdx d₀
  · refine .wk hsF ?_
      (ih d₀ (d_lt_wkRule _ _) (bitRemove ^⊥ (fstIdx d₀)) ⟨(insert_remove hf).symm, hd₀⟩)
    intro x hx
    have hx' := mem_bitRemove_iff.mp hx
    exact mem_of_mem_insert_of_ne (hsub hx'.2) hx'.1
  · refine .wk hsF ?_ ⟨d₀, rfl, hd₀⟩
    intro x hx
    exact mem_of_mem_insert_of_ne (hsub hx) (by rintro rfl; exact hf hx)

private lemma falsum_shift {d₀ : V} (ih : DeletesFalsumBelow L r (shiftRule (insert ^⊥ s) d₀))
    (hsF : IsFormulaSet L s) (hsh : insert ^⊥ s = setShift L (fstIdx d₀))
    (hd₀ : RankedDerivation (∅ : Theory L) r d₀) : RankedDerivable (∅ : Theory L) r s := by
  have hΔ := hd₀.isFormulaSet
  obtain ⟨x, hx, hxe⟩ :=
    mem_setShift_iff.mp (show (^⊥ : V) ∈ setShift L (fstIdx d₀) by rw [← hsh]; simp)
  obtain rfl : x = ^⊥ := shift_inj (hΔ x hx).isUFormula (by simp) (by rw [← hxe, shift_falsum])
  refine .wk hsF ?_
    (ih d₀ (d_lt_shiftRule _ _) (bitRemove ^⊥ (fstIdx d₀)) ⟨(insert_remove hx).symm, hd₀⟩).shift_m
  rw [setShift_bitRemove hΔ (by simp), shift_falsum, ← hsh]
  intro y hy
  have hy' := mem_bitRemove_iff.mp hy
  exact mem_of_mem_insert_of_ne hy'.2 hy'.1

private lemma falsum_cut {e d₁ d₂ : V} (ih : DeletesFalsumBelow L r (cutRule (insert ^⊥ s) e d₁ d₂))
    (he : formulaComplexity L e < r)
    (hd₁ : RankedDerivationOf (∅ : Theory L) r d₁ (insert e (insert ^⊥ s)))
    (hd₂ : RankedDerivationOf (∅ : Theory L) r d₂ (insert (neg L e) (insert ^⊥ s))) :
    RankedDerivable (∅ : Theory L) r s := by
  rw [insert_comm] at hd₁ hd₂
  exact .cut he (ih d₁ (d₁_lt_cutRule _ _ _ _) _ hd₁) (ih d₂ (d₂_lt_cutRule _ _ _ _) _ hd₂)

end deleteFalsum

/-- Deleting `⊥` from the end-sequent of a derivation code bounding the rest of it. -/
private lemma of_insert_falsum_aux (r : V) :
    ∀ d : V, ∀ s ≤ d, RankedDerivationOf (∅ : Theory L) r d (insert ^⊥ s) →
      RankedDerivable (∅ : Theory L) r s := by
  have hP : 𝚺ᴬ₁-Predicate fun d : V ↦ ∀ s ≤ d,
      RankedDerivationOf (∅ : Theory L) r d (insert ^⊥ s) →
      RankedDerivable (∅ : Theory L) r s := by
    definability
  intro d
  refine ISigma1.order_induction 𝚺 hP ?_ d
  intro d ih
  have ih' : DeletesFalsumBelow L r d := by
    intro d₀ hd₀ s₀ h
    exact ih d₀ hd₀ s₀ (le_of_fstIdx_eq_insert h.1) h
  rintro s - ⟨hd1, hd2⟩
  have hfs : IsFormulaSet L (insert ^⊥ s) := hd1 ▸ hd2.isFormulaSet
  have hsF : IsFormulaSet L s := fun x hx ↦ hfs x (by simp [hx])
  rcases hd2.case.2 with (⟨Γ, x, rfl, hx, hnx⟩ | ⟨Γ, rfl, hv⟩ |
    ⟨Γ, a, b, dp, dq, rfl, hab, hdp, hdq⟩ | ⟨Γ, a, b, d₀, rfl, hab, hd₀⟩ |
    ⟨Γ, a, d₀, rfl, ha, hd₀⟩ | ⟨Γ, a, t, d₀, rfl, ha, ht, hd₀⟩ |
    ⟨Γ, d₀, rfl, hsub, hd₀⟩ | ⟨Γ, d₀, rfl, hsh, hd₀⟩ |
    ⟨Γ, e, d₁, d₂, rfl, he, hd₁, hd₂⟩ | ⟨Γ, x, rfl, -, hT⟩)
  · rw [fstIdx_axL] at hd1
    subst hd1
    exact falsum_axL hfs hx hnx
  · rw [fstIdx_verumIntro] at hd1
    subst hd1
    exact .verum hsF (mem_of_mem_insert_of_ne hv (by simp [qqVerum, qqFalsum]))
  · rw [fstIdx_andIntro] at hd1
    subst hd1
    exact falsum_and ih' hab hdp hdq
  · rw [fstIdx_orIntro] at hd1
    subst hd1
    exact falsum_or ih' hab hd₀
  · rw [fstIdx_allIntro] at hd1
    subst hd1
    exact falsum_all ih' ha hd₀
  · rw [fstIdx_exsIntro] at hd1
    subst hd1
    exact falsum_exs ih' ha ht hd₀
  · rw [fstIdx_wkRule] at hd1
    subst hd1
    exact falsum_wk ih' hsF hsub hd₀
  · rw [fstIdx_shiftRule] at hd1
    subst hd1
    exact falsum_shift ih' hsF hsh hd₀
  · rw [fstIdx_cutRule] at hd1
    subst hd1
    exact falsum_cut ih' he hd₁ hd₂
  · exact absurd hT (not_mem_empty_Δ₁Class x)

/-- Deleting `⊥` from a sequent derivable with cut rank at most `r` over the empty theory leaves
it derivable with cut rank at most `r`. -/
theorem of_insert_falsum {s : V} (h : RankedDerivable (∅ : Theory L) r (insert ^⊥ s)) :
    RankedDerivable (∅ : Theory L) r s := by
  obtain ⟨d, hd⟩ := h
  exact of_insert_falsum_aux r d s (le_of_fstIdx_eq_insert hd.1) hd

end RankedDerivable

end FFL.FirstOrder.Arithmetic.Bootstrapping
