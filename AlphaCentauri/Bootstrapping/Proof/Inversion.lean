module

public import AlphaCentauri.Bootstrapping.Proof.CutFree
public import AlphaCentauri.Bootstrapping.Proof.Measures

/-!
# Inversion for the internal cut-free calculus

This module proves that the propositional rules of the internal cut-free calculus are invertible:
a cut-free derivation of a sequent containing a conjunction yields cut-free derivations of the
sequent with either conjunct in its place, and a cut-free derivation of a sequent containing a
disjunction yields a cut-free derivation of the sequent with both disjuncts in its place. It also
records the injectivity of the external-variable shift on codes, which the shift rule needs.
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic.Bootstrapping

open PeanoMinus ISigma0 ISigma1 InternalMeasures

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

/-- The external-variable shift is injective on term codes.
- No source; a routine technical fact about the coded syntax. -/
lemma termShift_inj {t u : V} (ht : IsUTerm L t) (hu : IsUTerm L u)
    (h : termShift L t = termShift L u) : t = u := by
  have H : ∀ t : V, IsUTerm L t → ∀ u, IsUTerm L u → termShift L t = termShift L u → t = u := by
    apply IsUTerm.induction 𝚷
      (P := fun t ↦ ∀ u, IsUTerm L u → termShift L t = termShift L u → t = u)
    · definability
    · intro z u hu h
      rcases hu.case with (⟨z', rfl⟩ | ⟨x', rfl⟩ | ⟨k', f', v', hf', hv', rfl⟩)
      · simpa using h
      · rw [termShift_bvar, termShift_fvar] at h
        simp [qqBvar, qqFvar] at h
      · rw [termShift_bvar, termShift_func hf' hv'] at h
        simp [qqBvar, qqFunc] at h
    · intro x u hu h
      rcases hu.case with (⟨z', rfl⟩ | ⟨x', rfl⟩ | ⟨k', f', v', hf', hv', rfl⟩)
      · rw [termShift_bvar, termShift_fvar] at h
        simp [qqBvar, qqFvar] at h
      · simpa using h
      · rw [termShift_fvar, termShift_func hf' hv'] at h
        simp [qqFvar, qqFunc] at h
    · intro k f v hf hv ih u hu h
      rcases hu.case with (⟨z', rfl⟩ | ⟨x', rfl⟩ | ⟨k', f', v', hf', hv', rfl⟩)
      · rw [termShift_func hf hv, termShift_bvar] at h
        simp [qqBvar, qqFunc] at h
      · rw [termShift_func hf hv, termShift_fvar] at h
        simp [qqFvar, qqFunc] at h
      · rw [termShift_func hf hv, termShift_func hf' hv'] at h
        obtain ⟨rfl, rfl, hvv⟩ :
            k = k' ∧ f = f' ∧ termShiftVec L k v = termShiftVec L k' v' := by simpa using h
        have : v = v' := by
          apply nth_ext' k hv.lh.symm hv'.lh.symm
          intro i hi
          refine ih i hi _ (hv'.nth hi) ?_
          rw [← nth_termShiftVec hv hi, ← nth_termShiftVec hv' hi, hvv]
        rw [this]
  exact H t ht u hu h

/-- The shape of a formula code, together with the value the external-variable shift takes on it.
- No source; a routine technical fact about the coded syntax. -/
private lemma shift_case {q : V} (hq : IsUFormula L q) :
    (∃ k R v, L.IsRel k R ∧ IsUTermVec L k v ∧ q = ^rel k R v ∧
      shift L q = ^rel k R (termShiftVec L k v)) ∨
    (∃ k R v, L.IsRel k R ∧ IsUTermVec L k v ∧ q = ^nrel k R v ∧
      shift L q = ^nrel k R (termShiftVec L k v)) ∨
    (q = ^⊤ ∧ shift L q = (^⊤ : V)) ∨
    (q = ^⊥ ∧ shift L q = (^⊥ : V)) ∨
    (∃ q₁ q₂, IsUFormula L q₁ ∧ IsUFormula L q₂ ∧ q = q₁ ^⋏ q₂ ∧
      shift L q = shift L q₁ ^⋏ shift L q₂) ∨
    (∃ q₁ q₂, IsUFormula L q₁ ∧ IsUFormula L q₂ ∧ q = q₁ ^⋎ q₂ ∧
      shift L q = shift L q₁ ^⋎ shift L q₂) ∨
    (∃ q₁, IsUFormula L q₁ ∧ q = ^∀ q₁ ∧ shift L q = ^∀ (shift L q₁)) ∨
    (∃ q₁, IsUFormula L q₁ ∧ q = ^∃ q₁ ∧ shift L q = ^∃ (shift L q₁)) := by
  rcases hq.case with (⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩ | rfl | rfl |
    ⟨q₁, q₂, hq₁, hq₂, rfl⟩ | ⟨q₁, q₂, hq₁, hq₂, rfl⟩ | ⟨q₁, hq₁, rfl⟩ | ⟨q₁, hq₁, rfl⟩)
  · exact Or.inl ⟨k, R, v, hR, hv, rfl, shift_rel hR hv⟩
  · exact Or.inr <| Or.inl ⟨k, R, v, hR, hv, rfl, shift_nrel hR hv⟩
  · exact Or.inr <| Or.inr <| Or.inl ⟨rfl, by simp⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, by simp⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨q₁, q₂, hq₁, hq₂, rfl, shift_and hq₁ hq₂⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨q₁, q₂, hq₁, hq₂, rfl, shift_or hq₁ hq₂⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨q₁, hq₁, rfl, shift_all hq₁⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      ⟨q₁, hq₁, rfl, shift_exs hq₁⟩

/-- The external-variable shift is injective on formula codes.
- No source; a routine technical fact about the coded syntax. -/
lemma shift_inj {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q)
    (h : shift L p = shift L q) : p = q := by
  have H : ∀ p : V, IsUFormula L p → ∀ q, IsUFormula L q → shift L p = shift L q → p = q := by
    apply IsUFormula.ISigma1.pi1_succ_induction
      (P := fun p ↦ ∀ q, IsUFormula L q → shift L p = shift L q → p = q) (by definability)
    case hrel =>
      intro k R v hR hv q hq h
      rw [shift_rel hR hv] at h
      rcases shift_case hq with
        (⟨k', R', v', hR', hv', rfl, hs⟩ | ⟨k', R', v', hR', hv', rfl, hs⟩ | ⟨rfl, hs⟩ |
          ⟨rfl, hs⟩ | ⟨q₁, q₂, hq₁, hq₂, rfl, hs⟩ | ⟨q₁, q₂, hq₁, hq₂, rfl, hs⟩ |
          ⟨q₁, hq₁, rfl, hs⟩ | ⟨q₁, hq₁, rfl, hs⟩) <;> simp only [hs] at h
      · obtain ⟨rfl, rfl, hvv⟩ :
            k = k' ∧ R = R' ∧ termShiftVec L k v = termShiftVec L k' v' := by simpa using h
        have : v = v' := by
          apply nth_ext' k hv.lh.symm hv'.lh.symm
          intro i hi
          refine termShift_inj (hv.nth hi) (hv'.nth hi) ?_
          rw [← nth_termShiftVec hv hi, ← nth_termShiftVec hv' hi, hvv]
        rw [this]
      · simp [qqRel, qqNRel] at h
      · simp [qqRel, qqVerum] at h
      · simp [qqRel, qqFalsum] at h
      · simp [qqRel, qqAnd] at h
      · simp [qqRel, qqOr] at h
      · simp [qqRel, qqAll] at h
      · simp [qqRel, qqExs] at h
    case hnrel =>
      intro k R v hR hv q hq h
      rw [shift_nrel hR hv] at h
      rcases shift_case hq with
        (⟨k', R', v', hR', hv', rfl, hs⟩ | ⟨k', R', v', hR', hv', rfl, hs⟩ | ⟨rfl, hs⟩ |
          ⟨rfl, hs⟩ | ⟨q₁, q₂, hq₁, hq₂, rfl, hs⟩ | ⟨q₁, q₂, hq₁, hq₂, rfl, hs⟩ |
          ⟨q₁, hq₁, rfl, hs⟩ | ⟨q₁, hq₁, rfl, hs⟩) <;> simp only [hs] at h
      · simp [qqRel, qqNRel] at h
      · obtain ⟨rfl, rfl, hvv⟩ :
            k = k' ∧ R = R' ∧ termShiftVec L k v = termShiftVec L k' v' := by simpa using h
        have : v = v' := by
          apply nth_ext' k hv.lh.symm hv'.lh.symm
          intro i hi
          refine termShift_inj (hv.nth hi) (hv'.nth hi) ?_
          rw [← nth_termShiftVec hv hi, ← nth_termShiftVec hv' hi, hvv]
        rw [this]
      · simp [qqNRel, qqVerum] at h
      · simp [qqNRel, qqFalsum] at h
      · simp [qqNRel, qqAnd] at h
      · simp [qqNRel, qqOr] at h
      · simp [qqNRel, qqAll] at h
      · simp [qqNRel, qqExs] at h
    case hverum =>
      intro q hq h
      rw [shift_verum] at h
      rcases shift_case hq with
        (⟨k', R', v', hR', hv', rfl, hs⟩ | ⟨k', R', v', hR', hv', rfl, hs⟩ | ⟨rfl, hs⟩ |
          ⟨rfl, hs⟩ | ⟨q₁, q₂, hq₁, hq₂, rfl, hs⟩ | ⟨q₁, q₂, hq₁, hq₂, rfl, hs⟩ |
          ⟨q₁, hq₁, rfl, hs⟩ | ⟨q₁, hq₁, rfl, hs⟩) <;> simp only [hs] at h
      · simp [qqRel, qqVerum] at h
      · simp [qqNRel, qqVerum] at h
      · rfl
      · simp [qqVerum, qqFalsum] at h
      · simp [qqVerum, qqAnd] at h
      · simp [qqVerum, qqOr] at h
      · simp [qqVerum, qqAll] at h
      · simp [qqVerum, qqExs] at h
    case hfalsum =>
      intro q hq h
      rw [shift_falsum] at h
      rcases shift_case hq with
        (⟨k', R', v', hR', hv', rfl, hs⟩ | ⟨k', R', v', hR', hv', rfl, hs⟩ | ⟨rfl, hs⟩ |
          ⟨rfl, hs⟩ | ⟨q₁, q₂, hq₁, hq₂, rfl, hs⟩ | ⟨q₁, q₂, hq₁, hq₂, rfl, hs⟩ |
          ⟨q₁, hq₁, rfl, hs⟩ | ⟨q₁, hq₁, rfl, hs⟩) <;> simp only [hs] at h
      · simp [qqRel, qqFalsum] at h
      · simp [qqNRel, qqFalsum] at h
      · simp [qqVerum, qqFalsum] at h
      · rfl
      · simp [qqFalsum, qqAnd] at h
      · simp [qqFalsum, qqOr] at h
      · simp [qqFalsum, qqAll] at h
      · simp [qqFalsum, qqExs] at h
    case hand =>
      intro p₁ p₂ hp₁ hp₂ ih₁ ih₂ q hq h
      rw [shift_and hp₁ hp₂] at h
      rcases shift_case hq with
        (⟨k', R', v', hR', hv', rfl, hs⟩ | ⟨k', R', v', hR', hv', rfl, hs⟩ | ⟨rfl, hs⟩ |
          ⟨rfl, hs⟩ | ⟨q₁, q₂, hq₁, hq₂, rfl, hs⟩ | ⟨q₁, q₂, hq₁, hq₂, rfl, hs⟩ |
          ⟨q₁, hq₁, rfl, hs⟩ | ⟨q₁, hq₁, rfl, hs⟩) <;> simp only [hs] at h
      · simp [qqRel, qqAnd] at h
      · simp [qqNRel, qqAnd] at h
      · simp [qqVerum, qqAnd] at h
      · simp [qqFalsum, qqAnd] at h
      · obtain ⟨h₁, h₂⟩ : shift L p₁ = shift L q₁ ∧ shift L p₂ = shift L q₂ := by simpa using h
        rw [ih₁ q₁ hq₁ h₁, ih₂ q₂ hq₂ h₂]
      · simp [qqAnd, qqOr] at h
      · simp [qqAnd, qqAll] at h
      · simp [qqAnd, qqExs] at h
    case hor =>
      intro p₁ p₂ hp₁ hp₂ ih₁ ih₂ q hq h
      rw [shift_or hp₁ hp₂] at h
      rcases shift_case hq with
        (⟨k', R', v', hR', hv', rfl, hs⟩ | ⟨k', R', v', hR', hv', rfl, hs⟩ | ⟨rfl, hs⟩ |
          ⟨rfl, hs⟩ | ⟨q₁, q₂, hq₁, hq₂, rfl, hs⟩ | ⟨q₁, q₂, hq₁, hq₂, rfl, hs⟩ |
          ⟨q₁, hq₁, rfl, hs⟩ | ⟨q₁, hq₁, rfl, hs⟩) <;> simp only [hs] at h
      · simp [qqRel, qqOr] at h
      · simp [qqNRel, qqOr] at h
      · simp [qqVerum, qqOr] at h
      · simp [qqFalsum, qqOr] at h
      · simp [qqAnd, qqOr] at h
      · obtain ⟨h₁, h₂⟩ : shift L p₁ = shift L q₁ ∧ shift L p₂ = shift L q₂ := by simpa using h
        rw [ih₁ q₁ hq₁ h₁, ih₂ q₂ hq₂ h₂]
      · simp [qqOr, qqAll] at h
      · simp [qqOr, qqExs] at h
    case hall =>
      intro p₁ hp₁ ih₁ q hq h
      rw [shift_all hp₁] at h
      rcases shift_case hq with
        (⟨k', R', v', hR', hv', rfl, hs⟩ | ⟨k', R', v', hR', hv', rfl, hs⟩ | ⟨rfl, hs⟩ |
          ⟨rfl, hs⟩ | ⟨q₁, q₂, hq₁, hq₂, rfl, hs⟩ | ⟨q₁, q₂, hq₁, hq₂, rfl, hs⟩ |
          ⟨q₁, hq₁, rfl, hs⟩ | ⟨q₁, hq₁, rfl, hs⟩) <;> simp only [hs] at h
      · simp [qqRel, qqAll] at h
      · simp [qqNRel, qqAll] at h
      · simp [qqVerum, qqAll] at h
      · simp [qqFalsum, qqAll] at h
      · simp [qqAnd, qqAll] at h
      · simp [qqOr, qqAll] at h
      · rw [ih₁ q₁ hq₁ (by simpa using h)]
      · simp [qqAll, qqExs] at h
    case hexs =>
      intro p₁ hp₁ ih₁ q hq h
      rw [shift_exs hp₁] at h
      rcases shift_case hq with
        (⟨k', R', v', hR', hv', rfl, hs⟩ | ⟨k', R', v', hR', hv', rfl, hs⟩ | ⟨rfl, hs⟩ |
          ⟨rfl, hs⟩ | ⟨q₁, q₂, hq₁, hq₂, rfl, hs⟩ | ⟨q₁, q₂, hq₁, hq₂, rfl, hs⟩ |
          ⟨q₁, hq₁, rfl, hs⟩ | ⟨q₁, hq₁, rfl, hs⟩) <;> simp only [hs] at h
      · simp [qqRel, qqExs] at h
      · simp [qqNRel, qqExs] at h
      · simp [qqVerum, qqExs] at h
      · simp [qqFalsum, qqExs] at h
      · simp [qqAnd, qqExs] at h
      · simp [qqOr, qqExs] at h
      · simp [qqAll, qqExs] at h
      · rw [ih₁ q₁ hq₁ (by simpa using h)]
  exact H p hp q hq h

/-- Removing a formula from a coded set commutes with the external-variable shift.
- No source; a routine technical fact about the coded syntax. -/
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

/-- A formula code whose external-variable shift is a conjunction is itself a conjunction, and its
conjuncts shift to the given ones.
- No source; a routine technical fact about the coded syntax. -/
lemma exists_and_of_shift_eq_and {r p q : V} (hr : IsUFormula L r) (h : shift L r = p ^⋏ q) :
    ∃ r₁ r₂, IsUFormula L r₁ ∧ IsUFormula L r₂ ∧ r = r₁ ^⋏ r₂ ∧
      shift L r₁ = p ∧ shift L r₂ = q := by
  rcases shift_case hr with
    (⟨k, R, v, hR, hv, rfl, hs⟩ | ⟨k, R, v, hR, hv, rfl, hs⟩ | ⟨rfl, hs⟩ | ⟨rfl, hs⟩ |
      ⟨r₁, r₂, hr₁, hr₂, rfl, hs⟩ | ⟨r₁, r₂, hr₁, hr₂, rfl, hs⟩ |
      ⟨r₁, hr₁, rfl, hs⟩ | ⟨r₁, hr₁, rfl, hs⟩) <;> rw [hs] at h
  · simp [qqRel, qqAnd] at h
  · simp [qqNRel, qqAnd] at h
  · simp [qqVerum, qqAnd] at h
  · simp [qqFalsum, qqAnd] at h
  · obtain ⟨h₁, h₂⟩ : shift L r₁ = p ∧ shift L r₂ = q := by simpa using h
    exact ⟨r₁, r₂, hr₁, hr₂, rfl, h₁, h₂⟩
  · simp [qqAnd, qqOr] at h
  · simp [qqAnd, qqAll] at h
  · simp [qqAnd, qqExs] at h

/-- A formula code whose external-variable shift is a disjunction is itself a disjunction, and its
disjuncts shift to the given ones.
- No source; a routine technical fact about the coded syntax. -/
lemma exists_or_of_shift_eq_or {r p q : V} (hr : IsUFormula L r) (h : shift L r = p ^⋎ q) :
    ∃ r₁ r₂, IsUFormula L r₁ ∧ IsUFormula L r₂ ∧ r = r₁ ^⋎ r₂ ∧
      shift L r₁ = p ∧ shift L r₂ = q := by
  rcases shift_case hr with
    (⟨k, R, v, hR, hv, rfl, hs⟩ | ⟨k, R, v, hR, hv, rfl, hs⟩ | ⟨rfl, hs⟩ | ⟨rfl, hs⟩ |
      ⟨r₁, r₂, hr₁, hr₂, rfl, hs⟩ | ⟨r₁, r₂, hr₁, hr₂, rfl, hs⟩ |
      ⟨r₁, hr₁, rfl, hs⟩ | ⟨r₁, hr₁, rfl, hs⟩) <;> rw [hs] at h
  · simp [qqRel, qqOr] at h
  · simp [qqNRel, qqOr] at h
  · simp [qqVerum, qqOr] at h
  · simp [qqFalsum, qqOr] at h
  · simp [qqAnd, qqOr] at h
  · obtain ⟨h₁, h₂⟩ : shift L r₁ = p ∧ shift L r₂ = q := by simpa using h
    exact ⟨r₁, r₂, hr₁, hr₂, rfl, h₁, h₂⟩
  · simp [qqOr, qqAll] at h
  · simp [qqOr, qqExs] at h

section

variable {T : Theory L} [T.Δ₁]

/-- Adding the same code twice to a coded set is adding it once.
- No source; a routine fact about coded sets. -/
private lemma insert_insert_self (x s : V) : insert x (insert x s) = insert x s := mem_ext <| by
  intro z
  simp only [mem_bitInsert_iff]
  tauto

/-- Adding two codes to a coded set does not depend on their order.
- No source; a routine fact about coded sets. -/
private lemma insert_comm (x y s : V) : insert x (insert y s) = insert y (insert x s) :=
  mem_ext <| by
    intro z
    simp only [mem_bitInsert_iff]
    tauto

/-- Removing a code just added to a coded set that did not contain it recovers the set.
- No source; a routine fact about coded sets. -/
private lemma bitRemove_insert_of_not_mem {x s : V} (h : x ∉ s) : bitRemove x (insert x s) = s :=
  mem_ext <| by
    intro z
    simp only [mem_bitRemove_iff, mem_bitInsert_iff]
    constructor
    · rintro ⟨hz, rfl | hz'⟩
      · exact absurd rfl hz
      · exact hz'
    · intro hz
      exact ⟨by rintro rfl; exact h hz, Or.inr hz⟩

/-- The end-sequent of a proof code is bounded by the code itself.
- No source; a routine fact about the coding of proofs. -/
lemma fstIdx_le (d : V) : fstIdx d ≤ d :=
  le_trans (pi₁_le_self (d - 1)) (by simp)

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
/-- No code is an axiom of the empty theory.
- No source; a routine fact about the internal presentation of a theory. -/
lemma not_mem_empty_Δ₁Class (p : V) : p ∉ (∅ : Theory L).Δ₁Class := by
  intro h
  have : V ⊧/![p] (⊥ : 𝚫₁.Semisentence 1).val := h
  simp at this

namespace CutFreeDerivation

/-- A cut-free derivation cuts on nothing, so its cut rank is `0`.
- [Bus98, Ch. I §2.4] -/
lemma cutRank_eq_zero {d : V} (h : CutFreeDerivation T d) : cutRank L d = 0 := by
  apply CutFreeDerivation.induction1 𝚺 ?_ h
  · intro s _ p _ _; simp
  · intro s _ _; simp
  · intro s _ p q dp dq _ _ _ ihp ihq; simp [ihp, ihq]
  · intro s _ p q d _ _ ih; simp [ih]
  · intro s _ p d _ _ ih; simp [ih]
  · intro s _ p t d _ _ _ ih; simp [ih]
  · intro s _ d _ _ ih; simp [ih]
  · rintro _ _ d rfl _ ih; simp [ih]
  · intro s _ p _ _; simp
  · definability

end CutFreeDerivation

/-- Adding a code already present to a coded set changes nothing.
- No source; a routine fact about coded sets. -/
private lemma insert_eq_self {x s : V} (h : x ∈ s) : insert x s = s := mem_ext <| by
  intro z
  simp only [mem_bitInsert_iff]
  constructor
  · rintro (rfl | hz)
    · exact h
    · exact hz
  · exact Or.inr

/-- A code in the end-sequent of a proof code is bounded by the proof code.
- No source; a routine fact about the coding of proofs. -/
private lemma le_of_mem_fstIdx {x d : V} (h : x ∈ fstIdx d) : x ≤ d :=
  le_trans (le_of_lt (lt_of_mem h)) (fstIdx_le d)

/-- A subset of the end-sequent of a proof code is bounded by the proof code.
- No source; a routine fact about the coding of proofs. -/
private lemma le_of_subset_fstIdx {u d : V} (h : u ⊆ fstIdx d) : u ≤ d :=
  le_trans (le_of_subset h) (fstIdx_le d)

/-- The data of a conjunction inversion is bounded by the derivation it is read off.
- No source; a bookkeeping device keeping the induction hypothesis `𝚺₁`. -/
private lemma and_bounds {p q c s d : V} (hc : c = p ∨ c = q)
    (h : fstIdx d = insert (p ^⋏ q) s) : p ≤ d ∧ q ≤ d ∧ c ≤ d ∧ s ≤ d := by
  have hb : p ^⋏ q ≤ d := le_of_mem_fstIdx (by rw [h]; simp)
  have hp : p ≤ d := le_trans (le_of_lt (by simp)) hb
  have hq : q ≤ d := le_trans (le_of_lt (by simp)) hb
  refine ⟨hp, hq, ?_, le_of_subset_fstIdx (by rw [h]; intro x hx; simp [hx])⟩
  rcases hc with rfl | rfl
  · exact hp
  · exact hq

/-- Adding two codes to a coded set already containing them changes nothing.
- No source; a routine fact about coded sets. -/
private lemma insert_pair_absorb (x y s : V) :
    insert x (insert y (insert x (insert y s))) = insert x (insert y s) := mem_ext <| by
  intro z
  simp only [mem_bitInsert_iff]
  tauto

/-- Adding two codes and then a third is adding the third and then the two.
- No source; a routine fact about coded sets. -/
private lemma insert_pair_comm (x y a s : V) :
    insert x (insert y (insert a s)) = insert a (insert x (insert y s)) := mem_ext <| by
  intro z
  simp only [mem_bitInsert_iff]
  tauto

/-- Adding two codes and then two more is adding the last two and then the first two.
- No source; a routine fact about coded sets. -/
private lemma insert_pair_comm₂ (x y a b s : V) :
    insert x (insert y (insert a (insert b s))) = insert a (insert b (insert x (insert y s))) :=
  mem_ext <| by
    intro z
    simp only [mem_bitInsert_iff]
    tauto

/-- The data of a disjunction inversion is bounded by the derivation it is read off.
- No source; a bookkeeping device keeping the induction hypothesis `𝚺₁`. -/
private lemma or_bounds {p q s d : V} (h : fstIdx d = insert (p ^⋎ q) s) :
    p ≤ d ∧ q ≤ d ∧ s ≤ d := by
  have hb : p ^⋎ q ≤ d := le_of_mem_fstIdx (by rw [h]; simp)
  exact ⟨le_trans (le_of_lt (by simp)) hb, le_trans (le_of_lt (by simp)) hb,
    le_of_subset_fstIdx (by rw [h]; intro x hx; simp [hx])⟩

/-- Every element is below its successor.
- No source; a routine arithmetical fact. -/
private lemma le_add_one (x : V) : x ≤ x + 1 := le_of_lt (lt_succ_iff_le.mpr le_rfl)

/-- Taking successors is monotone.
- No source; a routine arithmetical fact. -/
private lemma succ_le_succ {x y : V} (h : x ≤ y) : x + 1 ≤ y + 1 := by simpa using h

namespace CutFreeDerivation

/-- The `𝚺₁` form of the conjunction inversion that the course-of-values induction proves: every
piece of data is bounded by the derivation it is read off.
- [Bus98, Ch. I §2.4] -/
private lemma inversion_and_aux :
    ∀ d : V, ∀ p ≤ d, ∀ q ≤ d, ∀ c ≤ d, ∀ s ≤ d, (c = p ∨ c = q) →
      CutFreeDerivationOf (∅ : Theory L) d (insert (p ^⋏ q) s) →
      ∃ d', CutFreeDerivationOf (∅ : Theory L) d' (insert c s) ∧ height d' ≤ height d + 1 := by
  have hP : 𝚺-[1]-Predicate fun d : V ↦ ∀ p ≤ d, ∀ q ≤ d, ∀ c ≤ d, ∀ s ≤ d, (c = p ∨ c = q) →
      CutFreeDerivationOf (∅ : Theory L) d (insert (p ^⋏ q) s) →
      ∃ d', CutFreeDerivationOf (∅ : Theory L) d' (insert c s) ∧ height d' ≤ height d + 1 := by
    definability
  intro d
  refine ISigma1.order_induction 𝚺 hP ?_ d
  intro d ih
  rintro p - q - c - s - hc ⟨hd1, hd2⟩
  have hfs : IsFormulaSet L (insert (p ^⋏ q) s) := hd1 ▸ hd2.isFormulaSet
  have hpqF : IsFormula L (p ^⋏ q) := hfs _ (by simp)
  have hpF : IsFormula L p := (by simpa using hpqF : IsFormula L p ∧ IsFormula L q).1
  have hqF : IsFormula L q := (by simpa using hpqF : IsFormula L p ∧ IsFormula L q).2
  have hsF : IsFormulaSet L s := fun x hx ↦ hfs x (by simp [hx])
  have hcF : IsFormula L c := by rcases hc with rfl | rfl <;> assumption
  have hcsF : IsFormulaSet L (insert c s) := by
    intro x hx
    rcases mem_bitInsert_iff.mp hx with rfl | hx
    · exact hcF
    · exact hsF x hx
  obtain ⟨-, hcase⟩ := hd2.case
  rcases hcase with (⟨s₀, r, rfl, hrs, hnrs⟩ | ⟨s₀, rfl, hv⟩ |
    ⟨s₀, a, b, dp, dq, rfl, hab, hdp, hdq⟩ | ⟨s₀, a, b, d₀, rfl, hab, hd₀⟩ |
    ⟨s₀, a, d₀, rfl, ha, hd₀⟩ | ⟨s₀, a, t, d₀, rfl, ha, ht, hd₀⟩ |
    ⟨s₀, d₀, rfl, hsub, hd₀⟩ | ⟨s₀, d₀, rfl, hsh, hd₀⟩ | ⟨s₀, r, rfl, hrs, hT⟩)
  · -- axiom leaf
    simp only [fstIdx_axL] at hd1
    subst hd1
    have hnegpq : neg L (p ^⋏ q) = neg L p ^⋎ neg L q :=
      neg_and hpF.isUFormula hqF.isUFormula
    have hne : neg L p ^⋎ neg L q ≠ p ^⋏ q := by simp [qqAnd, qqOr]
    by_cases hor : neg L p ^⋎ neg L q ∈ s
    · refine ⟨Bootstrapping.orIntro (insert c s) (neg L p) (neg L q)
        (Bootstrapping.axL (insert (neg L p) (insert (neg L q) (insert c s))) c),
        ⟨by simp, CutFreeDerivation.orIntro (by simp [hor]) ⟨by simp, ?_⟩⟩, ?_⟩
      · refine CutFreeDerivation.axL ?_ (by simp) ?_
        · intro x hx
          rcases mem_bitInsert_iff.mp hx with rfl | hx
          · exact hpF.neg
          · rcases mem_bitInsert_iff.mp hx with rfl | hx
            · exact hqF.neg
            · exact hcsF x hx
        · rcases hc with rfl | rfl <;> simp
      · simp
    · have hnotmem : neg L p ^⋎ neg L q ∉ insert (p ^⋏ q) s := by
        intro hm
        rcases mem_bitInsert_iff.mp hm with he | hs'
        · exact hne he
        · exact hor hs'
      have hrne : r ≠ p ^⋏ q := by
        rintro rfl
        rw [hnegpq] at hnrs
        exact hnotmem hnrs
      have hnrne : neg L r ≠ p ^⋏ q := by
        intro he
        have hre : r = neg L p ^⋎ neg L q := by
          rw [← hnegpq, ← he, (hfs r hrs).isUFormula.neg_neg]
        rw [hre] at hrs
        exact hnotmem hrs
      have hrs' : r ∈ s := by
        rcases mem_bitInsert_iff.mp hrs with he | h
        · exact absurd he hrne
        · exact h
      have hnrs' : neg L r ∈ s := by
        rcases mem_bitInsert_iff.mp hnrs with he | h
        · exact absurd he hnrne
        · exact h
      refine ⟨Bootstrapping.axL (insert c s) r,
        ⟨by simp, CutFreeDerivation.axL hcsF (by simp [hrs']) (by simp [hnrs'])⟩, ?_⟩
      simp only [height_axL]
      exact le_add_one 0
  · -- verum leaf
    simp only [fstIdx_verumIntro] at hd1
    subst hd1
    have hvs : (^⊤ : V) ∈ s := by
      rcases mem_bitInsert_iff.mp hv with he | h
      · exact absurd he (by simp [qqVerum, qqAnd])
      · exact h
    refine ⟨Bootstrapping.verumIntro (insert c s),
      ⟨by simp, CutFreeDerivation.verumIntro hcsF (by simp [hvs])⟩, ?_⟩
    simp only [height_verumIntro]
    exact le_add_one 0
  · -- conjunction rule
    simp only [fstIdx_andIntro] at hd1
    subst hd1
    by_cases hab' : a ^⋏ b = p ^⋏ q
    · obtain ⟨ha', hb'⟩ : a = p ∧ b = q := by simpa using hab'
      rcases hc with hcp | hcq
      · rw [hcp]
        have heq : fstIdx dp = insert (p ^⋏ q) (insert p s) := by
          rw [hdp.1, ha', insert_comm p (p ^⋏ q) s]
        obtain ⟨b₁, b₂, b₃, b₄⟩ := and_bounds (Or.inl (rfl : p = p)) heq
        obtain ⟨d', hd', hh⟩ :=
          ih dp (dp_lt_andIntro _ _ _ _ _) _ b₁ _ b₂ _ b₃ _ b₄ (Or.inl rfl) ⟨heq, hdp.2⟩
        refine ⟨d', by rwa [insert_insert_self] at hd', ?_⟩
        refine le_trans hh ?_
        simp only [height_andIntro]
        exact le_trans (succ_le_succ (le_max_left (height dp) (height dq))) (le_add_one _)
      · rw [hcq]
        have heq : fstIdx dq = insert (p ^⋏ q) (insert q s) := by
          rw [hdq.1, hb', insert_comm q (p ^⋏ q) s]
        obtain ⟨b₁, b₂, b₃, b₄⟩ := and_bounds (Or.inr (rfl : q = q)) heq
        obtain ⟨d', hd', hh⟩ :=
          ih dq (dq_lt_andIntro _ _ _ _ _) _ b₁ _ b₂ _ b₃ _ b₄ (Or.inr rfl) ⟨heq, hdq.2⟩
        refine ⟨d', by rwa [insert_insert_self] at hd', ?_⟩
        refine le_trans hh ?_
        simp only [height_andIntro]
        exact le_trans (succ_le_succ (le_max_right (height dp) (height dq))) (le_add_one _)
    · have habs : a ^⋏ b ∈ s := by
        rcases mem_bitInsert_iff.mp hab with he | h
        · exact absurd he hab'
        · exact h
      have heqp : fstIdx dp = insert (p ^⋏ q) (insert a s) := by
        rw [hdp.1, insert_comm a (p ^⋏ q) s]
      obtain ⟨b₁, b₂, b₃, b₄⟩ := and_bounds hc heqp
      obtain ⟨dp', hdp', hhp⟩ :=
        ih dp (dp_lt_andIntro _ _ _ _ _) _ b₁ _ b₂ _ b₃ _ b₄ hc ⟨heqp, hdp.2⟩
      have heqq : fstIdx dq = insert (p ^⋏ q) (insert b s) := by
        rw [hdq.1, insert_comm b (p ^⋏ q) s]
      obtain ⟨b₁', b₂', b₃', b₄'⟩ := and_bounds hc heqq
      obtain ⟨dq', hdq', hhq⟩ :=
        ih dq (dq_lt_andIntro _ _ _ _ _) _ b₁' _ b₂' _ b₃' _ b₄' hc ⟨heqq, hdq.2⟩
      rw [insert_comm c a s] at hdp'
      rw [insert_comm c b s] at hdq'
      refine ⟨Bootstrapping.andIntro (insert c s) a b dp' dq',
        ⟨by simp, CutFreeDerivation.andIntro (by simp [habs]) hdp' hdq'⟩, ?_⟩
      simp only [height_andIntro]
      refine succ_le_succ (max_le ?_ ?_)
      · exact le_trans hhp (succ_le_succ (le_max_left (height dp) (height dq)))
      · exact le_trans hhq (succ_le_succ (le_max_right (height dp) (height dq)))
  · -- disjunction rule
    simp only [fstIdx_orIntro] at hd1
    subst hd1
    have habs : a ^⋎ b ∈ s := by
      rcases mem_bitInsert_iff.mp hab with he | h
      · exact absurd he (by simp [qqAnd, qqOr])
      · exact h
    have heq : fstIdx d₀ = insert (p ^⋏ q) (insert a (insert b s)) := by
      rw [hd₀.1, insert_comm b (p ^⋏ q) s, insert_comm a (p ^⋏ q) (insert b s)]
    obtain ⟨b₁, b₂, b₃, b₄⟩ := and_bounds hc heq
    obtain ⟨d', hd', hh⟩ :=
      ih d₀ (d_lt_orIntro _ _ _ _) _ b₁ _ b₂ _ b₃ _ b₄ hc ⟨heq, hd₀.2⟩
    rw [insert_comm c a (insert b s), insert_comm c b s] at hd'
    refine ⟨Bootstrapping.orIntro (insert c s) a b d',
      ⟨by simp, CutFreeDerivation.orIntro (by simp [habs]) hd'⟩, ?_⟩
    simp only [height_orIntro]
    exact succ_le_succ hh
  · -- universal rule
    simp only [fstIdx_allIntro] at hd1
    subst hd1
    have halls : ^∀ a ∈ s := by
      rcases mem_bitInsert_iff.mp ha with he | h
      · exact absurd he (by simp [qqAnd, qqAll])
      · exact h
    have heq : fstIdx d₀ =
        insert (shift L p ^⋏ shift L q) (insert (free L a) (setShift L s)) := by
      rw [hd₀.1]
      simp only [mem_setShift_insert, shift_and hpF.isUFormula hqF.isUFormula]
      exact insert_comm _ _ _
    have hc' : shift L c = shift L p ∨ shift L c = shift L q := by
      rcases hc with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    obtain ⟨b₁, b₂, b₃, b₄⟩ := and_bounds hc' heq
    obtain ⟨d', hd', hh⟩ :=
      ih d₀ (s_lt_allIntro _ _ _) _ b₁ _ b₂ _ b₃ _ b₄ hc' ⟨heq, hd₀.2⟩
    rw [insert_comm (shift L c) (free L a) (setShift L s)] at hd'
    refine ⟨Bootstrapping.allIntro (insert c s) a d',
      ⟨by simp, CutFreeDerivation.allIntro (by simp [halls]) (by simpa using hd')⟩, ?_⟩
    simp only [height_allIntro]
    exact succ_le_succ hh
  · -- existential rule
    simp only [fstIdx_exsIntro] at hd1
    subst hd1
    have hexss : ^∃ a ∈ s := by
      rcases mem_bitInsert_iff.mp ha with he | h
      · exact absurd he (by simp [qqAnd, qqExs])
      · exact h
    have heq : fstIdx d₀ = insert (p ^⋏ q) (insert (substs1 L t a) s) := by
      rw [hd₀.1, insert_comm (substs1 L t a) (p ^⋏ q) s]
    obtain ⟨b₁, b₂, b₃, b₄⟩ := and_bounds hc heq
    obtain ⟨d', hd', hh⟩ :=
      ih d₀ (d_lt_exsIntro _ _ _ _) _ b₁ _ b₂ _ b₃ _ b₄ hc ⟨heq, hd₀.2⟩
    rw [insert_comm c (substs1 L t a) s] at hd'
    refine ⟨Bootstrapping.exsIntro (insert c s) a t d',
      ⟨by simp, CutFreeDerivation.exsIntro (by simp [hexss]) ht hd'⟩, ?_⟩
    simp only [height_exsIntro]
    exact succ_le_succ hh
  · -- weakening
    simp only [fstIdx_wkRule] at hd1
    subst hd1
    by_cases hmem : p ^⋏ q ∈ fstIdx d₀
    · have heq : fstIdx d₀ = insert (p ^⋏ q) (bitRemove (p ^⋏ q) (fstIdx d₀)) :=
        (insert_remove hmem).symm
      obtain ⟨b₁, b₂, b₃, b₄⟩ := and_bounds hc heq
      obtain ⟨d', hd', hh⟩ :=
        ih d₀ (d_lt_wkRule _ _) _ b₁ _ b₂ _ b₃ _ b₄ hc ⟨heq, hd₀⟩
      refine ⟨Bootstrapping.wkRule (insert c s) d',
        ⟨by simp, CutFreeDerivation.wkRule hcsF ?_ hd'⟩, ?_⟩
      · intro x hx
        rcases mem_bitInsert_iff.mp hx with rfl | hx
        · simp
        · have hx' := mem_bitRemove_iff.mp hx
          rcases mem_bitInsert_iff.mp (hsub hx'.2) with he | hxs
          · exact absurd he hx'.1
          · simp [hxs]
      · simp only [height_wkRule]
        exact succ_le_succ hh
    · refine ⟨Bootstrapping.wkRule (insert c s) d₀,
        ⟨by simp, CutFreeDerivation.wkRule hcsF ?_ ⟨rfl, hd₀⟩⟩, ?_⟩
      · intro x hx
        rcases mem_bitInsert_iff.mp (hsub hx) with rfl | hxs
        · exact absurd hx hmem
        · simp [hxs]
      · simp only [height_wkRule]
        exact le_add_one _
  · -- shift
    simp only [fstIdx_shiftRule] at hd1
    subst hsh
    have hmem : p ^⋏ q ∈ setShift L (fstIdx d₀) := by rw [hd1]; simp
    rcases mem_setShift_iff.mp hmem with ⟨r, hrt, hrshift⟩
    have hrF : IsUFormula L r := (hd₀.isFormulaSet r hrt).isUFormula
    obtain ⟨r₁, r₂, hr₁, hr₂, rfl, hs₁, hs₂⟩ :=
      exists_and_of_shift_eq_and hrF hrshift.symm
    obtain ⟨c', hc'sel, hc'shift⟩ : ∃ c', (c' = r₁ ∨ c' = r₂) ∧ shift L c' = c := by
      rcases hc with rfl | rfl
      · exact ⟨r₁, Or.inl rfl, hs₁⟩
      · exact ⟨r₂, Or.inr rfl, hs₂⟩
    by_cases hps : p ^⋏ q ∈ s
    · have heq : fstIdx d₀ = insert (r₁ ^⋏ r₂) (fstIdx d₀) := (insert_eq_self hrt).symm
      obtain ⟨b₁, b₂, b₃, b₄⟩ := and_bounds hc'sel heq
      obtain ⟨d', hd', hh⟩ :=
        ih d₀ (d_lt_shiftRule _ _) _ b₁ _ b₂ _ b₃ _ b₄ hc'sel ⟨heq, hd₀⟩
      refine ⟨Bootstrapping.shiftRule (setShift L (insert c' (fstIdx d₀))) d',
        ⟨?_, CutFreeDerivation.shiftRule hd'⟩, ?_⟩
      · rw [fstIdx_shiftRule, mem_setShift_insert, hc'shift, hd1, insert_eq_self hps]
      · simp only [height_shiftRule]
        exact succ_le_succ hh
    · have heq : fstIdx d₀ = insert (r₁ ^⋏ r₂) (bitRemove (r₁ ^⋏ r₂) (fstIdx d₀)) :=
        (insert_remove hrt).symm
      obtain ⟨b₁, b₂, b₃, b₄⟩ := and_bounds hc'sel heq
      obtain ⟨d', hd', hh⟩ :=
        ih d₀ (d_lt_shiftRule _ _) _ b₁ _ b₂ _ b₃ _ b₄ hc'sel ⟨heq, hd₀⟩
      refine ⟨Bootstrapping.shiftRule
          (setShift L (insert c' (bitRemove (r₁ ^⋏ r₂) (fstIdx d₀)))) d',
        ⟨?_, CutFreeDerivation.shiftRule hd'⟩, ?_⟩
      · rw [fstIdx_shiftRule, mem_setShift_insert, hc'shift,
          setShift_bitRemove hd₀.isFormulaSet hrF, ← hrshift, hd1,
          bitRemove_insert_of_not_mem hps]
      · simp only [height_shiftRule]
        exact succ_le_succ hh
  · exact absurd hT (not_mem_empty_Δ₁Class r)

/-- Inversion for the conjunction rule: a cut-free derivation of a sequent containing `p ^⋏ q`
yields, for either conjunct `c`, a cut-free derivation of the sequent with `c` in place of
`p ^⋏ q`, of height at most one greater.
- [Bus98, Ch. I §2.4] -/
theorem inversion_and {p q c s d : V} (hc : c = p ∨ c = q)
    (hd : CutFreeDerivationOf (∅ : Theory L) d (insert (p ^⋏ q) s)) :
    ∃ d', CutFreeDerivationOf (∅ : Theory L) d' (insert c s) ∧ height d' ≤ height d + 1 := by
  obtain ⟨b₁, b₂, b₃, b₄⟩ := and_bounds hc hd.1
  exact inversion_and_aux d _ b₁ _ b₂ _ b₃ _ b₄ hc hd

/-- The `𝚺₁` form of the disjunction inversion that the course-of-values induction proves: every
piece of data is bounded by the derivation it is read off.
- [Bus98, Ch. I §2.4] -/
private lemma inversion_or_aux :
    ∀ d : V, ∀ p ≤ d, ∀ q ≤ d, ∀ s ≤ d,
      CutFreeDerivationOf (∅ : Theory L) d (insert (p ^⋎ q) s) →
      ∃ d', CutFreeDerivationOf (∅ : Theory L) d' (insert p (insert q s)) ∧
        height d' ≤ height d + 1 := by
  have hP : 𝚺-[1]-Predicate fun d : V ↦ ∀ p ≤ d, ∀ q ≤ d, ∀ s ≤ d,
      CutFreeDerivationOf (∅ : Theory L) d (insert (p ^⋎ q) s) →
      ∃ d', CutFreeDerivationOf (∅ : Theory L) d' (insert p (insert q s)) ∧
        height d' ≤ height d + 1 := by
    definability
  intro d
  refine ISigma1.order_induction 𝚺 hP ?_ d
  intro d ih
  rintro p - q - s - ⟨hd1, hd2⟩
  have hfs : IsFormulaSet L (insert (p ^⋎ q) s) := hd1 ▸ hd2.isFormulaSet
  have hpqF : IsFormula L (p ^⋎ q) := hfs _ (by simp)
  have hpF : IsFormula L p := (by simpa using hpqF : IsFormula L p ∧ IsFormula L q).1
  have hqF : IsFormula L q := (by simpa using hpqF : IsFormula L p ∧ IsFormula L q).2
  have hsF : IsFormulaSet L s := fun x hx ↦ hfs x (by simp [hx])
  have htF : IsFormulaSet L (insert p (insert q s)) := by
    intro x hx
    rcases mem_bitInsert_iff.mp hx with rfl | hx
    · exact hpF
    · rcases mem_bitInsert_iff.mp hx with rfl | hx
      · exact hqF
      · exact hsF x hx
  obtain ⟨-, hcase⟩ := hd2.case
  rcases hcase with (⟨s₀, r, rfl, hrs, hnrs⟩ | ⟨s₀, rfl, hv⟩ |
    ⟨s₀, a, b, dp, dq, rfl, hab, hdp, hdq⟩ | ⟨s₀, a, b, d₀, rfl, hab, hd₀⟩ |
    ⟨s₀, a, d₀, rfl, ha, hd₀⟩ | ⟨s₀, a, t, d₀, rfl, ha, ht, hd₀⟩ |
    ⟨s₀, d₀, rfl, hsub, hd₀⟩ | ⟨s₀, d₀, rfl, hsh, hd₀⟩ | ⟨s₀, r, rfl, hrs, hT⟩)
  · -- axiom leaf
    simp only [fstIdx_axL] at hd1
    subst hd1
    have hnegpq : neg L (p ^⋎ q) = neg L p ^⋏ neg L q :=
      neg_or hpF.isUFormula hqF.isUFormula
    have hne : neg L p ^⋏ neg L q ≠ p ^⋎ q := by simp [qqAnd, qqOr]
    by_cases hand : neg L p ^⋏ neg L q ∈ s
    · refine ⟨Bootstrapping.andIntro (insert p (insert q s)) (neg L p) (neg L q)
        (Bootstrapping.axL (insert (neg L p) (insert p (insert q s))) p)
        (Bootstrapping.axL (insert (neg L q) (insert p (insert q s))) q),
        ⟨by simp, CutFreeDerivation.andIntro (by simp [hand]) ⟨by simp, ?_⟩ ⟨by simp, ?_⟩⟩, ?_⟩
      · refine CutFreeDerivation.axL ?_ (by simp) (by simp)
        intro x hx
        rcases mem_bitInsert_iff.mp hx with rfl | hx
        · exact hpF.neg
        · exact htF x hx
      · refine CutFreeDerivation.axL ?_ (by simp) (by simp)
        intro x hx
        rcases mem_bitInsert_iff.mp hx with rfl | hx
        · exact hqF.neg
        · exact htF x hx
      · simp
    · have hnotmem : neg L p ^⋏ neg L q ∉ insert (p ^⋎ q) s := by
        intro hm
        rcases mem_bitInsert_iff.mp hm with he | hs'
        · exact hne he
        · exact hand hs'
      have hrne : r ≠ p ^⋎ q := by
        rintro rfl
        rw [hnegpq] at hnrs
        exact hnotmem hnrs
      have hnrne : neg L r ≠ p ^⋎ q := by
        intro he
        have hre : r = neg L p ^⋏ neg L q := by
          rw [← hnegpq, ← he, (hfs r hrs).isUFormula.neg_neg]
        rw [hre] at hrs
        exact hnotmem hrs
      have hrs' : r ∈ s := by
        rcases mem_bitInsert_iff.mp hrs with he | h
        · exact absurd he hrne
        · exact h
      have hnrs' : neg L r ∈ s := by
        rcases mem_bitInsert_iff.mp hnrs with he | h
        · exact absurd he hnrne
        · exact h
      refine ⟨Bootstrapping.axL (insert p (insert q s)) r,
        ⟨by simp, CutFreeDerivation.axL htF (by simp [hrs']) (by simp [hnrs'])⟩, ?_⟩
      simp only [height_axL]
      exact le_add_one 0
  · -- verum leaf
    simp only [fstIdx_verumIntro] at hd1
    subst hd1
    have hvs : (^⊤ : V) ∈ s := by
      rcases mem_bitInsert_iff.mp hv with he | h
      · exact absurd he (by simp [qqVerum, qqOr])
      · exact h
    refine ⟨Bootstrapping.verumIntro (insert p (insert q s)),
      ⟨by simp, CutFreeDerivation.verumIntro htF (by simp [hvs])⟩, ?_⟩
    simp only [height_verumIntro]
    exact le_add_one 0
  · -- conjunction rule
    simp only [fstIdx_andIntro] at hd1
    subst hd1
    have habs : a ^⋏ b ∈ s := by
      rcases mem_bitInsert_iff.mp hab with he | h
      · exact absurd he (by simp [qqAnd, qqOr])
      · exact h
    have heqp : fstIdx dp = insert (p ^⋎ q) (insert a s) := by
      rw [hdp.1, insert_comm a (p ^⋎ q) s]
    obtain ⟨b₁, b₂, b₃⟩ := or_bounds heqp
    obtain ⟨dp', hdp', hhp⟩ :=
      ih dp (dp_lt_andIntro _ _ _ _ _) _ b₁ _ b₂ _ b₃ ⟨heqp, hdp.2⟩
    have heqq : fstIdx dq = insert (p ^⋎ q) (insert b s) := by
      rw [hdq.1, insert_comm b (p ^⋎ q) s]
    obtain ⟨b₁', b₂', b₃'⟩ := or_bounds heqq
    obtain ⟨dq', hdq', hhq⟩ :=
      ih dq (dq_lt_andIntro _ _ _ _ _) _ b₁' _ b₂' _ b₃' ⟨heqq, hdq.2⟩
    rw [insert_pair_comm p q a s] at hdp'
    rw [insert_pair_comm p q b s] at hdq'
    refine ⟨Bootstrapping.andIntro (insert p (insert q s)) a b dp' dq',
      ⟨by simp, CutFreeDerivation.andIntro (by simp [habs]) hdp' hdq'⟩, ?_⟩
    simp only [height_andIntro]
    refine succ_le_succ (max_le ?_ ?_)
    · exact le_trans hhp (succ_le_succ (le_max_left (height dp) (height dq)))
    · exact le_trans hhq (succ_le_succ (le_max_right (height dp) (height dq)))
  · -- disjunction rule
    simp only [fstIdx_orIntro] at hd1
    subst hd1
    by_cases hab' : a ^⋎ b = p ^⋎ q
    · obtain ⟨ha', hb'⟩ : a = p ∧ b = q := by simpa using hab'
      have heq : fstIdx d₀ = insert (p ^⋎ q) (insert p (insert q s)) := by
        rw [hd₀.1, ha', hb', insert_pair_comm p q (p ^⋎ q) s]
      obtain ⟨b₁, b₂, b₃⟩ := or_bounds heq
      obtain ⟨d', hd', hh⟩ :=
        ih d₀ (d_lt_orIntro _ _ _ _) _ b₁ _ b₂ _ b₃ ⟨heq, hd₀.2⟩
      refine ⟨d', by rwa [insert_pair_absorb] at hd', ?_⟩
      refine le_trans hh ?_
      simp only [height_orIntro]
      exact le_add_one _
    · have habs : a ^⋎ b ∈ s := by
        rcases mem_bitInsert_iff.mp hab with he | h
        · exact absurd he hab'
        · exact h
      have heq : fstIdx d₀ = insert (p ^⋎ q) (insert a (insert b s)) := by
        rw [hd₀.1, insert_comm b (p ^⋎ q) s, insert_comm a (p ^⋎ q) (insert b s)]
      obtain ⟨b₁, b₂, b₃⟩ := or_bounds heq
      obtain ⟨d', hd', hh⟩ :=
        ih d₀ (d_lt_orIntro _ _ _ _) _ b₁ _ b₂ _ b₃ ⟨heq, hd₀.2⟩
      rw [insert_pair_comm₂ p q a b s] at hd'
      refine ⟨Bootstrapping.orIntro (insert p (insert q s)) a b d',
        ⟨by simp, CutFreeDerivation.orIntro (by simp [habs]) hd'⟩, ?_⟩
      simp only [height_orIntro]
      exact succ_le_succ hh
  · -- universal rule
    simp only [fstIdx_allIntro] at hd1
    subst hd1
    have halls : ^∀ a ∈ s := by
      rcases mem_bitInsert_iff.mp ha with he | h
      · exact absurd he (by simp [qqOr, qqAll])
      · exact h
    have heq : fstIdx d₀ =
        insert (shift L p ^⋎ shift L q) (insert (free L a) (setShift L s)) := by
      rw [hd₀.1]
      simp only [mem_setShift_insert, shift_or hpF.isUFormula hqF.isUFormula]
      exact insert_comm _ _ _
    obtain ⟨b₁, b₂, b₃⟩ := or_bounds heq
    obtain ⟨d', hd', hh⟩ :=
      ih d₀ (s_lt_allIntro _ _ _) _ b₁ _ b₂ _ b₃ ⟨heq, hd₀.2⟩
    rw [insert_pair_comm (shift L p) (shift L q) (free L a) (setShift L s)] at hd'
    refine ⟨Bootstrapping.allIntro (insert p (insert q s)) a d',
      ⟨by simp, CutFreeDerivation.allIntro (by simp [halls]) (by simpa using hd')⟩, ?_⟩
    simp only [height_allIntro]
    exact succ_le_succ hh
  · -- existential rule
    simp only [fstIdx_exsIntro] at hd1
    subst hd1
    have hexss : ^∃ a ∈ s := by
      rcases mem_bitInsert_iff.mp ha with he | h
      · exact absurd he (by simp [qqOr, qqExs])
      · exact h
    have heq : fstIdx d₀ = insert (p ^⋎ q) (insert (substs1 L t a) s) := by
      rw [hd₀.1, insert_comm (substs1 L t a) (p ^⋎ q) s]
    obtain ⟨b₁, b₂, b₃⟩ := or_bounds heq
    obtain ⟨d', hd', hh⟩ :=
      ih d₀ (d_lt_exsIntro _ _ _ _) _ b₁ _ b₂ _ b₃ ⟨heq, hd₀.2⟩
    rw [insert_pair_comm p q (substs1 L t a) s] at hd'
    refine ⟨Bootstrapping.exsIntro (insert p (insert q s)) a t d',
      ⟨by simp, CutFreeDerivation.exsIntro (by simp [hexss]) ht hd'⟩, ?_⟩
    simp only [height_exsIntro]
    exact succ_le_succ hh
  · -- weakening
    simp only [fstIdx_wkRule] at hd1
    subst hd1
    by_cases hmem : p ^⋎ q ∈ fstIdx d₀
    · have heq : fstIdx d₀ = insert (p ^⋎ q) (bitRemove (p ^⋎ q) (fstIdx d₀)) :=
        (insert_remove hmem).symm
      obtain ⟨b₁, b₂, b₃⟩ := or_bounds heq
      obtain ⟨d', hd', hh⟩ :=
        ih d₀ (d_lt_wkRule _ _) _ b₁ _ b₂ _ b₃ ⟨heq, hd₀⟩
      refine ⟨Bootstrapping.wkRule (insert p (insert q s)) d',
        ⟨by simp, CutFreeDerivation.wkRule htF ?_ hd'⟩, ?_⟩
      · intro x hx
        rcases mem_bitInsert_iff.mp hx with rfl | hx
        · simp
        · rcases mem_bitInsert_iff.mp hx with rfl | hx
          · simp
          · have hx' := mem_bitRemove_iff.mp hx
            rcases mem_bitInsert_iff.mp (hsub hx'.2) with he | hxs
            · exact absurd he hx'.1
            · simp [hxs]
      · simp only [height_wkRule]
        exact succ_le_succ hh
    · refine ⟨Bootstrapping.wkRule (insert p (insert q s)) d₀,
        ⟨by simp, CutFreeDerivation.wkRule htF ?_ ⟨rfl, hd₀⟩⟩, ?_⟩
      · intro x hx
        rcases mem_bitInsert_iff.mp (hsub hx) with rfl | hxs
        · exact absurd hx hmem
        · simp [hxs]
      · simp only [height_wkRule]
        exact le_add_one _
  · -- shift
    simp only [fstIdx_shiftRule] at hd1
    subst hsh
    have hmem : p ^⋎ q ∈ setShift L (fstIdx d₀) := by rw [hd1]; simp
    rcases mem_setShift_iff.mp hmem with ⟨r, hrt, hrshift⟩
    have hrF : IsUFormula L r := (hd₀.isFormulaSet r hrt).isUFormula
    obtain ⟨r₁, r₂, hr₁, hr₂, rfl, hs₁, hs₂⟩ :=
      exists_or_of_shift_eq_or hrF hrshift.symm
    by_cases hps : p ^⋎ q ∈ s
    · have heq : fstIdx d₀ = insert (r₁ ^⋎ r₂) (fstIdx d₀) := (insert_eq_self hrt).symm
      obtain ⟨b₁, b₂, b₃⟩ := or_bounds heq
      obtain ⟨d', hd', hh⟩ :=
        ih d₀ (d_lt_shiftRule _ _) _ b₁ _ b₂ _ b₃ ⟨heq, hd₀⟩
      refine ⟨Bootstrapping.shiftRule
          (setShift L (insert r₁ (insert r₂ (fstIdx d₀)))) d',
        ⟨?_, CutFreeDerivation.shiftRule hd'⟩, ?_⟩
      · rw [fstIdx_shiftRule, mem_setShift_insert, mem_setShift_insert, hs₁, hs₂, hd1,
          insert_eq_self hps]
      · simp only [height_shiftRule]
        exact succ_le_succ hh
    · have heq : fstIdx d₀ = insert (r₁ ^⋎ r₂) (bitRemove (r₁ ^⋎ r₂) (fstIdx d₀)) :=
        (insert_remove hrt).symm
      obtain ⟨b₁, b₂, b₃⟩ := or_bounds heq
      obtain ⟨d', hd', hh⟩ :=
        ih d₀ (d_lt_shiftRule _ _) _ b₁ _ b₂ _ b₃ ⟨heq, hd₀⟩
      refine ⟨Bootstrapping.shiftRule
          (setShift L (insert r₁ (insert r₂ (bitRemove (r₁ ^⋎ r₂) (fstIdx d₀))))) d',
        ⟨?_, CutFreeDerivation.shiftRule hd'⟩, ?_⟩
      · rw [fstIdx_shiftRule, mem_setShift_insert, mem_setShift_insert, hs₁, hs₂,
          setShift_bitRemove hd₀.isFormulaSet hrF, ← hrshift, hd1,
          bitRemove_insert_of_not_mem hps]
      · simp only [height_shiftRule]
        exact succ_le_succ hh
  · exact absurd hT (not_mem_empty_Δ₁Class r)

/-- Inversion for the disjunction rule: a cut-free derivation of a sequent containing `p ^⋎ q`
yields a cut-free derivation of the sequent with both disjuncts in place of `p ^⋎ q`, of height at
most one greater.
- [Bus98, Ch. I §2.4] -/
theorem inversion_or {p q s d : V}
    (hd : CutFreeDerivationOf (∅ : Theory L) d (insert (p ^⋎ q) s)) :
    ∃ d', CutFreeDerivationOf (∅ : Theory L) d' (insert p (insert q s)) ∧
      height d' ≤ height d + 1 := by
  obtain ⟨b₁, b₂, b₃⟩ := or_bounds hd.1
  exact inversion_or_aux d _ b₁ _ b₂ _ b₃ hd

end CutFreeDerivation

end

end LO.FirstOrder.Arithmetic.Bootstrapping
