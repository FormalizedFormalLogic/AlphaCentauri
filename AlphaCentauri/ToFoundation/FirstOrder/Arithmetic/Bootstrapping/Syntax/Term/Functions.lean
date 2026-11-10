module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax

/-!
# Gaps in Foundation's `Syntax/Term/Functions`

Substituting the bound variables of a closed semiterm, or shifting them, is the identity;
substituting into a semiterm with `m` bound variables depends only on the first `m` entries of the
vector. `bvarVec j k` is the vector of the bound variables `^#j, …, ^#(j + k - 1)`. If the
substitution of a term vector yields a term with its bound variables shifted by one, so does the
term.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

/-- Substituting the bound variables of a closed semiterm is the identity. -/
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

/-- Bound-shifting a closed semiterm is the identity. -/
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

/-- The shift of free variables does not decrease the code of a term. -/
lemma le_termShift {n t : V} (ht : IsSemiterm L n t) : t ≤ termShift L t := by
  apply IsSemiterm.induction 𝚷 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z _
    simp
  · intro x
    rw [termShift_fvar]
    simpa [qqFvar] using pair_le_pair_right 1 (show x ≤ x + 1 by simp)
  · intro k f v hf hv ih
    have hv' : v ≤ termShiftVec L k v := le_of_nth_le_nth (by simp [hv.isUTerm, hv.lh])
      fun i hi ↦ by
        rw [nth_termShiftVec hv.isUTerm (by simpa [hv.lh] using hi)]
        exact ih i (by simpa [hv.lh] using hi)
    rw [termShift_func hf hv.isUTerm]
    simpa [qqFunc] using
      pair_le_pair_right 2 <| pair_le_pair_right k <| pair_le_pair_right f hv'

lemma le_termShiftVec {k n v : V} (hv : IsSemitermVec L k n v) : v ≤ termShiftVec L k v :=
  le_of_nth_le_nth (by simp [hv.isUTerm, hv.lh]) fun i hi ↦ by
    rw [nth_termShiftVec hv.isUTerm (by simpa [hv.lh] using hi)]
    exact le_termShift (hv.nth (by simpa [hv.lh] using hi))

lemma isSemitermVec_fvarVec (m n : V) : IsSemitermVec L m n (fvarVec m) :=
  IsSemitermVec.iff.mpr ⟨len_fvarVec m, fun i hi ↦ by simp [nth_fvarVec m i hi]⟩

lemma nth_qVec_succ {k w j : V} (hw : IsUTermVec L k w) (hj : j < k) :
    (qVec L w).[j + 1] = termBShift L w.[j] := by
  rw [qVec, ← hw.lh, nth_adjoin_succ, nth_termBShiftVec hw hj]

lemma nth_qVec_qVec_fvarVec {m i : V} (hi : i < m) :
    (qVec ℒₒᵣ (qVec ℒₒᵣ (fvarVec m))).[i + 1 + 1] = ^&i := by
  have h₁ : IsUTermVec ℒₒᵣ m (fvarVec m) := (isSemitermVec_fvarVec m 0).isUTerm
  have h₂ : IsUTermVec ℒₒᵣ (m + 1) (qVec ℒₒᵣ (fvarVec m)) :=
    (isSemitermVec_fvarVec m 0).qVec.isUTerm
  rw [nth_qVec_succ h₂ (by simpa using hi), nth_qVec_succ h₁ hi, nth_fvarVec m i hi]
  simp

lemma isSemitermVec_cons_cons {m a b w' : V} (ha : IsSemiterm ℒₒᵣ 0 a)
    (hb : IsSemiterm ℒₒᵣ 0 b) (hw' : IsSemitermVec ℒₒᵣ m 0 w') :
    IsSemitermVec ℒₒᵣ (m + 2) 0 (a ∷ b ∷ w') := by
  rw [← one_add_one_eq_two, ← add_assoc]
  simp [ha, hb, hw']

lemma IsSemitermVec.exists_cons {m w : V} (hw : IsSemitermVec ℒₒᵣ (m + 1) 0 w) :
    ∃ w₀ w', w = w₀ ∷ w' ∧ IsSemiterm ℒₒᵣ 0 w₀ ∧ IsSemitermVec ℒₒᵣ m 0 w' := by
  rcases nil_or_adjoin w with rfl | ⟨w₀, w', rfl⟩
  · simpa using hw.lh
  · exact ⟨w₀, w', rfl, IsSemitermVec.cons_iff.mp hw⟩

/-! ## Congruence of substitution -/

lemma termSubst_congr {m t w w' : V} (ht : IsSemiterm L m t) (H : ∀ i < m, w.[i] = w'.[i]) :
    termSubst L w t = termSubst L w' t := by
  apply IsSemiterm.induction 𝚺 _ _ _ _ t ht
  · definability
  · intro z hz; simp [H z hz]
  · intro x; simp
  · intro k f v hf hv ih
    rw [termSubst_func hf hv.isUTerm, termSubst_func hf hv.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k (by rw [len_termSubstVec hv.isUTerm]) (by rw [len_termSubstVec hv.isUTerm])
    intro i hi
    rw [nth_termSubstVec hv.isUTerm hi, nth_termSubstVec hv.isUTerm hi, ih i hi]

lemma IsUTermVec.qVec {k w : V} (hw : IsUTermVec L k w) : IsUTermVec L (k + 1) (qVec L w) := by
  obtain rfl := hw.lh
  simpa [Bootstrapping.qVec] using hw.termBShiftVec.adjoin (t := ^#0) (by simp)

lemma qVec_congr {m k k' w w' : V} (hw : IsUTermVec L k w) (hw' : IsUTermVec L k' w')
    (hk : m ≤ k) (hk' : m ≤ k') (H : ∀ i < m, w.[i] = w'.[i]) :
    ∀ i < m + 1, (qVec L w).[i] = (qVec L w').[i] := by
  obtain rfl := hw.lh
  obtain rfl := hw'.lh
  intro i hi
  rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
  · simp [qVec]
  · have hi : i < m := by simpa using hi
    simp only [qVec, nth_adjoin_succ]
    rw [nth_termBShiftVec hw (lt_of_lt_of_le hi hk), nth_termBShiftVec hw' (lt_of_lt_of_le hi hk'),
      H i hi]

/-! ## Vectors of bound variables -/

section bvarVec

/-- The recursion defining `bvarVec`. -/
def bvarVec.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y j. y = 0”
  succ := .mkSigma “y ih k j. ∃ b, !qqBvarDef b (j + k) ∧ !concatDef y ih b”

/-- The realization of `bvarVec.blueprint`. -/
noncomputable def bvarVec.construction : PR.Construction V bvarVec.blueprint where
  zero := fun _ ↦ 0
  succ := fun x k ih ↦ concat ih (^#(x 0 + k))
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint]

/-- `bvarVec j k = ⟨^#j, …, ^#(j + k - 1)⟩`. -/
noncomputable def bvarVec (j k : V) : V := bvarVec.construction.result ![j] k

@[simp] lemma bvarVec_zero (j : V) : bvarVec j 0 = 0 := by
  simp [bvarVec, bvarVec.construction]

@[simp] lemma bvarVec_succ (j k : V) : bvarVec j (k + 1) = concat (bvarVec j k) (^#(j + k)) := by
  simp [bvarVec, bvarVec.construction]

/-- The $\Sigma_1$ graph of `bvarVec`, with argument order `(y, j, k)`. -/
def _root_.FFL.FirstOrder.Arithmetic.bvarVecDef : 𝚺ᴬ₁.Semisentence 3 :=
  bvarVec.blueprint.resultDef |>.rew (Rew.subst ![#0, #2, #1])

instance bvarVec_defined : 𝚺ᴬ₁-Function₂ (bvarVec : V → V → V) via bvarVecDef := .mk
  fun v ↦ by simp [bvarVec.construction.result_defined_iff, bvarVecDef]; rfl

instance bvarVec_definable : 𝚺ᴬ₁-Function₂ (bvarVec : V → V → V) :=
  bvarVec_defined.to_definable

instance bvarVec_definable' {Γ : Polarity} {m : ℕ} :
    Γᴬ_[m + 1]-Function₂ (bvarVec : V → V → V) := bvarVec_definable.of_sigmaOne

@[simp] lemma len_bvarVec (j k : V) : len (bvarVec j k) = k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih => simp [ih]

lemma nth_bvarVec (j k : V) : ∀ i < k, (bvarVec j k).[i] = ^#(j + i) := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    intro i hi
    rcases (lt_succ_iff_le.mp hi).lt_or_eq with hlt | rfl
    · rw [bvarVec_succ, concat_nth_lt _ _ (by simpa using hlt)]
      exact ih i hlt
    · rw [bvarVec_succ, concat_nth_len' _ _ (by simp)]


lemma IsSemitermVec.bvarVec {j k n : V} (h : j + k ≤ n) : IsSemitermVec L k n (bvarVec j k) :=
  IsSemitermVec.iff.mpr ⟨by simp, fun i hi ↦ by
    rw [nth_bvarVec j k i hi, IsSemiterm.bvar]
    exact lt_of_lt_of_le (by simpa using hi) h⟩

lemma bvarVec_eq_matrixToVec (j : V) (k : ℕ) :
    bvarVec j (k : V) = matrixToVec fun i : Fin k ↦ ^#(((i : ℕ) : V) + j) := by
  apply nth_ext' (k : V) (by simp) (by simp)
  intro i hi
  obtain ⟨i, rfl⟩ := eq_fin_of_lt_nat hi
  simp [nth_bvarVec _ _ _ hi, add_comm]

end bvarVec

lemma exists_vec_bvar_append (w k : V) :
    ∃ v : V, len v = k + len w ∧ (∀ i < k, v.[i] = ^#i) ∧ ∀ j < len w, v.[k + j] = w.[j] := by
  obtain ⟨v, hvl, hv⟩ := sigmaOne_skolem_vec
    (R := fun i y : V ↦ (i < k → y = ^#i) ∧ (k ≤ i → y = w.[i - k])) (by definability)
    (l := k + len w) (fun i _ ↦ by
      by_cases hi : i < k
      · exact ⟨^#i, fun _ ↦ rfl, fun h ↦ absurd hi (not_lt.mpr h)⟩
      · exact ⟨w.[i - k], fun h ↦ absurd h hi, fun _ ↦ rfl⟩)
  exact ⟨v, hvl, fun i hi ↦ (hv i (by simp [lt_of_lt_of_le hi])).1 hi,
    fun j hj ↦ by simpa using (hv (k + j) (by simpa using hj)).2 (by simp)⟩

/-- The vector `^#0, …, ^#(r - 1), t`. -/
lemma exists_vec_bvar_term (r t : V) :
    ∃ v, len v = r + 1 ∧ (∀ i < r, v.[i] = ^#i) ∧ v.[r] = t := by
  obtain ⟨v, hvl, hv₁, hvk⟩ := exists_vec_bvar_append (?[t] : V) r
  exact ⟨v, by simpa using hvl, hv₁, by simpa using hvk 0 (by simp)⟩

lemma isSemitermVec_fvar_bvar (u : V) : IsSemitermVec L 2 1 (?[^&u, ^#(0 : V)] : V) :=
  IsSemitermVec.adjoin (IsSemitermVec.adjoin (IsSemitermVec.nil _) (by simp)) (by simp)

lemma add_arity_comm (k n : V) : k + 1 + n = n + 1 + k := by
  simp only [add_comm, add_left_comm]

lemma termShiftVec_bvarVec (s n : V) : termShiftVec L n (bvarVec s n) = bvarVec s n := by
  have h₁ : IsUTermVec L n (bvarVec s n) :=
    (IsSemitermVec.bvarVec (L := L) (n := s + n) le_rfl).isUTerm
  apply nth_ext' n (by rw [len_termShiftVec h₁]) (by simp)
  intro i hi
  rw [nth_termShiftVec h₁ hi, nth_bvarVec _ _ _ hi, termShift_bvar]

lemma termShiftVec_bvarVec_cons (i s n : V) :
    termShiftVec L (n + 1) (^#i ∷ bvarVec s n) = ^#i ∷ bvarVec s n := by
  have h₁ : IsUTermVec L n (bvarVec s n) :=
    (IsSemitermVec.bvarVec (L := L) (n := s + n) le_rfl).isUTerm
  rw [termShiftVec_cons (show IsUTerm L ^#i by simp) h₁, termShift_bvar, termShiftVec_bvarVec]

lemma IsSemitermVec.of_var {L' : Language} [L'.Encodable] [L'.LORDefinable] {n m w : V}
    (hw : IsSemitermVec L n m w) (hvar : ∀ i < n, (∃ z, w.[i] = ^#z) ∨ (∃ x, w.[i] = ^&x)) :
    IsSemitermVec L' n m w := by
  refine IsSemitermVec.iff.mpr ⟨hw.lh, fun i hi ↦ ?_⟩
  have h := hw.nth hi
  rcases hvar i hi with ⟨z, hz⟩ | ⟨x, hx⟩
  · rw [hz] at h
    rw [hz]
    exact IsSemiterm.bvar.mpr (IsSemiterm.bvar.mp h)
  · rw [hx]
    exact IsSemiterm.fvar _ _

lemma termSubst_bvarVec_termBShift (k : V) {m t : V} (ht : IsSemiterm L m t) :
    termSubst L (bvarVec k (m + 1)) (termBShift L t) = termSubst L (bvarVec (k + 1) m) t := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz
    rw [termBShift_bvar, termSubst_bvar, termSubst_bvar, nth_bvarVec _ _ _ (by simpa using hz),
      nth_bvarVec _ _ _ hz]
    congr 1
    simp only [add_comm, add_left_comm]
  · intro x; simp
  · intro k' f v hf hv ih
    rw [termBShift_func hf hv.isUTerm, termSubst_func hf hv.termBShiftVec.isUTerm,
      termSubst_func hf hv.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k' (len_termSubstVec hv.termBShiftVec.isUTerm) (len_termSubstVec hv.isUTerm)
    intro i hi
    rw [nth_termSubstVec hv.termBShiftVec.isUTerm hi, nth_termSubstVec hv.isUTerm hi,
      nth_termBShiftVec hv.isUTerm hi, ih i hi]

lemma termBShift_termSubst_bvarVec (k : V) {m t : V} (ht : IsSemiterm L m t) :
    termBShift L (termSubst L (bvarVec k m) t) = termSubst L (bvarVec (k + 1) m) t := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz
    rw [termSubst_bvar, termSubst_bvar, nth_bvarVec _ _ _ hz, nth_bvarVec _ _ _ hz, termBShift_bvar]
    congr 1
    simp only [add_assoc, add_comm, add_left_comm]
  · intro x; simp
  · intro k' f v hf hv ih
    have hs : IsSemitermVec L k' (m + k) (termSubstVec L k' (bvarVec k m) v) :=
      (IsSemitermVec.bvarVec (k := m) (n := m + k) (j := k) (add_comm k m).le).termSubstVec hv
    rw [termSubst_func hf hv.isUTerm, termBShift_func hf hs.isUTerm,
      termSubst_func hf hv.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k' (len_termBShiftVec hs.isUTerm) (len_termSubstVec hv.isUTerm)
    intro i hi
    simp only [nth_termBShiftVec hs.isUTerm hi, nth_termSubstVec hv.isUTerm hi]
    exact ih i hi

lemma termSubst_bvarVec_zero {m t : V} (ht : IsSemiterm L m t) : termSubst L (bvarVec 0 m) t = t :=
  termSubst_eq_self ht fun i hi ↦ by rw [nth_bvarVec _ _ _ hi, zero_add]

@[simp] lemma nth_qVec_zero (w : V) : (qVec L w).[0] = ^#0 := by simp [qVec]

lemma qVec_eq_of_var {L' : Language} [L'.Encodable] [L'.LORDefinable] {n m w : V}
    (hw : IsSemitermVec L n m w) (hvar : ∀ i < n, (∃ z, w.[i] = ^#z) ∨ (∃ x, w.[i] = ^&x)) :
    qVec L w = qVec L' w := by
  have h₁ : IsUTermVec L (len w) w := by rw [hw.lh]; exact hw.isUTerm
  have h₂ : IsUTermVec L' (len w) w := by rw [hw.lh]; exact (hw.of_var (L' := L') hvar).isUTerm
  have h₃ : termBShiftVec L (len w) w = termBShiftVec L' (len w) w := by
    apply nth_ext' (len w) (len_termBShiftVec h₁) (len_termBShiftVec h₂)
    intro i hi
    rw [nth_termBShiftVec h₁ hi, nth_termBShiftVec h₂ hi]
    rcases hvar i (by rw [hw.lh] at hi; exact hi) with ⟨z, hz⟩ | ⟨x, hx⟩
    · rw [hz, termBShift_bvar, termBShift_bvar]
    · rw [hx, termBShift_fvar, termBShift_fvar]
  unfold qVec
  rw [h₃]

lemma hvar_qVec {n m w : V} (hw : IsSemitermVec L n m w)
    (hvar : ∀ i < n, (∃ z, w.[i] = ^#z) ∨ (∃ x, w.[i] = ^&x)) :
    ∀ i < n + 1, (∃ z, (qVec L w).[i] = ^#z) ∨ (∃ x, (qVec L w).[i] = ^&x) := by
  intro i hi
  rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
  · exact Or.inl ⟨0, nth_qVec_zero w⟩
  · have hi' : i < n := by simpa using hi
    rcases hvar i hi' with ⟨z, hz⟩ | ⟨x, hx⟩
    · exact Or.inl ⟨z + 1, by rw [nth_qVec_succ hw.isUTerm hi', hz, termBShift_bvar]⟩
    · exact Or.inr ⟨x, by rw [nth_qVec_succ hw.isUTerm hi', hx, termBShift_fvar]⟩

lemma exists_vec_shift {n m w : V} (hw : IsSemitermVec L n m w) (k : V) :
    ∃ v, IsSemitermVec L (n + k) (m + k) v ∧ (∀ i < k, v.[i] = ^#i) ∧
      ∀ j < n, v.[k + j] = termSubst L (bvarVec k m) w.[j] := by
  have hsub : IsSemitermVec L m (m + k) (bvarVec k m) :=
    IsSemitermVec.bvarVec (j := k) (k := m) (n := m + k) (add_comm k m).le
  have hrest : IsSemitermVec L n (m + k) (termSubstVec L n (bvarVec k m) w) :=
    hsub.termSubstVec hw
  have hl : len (termSubstVec L n (bvarVec k m) w) = n := len_termSubstVec hw.isUTerm
  obtain ⟨v, hvl, hv₁, hv₂⟩ := exists_vec_bvar_append (termSubstVec L n (bvarVec k m) w) k
  refine ⟨v, IsSemitermVec.iff.mpr ⟨by rw [hvl, hl, add_comm], fun i hi ↦ ?_⟩, hv₁, fun j hj ↦ ?_⟩
  · rcases lt_or_ge i k with hik | hik
    · rw [hv₁ i hik]
      exact IsSemiterm.bvar.mpr (lt_of_lt_of_le hik le_add_self)
    · obtain ⟨j, rfl⟩ := exists_add_of_le hik
      have hj' : j < n := by
        rw [add_comm n k] at hi
        exact (add_lt_add_iff_left k).mp hi
      rw [hv₂ j (by rw [hl]; exact hj'), nth_termSubstVec hw.isUTerm hj']
      exact hsub.termSubst (hw.nth hj')
  · rw [hv₂ j (by rw [hl]; exact hj), nth_termSubstVec hw.isUTerm hj]

lemma isSemitermVec_of_fvar {w : V} (n : V) (hw : ∀ i < len w, ∃ x, w.[i] = ^&x) :
    IsSemitermVec L (len w) n w :=
  IsSemitermVec.iff.mpr ⟨rfl, fun i hi ↦ by obtain ⟨x, hx⟩ := hw i hi; simp [hx]⟩

lemma IsSemiterm.of_zero {n t : V} (ht : IsSemiterm L 0 t) : IsSemiterm L n t :=
  IsSemiterm.def.mpr ⟨(IsSemiterm.def.mp ht).1, (IsSemiterm.def.mp ht).2.trans (by simp)⟩

lemma qVec_closed {t : V} (ht : IsSemiterm L 0 t) :
    qVec L (?[t] : V) = (?[^#(0 : V), t] : V) := by
  simp [qVec, len_adjoin, termBShift_zero ht, termBShiftVec_cons₁ ht.isUTerm]

/-! ## Terms that are bound-shifted -/


lemma termBShift_ne_bvar_zero {t : V} (ht : IsUTerm L t) : termBShift L t ≠ ^#0 := by
  rcases ht.case with (⟨z, rfl⟩ | ⟨x, rfl⟩ | ⟨k, f, v, hf, hv, rfl⟩) <;> simp_all
  all_goals simp_all [qqBvar, qqFvar, qqFunc]

lemma eq_bvar_zero_of_termSubst_qVec_eq {n m w t : V} (hw : IsSemitermVec L n m w)
    (ht : IsSemiterm L (n + 1) t) (h : termSubst L (qVec L w) t = ^#0) : t = ^#0 := by
  rcases ht.case with (⟨z, hz, rfl⟩ | ⟨x, rfl⟩ | ⟨k, f, v, hf, hv, rfl⟩)
  · rcases zero_or_succ z with rfl | ⟨z, rfl⟩
    · rfl
    · have hz : z < len w := by simpa [hw.lh] using hz
      rw [termSubst_bvar, qVec, nth_adjoin_succ, nth_termBShiftVec (hw.lh ▸ hw.isUTerm) hz] at h
      exact absurd h (termBShift_ne_bvar_zero (hw.nth (hw.lh ▸ hz)).isUTerm)
  · rw [termSubst_fvar] at h
    simp [qqFvar, qqBvar] at h
  · rw [termSubst_func hf hv.isUTerm] at h
    simp [qqFunc, qqBvar] at h

/-- If the instance of `t` by `qVec L w` is a term with its bound variables shifted by one, so is
`t`. -/
lemma exists_eq_termBShift_of_termSubst_qVec_eq {n w t u : V} (ht : IsSemiterm L (n + 1) t)
    (hu : IsUTerm L u) (h : termSubst L (qVec L w) t = termBShift L u) :
    ∃ t', IsUTerm L t' ∧ t = termBShift L t' := by
  have hρ : IsSemitermVec L (n + 1) n (^&0 ∷ bvarVec 0 n) :=
    IsSemitermVec.cons_iff.mpr ⟨by simp, IsSemitermVec.bvarVec (by simp)⟩
  suffices ∀ t, IsSemiterm L (n + 1) t → ∀ u, IsUTerm L u →
      termSubst L (qVec L w) t = termBShift L u →
        t = termBShift L (termSubst L (^&0 ∷ bvarVec 0 n) t) from
    ⟨_, (hρ.termSubst ht).isUTerm, this t ht u hu h⟩
  apply IsSemiterm.induction 𝚷 (P := fun t ↦ ∀ u, IsUTerm L u →
    termSubst L (qVec L w) t = termBShift L u →
      t = termBShift L (termSubst L (^&0 ∷ bvarVec 0 n) t)) (by definability)
  · intro z hz u hu h
    rcases zero_or_succ z with rfl | ⟨z, rfl⟩
    · simp only [termSubst_bvar, qVec, nth_adjoin_zero] at h
      exact absurd h.symm (termBShift_ne_bvar_zero hu)
    · have hz : z < n := by simpa using hz
      simp [nth_bvarVec 0 n z hz]
  · intro x u _ _
    simp
  · intro k f v hf hv ih u hu h
    rw [termSubst_func hf hv.isUTerm] at h
    have hρv := hρ.termSubstVec hv
    rcases hu.case with (⟨z, rfl⟩ | ⟨x, rfl⟩ | ⟨k', f', v', hf', hv', rfl⟩)
    · rw [termBShift_bvar] at h
      simp [qqFunc, qqBvar] at h
    · rw [termBShift_fvar] at h
      simp [qqFunc, qqFvar] at h
    rw [termBShift_func hf' hv', qqFunc_inj] at h
    obtain ⟨rfl, rfl, hvv⟩ := h
    rw [termSubst_func hf hv.isUTerm, termBShift_func hf hρv.isUTerm, qqFunc_inj]
    refine ⟨rfl, rfl, nth_ext' k hv.lh (by simp [hρv.isUTerm]) fun i hi ↦ ?_⟩
    rw [nth_termBShiftVec hρv.isUTerm hi, nth_termSubstVec hv.isUTerm hi]
    apply ih i hi v'.[i] (hv'.nth hi)
    simpa [nth_termSubstVec hv.isUTerm hi, nth_termBShiftVec hv' hi] using congrArg (·.[i]) hvv

end FFL.FirstOrder.Arithmetic.Bootstrapping
