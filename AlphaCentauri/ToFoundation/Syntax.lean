module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax

/-!
# Gaps in Foundation's internal syntax

Negation has no fixed point on coded formulas, the shift of free variables is monotone on coded
formula sets, and substitution of closed terms interacts with `qVec`, `fvarVec` and the head of a
vector of closed terms. Substituting into a coded semiterm or semiformula with `m` bound variables
depends only on the first `m` entries of the vector. `bvarVec j k` is the vector of the bound
variables `^#j, …, ^#(j + k - 1)`; the shift of free variables and the substitution of terms
without bound variables pass through a block `qqAlls p k` of universal quantifiers, and
instantiating the outermost quantifier of a block `qqExss p k` of existential quantifiers by a
closed term instantiates the outermost bound variable. Structural induction on one-variable
formulas instantiates the quantifier case by a free variable.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

lemma neg_ne_self {p : V} (hp : IsUFormula L p) : neg L p ≠ p := by
  rcases hp.case with (⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩ | rfl | rfl |
    ⟨q, r, hq, hr, rfl⟩ | ⟨q, r, hq, hr, rfl⟩ | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩)
  · rw [neg_rel hR hv]; simp [qqRel, qqNRel]
  · rw [neg_nrel hR hv]; simp [qqRel, qqNRel]
  · rw [neg_verum]; simp [qqVerum, qqFalsum]
  · rw [neg_falsum]; simp [qqVerum, qqFalsum]
  · rw [neg_and hq hr]; simp [qqAnd, qqOr]
  · rw [neg_or hq hr]; simp [qqAnd, qqOr]
  · rw [neg_all hq]; simp [qqAll, qqExs]
  · rw [neg_ex hq]; simp [qqAll, qqExs]

lemma setShift_subset_setShift {s t : V} (h : s ⊆ t) : setShift L s ⊆ setShift L t := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_setShift_iff.mp hx
  exact shift_mem_setShift (h hy)

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

/-- The shift of free variables does not decrease the code of a formula. -/
lemma le_shift {n p : V} (hp : IsSemiformula L n p) : p ≤ shift L p := by
  apply IsSemiformula.pi1_structural_induction (P := fun _ p ↦ p ≤ shift L p)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R v hR hv
    rw [shift_rel hR hv.isUTerm]
    simpa [qqRel] using
      pair_le_pair_right 0 <| pair_le_pair_right k <| pair_le_pair_right R (le_termShiftVec hv)
  · intro n k R v hR hv
    rw [shift_nrel hR hv.isUTerm]
    simpa [qqNRel] using
      pair_le_pair_right 1 <| pair_le_pair_right k <| pair_le_pair_right R (le_termShiftVec hv)
  · intro n
    simp
  · intro n
    simp
  · intro n p q hp hq ihp ihq
    rw [shift_and hp.isUFormula hq.isUFormula]
    simpa [qqAnd] using pair_le_pair_right 4 <| pair_le_pair ihp ihq
  · intro n p q hp hq ihp ihq
    rw [shift_or hp.isUFormula hq.isUFormula]
    simpa [qqOr] using pair_le_pair_right 5 <| pair_le_pair ihp ihq
  · intro n p hp ih
    rw [shift_all hp.isUFormula]
    simpa [qqAll] using pair_le_pair_right 6 ih
  · intro n p hp ih
    rw [shift_exs hp.isUFormula]
    simpa [qqExs] using pair_le_pair_right 7 ih

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

lemma subst_subst_qVec_fvarVec {m Z t : V} (hZ : IsSemiformula ℒₒᵣ (m + 1) Z)
    (ht : IsSemiterm ℒₒᵣ 2 t) :
    subst ℒₒᵣ ?[t] (subst ℒₒᵣ (qVec ℒₒᵣ (fvarVec m)) Z) = subst ℒₒᵣ (t ∷ fvarVec m) Z := by
  have h₁ : IsSemitermVec ℒₒᵣ 1 2 (?[t] : V) := by simp [ht]
  have h₂ : IsSemitermVec ℒₒᵣ (m + 1) 1 (qVec ℒₒᵣ (fvarVec m)) := by
    simpa using (isSemitermVec_fvarVec m 0).qVec
  rw [substs_substs hZ h₁ h₂]
  congr 1
  have h₃ : IsUTermVec ℒₒᵣ m (fvarVec m) := (isSemitermVec_fvarVec m 0).isUTerm
  apply nth_ext' (m + 1) (by simp [(h₁.termSubstVec h₂).lh])
    (by simp)
  intro i hi
  rw [nth_termSubstVec h₂.isUTerm hi]
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simp [qVec]
  · have hi : i < m := by simpa using hi
    simp [nth_qVec_succ h₃ hi, nth_fvarVec m i hi]

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

lemma substs1_subst_qVec {j w q t : V} (hw : IsSemitermVec L j 0 w)
    (hq : IsSemiformula L (j + 1) q) (ht : IsSemiterm L 0 t) :
    substs1 L t (subst L (qVec L w) q) = subst L (t ∷ w) q := by
  have h₁ : IsSemitermVec L 1 0 (?[t] : V) := by simp [ht]
  have h₂ : IsSemitermVec L (j + 1) 1 (qVec L w) := by simpa using hw.qVec
  rw [substs1, substs_substs hq h₁ h₂]
  congr 1
  apply nth_ext' (j + 1) (by simp [(h₁.termSubstVec h₂).lh]) (by simp [hw.lh])
  intro i hi
  rw [nth_termSubstVec h₂.isUTerm hi]
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simp [qVec]
  · have hi : i < j := by simpa using hi
    rw [qVec, nth_adjoin_succ, hw.lh, nth_termBShiftVec hw.isUTerm hi,
      termBShift_zero (hw.nth hi), termSubst_eq_self (hw.nth hi) (by simp)]
    simp

/-! ## Congruence of substitution -/

section substCongruence

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

private lemma qVec_congr {m k k' w w' : V} (hw : IsUTermVec L k w) (hw' : IsUTermVec L k' w')
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

lemma subst_congr {m p : V} (hp : IsSemiformula L m p) {k k' w w' : V}
    (hw : IsUTermVec L k w) (hw' : IsUTermVec L k' w') (hk : m ≤ k) (hk' : m ≤ k')
    (H : ∀ i < m, w.[i] = w'.[i]) : subst L w p = subst L w' p := by
  revert k k' w w'
  apply IsSemiformula.pi1_structural_induction _ _ _ _ _ _ _ _ _ hp
  · definability
  · intro m l R v hR hv k k' w w' _ _ _ _ H
    rw [substs_rel hR hv.isUTerm, substs_rel hR hv.isUTerm]
    simp only [qqRel_inj, true_and]
    apply nth_ext' l (by rw [len_termSubstVec hv.isUTerm]) (by rw [len_termSubstVec hv.isUTerm])
    intro i hi
    rw [nth_termSubstVec hv.isUTerm hi, nth_termSubstVec hv.isUTerm hi,
      termSubst_congr (hv.nth hi) H]
  · intro m l R v hR hv k k' w w' _ _ _ _ H
    rw [substs_nrel hR hv.isUTerm, substs_nrel hR hv.isUTerm]
    simp only [qqNRel_inj, true_and]
    apply nth_ext' l (by rw [len_termSubstVec hv.isUTerm]) (by rw [len_termSubstVec hv.isUTerm])
    intro i hi
    rw [nth_termSubstVec hv.isUTerm hi, nth_termSubstVec hv.isUTerm hi,
      termSubst_congr (hv.nth hi) H]
  · intro m k k' w w' _ _ _ _ _; simp
  · intro m k k' w w' _ _ _ _ _; simp
  · intro m p q hp hq ihp ihq k k' w w' hw hw' hk hk' H
    rw [substs_and hp.isUFormula hq.isUFormula, substs_and hp.isUFormula hq.isUFormula,
      ihp hw hw' hk hk' H, ihq hw hw' hk hk' H]
  · intro m p q hp hq ihp ihq k k' w w' hw hw' hk hk' H
    rw [substs_or hp.isUFormula hq.isUFormula, substs_or hp.isUFormula hq.isUFormula,
      ihp hw hw' hk hk' H, ihq hw hw' hk hk' H]
  · intro m p hp ih k k' w w' hw hw' hk hk' H
    rw [substs_all hp.isUFormula, substs_all hp.isUFormula,
      ih (hw.qVec) (hw'.qVec) (by simpa using hk) (by simpa using hk') (qVec_congr hw hw' hk hk' H)]
  · intro m p hp ih k k' w w' hw hw' hk hk' H
    rw [substs_ex hp.isUFormula, substs_ex hp.isUFormula,
      ih (hw.qVec) (hw'.qVec) (by simpa using hk) (by simpa using hk') (qVec_congr hw hw' hk hk' H)]

end substCongruence

/-! ## Blocks of quantifiers and vectors of bound variables -/

section iteration

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

end bvarVec

/-! ## Blocks of universal quantifiers -/

section qqAlls


lemma shift_qqAlls {p : V} (hp : IsUFormula L p) (k : V) :
    shift L (qqAlls p k) = qqAlls (shift L p) k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih => rw [qqAlls_succ, shift_all (isUFormula_qqAlls.mpr hp), ih, qqAlls_succ]

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

/-- Substituting terms `w` without bound variables for the outermost bound variables of a block of
`k` universal quantifiers: inside the block they become `w'`, which keeps the `k` variables bound
by the block and continues with `w`. -/
lemma subst_qqAlls {k w w' p : V} (hw : IsSemitermVec L (len w) 0 w) (hp : IsUFormula L p)
    (hl : len w' = k + len w) (h₁ : ∀ i < k, w'.[i] = ^#i) (h₂ : ∀ i < len w, w'.[k + i] = w.[i]) :
    subst L w (qqAlls p k) = qqAlls (subst L w' p) k := by
  induction k using ISigma1.pi1_succ_induction generalizing p w'
  · definability
  case zero =>
    have : w' = w := nth_ext' (len w) (by simpa using hl) rfl fun i hi ↦ by simpa using h₂ i hi
    simp [this]
  case succ k ih =>
    obtain ⟨v, hvl, hv₁, hvk⟩ := exists_vec_bvar_append w k
    have hvu : IsUTermVec L (len v) v := ⟨rfl, fun i hi ↦ by
      rcases lt_or_ge i k with hik | hik
      · simp [hv₁ i hik]
      · obtain ⟨j, rfl⟩ := exists_add_of_le hik
        have hj : j < len w := by simpa [hvl] using hi
        simpa [hvk j hj] using (hw.nth hj).isUTerm⟩
    have hqv : qVec L v = w' := by
      apply nth_ext' (k + len w + 1) (by rw [len_qVec hvu, hvl]) (by rw [hl, add_right_comm])
      intro i hi
      rcases zero_or_succ i with rfl | ⟨i, rfl⟩
      · simp [qVec, h₁ 0 (by simp)]
      · have hi' : i < len v := by simpa [hvl] using hi
        rw [qVec, nth_adjoin_succ, nth_termBShiftVec hvu hi']
        rcases lt_or_ge i k with hik | hik
        · rw [hv₁ i hik, termBShift_bvar, h₁ (i + 1) (by simpa using hik)]
        · obtain ⟨j, rfl⟩ := exists_add_of_le hik
          have hj : j < len w := by simpa [hvl] using hi'
          rw [hvk j hj, termBShift_zero (hw.nth hj), ← h₂ j hj, add_right_comm]
    rw [qqAlls_succ', ih (by simpa using hp) hvl (fun i hi ↦ hv₁ i hi) hvk, substs_all hp,
      ← qqAlls_succ', hqv]

lemma free_qqAlls {k w p : V} (hp : IsUFormula L p) (hl : len w = k + 1)
    (h₁ : ∀ i < k, w.[i] = ^#i) (h₂ : w.[k] = ^&0) :
    free L (qqAlls p k) = qqAlls (subst L w (shift L p)) k := by
  rw [free, substs1, shift_qqAlls hp]
  apply subst_qqAlls (by simp) hp.shift (by simpa using hl) h₁
  intro i hi
  obtain rfl : i = 0 := by simpa using hi
  simpa using h₂

end qqAlls


/-! ## Blocks of existential quantifiers -/

section qqExss


def qqExss.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y x. y = x”
  succ := .mkSigma “y ih n x. !qqExsDef y ih”

noncomputable def qqExss.construction : PR.Construction V qqExss.blueprint where
  zero := fun x ↦ x 0
  succ := fun _ _ ih ↦ ^∃ ih
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint, qqExs]

/-- `qqExss p k = ^∃ ^∃ ⋯ ^∃ p`, with `k` existential quantifiers. -/
noncomputable def qqExss (p k : V) : V := qqExss.construction.result ![p] k

@[simp] lemma qqExss_zero (p : V) : qqExss p 0 = p := by simp [qqExss, qqExss.construction]

@[simp] lemma qqExss_succ (p k : V) : qqExss p (k + 1) = ^∃ (qqExss p k) := by
  simp [qqExss, qqExss.construction]

def _root_.FFL.FirstOrder.Arithmetic.qqExssDef : 𝚺ᴬ₁.Semisentence 3 :=
  qqExss.blueprint.resultDef |>.rew (Rew.subst ![#0, #2, #1])

instance qqExss.defined : 𝚺ᴬ₁-Function₂ (qqExss : V → V → V) via qqExssDef := .mk
  fun v ↦ by simp [qqExss.construction.result_defined_iff, qqExssDef]; rfl

instance qqExss.definable : 𝚺ᴬ₁-Function₂ (qqExss : V → V → V) := qqExss.defined.to_definable

instance qqExss.definable' {Γ : Polarity} {m : ℕ} :
    Γᴬ_[m + 1]-Function₂ (qqExss : V → V → V) := qqExss.definable.of_sigmaOne

lemma qqExss_exs (p k : V) : qqExss (^∃ p) k = ^∃ (qqExss p k) := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih => rw [qqExss_succ, ih, qqExss_succ]

lemma qqExss_succ' (p k : V) : qqExss p (k + 1) = qqExss (^∃ p) k := by
  rw [qqExss_succ, qqExss_exs]

@[simp] lemma isUFormula_qqExss {p k : V} : IsUFormula L (qqExss p k) ↔ IsUFormula L p := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih => rw [qqExss_succ, IsUFormula.ex, ih]

lemma shift_qqExss {p : V} (hp : IsUFormula L p) (k : V) :
    shift L (qqExss p k) = qqExss (shift L p) k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih => rw [qqExss_succ, shift_exs (isUFormula_qqExss.mpr hp), ih, qqExss_succ]

lemma neg_qqAlls {p : V} (hp : IsUFormula L p) (k : V) :
    neg L (qqAlls p k) = qqExss (neg L p) k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    rw [qqAlls_succ, neg_all (isUFormula_qqAlls.mpr hp), ih, qqExss_succ]

lemma IsSemiformula.qqExss {n k p : V} (h : IsSemiformula L (n + k) p) :
    IsSemiformula L n (qqExss p k) := by
  induction k using ISigma1.pi1_succ_induction generalizing n
  · definability
  case zero => simpa using h
  case succ k ih =>
    rw [qqExss_succ, IsSemiformula.exs]
    exact ih (by rwa [add_right_comm, add_assoc])

lemma qqExss_inj {p q m n : V} (hp : ∀ a, p ≠ ^∃ a) (hq : ∀ a, q ≠ ^∃ a)
    (h : qqExss p m = qqExss q n) : m = n ∧ p = q := by
  induction m using ISigma1.pi1_succ_induction generalizing n
  · definability
  case zero =>
    rcases zero_or_succ n with rfl | ⟨n, rfl⟩
    · simpa using h
    · exact absurd (by simpa using h) (hp _)
  case succ m ih =>
    rcases zero_or_succ n with rfl | ⟨n, rfl⟩
    · exact absurd (by simpa using h.symm) (hq _)
    · obtain ⟨rfl, rfl⟩ := ih (by simpa using h)
      exact ⟨rfl, rfl⟩

end qqExss

/-! ## Instantiating the outermost quantifier of a block -/

/-- The vector `^#0, …, ^#(r - 1), t`. -/
lemma exists_vec_bvar_term (r t : V) :
    ∃ v, len v = r + 1 ∧ (∀ i < r, v.[i] = ^#i) ∧ v.[r] = t := by
  obtain ⟨v, hvl, hv₁, hvk⟩ := exists_vec_bvar_append (?[t] : V) r
  exact ⟨v, by simpa using hvl, hv₁, by simpa using hvk 0 (by simp)⟩

/-- Instantiating the outermost quantifier of `qqExss q r` with a closed term `t` instantiates the
outermost bound variable `^#r` of `q`, where `v` is the vector `^#0, …, ^#(r - 1), t`. -/
lemma substs1_qqExss {t q v r : V} (ht : IsSemiterm ℒₒᵣ 0 t) (hq : IsSemiformula ℒₒᵣ (r + 1) q)
    (hv : len v = r + 1) (hvb : ∀ i < r, v.[i] = ^#i) (hvr : v.[r] = t) :
    substs1 ℒₒᵣ t (qqExss q r) = qqExss (subst ℒₒᵣ v q) r := by
  induction r using ISigma1.pi1_succ_induction generalizing q v
  · definability
  case zero =>
    have : v = ?[t] := nth_ext' 1 (by simpa using hv) (by simp) (by
      intro i hi
      obtain rfl : i = 0 := by simpa using hi
      simpa using hvr)
    simp [substs1, this]
  case succ r ih =>
    obtain ⟨v', hv'l, hv'b, hv'r⟩ := exists_vec_bvar_term r t
    have hv'u : IsUTermVec ℒₒᵣ (r + 1) v' := by
      refine ⟨hv'l.symm, ?_⟩
      intro i hi
      rcases lt_or_eq_of_le (lt_succ_iff_le.mp hi) with hir | rfl
      · simp [hv'b i hir]
      · simpa [hv'r] using ht.isUTerm
    have hqv : qVec ℒₒᵣ v' = v := by
      apply nth_ext' (r + 1 + 1) (len_qVec hv'u) hv
      intro i hi
      rcases zero_or_succ i with rfl | ⟨i, rfl⟩
      · simp [qVec, hvb 0 (by simp)]
      · have hi : i < r + 1 := by simpa using hi
        rw [qVec, nth_adjoin_succ, hv'l, nth_termBShiftVec hv'u hi]
        rcases lt_or_eq_of_le (lt_succ_iff_le.mp hi) with hir | rfl
        · simp [hv'b i hir, hvb (i + 1) (by simpa using hir)]
        · rw [hv'r, termBShift_zero ht, hvr]
    rw [qqExss_succ', ih (by simpa using hq) hv'l hv'b hv'r, substs_ex hq.isUFormula, qqExss_exs,
      ← qqExss_succ, hqv]

end iteration

/-! ## Induction on one-variable formulas -/

section fvarInduction

lemma isSemitermVec_fvar_bvar (u : V) : IsSemitermVec L 2 1 (?[^&u, ^#(0 : V)] : V) :=
  IsSemitermVec.adjoin (IsSemitermVec.adjoin (IsSemitermVec.nil _) (by simp)) (by simp)

/-- Structural induction on one-variable formulas whose quantifier case instantiates the inner
bound variable with the free variable `^&(g (^∀ p))`. -/
lemma IsSemiformula.sigma1_induction_fvar {P : V → Prop} (hP : 𝚺ᴬ₁-Predicate P)
    {g : V → V} (hg : 𝚺ᴬ₁-Function₁ g)
    (hrel : ∀ k r v, L.IsRel k r → IsSemitermVec L k 1 v → P (^rel k r v))
    (hnrel : ∀ k r v, L.IsRel k r → IsSemitermVec L k 1 v → P (^nrel k r v))
    (hverum : P ^⊤) (hfalsum : P ^⊥)
    (hand : ∀ p q, IsSemiformula L 1 p → IsSemiformula L 1 q → P p → P q → P (p ^⋏ q))
    (hor : ∀ p q, IsSemiformula L 1 p → IsSemiformula L 1 q → P p → P q → P (p ^⋎ q))
    (hall : ∀ p, IsSemiformula L 2 p →
      P (Bootstrapping.subst L ?[^&(g (^∀ p)), ^#(0 : V)] p) → P (^∀ p))
    (hexs : ∀ p, IsSemiformula L 2 p →
      P (Bootstrapping.subst L ?[^&(g (^∃ p)), ^#(0 : V)] p) → P (^∃ p))
    {p : V} : IsSemiformula L 1 p → P p := by
  have hm : 𝚺ᴬ₁-Function₁[V] formulaComplexity L := inferInstance
  let f : V → V := fun p ↦ max p (Bootstrapping.subst L ?[^&(g p), ^#(0 : V)] (π₂ (p - 1)))
  have hf : 𝚺ᴬ₁-Function₁ f := by unfold f; definability
  apply measured_bounded_sigma1_order_induction hm hf ?_ ?_ p
  · definability
  intro p ih hp
  rcases IsSemiformula.case_iff.mp hp with
    (⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩
      | rfl | rfl
      | ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, p₂, h₁, h₂, rfl⟩
      | ⟨p₁, h₁, rfl⟩ | ⟨p₁, h₁, rfl⟩)
  · exact hrel _ _ _ hR hv
  · exact hnrel _ _ _ hR hv
  · exact hverum
  · exact hfalsum
  · have ih₁ : P p₁ :=
      ih p₁ (by simp only [le_sup_iff, f]; left; exact le_of_lt <| by simp)
          (by simp [h₁.isUFormula, h₂.isUFormula]) h₁
    have ih₂ : P p₂ :=
      ih p₂ (by simp only [le_sup_iff, f]; left; exact le_of_lt <| by simp)
          (by simp [h₁.isUFormula, h₂.isUFormula]) h₂
    exact hand _ _ h₁ h₂ ih₁ ih₂
  · have ih₁ : P p₁ :=
      ih p₁ (by simp only [le_sup_iff, f]; left; exact le_of_lt <| by simp)
          (by simp [h₁.isUFormula, h₂.isUFormula]) h₁
    have ih₂ : P p₂ :=
      ih p₂ (by simp only [le_sup_iff, f]; left; exact le_of_lt <| by simp)
          (by simp [h₁.isUFormula, h₂.isUFormula]) h₂
    exact hor _ _ h₁ h₂ ih₁ ih₂
  · have h₁ : IsSemiformula L 2 p₁ := by simpa [one_add_one_eq_two] using h₁
    have hw : IsSemitermVec L 2 1 (?[^&(g (^∀ p₁)), ^#(0 : V)] : V) :=
      isSemitermVec_fvar_bvar _
    have h₂ : IsSemiformula L 1 (Bootstrapping.subst L ?[^&(g (^∀ p₁)), ^#(0 : V)] p₁) :=
      h₁.subst hw
    have : P (Bootstrapping.subst L ?[^&(g (^∀ p₁)), ^#(0 : V)] p₁) :=
      ih (Bootstrapping.subst L ?[^&(g (^∀ p₁)), ^#(0 : V)] p₁)
        (by simp only [le_sup_iff, f]; right; simp [qqAll])
        (by simp [fomulaComplexity_substs h₁ hw, h₁.isUFormula]) h₂
    exact hall _ h₁ this
  · have h₁ : IsSemiformula L 2 p₁ := by simpa [one_add_one_eq_two] using h₁
    have hw : IsSemitermVec L 2 1 (?[^&(g (^∃ p₁)), ^#(0 : V)] : V) :=
      isSemitermVec_fvar_bvar _
    have h₂ : IsSemiformula L 1 (Bootstrapping.subst L ?[^&(g (^∃ p₁)), ^#(0 : V)] p₁) :=
      h₁.subst hw
    have : P (Bootstrapping.subst L ?[^&(g (^∃ p₁)), ^#(0 : V)] p₁) :=
      ih (Bootstrapping.subst L ?[^&(g (^∃ p₁)), ^#(0 : V)] p₁)
        (by simp only [le_sup_iff, f]; right; simp [qqExs])
        (by simp [fomulaComplexity_substs h₁ hw, h₁.isUFormula]) h₂
    exact hexs _ h₁ this

end fvarInduction

/-! ## Substitution, shift and implication -/

section substLemmas

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

lemma exists_map_qqConj {n : V} {f : V → V} [𝚺ᴬ₁-Function₁ f]
    (hand : ∀ p q, IsUFormula L p → IsUFormula L q → f (p ^⋏ q) = f p ^⋏ f q) (hverum : f ^⊤ = ^⊤)
    (ps : V) (hps : ∀ i < len ps, IsSemiformula L n ps.[i]) :
    ∃ qs, len qs = len ps ∧ (∀ i < len ps, qs.[i] = f ps.[i]) ∧ f (^⋀ ps) = ^⋀ qs := by
  revert hps
  induction ps using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => intro _; exact ⟨0, by simp [hverum]⟩
  case adjoin p ps ih =>
    intro hps
    have h₁ : IsSemiformula L n p := by simpa using hps 0 (by simp)
    have h₂ : ∀ i < len ps, IsSemiformula L n ps.[i] := fun i hi ↦ by
      simpa using hps (i + 1) (by simpa using hi)
    obtain ⟨qs, hlen, hq, hsh⟩ := ih h₂
    refine ⟨f p ∷ qs, by simp [hlen], fun i hi ↦ ?_, ?_⟩
    · rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
      · simp
      · simpa using hq i (by simpa using hi)
    · rw [qqConj_cons, qqConj_cons, hand p _ h₁.isUFormula (qqConj_semiformula.mpr h₂).isUFormula,
        hsh]

lemma shift_imp {n p q : V} (hp : IsSemiformula L n p) (hq : IsSemiformula L n q) :
    shift L (imp L p q) = imp L (shift L p) (shift L q) := by
  unfold imp
  rw [shift_or hp.isUFormula.neg hq.isUFormula, shift_neg hp]

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

lemma subst_eq_self_of_le {m k p w : V} (hp : IsSemiformula L m p) (hw : IsUTermVec L k w)
    (hk : m ≤ k) (H : ∀ i < m, w.[i] = ^#i) : subst L w p = p := by
  have h₁ : IsSemitermVec L m m (bvarVec 0 m) := IsSemitermVec.bvarVec (by simp)
  calc subst L w p = subst L (bvarVec 0 m) p := by
        apply subst_congr hp hw h₁.isUTerm hk le_rfl
        intro i hi
        rw [H i hi, nth_bvarVec _ _ _ hi, zero_add]
    _ = p := subst_eq_self hp h₁ fun i hi ↦ by rw [nth_bvarVec _ _ _ hi, zero_add]

lemma subst_imp {n m w p q : V} (hw : IsSemitermVec L n m w) (hp : IsSemiformula L n p)
    (hq : IsSemiformula L n q) : subst L w (imp L p q) = imp L (subst L w p) (subst L w q) := by
  unfold imp
  rw [substs_or hp.isUFormula.neg hq.isUFormula, substs_neg hp hw]

lemma subst_qqAlls_vec {k n m w v p : V} (hw : IsSemitermVec L n m w) (hp : IsUFormula L p)
    (hv : IsSemitermVec L (n + k) (m + k) v) (h₁ : ∀ i < k, v.[i] = ^#i)
    (h₂ : ∀ j < n, v.[k + j] = termSubst L (bvarVec k m) w.[j]) :
    subst L w (qqAlls p k) = qqAlls (subst L v p) k := by
  induction k using ISigma1.pi1_succ_induction generalizing p v
  · definability
  case zero =>
    have hvw : v = w := nth_ext' n (by simpa using hv.lh) hw.lh fun i hi ↦ by
      simpa [termSubst_bvarVec_zero (hw.nth hi)] using h₂ i hi
    rw [qqAlls_zero, qqAlls_zero, hvw]
  case succ k ih =>
    obtain ⟨v', hv', hv'₁, hv'₂⟩ := exists_vec_shift hw k
    have hqv : qVec L v' = v := by
      have hl : len (qVec L v') = len v := by rw [len_qVec hv'.isUTerm, hv.lh, add_assoc]
      refine nth_ext' (len v) hl rfl ?_
      intro i hi
      rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
      · rw [nth_qVec_zero, h₁ 0 (by simp)]
      · rcases lt_or_ge i k with hik | hik
        · rw [nth_qVec_succ hv'.isUTerm (lt_of_lt_of_le hik le_add_self), hv'₁ i hik,
            termBShift_bvar, h₁ (i + 1) (by simpa using hik)]
        · obtain ⟨j, rfl⟩ := exists_add_of_le hik
          have hj : j < n := by
            have e : n + (k + 1) = k + (n + 1) := by rw [← add_assoc, add_comm n k, add_assoc]
            rw [hv.lh, e, add_assoc k j 1] at hi
            exact (add_lt_add_iff_right 1).mp ((add_lt_add_iff_left k).mp hi)
          have hkj : k + j < n + k := by
            rw [add_comm n k]
            exact (add_lt_add_iff_left k).mpr hj
          rw [nth_qVec_succ hv'.isUTerm hkj, hv'₂ j hj, termBShift_termSubst_bvarVec k (hw.nth hj),
            show k + j + 1 = k + 1 + j by simp only [add_assoc, add_comm, add_left_comm], h₂ j hj]
    rw [qqAlls_succ' p k, qqAlls_succ' (subst L v p) k,
      ih (IsUFormula.all.mpr hp) hv' hv'₁ hv'₂, substs_all hp, hqv]

lemma isSemitermVec_of_fvar {w : V} (n : V) (hw : ∀ i < len w, ∃ x, w.[i] = ^&x) :
    IsSemitermVec L (len w) n w :=
  IsSemitermVec.iff.mpr ⟨rfl, fun i hi ↦ by obtain ⟨x, hx⟩ := hw i hi; simp [hx]⟩

lemma IsSemiterm.of_zero {n t : V} (ht : IsSemiterm L 0 t) : IsSemiterm L n t :=
  IsSemiterm.def.mpr ⟨(IsSemiterm.def.mp ht).1, (IsSemiterm.def.mp ht).2.trans (by simp)⟩

lemma substs1_subst_fvar_bvar {t u q : V} (ht : IsSemiterm L 0 t) (hq : IsSemiformula L 2 q) :
    substs1 L t (subst L ?[^&u, ^#(0 : V)] q) =
      substs1 L (^&u) (subst L ?[^#(0 : V), t] q) := by
  have h₁ : IsSemitermVec L 2 1 (?[^&u, ^#(0 : V)] : V) := isSemitermVec_fvar_bvar u
  have h₂ : IsSemitermVec L 1 0 (?[t] : V) := by simp [ht]
  have h₃ : IsSemitermVec L 2 1 (?[^#(0 : V), t] : V) := by
    simp [IsSemiterm.of_zero ht]
  have h₄ : IsSemitermVec L 1 1 (?[^&u] : V) := by simp
  have h₅ : termSubstVec L 2 (?[t] : V) (?[^&u, ^#(0 : V)] : V) =
      termSubstVec L 2 (?[^&u] : V) (?[^#(0 : V), t] : V) := by
    simp [termSubstVec_cons₂ (t₁ := ^#(0 : V)) (by simp) ht.isUTerm, termSubst_zero ht]
  unfold substs1
  rw [substs_substs hq h₂ h₁, substs_substs hq h₄ h₃, h₅]

lemma qVec_closed {t : V} (ht : IsSemiterm L 0 t) :
    qVec L (?[t] : V) = (?[^#(0 : V), t] : V) := by
  simp [qVec, len_adjoin, termBShift_zero ht, termBShiftVec_cons₁ ht.isUTerm]

lemma subst_iff {m w p q : V} (hp : IsSemiformula L 1 p) (hq : IsSemiformula L 1 q)
    (hw : IsSemitermVec L 1 m w) :
    subst L w (iff L p q) = iff L (subst L w p) (subst L w q) := by
  have hpq : IsUFormula L (neg L p ^⋎ q) := (IsSemiformula.imp.mpr ⟨hp, hq⟩).isUFormula
  have hqp : IsUFormula L (neg L q ^⋎ p) := (IsSemiformula.imp.mpr ⟨hq, hp⟩).isUFormula
  unfold iff imp
  rw [substs_and hpq hqp, substs_or hp.isUFormula.neg hq.isUFormula,
    substs_or hq.isUFormula.neg hp.isUFormula, substs_neg hp hw, substs_neg hq hw]

lemma substs1_and {t p q : V} (hp : IsSemiformula L 1 p) (hq : IsSemiformula L 1 q) :
    substs1 L t (p ^⋏ q) = substs1 L t p ^⋏ substs1 L t q := by
  unfold substs1
  exact substs_and hp.isUFormula hq.isUFormula

lemma substs1_or {t p q : V} (hp : IsSemiformula L 1 p) (hq : IsSemiformula L 1 q) :
    substs1 L t (p ^⋎ q) = substs1 L t p ^⋎ substs1 L t q := by
  unfold substs1
  exact substs_or hp.isUFormula hq.isUFormula

lemma pi2_qqAll_sub_one (q : V) : π₂ ((^∀ q) - 1) = q := by
  simp [qqAll]

lemma pi2_qqExs_sub_one (q : V) : π₂ ((^∃ q) - 1) = q := by
  simp [qqExs]

lemma shift_substs1_qqFvar {p j : V} (hp : IsSemiformula L 1 p) :
    shift L (substs1 L (^&j) p) = substs1 L (^&(j + 1)) (shift L p) := by
  have hv : IsSemitermVec L 1 (0 : V) ?[^&j] := by simp
  rw [substs1, shift_substs hp hv]
  congr 1
  apply nth_ext' 1 (by simp) (by simp)
  intro i hi
  rcases (show i = 0 by simpa using hi)
  simp

lemma shift_neg_substs1_qqFvar {d j : V} (hd : IsSemiformula L 1 d) (hds : shift L d = d) :
    shift L (neg L (substs1 L (^&j) d)) = neg L (substs1 L (^&(j + 1)) d) := by
  rw [shift_neg (IsSemiformula.substs1 (n := 0) (by simp) hd), shift_substs1_qqFvar hd, hds]

end substLemmas

end FFL.FirstOrder.Arithmetic.Bootstrapping
