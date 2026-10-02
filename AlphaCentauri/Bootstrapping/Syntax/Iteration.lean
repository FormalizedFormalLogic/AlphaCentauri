module

public import AlphaCentauri.Bootstrapping.Proof.FvSubst

/-!
# Blocks of universal quantifiers and vectors of bound variables

`bvarVec j k` is the vector of the bound variables `^#j, …, ^#(j + k - 1)`. The shift of free
variables passes through a block `qqAlls p k` of universal quantifiers, and so does the
substitution of terms without bound variables for its outermost bound variables.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

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
    Γᴬ-[m + 1]-Function₂ (bvarVec : V → V → V) := bvarVec_definable.of_sigmaOne

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

variable {L : Language} [L.Encodable] [L.LORDefinable]

lemma IsSemitermVec.bvarVec {j k n : V} (h : j + k ≤ n) : IsSemitermVec L k n (bvarVec j k) :=
  IsSemitermVec.iff.mpr ⟨by simp, fun i hi ↦ by
    rw [nth_bvarVec j k i hi, IsSemiterm.bvar]
    exact lt_of_lt_of_le (by simpa using hi) h⟩

end bvarVec

/-! ## Blocks of universal quantifiers -/

section qqAlls

variable {L : Language} [L.Encodable] [L.LORDefinable]

lemma shift_qqAlls {p : V} (hp : IsUFormula L p) (k : V) :
    shift L (qqAlls p k) = qqAlls (shift L p) k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih => rw [qqAlls_succ, shift_all (isUFormula_qqAlls.mpr hp), ih, qqAlls_succ]

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
    obtain ⟨v, hvl, hv⟩ := sigmaOne_skolem_vec
      (R := fun i y : V ↦ (i < k → y = ^#i) ∧ (k ≤ i → y = w.[i - k])) (by definability)
      (l := k + len w) (fun i _ ↦ by
        by_cases hi : i < k
        · exact ⟨^#i, fun _ ↦ rfl, fun h ↦ absurd hi (not_lt.mpr h)⟩
        · exact ⟨w.[i - k], fun h ↦ absurd h hi, fun _ ↦ rfl⟩)
    have hvk (j : V) (hj : j < len w) : v.[k + j] = w.[j] := by
      simpa using (hv (k + j) (by simpa using hj)).2 (by simp)
    have hvu : IsUTermVec L (len v) v := ⟨rfl, fun i hi ↦ by
      rcases lt_or_ge i k with hik | hik
      · simp [(hv i (hvl ▸ hi)).1 hik]
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
        · rw [(hv i (hvl ▸ hi')).1 hik, termBShift_bvar, h₁ (i + 1) (by simpa using hik)]
        · obtain ⟨j, rfl⟩ := exists_add_of_le hik
          have hj : j < len w := by simpa [hvl] using hi'
          rw [hvk j hj, termBShift_zero (hw.nth hj), ← h₂ j hj, add_right_comm]
    rw [qqAlls_succ', ih (by simpa using hp) hvl (fun i hi ↦ (hv i (by simp [lt_of_lt_of_le hi]
      )).1 hi) hvk, substs_all hp, ← qqAlls_succ', hqv]

lemma free_qqAlls {k w p : V} (hp : IsUFormula L p) (hl : len w = k + 1)
    (h₁ : ∀ i < k, w.[i] = ^#i) (h₂ : w.[k] = ^&0) :
    free L (qqAlls p k) = qqAlls (subst L w (shift L p)) k := by
  rw [free, substs1, shift_qqAlls hp]
  apply subst_qqAlls (by simp) hp.shift (by simpa using hl) h₁
  intro i hi
  obtain rfl : i = 0 := by simpa using hi
  simpa using h₂

end qqAlls

end FFL.FirstOrder.Arithmetic.Bootstrapping
