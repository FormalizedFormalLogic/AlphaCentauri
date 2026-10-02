module

public import AlphaCentauri.Bootstrapping.Proof.FvSubst

/-!
# Blocks of quantifiers and vectors of bound variables

`bvarVec j k` is the vector of the bound variables `^#j, …, ^#(j + k - 1)`. The shift of free
variables passes through a block `qqAlls p k` of universal quantifiers, and so does the
substitution of terms without bound variables for its outermost bound variables. `qqExss p k` is
the block of `k` existential quantifiers over `p`, the negation of `qqAlls`, and instantiating its
outermost quantifier by a closed term instantiates the outermost bound variable of `p`.
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


/-! ## Blocks of existential quantifiers -/

section qqExss

variable {L : Language} [L.Encodable] [L.LORDefinable]

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
    Γᴬ-[m + 1]-Function₂ (qqExss : V → V → V) := qqExss.definable.of_sigmaOne

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
  have h : ∀ i < r + 1, ∃ y : V, (i < r → y = ^#i) ∧ (r ≤ i → y = t) := by
    intro i _
    by_cases hi : i < r
    · exact ⟨^#i, fun _ ↦ rfl, fun h ↦ absurd hi (not_lt.mpr h)⟩
    · exact ⟨t, fun h ↦ absurd h hi, fun _ ↦ rfl⟩
  obtain ⟨v, hvl, hv⟩ := sigmaOne_skolem_vec (by definability) h
  exact ⟨v, hvl, fun i hi ↦ (hv i (lt_trans hi (by simp))).1 hi, (hv r (by simp)).2 le_rfl⟩

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

end FFL.FirstOrder.Arithmetic.Bootstrapping
